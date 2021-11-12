//! Pure type system type-checking algorithm.

use std::rc::Rc;

use crate::{
    ast::{self, Def, TermEnum},
    env::PureTypeSystem,
    Binding, Env, Id, Term, TypeCheckError,
};

/// Returns a term in normal form.
pub fn type_check(env: &Env, term: &Term) -> Result<Term, TypeCheckError> {
    match term.inner() {
        TermEnum::Constant(c) => env.system.get_constant_type(c),
        TermEnum::Variable(id) => Ok(env
            .get(id)
            .ok_or_else(|| TypeCheckError::UndeclaredVar(id.clone()))?
            .ty
            .clone()),
        TermEnum::Lambda(param, param_ty, body) => {
            let param_sort = type_check(env, param_ty)?;
            let param_ty = env.eval(param_ty)?;

            let body_env = env.with_param(param.clone(), param_ty.clone());
            let body_ty = type_check(&body_env, body)?;
            let body_sort = type_check(&body_env, &body_ty)?;
            get_function_sort(env, term, &param_ty, param_sort, &body_ty, body_sort)?;
            Ok(ast::pi(param, param_ty, body_ty))
        }
        TermEnum::Pi(param, param_ty, body_ty) => {
            let param_sort = type_check(env, param_ty)?;
            let body_sort = type_check(&env.with_param(param, param_ty.clone()), body_ty)?;
            let fn_sort = get_function_sort(env, term, param_ty, param_sort, body_ty, body_sort)?;
            Ok(ast::constant(fn_sort))
        }
        TermEnum::Apply(fun, arg) => {
            let fun_ty = type_check(env, fun)?;
            let arg_ty = type_check(env, arg)?;
            if let TermEnum::Pi(param, param_ty, body_ty) = fun_ty.inner() {
                check_judgmental_eq(&env.system, &arg_ty, param_ty)?;
                env.with(
                    param,
                    Binding {
                        ty: arg_ty,
                        def: Some(arg.clone()),
                    },
                )
                .eval(body_ty)
            } else {
                Err(TypeCheckError::FunctionExpected(
                    term.clone(),
                    fun.clone(),
                    fun_ty,
                ))
            }
        }
        TermEnum::Subst(id, binding, body) => type_check(&env.with(id, binding.clone()), body),
    }
}

fn get_function_sort<'env>(
    env: &'env Env,
    term: &Term,
    param_ty: &Term,
    param_sort: Term,
    body_ty: &Term,
    body_sort: Term,
) -> Result<&'env Id, TypeCheckError> {
    use TypeCheckError::*;

    let is_pi = matches!(term.inner(), TermEnum::Pi(..));

    let param_sort = match param_sort.inner() {
        TermEnum::Constant(c) => c,
        _ => {
            let err = if is_pi {
                InvalidPiParameterType
            } else {
                InvalidLambdaParameterType
            };

            return Err(err(term.clone(), param_ty.clone()));
        }
    };

    let body_sort = match body_sort.inner() {
        TermEnum::Constant(c) => c,
        _ => {
            let err = if is_pi {
                InvalidPiReturnType
            } else {
                InvalidLambdaParameterType
            };
            return Err(err(term.clone(), body_ty.clone()));
        }
    };

    env.system
        .get_function_sort(param_sort, body_sort)
        .ok_or_else(|| {
            let err = if is_pi {
                InvalidPiSorts
            } else {
                InvalidLambdaSorts
            };
            err(term.clone(), param_sort.clone(), body_sort.clone())
        })
}

/// a and b must already be in normal form. No free variables with known
/// definitions.
///
/// Unfortunately normal form means inlining all function calls. I'm sure this
/// isn't how real systems work. There's a more efficient way to do this that
/// also doesn't require them to be in normal form first. It would involve
/// environments.
pub(crate) fn check_judgmental_eq(
    system: &Rc<PureTypeSystem>,
    a: &Term,
    b: &Term,
) -> Result<(), TypeCheckError> {
    match (a.inner(), b.inner()) {
        (TermEnum::Constant(c), TermEnum::Constant(d)) if *c == *d => Ok(()),
        (TermEnum::Variable(a), TermEnum::Variable(b)) if *a == *b => Ok(()),
        (TermEnum::Lambda(v1, t1, b1), TermEnum::Lambda(v2, t2, b2)) => {
            check_judgmental_eq(system, t1, t2)?;
            if *v1 == *v2 {
                check_judgmental_eq(system, b1, b2)
            } else {
                let env = Env::new(Rc::clone(system)).with(
                    v2,
                    Binding {
                        ty: t2.clone(),
                        def: Some(ast::var(v1)),
                    },
                );
                let b2 = env.eval(b2)?;
                check_judgmental_eq(system, b1, &b2)
            }
        }
        (TermEnum::Pi(v1, t1, b1), TermEnum::Pi(v2, t2, b2)) => check_judgmental_eq(
            system,
            &ast::lambda(v1, t1.clone(), b1.clone()),
            &ast::lambda(v2, t2.clone(), b2.clone()),
        ),
        (TermEnum::Apply(f, a), TermEnum::Apply(g, b)) => {
            check_judgmental_eq(system, f, g)?;
            check_judgmental_eq(system, a, b)
        }
        _ => Err(TypeCheckError::UnifyMismatch(a.clone(), b.clone())),
    }
}

pub fn type_check_program(env: &Env, program: &[Def]) -> Result<Env, TypeCheckError> {
    program.iter().try_fold(env.clone(), |env, def| {
        let def_ty = def
            .ty
            .as_ref()
            .ok_or_else(|| TypeCheckError::MissingType(def.id.clone()))?;
        let def_ty = env.eval(def_ty)?;
        type_check(&env, &def_ty)?;

        let def_term = match &def.term {
            None => None,
            Some(term) => {
                let actual_ty = type_check(&env, term)?;
                check_judgmental_eq(&env.system, &actual_ty, &def_ty)?;
                Some(env.eval(term)?)
            }
        };
        let binding = Binding {
            ty: def_ty,
            def: def_term,
        };
        Ok(env.with(def.id.clone(), binding))
    })
}
