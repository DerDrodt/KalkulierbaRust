use actix_web::{error, web, HttpResponse, Responder, Result};
use kalkulierbar::{session, Calculus};

use crate::{MoveForm, ParseForm, StateForm};

pub(crate) async fn dpll() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus dpll loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::dpll;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<()> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = dpll::DPLL::parse_formula(&formula, params).map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::dpll;

    session(|| {
        let StateForm { state } = form.0;

        let state: dpll::DPLLState = serde_json::from_str(&state)?;
        let res = dpll::DPLL::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn r#move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::dpll;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: dpll::DPLLState = serde_json::from_str(&state)?;
        let r#move: dpll::DPLLMove = serde_json::from_str(&r#move)?;

        let state = dpll::DPLL::apply_move(state, r#move).map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::dpll;

    session(|| {
        let StateForm { state } = form.0;

        let state: dpll::DPLLState = serde_json::from_str(&state)?;

        let res = dpll::DPLL::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}
