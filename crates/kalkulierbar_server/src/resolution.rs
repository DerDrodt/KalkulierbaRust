use actix_web::{error, web, HttpResponse, Responder, Result};
use kalkulierbar::{session, Calculus};

use crate::{MoveForm, ParseForm, StateForm};

pub(crate) async fn prop() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus prop-tableaux loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn prop_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::resolution::prop;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<prop::PropResParam> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = prop::PropResolution::parse_formula(&formula, params)
            .map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn prop_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::resolution::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::PropResState = serde_json::from_str(&state)?;
        let res = prop::PropResolution::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn prop_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::resolution::prop;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: prop::PropResState = serde_json::from_str(&state)?;
        let r#move: prop::PropResMove = serde_json::from_str(&r#move)?;

        let state =
            prop::PropResolution::apply_move(state, r#move).map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn prop_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::resolution::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::PropResState = serde_json::from_str(&state)?;

        let res = prop::PropResolution::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}
