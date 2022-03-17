use actix_web::{error, web, HttpResponse, Responder, Result};
use kalkulierbar::{session, Calculus};

use crate::{MoveForm, ParseForm, StateForm};

pub(crate) async fn prop() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus prop-sequent loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn prop_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, prop};

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<sequent::SequentParams> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = prop::PropSequent::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn prop_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, prop};

    session(|| {
        let StateForm { state } = form.0;

        let state: sequent::SequentState<prop::PropSeqMove> = serde_json::from_str(&state)?;
        let res = prop::PropSequent::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn prop_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, prop};

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: sequent::SequentState<prop::PropSeqMove> = serde_json::from_str(&state)?;
        let r#move: prop::PropSeqMove = serde_json::from_str(&r#move)?;

        let state = prop::PropSequent::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn prop_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, prop};

    session(|| {
        let StateForm { state } = form.0;

        let state: sequent::SequentState<prop::PropSeqMove> = serde_json::from_str(&state)?;

        let res = prop::PropSequent::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn fo() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus prop-sequent loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn fo_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, fo};

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<sequent::SequentParams> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = fo::FOSequent::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn fo_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, fo};

    session(|| {
        let StateForm { state } = form.0;

        let state: sequent::SequentState<fo::FOSeqMove> = serde_json::from_str(&state)?;
        let res = fo::FOSequent::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn fo_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, fo};

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: sequent::SequentState<fo::FOSeqMove> = serde_json::from_str(&state)?;
        let r#move: fo::FOSeqMove = serde_json::from_str(&r#move)?;

        let state = fo::FOSequent::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn fo_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::sequent::{self, fo};

    session(|| {
        let StateForm { state } = form.0;

        let state: sequent::SequentState<fo::FOSeqMove> = serde_json::from_str(&state)?;

        let res = fo::FOSequent::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}
