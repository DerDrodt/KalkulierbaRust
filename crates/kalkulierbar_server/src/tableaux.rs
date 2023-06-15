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
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<prop::Params> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = prop::PropTableaux::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().body(serde_json::to_string(&state)?))
    })
}

pub(crate) async fn prop_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::State = serde_json::from_str(&state)?;
        let res = prop::PropTableaux::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn prop_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: prop::State = serde_json::from_str(&state)?;
        let r#move: prop::Move = serde_json::from_str(&r#move)?;

        let state = prop::PropTableaux::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn prop_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::State = serde_json::from_str(&state)?;

        let res = prop::PropTableaux::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn fo() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus fo-tableaux loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn fo_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::fo;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<fo::Params> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = fo::FOTableaux::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn fo_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::fo;

    session(|| {
        let StateForm { state } = form.0;

        let state: fo::State = serde_json::from_str(&state)?;
        let res = fo::FOTableaux::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn fo_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::fo;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: fo::State = serde_json::from_str(&state)?;
        let r#move: fo::Move = serde_json::from_str(&r#move)?;

        let state = fo::FOTableaux::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn fo_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::fo;

    session(|| {
        let StateForm { state } = form.0;

        let state: fo::State = serde_json::from_str(&state)?;

        let res = fo::FOTableaux::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn nc() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus nc-tableaux loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn nc_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::nc;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<()> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = nc::NCTableaux::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn nc_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::nc;

    session(|| {
        let StateForm { state } = form.0;

        let state: nc::State = serde_json::from_str(&state)?;
        let res = nc::NCTableaux::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn nc_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::nc;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: nc::State = serde_json::from_str(&state)?;
        let r#move: nc::Move = serde_json::from_str(&r#move)?;

        let state = nc::NCTableaux::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn nc_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::nc;

    session(|| {
        let StateForm { state } = form.0;

        let state: nc::State = serde_json::from_str(&state)?;

        let res = nc::NCTableaux::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn modal() -> impl Responder {
    HttpResponse::Ok().body(
        "Calculus signed-modal-tableaux loaded.
Interact via the /parse /move /close and /validate endpoints"
            .to_string(),
    )
}

pub(crate) async fn modal_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::modal;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<modal::SignedModalTabParams> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = modal::SignedModalTableaux::parse_formula(&formula, params)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn modal_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::modal;

    session(|| {
        let StateForm { state } = form.0;

        let state: modal::State = serde_json::from_str(&state)?;
        let res = modal::SignedModalTableaux::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

pub(crate) async fn modal_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::modal;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: modal::State = serde_json::from_str(&state)?;
        let r#move: modal::Move = serde_json::from_str(&r#move)?;

        let state = modal::SignedModalTableaux::apply_move(state, r#move)
            .map_err(|e| error::ErrorBadRequest(e.to_string()))?;

        Ok(HttpResponse::Ok().json(state))
    })
}

pub(crate) async fn modal_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::modal;

    session(|| {
        let StateForm { state } = form.0;

        let state: modal::State = serde_json::from_str(&state)?;

        let res = modal::SignedModalTableaux::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}
