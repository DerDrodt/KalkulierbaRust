use actix_web::{error, web, App, HttpResponse, HttpServer, Responder, Result};
use kalkulierbar::{session, Calculus};
use serde::Deserialize;

#[derive(Deserialize)]
struct ParseForm {
    formula: String,
    params: Option<String>,
}

#[derive(Deserialize)]
struct StateForm {
    state: String,
}

#[derive(Deserialize)]
struct MoveForm {
    state: String,
    r#move: String,
}

async fn index() -> impl Responder {
    HttpResponse::Ok().body(
        "KalkulierbaR API Server

Available calculus endpoints:
prop-tableaux",
    )
}

async fn prop_tableaux() -> impl Responder {
    HttpResponse::Ok().body("Calculus prop-tableaux loaded.
Interact via the /parse /move /close and /validate endpoints".to_string())
}

async fn prop_tableaux_parse(form: web::Form<ParseForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let ParseForm { formula, params } = form.0;
        let params: Option<prop::PropTableauxParams> = match params {
            Some(p) => Some(serde_json::from_str(&p)?),
            None => None,
        };

        let state = prop::PropTableaux::parse_formula(&formula, params)
            .map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

async fn prop_tableaux_validate(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::PropTableauxState = serde_json::from_str(&state)?;
        let res = prop::PropTableaux::validate(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

async fn prop_tableaux_move(form: web::Form<MoveForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let MoveForm { state, r#move } = form.0;

        let state: prop::PropTableauxState = serde_json::from_str(&state)?;
        let r#move: prop::PropTableauxMove = serde_json::from_str(&r#move)?;

        let state =
            prop::PropTableaux::apply_move(state, r#move).map_err(error::ErrorBadRequest)?;

        Ok(HttpResponse::Ok().json(state))
    })
}

async fn prop_tableaux_close(form: web::Form<StateForm>) -> Result<HttpResponse> {
    use kalkulierbar::calculi::tableaux::prop;

    session(|| {
        let StateForm { state } = form.0;

        let state: prop::PropTableauxState = serde_json::from_str(&state)?;

        let res = prop::PropTableaux::check_close(state);

        Ok(HttpResponse::Ok().json(res))
    })
}

#[actix_rt::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .wrap(
                actix_web::middleware::DefaultHeaders::new()
                    .header("Access-Control-Allow-Origin", "*"),
            )
            .route("/", web::get().to(index))
            .route("/prop-tableaux", web::get().to(prop_tableaux))
            .route("/prop-tableaux/parse", web::post().to(prop_tableaux_parse))
            .route(
                "/prop-tableaux/validate",
                web::post().to(prop_tableaux_validate),
            )
            .route("/prop-tableaux/move", web::post().to(prop_tableaux_move))
            .route("/prop-tableaux/close", web::post().to(prop_tableaux_close))
    })
    .bind("127.0.0.1:7000")?
    .run()
    .await
}
