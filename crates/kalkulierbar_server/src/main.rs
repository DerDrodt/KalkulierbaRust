use std::env;

use actix_web::http::{header, StatusCode};
use actix_web::middleware::{ErrorHandlerResponse, ErrorHandlers, Logger};
use actix_web::{dev, error, web, App, HttpResponse, HttpServer, Responder, Result};
use env_logger::Env;

use kalkulierbar::CalculusKind;
use serde::Deserialize;

use crate::statekeeper::StateKeeper;

mod dpll;
mod resolution;
mod sequent;
mod tableaux;

mod statekeeper;

#[macro_use]
extern crate lazy_static;

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

#[derive(Deserialize)]
struct CheckCredForm {
    mac: String,
}

#[derive(Deserialize)]
struct SetCalculusForm {
    calculus: CalculusKind,
    enable: bool,
    mac: String,
}

#[derive(Deserialize)]
struct AddExampleForm {
    example: String,
    mac: String,
}

#[derive(Deserialize)]
struct DelExampleForm {
    #[serde(rename = "exampleID")]
    example_id: usize,
    mac: String,
}

fn add_error_header<B>(mut res: dev::ServiceResponse<B>) -> Result<ErrorHandlerResponse<B>> {
    res.response_mut().headers_mut().insert(
        header::CONTENT_TYPE,
        header::HeaderValue::from_static("Error"),
    );

    Ok(ErrorHandlerResponse::Response(res.map_into_left_body()))
}

async fn index() -> impl Responder {
    HttpResponse::Ok().body(
        "KalkulierbaR API Server

Available calculus endpoints:
prop-tableaux",
    )
}

pub(crate) async fn config(s_keeper: web::Data<StateKeeper>) -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(&s_keeper.get_config()))
}

pub(crate) async fn check_creds(
    form: web::Form<CheckCredForm>,
    s_keeper: web::Data<StateKeeper>,
) -> Result<HttpResponse> {
    let CheckCredForm { mac } = form.0;

    let res = s_keeper
        .check_credentials(&mac)
        .map_err(error::ErrorBadRequest)?;

    Ok(HttpResponse::Ok().json(res))
}

pub(crate) async fn set_calculus_state(
    form: web::Form<SetCalculusForm>,
    s_keeper: web::Data<StateKeeper>,
) -> Result<HttpResponse> {
    let SetCalculusForm {
        calculus,
        enable,
        mac,
    } = form.0;

    let res = s_keeper
        .set_calculus_state(calculus, enable, &mac)
        .map_err(error::ErrorBadRequest)?;

    Ok(HttpResponse::Ok().json(res))
}

pub(crate) async fn add_example(
    form: web::Form<AddExampleForm>,
    s_keeper: web::Data<StateKeeper>,
) -> Result<HttpResponse> {
    let AddExampleForm { example, mac } = form.0;

    let res = s_keeper
        .add_example(serde_json::from_str(&example)?, &example, &mac)
        .map_err(error::ErrorBadRequest)?;

    Ok(HttpResponse::Ok().json(res))
}

pub(crate) async fn del_example(
    form: web::Form<DelExampleForm>,
    s_keeper: web::Data<StateKeeper>,
) -> Result<HttpResponse> {
    let DelExampleForm { example_id, mac } = form.0;

    let res = s_keeper
        .remove_example(example_id, &mac)
        .map_err(error::ErrorBadRequest)?;

    Ok(HttpResponse::Ok().json(res))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    let port: u16 = env::var("PATH").unwrap_or_default().parse().unwrap_or(7000);
    let listen_globally = env::args().any(|a| a == "-g" || a == "--global");
    let host = if listen_globally {
        "0.0.0.0"
    } else {
        "localhost"
    };

    env_logger::init_from_env(Env::default().default_filter_or("info"));

    HttpServer::new(|| {
        App::new()
            .wrap(
                actix_web::middleware::DefaultHeaders::new()
                    .add(("Access-Control-Allow-Origin", "*")),
            )
            .wrap(Logger::default())
            //.wrap(Logger::new("%a %{User-Agent}i"))
            .wrap(ErrorHandlers::new().handler(StatusCode::INTERNAL_SERVER_ERROR, add_error_header))
            .route("/", web::get().to(index))
            .route("/config", web::get().to(config))
            .route("/admin/checkCredentials", web::get().to(check_creds))
            .route("/admin/setCalculusState", web::get().to(set_calculus_state))
            .route("/admin/addExample", web::get().to(add_example))
            .route("/admin/delExample", web::get().to(del_example))
            // Prop Tableaux
            .route("/prop-tableaux", web::get().to(tableaux::prop))
            .route("/prop-tableaux/parse", web::post().to(tableaux::prop_parse))
            .route(
                "/prop-tableaux/validate",
                web::post().to(tableaux::prop_validate),
            )
            .route("/prop-tableaux/move", web::post().to(tableaux::prop_move))
            .route("/prop-tableaux/close", web::post().to(tableaux::prop_close))
            // FO Tableaux
            .route("/fo-tableaux", web::get().to(tableaux::fo))
            .route("/fo-tableaux/parse", web::post().to(tableaux::fo_parse))
            .route(
                "/fo-tableaux/validate",
                web::post().to(tableaux::fo_validate),
            )
            .route("/fo-tableaux/move", web::post().to(tableaux::fo_move))
            .route("/fo-tableaux/close", web::post().to(tableaux::fo_close))
            // Prop Resolution
            .route("/prop-resolution", web::get().to(resolution::prop))
            .route(
                "/prop-resolution/parse",
                web::post().to(resolution::prop_parse),
            )
            .route(
                "/prop-resolution/validate",
                web::post().to(resolution::prop_validate),
            )
            .route(
                "/prop-resolution/move",
                web::post().to(resolution::prop_move),
            )
            .route(
                "/prop-resolution/close",
                web::post().to(resolution::prop_close),
            )
            // FO Resolution
            .route("/fo-resolution", web::get().to(resolution::fo))
            .route("/fo-resolution/parse", web::post().to(resolution::fo_parse))
            .route(
                "/fo-resolution/validate",
                web::post().to(resolution::fo_validate),
            )
            .route("/fo-resolution/move", web::post().to(resolution::fo_move))
            .route("/fo-resolution/close", web::post().to(resolution::fo_close))
            // DPLL
            .route("/dpll", web::get().to(dpll::dpll))
            .route("/dpll/parse", web::post().to(dpll::parse))
            .route("/dpll/validate", web::post().to(dpll::validate))
            .route("/dpll/move", web::post().to(dpll::r#move))
            .route("/dpll/close", web::post().to(dpll::close))
            // Non-clausal Tableaux
            .route("/nc-tableaux", web::get().to(tableaux::nc))
            .route("/nc-tableaux/parse", web::post().to(tableaux::nc_parse))
            .route(
                "/nc-tableaux/validate",
                web::post().to(tableaux::nc_validate),
            )
            .route("/nc-tableaux/move", web::post().to(tableaux::nc_move))
            .route("/nc-tableaux/close", web::post().to(tableaux::nc_close))
            // Prop Sequent
            .route("/prop-sequent", web::get().to(sequent::prop))
            .route("/prop-sequent/parse", web::post().to(sequent::prop_parse))
            .route(
                "/prop-sequent/validate",
                web::post().to(sequent::prop_validate),
            )
            .route("/prop-sequent/move", web::post().to(sequent::prop_move))
            .route("/prop-sequent/close", web::post().to(sequent::prop_close))
            // FO Sequent
            .route("/fo-sequent", web::get().to(sequent::fo))
            .route("/fo-sequent/parse", web::post().to(sequent::fo_parse))
            .route("/fo-sequent/validate", web::post().to(sequent::fo_validate))
            .route("/fo-sequent/move", web::post().to(sequent::fo_move))
            .route("/fo-sequent/close", web::post().to(sequent::fo_close))
            // Modal Tableaux
            .route("/signed-modal-tableaux", web::get().to(tableaux::modal))
            .route(
                "/signed-modal-tableaux/parse",
                web::get().to(tableaux::modal_parse),
            )
            .route(
                "/signed-modal-tableaux/validate",
                web::get().to(tableaux::modal_validate),
            )
            .route(
                "/signed-modal-tableaux/move",
                web::get().to(tableaux::modal_move),
            )
            .route(
                "/signed-modal-tableaux/close",
                web::get().to(tableaux::modal_close),
            )
            // App data
            .app_data(StateKeeper::new())
    })
    .bind((host, port))?
    .run()
    .await
}
