use actix_web::{web, App, HttpResponse, HttpServer, Responder};

use serde::Deserialize;

mod dpll;
mod resolution;
mod sequent;
mod tableaux;

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

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .wrap(
                actix_web::middleware::DefaultHeaders::new()
                    .header("Access-Control-Allow-Origin", "*"),
            )
            .route("/", web::get().to(index))
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
    })
    .bind("127.0.0.1:7000")?
    .run()
    .await
}
