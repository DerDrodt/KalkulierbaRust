use actix_web::{web, App, HttpResponse, HttpServer, Responder};

use serde::Deserialize;

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
            .route("/prop-tableaux", web::get().to(tableaux::prop))
            .route("/prop-tableaux/parse", web::post().to(tableaux::prop_parse))
            .route(
                "/prop-tableaux/validate",
                web::post().to(tableaux::prop_validate),
            )
            .route("/prop-tableaux/move", web::post().to(tableaux::prop_move))
            .route("/prop-tableaux/close", web::post().to(tableaux::prop_close))
            .route("/fo-tableaux", web::get().to(tableaux::fo))
            .route("/fo-tableaux/parse", web::post().to(tableaux::fo_parse))
            .route(
                "/fo-tableaux/validate",
                web::post().to(tableaux::fo_validate),
            )
            .route("/fo-tableaux/move", web::post().to(tableaux::fo_move))
            .route("/fo-tableaux/close", web::post().to(tableaux::fo_close))
    })
    .bind("127.0.0.1:7000")?
    .run()
    .await
}
