use std::error::Error;


pub fn box_dyn_error(s: &str) -> Box<dyn Error> {
    let err: Box<dyn Error> = String::from(s).into();
    err
}
