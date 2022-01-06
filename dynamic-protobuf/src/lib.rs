use dynamic::SmolStr;
use thiserror::Error;

mod descriptors;
mod message;
mod view;
pub use descriptors::*;
pub use message::*;
pub use view::*;

#[cfg(test)]
mod tests;

#[derive(Error, Debug)]
pub enum Error {
    #[error("missing descriptor")]
    MissingDescriptor,
    #[error("prost decode error {0}")]
    ProstDecode(#[from] prost::DecodeError),
    #[error("decode error {0}")]
    Decode(SmolStr),
    #[error("unimplemented")]
    Unimplemented,
    #[error("incorrect type (expected {expected:?}, found {found:?})")]
    IncorrectType { expected: SmolStr, found: SmolStr },
    #[error("{0}")]
    Dynamic(#[from] dynamic::Error),
    #[error("utf8 error")]
    Utf8(#[from] std::str::Utf8Error),
}
