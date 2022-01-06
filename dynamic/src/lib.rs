//! Dynamic provides reflection for virtually any Rust type. It does this through a set of traits,
//! and type-erasing enums.
//!
//! We allow the user to store any type, regardless of lifetime, through a trait called [`Instance`].
//! [`Instance`] has a lifetime attached to it,
//! that outlives the lifetime of any type it downcasts to.
//! This ensures that lifetime guarantee are maintained at compile-time.
//! Much like [`std::any::Any`], we perform runtime type-checks to ensure type-safety.
//!
//! Generally it is best to use the derive macros from [`dynamic_derive`]
//! to implement the various traits here,
//! as care must be taken when implementing them to not enable
//! undefined behaviour. Check out the docs for [`Value`], [`StructInstance`], [`VecInstance`],
//! [`OptionInstance`], and [`EnumInstance`] for
//!
//!
//! # Examples
//!
//! ## Struct reflection
//!
//! ```
//! use dynamic::Typed;
//! use dynamic_derive::Instance;
//!
//! #[derive(Instance, Clone, PartialEq)]
//! struct Foo {
//!  text: String,
//!  int: i32,
//! }
//!
//! let test = Foo { text: "Test".to_string(), int: -2 };
//! let val = test.as_value();
//! let inst = val.as_reflected_struct().unwrap();
//! let value  = inst.get_value("text").expect("field not found");
//! let text = value.as_ref().borrow::<&String>().expect("borrow failed");
//! assert_eq!(text, &test.text);
//! ```
//!
//! ## Vec reflection
//!
//! ```
//! use dynamic::{Typed, VecInstance};
//!
//! let vec = vec!["test".to_string(), "123".to_string(), "foo".to_string()];
//! let first = vec.get_value(0).expect("get value failed");
//! assert_eq!(first, "test".to_string().as_value());
//! ```
//!
//! # Safety Details
//!
//! We can't use [`std::any::TypeId`], like [`std::any::Any`] does.
//! So instead we create an enum called [`ValueTy`] that describes the reflected type.
//! [`ValueTy`] internally stores the [`std::any::TypeId`] of a type.
//! For types with generic lifetimes (or non-static lifetimes) we require that the implementer
//! return the [`std::any::TypeId`] of the static version of that type.
//! Imagine a struct defined like: `struct Foo<'a>(&'a str)`.
//! The [`ValueTy`] for this type would be constructed like so:
//!
//! ```
//! # use dynamic::ValueTy;
//! # struct Foo<'a>(&'a str);
//!
//! let _ = ValueTy::Struct(std::any::TypeId::of::<Foo<'static>>());
//! ```
//!
//! [`dynamic_derive`]: ../dynamic_derive/index.html
pub use bytes::Bytes;
pub use smol_str::SmolStr;
use std::any::TypeId;
use thiserror::Error;

mod field_mask;
mod instance;
mod owned;
mod primatives;
mod typed;
mod value;

pub use field_mask::*;
pub use instance::*;
pub use owned::*;
pub use primatives::*;
pub use typed::*;
pub use value::*;

#[cfg(test)]
mod tests;

#[derive(Error, Debug)]
pub enum Error {
    #[error("{0} not found")]
    NotFound(SmolStr),
    #[error("type error expected {expected} found {found}")]
    TypeError { expected: SmolStr, found: SmolStr },
}

/// A trait for types that are stored directly in [`Value`].
///
/// This is implemented for various primitives, and generally shouldn't
/// be implemented for our own types
pub trait FromValue<'a, 's>: Sized {
    fn from_value(value: &Value<'a, 's>) -> Option<Self>;
}

/// A ext trait for [`dynamic_derive`] meant to consume a [`OwnedValue`] and return `T`
///
/// [`dynamic_derive`]: ../dynamic_derive
pub trait IntoInner<T> {
    fn into_inner(self) -> Result<T, Error>;
}

impl<'val, 'ty, 'r, T: Typed<'ty> + Sized + 'ty> FromValue<'val, 'ty> for &'r T
where
    'val: 'r,
    'ty: 'val,
{
    fn from_value(value: &Value<'val, 'ty>) -> Option<Self> {
        match value.0 {
            ValueInner::String(s) => s.as_inst().downcast_ref::<T>(),
            ValueInner::Bytes(b) => b.as_inst().downcast_ref::<T>(),
            ValueInner::Vec(v) => v.as_inst().downcast_ref::<T>(),
            ValueInner::Struct(s) => s.as_inst().downcast_ref::<T>(),
            ValueInner::Enum(s) => s.as_inst().downcast_ref::<T>(),
            ValueInner::Option(s) => s.as_inst().downcast_ref::<T>(),
            _ => None,
        }
    }
}

/// A trait for types that are stored directly in [`Value`].
///
/// This is implemented for various primitives, and generally shouldn't
/// be implemented for our own types
pub trait IntoValue {
    fn into_value<'val, 'ty>(self) -> Value<'val, 'ty>;
}

impl<'ty, T: Instance<'ty> + Typed<'ty> + 'ty> IntoInner<T> for OwnedValue<'ty> {
    fn into_inner(self) -> Result<T, Error> {
        let inst = match self {
            OwnedValue::Vec(s) => s.into_boxed_instance(),
            OwnedValue::Enum(s) => s.into_boxed_instance(),
            OwnedValue::Struct(s) => s.into_boxed_instance(),
            OwnedValue::Option(s) => s.into_boxed_instance(),
            OwnedValue::String(s) => Box::new(s),
            OwnedValue::Bytes(s) => Box::new(s),
            _ => {
                return Err(Error::TypeError {
                    expected: "instance".into(),
                    found: format!("{:?}", self).into(),
                });
            }
        };
        let inst = inst.downcast::<T>().ok_or_else(|| Error::TypeError {
            expected: "instance".into(),
            found: "other".into(),
        })?;
        Ok(*inst)
    }
}

impl<'val, 'ty> FromValue<'val, 'ty> for &'val (dyn OptionInstance<'ty> + 'ty) {
    //This lifetime bound could be better
    fn from_value(value: &Value<'val, 'ty>) -> Option<Self> {
        if let ValueInner::Option(o) = value.0 {
            Some(o)
        } else {
            None
        }
    }
}

impl<'val, 'ty> FromValue<'val, 'ty> for &'val str {
    fn from_value(value: &Value<'val, 'ty>) -> Option<&'val str> {
        if let ValueInner::Str(s) = value.0 {
            Some(s)
        } else {
            None
        }
    }
}

/// A description of a reflected type
#[derive(Clone, PartialEq, Debug)]
pub enum ValueTy {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Bool,
    Str,
    String,
    Bytes,
    VecInstance,
    Vec(Box<ValueTy>),
    StructInstance,
    Struct(TypeId),
    Enum(TypeId),
    Option(Box<ValueTy>),
}

impl<'ty, T: Typed<'ty> + Clone + 'ty> Instance<'ty> for Option<T> {
    fn name(&self) -> SmolStr {
        format!("Option<{:?}>", T::ty()).into()
    }

    fn as_inst(&self) -> &(dyn Instance<'ty> + 'ty) {
        self
    }
}

impl<'ty, T: Typed<'ty> + Clone + 'ty> OptionInstance<'ty> for Option<T> {
    fn value<'val>(&'val self) -> Option<Value<'val, 'ty>>
    where
        'ty: 'val,
    {
        self.as_ref().map(|val| val.as_value())
    }

    fn boxed_clone(&self) -> Box<dyn OptionInstance<'ty> + 'ty> {
        Box::new(self.clone())
    }

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'ty> + 'ty> {
        self
    }
}
