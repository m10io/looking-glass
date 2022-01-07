use crate::*;
pub use bytes::Bytes;
pub use smol_str::SmolStr;

/// Any type that can be contained in a [`Value`]
///
/// [`Typed`] needs to be implemented for any primatives including in a relected instance, and
/// any reflected struct or enum.
pub trait Typed<'ty>: Send + Sync {
    fn ty() -> ValueTy;

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val;
}

impl<'ty> Typed<'ty> for str {
    fn ty() -> ValueTy {
        ValueTy::Str
    }

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val,
    {
        Value(ValueInner::Str(self))
    }
}

impl<'ty> Typed<'ty> for String {
    fn ty() -> ValueTy {
        ValueTy::String
    }

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val,
    {
        Value(ValueInner::String(self))
    }
}

impl<'ty> Typed<'ty> for Bytes {
    fn ty() -> ValueTy {
        ValueTy::Bytes
    }

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val,
    {
        Value(ValueInner::Bytes(self))
    }
}

impl<'ty> Typed<'ty> for Box<dyn VecInstance<'ty>> {
    fn ty() -> ValueTy {
        ValueTy::VecInstance
    }

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val,
    {
        Value::from_vec(self.as_ref())
    }
}

impl<'ty> Typed<'ty> for Box<dyn StructInstance<'ty> + 'ty> {
    fn ty() -> ValueTy {
        ValueTy::StructInstance
    }

    fn as_value<'val>(&'val self) -> Value<'val, 'ty>
    where
        'ty: 'val,
    {
        Value::from_struct(self.as_ref())
    }
}

/// Provides `inst_ty` for any [`Typed`] type
pub trait TypedObj {
    fn inst_ty(&self) -> ValueTy;
}

impl<'ty, T> TypedObj for T
where
    T: Typed<'ty> + ?Sized,
{
    fn inst_ty(&self) -> ValueTy {
        T::ty()
    }
}
