use crate::*;
pub use bytes::Bytes;
pub use smol_str::SmolStr;

macro_rules! impl_value_for_value {
    ($enum:ident, $type:ident) => {
        impl<'val, 'ty> FromValue<'val, 'ty> for $type {
            fn from_value(value: &Value<'val, 'ty>) -> Option<Self> {
                if let ValueInner::$enum(val) = value.0 {
                    Some(val)
                } else {
                    None
                }
            }
        }

        impl<'ty> Typed<'ty> for $type {
            fn ty() -> ValueTy {
                ValueTy::$enum
            }
            fn as_value<'val>(&'val self) -> Value<'val, 'ty>
            where
                'ty: 'val,
            {
                Value(ValueInner::$enum(self.clone()))
            }
        }

        impl IntoValue for $type {
            fn into_value<'val, 'ty>(self) -> Value<'val, 'ty> {
                Value(ValueInner::$enum(self.clone()))
            }
        }

        impl<'val> IntoInner<$type> for OwnedValue<'val> {
            fn into_inner(self) -> Result<$type, Error> {
                if let OwnedValue::$enum(x) = self {
                    Ok(x)
                } else {
                    Err(Error::TypeError {
                        expected: SmolStr::new("$enum"),
                        found: SmolStr::new("n/a"),
                    })
                }
            }
        }

        impl<'ty> From<$type> for OwnedValue<'ty> {
            fn from(val: $type) -> Self {
                OwnedValue::$enum(val)
            }
        }
    };
}

impl_value_for_value!(U64, u64);
impl_value_for_value!(U32, u32);
impl_value_for_value!(U16, u16);
impl_value_for_value!(U8, u8);
impl_value_for_value!(I64, i64);
impl_value_for_value!(I32, i32);
impl_value_for_value!(I16, i16);
impl_value_for_value!(I8, i8);
impl_value_for_value!(F32, f32);
impl_value_for_value!(F64, f64);
impl_value_for_value!(Bool, bool);
