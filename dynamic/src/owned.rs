use crate::typed::Typed;
use crate::*;
pub use bytes::Bytes;
pub use smol_str::SmolStr;

/// An enum containing an owned copy of a [`Value`]
#[derive(Clone, Debug)]
pub enum OwnedValue<'ty> {
    U64(u64),
    U32(u32),
    U16(u16),
    U8(u8),
    I64(i64),
    I32(i32),
    I16(i16),
    I8(i8),
    F32(f32),
    F64(f64),
    Bool(bool),
    String(String),
    Vec(Box<dyn VecInstance<'ty> + 'ty>),
    Struct(Box<dyn StructInstance<'ty> + 'ty>),
    Enum(Box<dyn EnumInstance<'ty> + 'ty>),
    Bytes(Bytes),
    Option(Box<dyn OptionInstance<'ty> + 'ty>),
}

impl<'ty> PartialEq for OwnedValue<'ty> {
    fn eq(&self, other: &Self) -> bool {
        use OwnedValue::*;
        match (self, other) {
            (U64(l), U64(r)) => l == r,
            (U32(l), U32(r)) => l == r,
            (U16(l), U16(r)) => l == r,
            (U8(l), U8(r)) => l == r,
            (I64(l), I64(r)) => l == r,
            (I32(l), I32(r)) => l == r,
            (I16(l), I16(r)) => l == r,
            (I8(l), I8(r)) => l == r,
            (F32(l), F32(r)) => l == r,
            (F64(l), F64(r)) => l == r,
            (Bool(l), Bool(r)) => l == r,
            (String(l), String(r)) => l == r,
            (Vec(l), Vec(r)) => l == r,
            (Struct(l), Struct(r)) => l == r,
            (Enum(l), Enum(r)) => l == r,
            (Bytes(l), Bytes(r)) => l == r,
            _ => false,
        }
    }
}

impl<'v> OwnedValue<'v> {
    /// Returns a [`Value`] as a reference to the [`OwnedValue`]
    pub fn as_ref<'val>(&'val self) -> Value<'val, 'v>
    where
        'v: 'val,
    {
        match self {
            OwnedValue::U64(a) => a.as_value(),
            OwnedValue::U32(a) => a.as_value(),
            OwnedValue::U16(a) => a.as_value(),
            OwnedValue::U8(a) => a.as_value(),
            OwnedValue::I64(a) => a.as_value(),
            OwnedValue::I32(a) => a.as_value(),
            OwnedValue::I16(a) => a.as_value(),
            OwnedValue::I8(a) => a.as_value(),
            OwnedValue::F32(a) => a.as_value(),
            OwnedValue::F64(a) => a.as_value(),
            OwnedValue::Bool(a) => a.as_value(),
            OwnedValue::String(a) => a.as_value(),
            OwnedValue::Vec(a) => Value::from_vec(a.as_ref()),
            OwnedValue::Struct(a) => Value::from_struct(a.as_ref()),
            OwnedValue::Enum(a) => Value::from_enum(a.as_ref()),
            OwnedValue::Bytes(b) => b.as_value(),
            OwnedValue::Option(o) => Value::from_option(o.as_ref()),
        }
    }
}

impl<'ty> From<String> for OwnedValue<'ty> {
    fn from(val: String) -> OwnedValue<'ty> {
        OwnedValue::String(val)
    }
}

#[derive(Clone)]
pub enum CowValue<'val, 'ty> {
    Owned(OwnedValue<'ty>),
    Ref(Value<'val, 'ty>),
}

impl<'val, 'ty> From<Value<'val, 'ty>> for CowValue<'val, 'ty> {
    fn from(v: Value<'val, 'ty>) -> Self {
        Self::Ref(v)
    }
}

impl<'val, 'ty> From<OwnedValue<'ty>> for CowValue<'val, 'ty> {
    fn from(v: OwnedValue<'ty>) -> Self {
        Self::Owned(v)
    }
}

impl<'val, 'ty> CowValue<'val, 'ty> {
    pub fn slow_eq<'c, 'd>(&self, other: &CowValue<'c, 'd>) -> bool {
        self.as_ref().slow_eq(&other.as_ref())
    }
}

impl std::fmt::Debug for CowValue<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CowValue::Owned(o) => std::fmt::Debug::fmt(&o, f),
            CowValue::Ref(r) => std::fmt::Debug::fmt(&r, f),
        }
    }
}

impl PartialEq for CowValue<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<'val, 'ty> CowValue<'val, 'ty> {
    pub fn as_ref(&'val self) -> Value<'val, 'ty> {
        match self {
            CowValue::Owned(owned) => owned.as_ref(),
            CowValue::Ref(r) => r.clone(),
        }
    }

    pub fn to_owned(&self) -> OwnedValue<'ty> {
        match self {
            CowValue::Owned(owned) => owned.clone(),
            CowValue::Ref(r) => r.to_owned(),
        }
    }
}
