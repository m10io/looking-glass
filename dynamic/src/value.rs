use crate::*;
pub use bytes::Bytes;
pub use smol_str::SmolStr;

use std::{collections::HashMap, hash::Hash};

/// A container for a type-erased value.
///
/// Value is, in essence, a smart-pointer that can hold any reflected type. It is slightly larger than a standard fat-pointer, since it contains
/// metadata about the type it contains.
#[derive(Clone)]
pub struct Value<'val, 'ty>(pub(crate) ValueInner<'val, 'ty>)
where
    'ty: 'val;

#[derive(Clone)]
pub(crate) enum ValueInner<'val, 'ty>
where
    'ty: 'val,
{
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
    String(&'val String),
    Str(&'val str),
    Vec(&'val (dyn VecInstance<'ty> + 'ty)),
    Struct(&'val (dyn StructInstance<'ty> + 'ty)),
    Enum(&'val (dyn EnumInstance<'ty> + 'ty)),
    Bytes(&'val Bytes),
    Option(&'val (dyn OptionInstance<'ty> + 'ty)),
}

impl<'val, 'ty> Value<'val, 'ty> {
    /// Creates a [`Value`] from a reflected [`Vec`]
    pub fn from_vec(s: &'val (dyn VecInstance<'ty> + 'ty)) -> Value<'val, 'ty> {
        Value(ValueInner::Vec(s))
    }

    /// Creates a [`Value`] from a reflected struct
    pub fn from_struct(s: &'val (dyn StructInstance<'ty> + 'ty)) -> Value<'val, 'ty> {
        Value(ValueInner::Struct(s))
    }

    /// Creates a [`Value`] from a reflected enum
    pub fn from_enum(s: &'val (dyn EnumInstance<'ty> + 'ty)) -> Value<'val, 'ty> {
        Value(ValueInner::Enum(s))
    }

    /// Creates a [`Value`] from a reflected option
    pub fn from_option(s: &'val (dyn OptionInstance<'ty> + 'ty)) -> Value<'val, 'ty> {
        Value(ValueInner::Option(s))
    }

    /// Borrows the value as an underlying type. This will return `None`,
    /// when the runtime type-check fails
    pub fn borrow<'b, T: FromValue<'val, 'ty>>(&'b self) -> Option<T>
    where
        'val: 'b,
        'ty: 'b,
    {
        T::from_value(self)
    }

    /// Consumes the `Value` and returns the internal `T`.
    ///
    /// This only works for types that implement [`FromValue`], which are generally primitives
    /// that implement `Copy`.
    pub fn into<T: FromValue<'val, 'ty> + 'ty>(self) -> Option<T> {
        T::from_value(&self)
    }

    /// Attempts to cast `Value` to a [`VecInstance`]
    pub fn as_reflected_vec(&self) -> Option<&'val (dyn VecInstance<'ty> + 'ty)> {
        match self.0 {
            ValueInner::Vec(v) => Some(v),
            _ => None,
        }
    }

    /// Attempts to cast `Value` to a [`StructInstance`]
    pub fn as_reflected_struct(&self) -> Option<&'val (dyn StructInstance<'ty> + 'ty)> {
        match self.0 {
            ValueInner::Struct(v) => Some(v),
            _ => None,
        }
    }

    /// Attempts to cast `Value` to a [`EnumInstance`]
    pub fn as_reflected_enum(&'val self) -> Option<&(dyn EnumInstance<'ty> + 'ty)> {
        match self.0 {
            ValueInner::Enum(v) => Some(v),
            _ => None,
        }
    }

    /// Attempts to cast `Value` to a [`OptionInstance`]
    pub fn as_reflected_option(&'val self) -> Option<&(dyn OptionInstance<'ty> + 'ty)> {
        match self.0 {
            ValueInner::Option(v) => Some(v),
            _ => None,
        }
    }

    /// Clones the underlying value, and returns a [`OwnedValue`]
    pub fn to_owned(&self) -> OwnedValue<'ty> {
        match self.0 {
            ValueInner::U64(u) => OwnedValue::U64(u),
            ValueInner::U32(u) => OwnedValue::U32(u),
            ValueInner::U16(u) => OwnedValue::U16(u),
            ValueInner::U8(u) => OwnedValue::U8(u),
            ValueInner::I64(u) => OwnedValue::I64(u),
            ValueInner::I32(u) => OwnedValue::I32(u),
            ValueInner::I16(u) => OwnedValue::I16(u),
            ValueInner::I8(u) => OwnedValue::I8(u),
            ValueInner::F32(u) => OwnedValue::F32(u),
            ValueInner::F64(u) => OwnedValue::F64(u),
            ValueInner::Bool(u) => OwnedValue::Bool(u),
            ValueInner::String(s) => OwnedValue::String(s.clone()),
            ValueInner::Str(s) => OwnedValue::String(s.to_string()),
            ValueInner::Vec(v) => OwnedValue::Vec(v.boxed_clone()),
            ValueInner::Struct(s) => OwnedValue::Struct(s.boxed_clone()),
            ValueInner::Enum(e) => OwnedValue::Enum(e.boxed_clone()),
            ValueInner::Bytes(b) => OwnedValue::Bytes(b.clone()),
            ValueInner::Option(o) => OwnedValue::Option(o.boxed_clone()),
        }
    }

    /// Attempts to has the [`Value`], only returning a value if the underlying type is hashable
    pub fn try_hash<H: std::hash::Hasher>(&self, mut hasher: H) -> Option<u64> {
        match self.0 {
            ValueInner::U64(x) => x.hash(&mut hasher),
            ValueInner::U32(x) => x.hash(&mut hasher),
            ValueInner::U16(x) => x.hash(&mut hasher),
            ValueInner::U8(x) => x.hash(&mut hasher),
            ValueInner::I64(x) => x.hash(&mut hasher),
            ValueInner::I32(x) => x.hash(&mut hasher),
            ValueInner::I16(x) => x.hash(&mut hasher),
            ValueInner::I8(x) => x.hash(&mut hasher),
            ValueInner::Bool(x) => x.hash(&mut hasher),
            ValueInner::String(x) => x.hash(&mut hasher),
            ValueInner::Str(x) => x.hash(&mut hasher),
            ValueInner::Bytes(x) => x.hash(&mut hasher),
            _ => return None,
        };
        Some(hasher.finish())
    }

    /// Checks if two `Values` are equal.
    ///
    /// This is slower than the implementations in [`PartialEq`],
    /// but it works with `Values` of different lifetimes.
    /// It is slower, because it is implemented using reflection calls,
    /// rather than downcasting.
    pub fn slow_eq<'c, 'd>(&self, r: &Value<'c, 'd>) -> bool {
        match (&self.0, &r.0) {
            (ValueInner::U64(l), ValueInner::U64(r)) => l == r,
            (ValueInner::U32(l), ValueInner::U32(r)) => l == r,
            (ValueInner::U16(l), ValueInner::U16(r)) => l == r,
            (ValueInner::U8(l), ValueInner::U8(r)) => l == r,
            (ValueInner::I64(l), ValueInner::I64(r)) => l == r,
            (ValueInner::I32(l), ValueInner::I32(r)) => l == r,
            (ValueInner::I16(l), ValueInner::I16(r)) => l == r,
            (ValueInner::I8(l), ValueInner::I8(r)) => l == r,
            (ValueInner::F32(l), ValueInner::F32(r)) => l == r,
            (ValueInner::F64(l), ValueInner::F64(r)) => l == r,
            (ValueInner::Bool(l), ValueInner::Bool(r)) => l == r,
            (ValueInner::String(l), ValueInner::String(r)) => l == r,
            (ValueInner::Str(l), ValueInner::Str(r)) => l == r,
            (ValueInner::String(l), ValueInner::Str(r))
            | (ValueInner::Str(r), ValueInner::String(l)) => l == r,
            (ValueInner::Bytes(l), ValueInner::Bytes(r)) => l == r,
            (ValueInner::Struct(l), ValueInner::Struct(r)) => {
                match_map_fields(l.values(), r.values())
            }
            (ValueInner::Vec(l), ValueInner::Vec(r)) => match_vec_fields(l.values(), r.values()),
            (ValueInner::Enum(l), ValueInner::Enum(r)) => match (l.field(), r.field()) {
                (EnumField::Unit(l), EnumField::Unit(r)) => l == r,
                (
                    EnumField::Tuple {
                        name: l_name,
                        fields: l_fields,
                    },
                    EnumField::Tuple {
                        name: r_name,
                        fields: r_fields,
                    },
                ) => {
                    if l_name == r_name {
                        match_vec_fields(l_fields, r_fields)
                    } else {
                        false
                    }
                }
                (
                    EnumField::Struct {
                        name: l_name,
                        fields: l_fields,
                    },
                    EnumField::Struct {
                        name: r_name,
                        fields: r_fields,
                    },
                ) => {
                    if l_name == r_name {
                        match_map_fields(l_fields, r_fields)
                    } else {
                        false
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }
}

impl<'val, 'ty> From<&'val Bytes> for Value<'val, 'ty> {
    fn from(bytes: &'val Bytes) -> Self {
        Self(ValueInner::Bytes(bytes))
    }
}

fn match_vec_fields(l_fields: Vec<CowValue<'_, '_>>, r_fields: Vec<CowValue<'_, '_>>) -> bool {
    if l_fields.len() != r_fields.len() {
        return false;
    }
    for (i, l_val) in l_fields.iter().enumerate() {
        if let Some(r_val) = r_fields.get(i) {
            if !l_val.slow_eq(r_val) {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}

fn match_map_fields(
    l_fields: HashMap<SmolStr, CowValue<'_, '_>>,
    r_fields: HashMap<SmolStr, CowValue<'_, '_>>,
) -> bool {
    if l_fields.len() != r_fields.len() {
        return false;
    }
    for (field, l_val) in &l_fields {
        if let Some(r_val) = r_fields.get(field) {
            if !l_val.slow_eq(r_val) {
                return false;
            }
        } else {
            return false;
        }
    }
    true
}

impl std::fmt::Debug for Value<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            ValueInner::U64(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::U32(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::U16(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::U8(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::I64(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::I32(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::I16(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::I8(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::F32(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::F64(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Bool(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::String(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Str(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Vec(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Struct(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Enum(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Bytes(x) => std::fmt::Debug::fmt(&x, f),
            ValueInner::Option(x) => std::fmt::Debug::fmt(&x, f),
        }
    }
}

impl PartialEq for Value<'_, '_> {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (ValueInner::U64(l), ValueInner::U64(r)) => l == r,
            (ValueInner::U32(l), ValueInner::U32(r)) => l == r,
            (ValueInner::U16(l), ValueInner::U16(r)) => l == r,
            (ValueInner::U8(l), ValueInner::U8(r)) => l == r,
            (ValueInner::I64(l), ValueInner::I64(r)) => l == r,
            (ValueInner::I32(l), ValueInner::I32(r)) => l == r,
            (ValueInner::I16(l), ValueInner::I16(r)) => l == r,
            (ValueInner::I8(l), ValueInner::I8(r)) => l == r,
            (ValueInner::F32(l), ValueInner::F32(r)) => l == r,
            (ValueInner::F64(l), ValueInner::F64(r)) => l == r,
            (ValueInner::Bool(l), ValueInner::Bool(r)) => l == r,
            (ValueInner::String(l), ValueInner::String(r)) => l == r,
            (ValueInner::Str(st), ValueInner::String(s))
            | (ValueInner::String(s), ValueInner::Str(st)) => st == s,
            (ValueInner::Str(l), ValueInner::Str(r)) => l == r,
            (ValueInner::Vec(l), ValueInner::Vec(r)) => l == r,
            (ValueInner::Bytes(l), ValueInner::Bytes(r)) => l == r,
            (ValueInner::Struct(l), ValueInner::Struct(r)) => l == r,
            (ValueInner::Option(l), ValueInner::Option(r)) => l == r,
            (ValueInner::Enum(l), ValueInner::Enum(r)) => l == r,
            (_, _) => false,
        }
    }
}
