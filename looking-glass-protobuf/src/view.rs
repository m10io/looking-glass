use crate::{descriptors::*, DynamicMessage, Error};
use bytes::{buf::Buf, Bytes};
use looking_glass::{CowValue, Instance, OwnedValue, SmolStr, StructInstance, Typed, Value, ValueTy};
use once_cell::sync::OnceCell;
use prost::encoding::{decode_key, decode_varint, WireType};
use rustc_hash::FxHashMap;
use std::{any::TypeId, collections::HashMap, convert::TryFrom, sync::Arc};
use std::{
    fmt::Formatter,
    ops::{Bound, RangeBounds},
};

#[derive(Clone, Debug, PartialEq)]
pub enum RawField<T> {
    Single { wire_type: WireType, bytes: T },
    Repeated { wire_type: WireType, bytes: Vec<T> },
}

/// A view into the bytes of a Protocol Buffer message
///
/// `RawMessageView` allows you to lookup individuals tags of a Protocol Buffer message from a lookup table.
/// This allows for efficent zero-copy decoding of the message. `RawMessageView` uses the `Bytes` crate to store the contents it is viewing.
///
/// `RawMessageView` was created originally for use in query systems operating on arbitary Protocol Buffers where it is more efficent to not decode any values.
/// `RawMessageView` can also be used to easily implement fast-signature verification using Protocol Buffers.
///  We can view the bytes of an embedded payload and check the signature against that.
#[derive(Clone, Debug, PartialEq)]
pub struct RawMessageView<T> {
    pub tranche: T,
    tag_table: FxHashMap<u32, RawField<T>>,
}

impl<'a, T: Tranche> RawMessageView<T> {
    pub fn new(tranche: T) -> Result<RawMessageView<T>, Error> {
        let mut tag_tranche = tranche.clone();
        Ok(RawMessageView {
            tranche,
            tag_table: build_tag_table(&mut tag_tranche)?,
        })
    }

    pub fn raw_field_by_tag(&self, tag: u32, _repeated: bool) -> Option<RawField<T>> {
        self.tag_table.get(&tag).cloned()
    }
}

/// A parsed view into the bytes of a Protocol Buffer message
///
/// `MessageView` allows you to lookup fields on a Protocol Buffer message, and get zero-copy access to their parsed values.
/// For certain fields (fixed length, strings, and bytes) this can be done with virutally no decoding step.
/// Protocol Buffers encodes many of it's primatives with varint encoding. To access these values some decoding must be done.
///
/// It is important to note that there is no caching when reading the message. This means that this struct is best used when
/// reading values just once. The cost of decoding is low, but for consistent access of individual fields it is probably best to deseralize into a [`DynamicMessage`]
/// or another struct.
///
/// [`DynamicMessage`]: ./struct.DynamicMessage.html
#[derive(Clone, Debug)]
pub struct MessageView<T: Tranche> {
    raw_message_view: RawMessageView<T>,
    table: FxHashMap<u32, OnceCell<ValueView<T>>>,
    pub descriptor_name: String,
    pub descriptor_database: Arc<DescriptorDatabase>,
}

impl<T: Tranche> MessageView<T> {
    pub fn new(
        raw_message_view: RawMessageView<T>,
        descriptor_name: String,
        descriptor_database: Arc<DescriptorDatabase>,
    ) -> Result<MessageView<T>, Error> {
        let descriptor = descriptor_database
            .descriptor(&descriptor_name)
            .ok_or_else(|| looking_glass::Error::NotFound("missing descriptor".into()))?;
        let table = descriptor
            .fields
            .keys()
            .map(|t| (*t, OnceCell::new()))
            .collect();
        Ok(MessageView {
            raw_message_view,
            table,
            descriptor_name,
            descriptor_database,
        })
    }

    pub fn view_tag(&self, tag: u32) -> Result<&ValueView<T>, Error> {
        self.table
            .get(&tag)
            .ok_or_else(|| looking_glass::Error::NotFound("missing tag".into()))?
            .get_or_try_init(|| self.view_tag_inner(tag))
    }

    fn view_tag_inner(&self, tag: u32) -> Result<ValueView<T>, Error> {
        let descriptor = self
            .descriptor_database
            .descriptor(&self.descriptor_name)
            .ok_or_else(|| looking_glass::Error::NotFound("missing descriptor".into()))?;
        let field = descriptor
            .fields
            .get(&(tag as u32))
            .ok_or_else(|| looking_glass::Error::NotFound("field".into()))?;
        let bytes = self.raw_message_view.raw_field_by_tag(tag, field.repeated);
        match (field.repeated, bytes) {
            (false, Some(RawField::Single { mut bytes, .. })) => Ok(bytes_to_value_view(
                &mut bytes,
                &field.field_type,
                Some(&self.descriptor_database),
            )?),
            (true, Some(RawField::Single { mut bytes, .. })) => {
                let mut v = RepeatedValueView::empty_from_field(&field.field_type)?;
                while bytes.remaining() > 0 {
                    add_bytes_to_repeated_view(
                        &mut bytes,
                        &field.field_type,
                        Some(&self.descriptor_database),
                        &mut v,
                    )?;
                }
                Ok(ValueView::Repeated(v))
            }
            (true, Some(RawField::Repeated { bytes, .. })) => {
                let mut v = RepeatedValueView::empty_from_field(&field.field_type)?;
                for mut b in bytes.into_iter() {
                    add_bytes_to_repeated_view(
                        &mut b,
                        &field.field_type,
                        Some(&self.descriptor_database),
                        &mut v,
                    )?;
                }
                Ok(ValueView::Repeated(v))
            }
            (false, Some(RawField::Repeated { mut bytes, .. })) => {
                if let Some(mut bytes) = bytes.pop() {
                    Ok(bytes_to_value_view(
                        &mut bytes,
                        &field.field_type,
                        Some(&self.descriptor_database),
                    )?)
                } else {
                    Ok(field.field_type.default_value_view())
                }
            }
            (true, None) => Ok(ValueView::Repeated(RepeatedValueView::empty_from_field(
                &field.field_type,
            )?)),
            (false, None) => Ok(field.field_type.default_value_view()),
        }
    }

    pub fn view_field(&self, field: &str) -> Result<&ValueView<T>, Error> {
        let tag = {
            let descriptor = self
                .descriptor_database
                .descriptor(&self.descriptor_name)
                .ok_or_else(|| looking_glass::Error::NotFound("missing descriptor".into()))?;
            *descriptor
                .tags_by_name
                .get(field)
                .ok_or_else(|| looking_glass::Error::NotFound("field".into()))?
        };
        self.view_tag(tag)
    }

    pub fn message_tranche(&self) -> T {
        self.raw_message_view.tranche.clone()
    }
}

impl<T> PartialEq for MessageView<T>
where
    T: Tranche + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.table.len() == other.table.len()
            && self
                .table
                .keys()
                .all(|i| self.view_tag(*i).ok() == other.view_tag(*i).ok())
    }
}

pub fn bytes_to_value_view<T: Tranche>(
    bytes: &mut T,
    field_type: &FieldType,
    descriptor_database: Option<&Arc<DescriptorDatabase>>,
) -> Result<ValueView<T>, Error> {
    //TODO: Add saftey checks here
    Ok(match field_type {
        FieldType::Double => ValueView::F64(bytes.get_f64()),
        FieldType::Float => ValueView::F32(bytes.get_f32()),
        FieldType::UInt32 => ValueView::U32(decode_varint(bytes)? as u32),
        FieldType::UInt64 => ValueView::U64(decode_varint(bytes)? as u64),
        FieldType::Int32 => ValueView::I32(decode_varint(bytes)? as i32),
        FieldType::Int64 => ValueView::I64(decode_varint(bytes)? as i64),
        FieldType::SInt32 => {
            let value = decode_varint(bytes)? as u32;
            ValueView::S32(((value >> 1) as i32) ^ (-((value & 1) as i32)))
        }
        FieldType::SInt64 => {
            let value = decode_varint(bytes)?;
            ValueView::S64(((value >> 1) as i64) ^ (-((value & 1) as i64)))
        }
        FieldType::Fixed64 => ValueView::Fixed64(bytes.get_u64_le()),
        FieldType::Fixed32 => ValueView::Fixed32(bytes.get_u32_le()),
        FieldType::SFixed64 => ValueView::SFixed64(bytes.get_i64_le()),
        FieldType::SFixed32 => ValueView::SFixed32(bytes.get_i32_le()),
        FieldType::Bool => ValueView::Bool(decode_varint(bytes)? == 1),
        FieldType::String => ValueView::String(StrTranche::new(bytes)),
        FieldType::Message(name) => {
            if let Some(descriptor_database) = descriptor_database {
                let raw_message = RawMessageView::new(bytes.clone())?;
                bytes.advance(bytes.remaining());
                ValueView::Message(Some(MessageView::new(
                    raw_message,
                    name.to_string(),
                    descriptor_database.clone(),
                )?))
            } else {
                return Err(Error::LookingGlass(looking_glass::Error::NotFound("field".into())));
            }
        }
        FieldType::Bytes => {
            let view = ValueView::Bytes(bytes.clone());
            bytes.advance(bytes.remaining());
            view
        }
        FieldType::Enum(_) => ValueView::Enum(decode_varint(bytes)? as i32),
        FieldType::Group => return Err(Error::Unimplemented),
    })
}

pub fn add_bytes_to_repeated_view<T: Tranche>(
    bytes: &mut T,
    field_type: &FieldType,
    descriptor_database: Option<&Arc<DescriptorDatabase>>,
    repeated: &mut RepeatedValueView<T>,
) -> Result<(), Error> {
    match (field_type, repeated) {
        (FieldType::Double, RepeatedValueView::F64(v)) => v.push(bytes.get_f64()),
        (FieldType::Float, RepeatedValueView::F32(v)) => v.push(bytes.get_f32()),
        (FieldType::UInt32, RepeatedValueView::U32(v)) => v.push(decode_varint(bytes)? as u32),
        (FieldType::UInt64, RepeatedValueView::U64(v)) => v.push(decode_varint(bytes)? as u64),
        (FieldType::Int64, RepeatedValueView::I64(v)) => v.push(decode_varint(bytes)? as i64),
        (FieldType::Int32, RepeatedValueView::I32(v)) => v.push(decode_varint(bytes)? as i32),
        (FieldType::SInt32, RepeatedValueView::S32(v)) => {
            let value = decode_varint(bytes)? as u32;
            v.push(((value >> 1) as i32) ^ (-((value & 1) as i32)))
        }
        (FieldType::SInt64, RepeatedValueView::S64(v)) => {
            let value = decode_varint(bytes)? as u32;
            v.push(((value >> 1) as i64) ^ (-((value & 1) as i64)))
        }
        (FieldType::Fixed64, RepeatedValueView::Fixed64(v)) => v.push(bytes.get_u64_le()),
        (FieldType::Fixed32, RepeatedValueView::Fixed32(v)) => v.push(bytes.get_u32_le()),
        (FieldType::SFixed64, RepeatedValueView::SFixed64(v)) => v.push(bytes.get_i64_le()),
        (FieldType::SFixed32, RepeatedValueView::SFixed32(v)) => v.push(bytes.get_i32_le()),
        (FieldType::Bool, RepeatedValueView::Bool(v)) => v.push(decode_varint(bytes)? == 1),
        (FieldType::String, RepeatedValueView::String(v)) => v.push(StrTranche::new(bytes)),
        (FieldType::Message(name), RepeatedValueView::Message(v)) => {
            if let Some(descriptor_database) = descriptor_database {
                let raw_message = RawMessageView::new(bytes.clone())?;
                bytes.advance(bytes.remaining());
                let val =
                    MessageView::new(raw_message, name.to_string(), descriptor_database.clone())?;
                v.push(val)
            } else {
                return Err(Error::LookingGlass(looking_glass::Error::NotFound("field".into())));
            }
        }
        (FieldType::Bytes, RepeatedValueView::Bytes(v)) => {
            let view = bytes.clone();
            bytes.advance(bytes.remaining());
            v.push(view);
        }
        (FieldType::Enum(_), RepeatedValueView::Enum(v)) => v.push(decode_varint(bytes)? as i32),
        (FieldType::Group, _) => return Err(Error::Unimplemented),
        (f, r) => {
            return Err(Error::IncorrectType {
                expected: format!("{:?}", f).into(),
                found: format!("{:?}", r).into(),
            });
        }
    }
    Ok(())
}

/// A view into a Protocol Buffer value
#[derive(Clone, Debug, PartialEq)]
pub enum ValueView<T: Tranche> {
    /// A boolean value.
    Bool(bool),
    /// A 32-bit signed integer.
    I32(i32),
    /// A 64-bit signed integer.
    I64(i64),
    /// A 32-bit unsigned integer.
    U32(u32),
    /// A 64-bit unsigned integer.
    U64(u64),
    /// A 32-bit floating point value.
    F32(f32),
    /// A 64-bit floating point value.
    F64(f64),
    /// A 64-bit signed integer that is more efficent for signed values.
    S64(i64),
    /// A 32-bit signed integer that is more efficent for signed values.
    S32(i32),
    /// A 64-bit fixed length unsigned integer.
    Fixed64(u64),
    /// A 32-bit fixed length unsigned integer.
    Fixed32(u32),
    /// A 64-bit fixed length signed integer.
    SFixed64(i64),
    /// A 32-bit fixed length signed integer.
    SFixed32(i32),
    /// A byte vector.
    Bytes(T),
    /// A string.
    String(StrTranche<T>),
    /// An enum value.
    Enum(i32),
    /// A message.
    Message(Option<MessageView<T>>),
    /// Repeated
    Repeated(RepeatedValueView<T>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum RepeatedValueView<T: Tranche> {
    /// A boolean value.
    Bool(Vec<bool>),
    /// A 32-bit signed integer.
    I32(Vec<i32>),
    /// A 64-bit signed integer.
    I64(Vec<i64>),
    /// A 32-bit unsigned integer.
    U32(Vec<u32>),
    /// A 64-bit unsigned integer.
    U64(Vec<u64>),
    /// A 32-bit floating point value.
    F32(Vec<f32>),
    /// A 64-bit floating point value.
    F64(Vec<f64>),
    /// A 64-bit signed integer that is more efficent for signed values.
    S64(Vec<i64>),
    /// A 32-bit signed integer that is more efficent for signed values.
    S32(Vec<i32>),
    /// A 64-bit fixed length unsigned integer.
    Fixed64(Vec<u64>),
    /// A 32-bit fixed length unsigned integer.
    Fixed32(Vec<u32>),
    /// A 64-bit fixed length signed integer.
    SFixed64(Vec<i64>),
    /// A 32-bit fixed length signed integer.
    SFixed32(Vec<i32>),
    /// A byte vector.
    Bytes(Vec<T>),
    /// A string.
    String(Vec<StrTranche<T>>),
    /// An enum value.
    Enum(Vec<i32>),
    /// A message.
    Message(Vec<MessageView<T>>),
}

impl<T: Tranche> RepeatedValueView<T> {
    fn empty_from_field(ty: &FieldType) -> Result<Self, Error> {
        Ok(match ty {
            FieldType::Double => RepeatedValueView::F64(vec![]),
            FieldType::Float => RepeatedValueView::F32(vec![]),
            FieldType::Int64 => RepeatedValueView::I64(vec![]),
            FieldType::UInt64 => RepeatedValueView::U64(vec![]),
            FieldType::Int32 => RepeatedValueView::I32(vec![]),
            FieldType::Fixed64 => RepeatedValueView::Fixed64(vec![]),
            FieldType::Fixed32 => RepeatedValueView::Fixed32(vec![]),
            FieldType::Bool => RepeatedValueView::Bool(vec![]),
            FieldType::String => RepeatedValueView::String(vec![]),
            FieldType::Group => return Err(Error::Unimplemented),
            FieldType::Bytes => RepeatedValueView::Bytes(vec![]),
            FieldType::UInt32 => RepeatedValueView::U32(vec![]),
            FieldType::SFixed32 => RepeatedValueView::SFixed32(vec![]),
            FieldType::SFixed64 => RepeatedValueView::SFixed64(vec![]),
            FieldType::SInt32 => RepeatedValueView::SFixed32(vec![]),
            FieldType::SInt64 => RepeatedValueView::SFixed64(vec![]),
            FieldType::Message(_) => RepeatedValueView::Message(vec![]),
            FieldType::Enum(_) => RepeatedValueView::Enum(vec![]),
        })
    }
}

#[derive(Clone, PartialEq)]
pub struct StrTranche<T>(T);

impl<T: Tranche> StrTranche<T> {
    pub fn new(src: &mut T) -> StrTranche<T> {
        match std::str::from_utf8(src.chunk()) {
            Ok(_) => StrTranche(src.clone()),
            Err(e) => {
                let tranche = src.slice(0..e.valid_up_to());
                StrTranche(tranche)
            }
        }
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        unsafe { std::str::from_utf8_unchecked(self.0.chunk()) }
    }
}

impl<'a> From<&'a str> for StrTranche<&'a [u8]> {
    fn from(s: &'a str) -> Self {
        StrTranche(s.as_bytes())
    }
}

impl<T: Tranche> std::fmt::Debug for StrTranche<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("StrTranche").field(&self.as_str()).finish()
    }
}

impl<T: Tranche> TryFrom<&ValueView<T>> for OwnedValue<'static> {
    type Error = Error;
    fn try_from(value: &ValueView<T>) -> Result<Self, Self::Error> {
        Ok(match value {
            ValueView::Bool(b) => OwnedValue::Bool(*b),
            ValueView::I32(i) => OwnedValue::I32(*i),
            ValueView::I64(i) => OwnedValue::I64(*i),
            ValueView::U32(u) => OwnedValue::U32(*u),
            ValueView::U64(u) => OwnedValue::U64(*u),
            ValueView::F32(f) => OwnedValue::F32(*f),
            ValueView::F64(f) => OwnedValue::F64(*f),
            ValueView::S64(i) => OwnedValue::I64(*i),
            ValueView::S32(i) => OwnedValue::I32(*i),
            ValueView::Fixed64(u) => OwnedValue::U64(*u),
            ValueView::Fixed32(u) => OwnedValue::U32(*u),
            ValueView::SFixed64(i) => OwnedValue::I64(*i),
            ValueView::SFixed32(i) => OwnedValue::I32(*i),
            ValueView::Bytes(bytes) => OwnedValue::Bytes(Bytes::copy_from_slice(bytes.chunk())), //TODO: This seems needlessly inefficent for ValueView<Bytes>
            ValueView::String(s) => OwnedValue::String(s.as_str().to_string()),
            ValueView::Enum(e) => OwnedValue::I32(*e),
            ValueView::Message(m) => match m {
                Some(m) => OwnedValue::Option(Box::new(Some(DynamicMessage::new(m)?))),
                None => OwnedValue::Option(Box::new(None as Option<DynamicMessage>)),
            },

            ValueView::Repeated(r) => match r {
                RepeatedValueView::Bool(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::I32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::I64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::U32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::U64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::F32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::F64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::S64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::S32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::Fixed64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::Fixed32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::SFixed64(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::SFixed32(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::Bytes(v) => OwnedValue::Vec(Box::new(
                    v.iter()
                        .map(|bytes| Bytes::copy_from_slice(bytes.chunk()))
                        .collect::<Vec<Bytes>>(),
                )),
                RepeatedValueView::String(v) => OwnedValue::Vec(Box::new(
                    v.iter()
                        .map(|s| s.as_str().to_string())
                        .collect::<Vec<String>>(),
                )),
                RepeatedValueView::Enum(v) => OwnedValue::Vec(Box::new(v.clone())),
                RepeatedValueView::Message(v) => OwnedValue::Vec(Box::new(
                    v.iter()
                        .filter_map(|m| DynamicMessage::new(m).ok())
                        .collect::<Vec<DynamicMessage>>(),
                )),
            },
        })
    }
}

impl<'s> ValueView<Bytes> {
    fn as_value<'a>(&'a self) -> Value<'a, 's>
    where
        's: 'a,
    {
        match self {
            ValueView::Bool(b) => b.as_value(),
            ValueView::I32(i) => i.as_value(),
            ValueView::I64(i) => i.as_value(),
            ValueView::U32(u) => u.as_value(),
            ValueView::U64(u) => u.as_value(),
            ValueView::F32(f) => f.as_value(),
            ValueView::F64(f) => f.as_value(),
            ValueView::S64(i) => i.as_value(),
            ValueView::S32(i) => i.as_value(),
            ValueView::Fixed64(u) => u.as_value(),
            ValueView::Fixed32(u) => u.as_value(),
            ValueView::SFixed64(i) => i.as_value(),
            ValueView::SFixed32(i) => i.as_value(),
            ValueView::Bytes(bytes) => bytes.as_value(),
            ValueView::String(s) => s.as_str().as_value(),
            ValueView::Enum(e) => e.as_value(),
            ValueView::Message(m) => match m {
                Some(m) => m.as_value(),
                None => Value::from_option(&(None as Option<MessageView<Bytes>>)),
            },
            ValueView::Repeated(r) => match r {
                RepeatedValueView::Bool(v) => v.as_value(),
                RepeatedValueView::I32(v) => v.as_value(),
                RepeatedValueView::I64(v) => v.as_value(),
                RepeatedValueView::U32(v) => v.as_value(),
                RepeatedValueView::U64(v) => v.as_value(),
                RepeatedValueView::F32(v) => v.as_value(),
                RepeatedValueView::F64(v) => v.as_value(),
                RepeatedValueView::S64(v) => v.as_value(),
                RepeatedValueView::S32(v) => v.as_value(),
                RepeatedValueView::Fixed64(v) => v.as_value(),
                RepeatedValueView::Fixed32(v) => v.as_value(),
                RepeatedValueView::SFixed64(v) => v.as_value(),
                RepeatedValueView::SFixed32(v) => v.as_value(),
                RepeatedValueView::Bytes(v) => v.as_value(),
                RepeatedValueView::String(v) => v.as_value(),
                RepeatedValueView::Enum(v) => v.as_value(),
                RepeatedValueView::Message(v) => v.as_value(),
            },
        }
    }
}

fn build_tag_table<T: Tranche>(mut bytes: &mut T) -> Result<FxHashMap<u32, RawField<T>>, Error> {
    let mut map = FxHashMap::default();
    while bytes.remaining() > 0 {
        let (tag, wire_type) = decode_key(&mut bytes)?;
        let slice = field_slice(wire_type, bytes)?;
        let field = if let Some(field) = map.remove(&tag) {
            match field {
                RawField::Single {
                    wire_type: first_wire_type,
                    bytes: first_bytes,
                } => {
                    if wire_type == first_wire_type {
                        RawField::Repeated {
                            wire_type,
                            bytes: vec![first_bytes, slice],
                        }
                    } else {
                        return Err(Error::Decode("wire-type mismatch in repeated".into()));
                    }
                }
                RawField::Repeated {
                    wire_type: first_wire_type,
                    bytes: mut bytes_vec,
                } => {
                    if wire_type == first_wire_type {
                        bytes_vec.push(slice);
                        RawField::Repeated {
                            wire_type,
                            bytes: bytes_vec,
                        }
                    } else {
                        return Err(Error::Decode("wire-type mismatch in repeated".into()));
                    }
                }
            }
        } else {
            RawField::Single {
                wire_type,
                bytes: slice,
            }
        };
        map.insert(tag, field);
    }
    Ok(map)
}

// Heavily based on skip_field in
// https://github.com/danburkert/prost/blob/master/src/encoding.rs
fn field_slice<T: Tranche>(wire_type: WireType, bytes: &mut T) -> Result<T, Error> {
    let len: usize = match wire_type {
        WireType::Varint => variant_length(bytes)? as usize,
        WireType::ThirtyTwoBit => 4,
        WireType::SixtyFourBit => 8,
        WireType::LengthDelimited => decode_varint(bytes)? as usize,
        WireType::StartGroup => return Err(Error::Decode("groups aren't supported yet".into())),
        WireType::EndGroup => return Err(Error::Decode("unexpected end group tag".into())),
    };

    if len > bytes.remaining() {
        return Err(Error::Decode("underflow".into()));
    }

    let slice = bytes.slice(0..len);
    bytes.advance(len);
    Ok(slice)
}

// Heavily based on decode_variant_slow
// https://github.com/danburkert/prost/blob/master/src/encoding.rs
fn variant_length<B: Buf>(buf: &mut B) -> Result<usize, Error> {
    for count in 0..std::cmp::min(10, buf.remaining()) {
        let byte = buf.chunk()[count];
        if byte <= 0x7F {
            return Ok(count + 1);
        }
    }
    Err(Error::Decode("invalid varint".into()))
}

pub trait Tranche: Buf + Clone + std::fmt::Debug + Default {
    fn slice(&self, range: impl RangeBounds<usize>) -> Self;
}

impl Tranche for Bytes {
    fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        Bytes::slice(self, range)
    }
}

impl Tranche for &[u8] {
    fn slice(&self, range: impl RangeBounds<usize>) -> Self {
        let len = self.len();
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };

        let stop = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => len,
        };
        &self[start..stop]
    }
}

impl<'s> Instance<'s> for MessageView<Bytes> {
    fn name(&self) -> SmolStr {
        SmolStr::from(&self.descriptor_name)
    }

    fn as_inst(&self) -> &(dyn Instance<'s> + 's) {
        self
    }
}

impl<'s> StructInstance<'s> for MessageView<Bytes> {
    fn get_value<'a>(&'a self, field: &str) -> Option<CowValue<'a, 's>>
    where
        's: 'a,
    {
        Some(CowValue::Ref(self.view_field(field).ok()?.as_value()))
    }

    fn update(
        &mut self,
        _update: &dyn StructInstance,
        _field_mask: Option<&looking_glass::FieldMask>,
        _replace_repeated: bool,
    ) -> Result<(), looking_glass::Error> {
        Ok(())
    }

    fn values<'a>(&'a self) -> HashMap<SmolStr, CowValue<'a, 's>> {
        if let Some(descriptor) = self.descriptor_database.descriptor(&self.descriptor_name) {
            self.table
                .iter()
                .filter_map(|(t, v)| {
                    let name = &descriptor.fields.get(t)?.name;
                    Some((
                        name.clone(),
                        CowValue::Ref(
                            v.get_or_try_init(|| self.view_tag_inner(*t))
                                .ok()?
                                .as_value(),
                        ),
                    ))
                })
                .collect()
        } else {
            HashMap::default()
        }
    }

    fn boxed_clone(&self) -> Box<dyn StructInstance<'s> + 's> {
        Box::new(self.clone())
    }

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s>> {
        self
    }
}

impl<'s> Typed<'s> for MessageView<Bytes> {
    fn ty() -> looking_glass::ValueTy {
        ValueTy::Struct(TypeId::of::<Self>())
    }

    fn as_value<'a>(&'a self) -> Value<'a, 's>
    where
        's: 'a,
    {
        Value::from_struct(self)
    }
}

impl<'s> Typed<'s> for StrTranche<Bytes> {
    fn ty() -> ValueTy {
        ValueTy::Str
    }

    fn as_value<'a>(&'a self) -> Value<'a, 's>
    where
        's: 'a,
    {
        self.as_str().as_value()
    }
}
