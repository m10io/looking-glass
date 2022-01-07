use crate::{DescriptorDatabase, Error, Tranche};
use crate::{FieldType, MessageView};
use bytes::{Buf, BufMut, Bytes};
use looking_glass::{CowValue, Instance, IntoInner, OwnedValue, SmolStr, StructInstance, Typed, ValueTy};
use prost::encoding::{encode_key, encode_varint, encoded_len_varint, key_len, WireType};
use std::{
    any::TypeId,
    collections::{BTreeMap, HashMap},
    convert::TryFrom,
    sync::Arc,
};

/// A looking_glass representation of a ProtocolBuffer message.
///
/// DynamicMessage allows users to create and read ProtocolBuffer messages at runtime. A DynamicMessage is created from a [`MessageView`], but unlike a [`MessageView`] it owns its data.
/// This means that DynamicMessages can be modified and re-encoded. In the name of efficiency string and byte, types are reference counted from their source.
#[derive(Debug, PartialEq, Clone)]
pub struct DynamicMessage {
    values: BTreeMap<u32, Field<OwnedValue<'static>>>,
    descriptor_name: String,
    descriptor_database: Arc<DescriptorDatabase>,
}

impl DynamicMessage {
    /// Builds a new `DynamicMessage` from a [`MessageView`].
    pub fn new<T: Tranche>(view: &MessageView<T>) -> Result<DynamicMessage, Error> {
        let descriptor_database = view.descriptor_database.clone();
        let descriptor_name = view.descriptor_name.clone();
        let descriptor = descriptor_database
            .descriptor(&descriptor_name)
            .ok_or_else(|| looking_glass::Error::NotFound("descriptor".into()))?;
        let values = descriptor
            .fields
            .iter()
            .map(|(tag, field)| match view.view_tag(*tag) {
                Ok(view) => Ok((
                    *tag,
                    Field {
                        field_type: field.field_type.clone(),
                        attr: OwnedValue::try_from(view)?,
                    },
                )),
                Err(e) => Err(e),
            })
            .collect::<Result<BTreeMap<_, _>, Error>>()?;
        Ok(DynamicMessage {
            values,
            descriptor_name,
            descriptor_database,
        })
    }

    /// The length of the mesage once encoded
    pub fn encoded_len(&self) -> usize {
        self.values
            .iter()
            .map(|(tag, field)| field.encoded_len(*tag))
            .sum()
    }

    /// Encoded a [`DynamicMessage`] to the passed buffer
    pub fn encode(&self, buf: &mut impl BufMut) {
        for (tag, field) in &self.values {
            field.encode(*tag, buf)
        }
    }

    pub fn descriptor_name(&self) -> String {
        self.descriptor_name.clone()
    }

    pub fn descriptor_database(&self) -> Arc<DescriptorDatabase> {
        self.descriptor_database.clone()
    }
}

impl Instance<'static> for DynamicMessage {
    fn name(&self) -> SmolStr {
        SmolStr::new(&self.descriptor_name)
    }

    fn as_inst(&self) -> &(dyn Instance<'static> + 'static) {
        self
    }
}

impl StructInstance<'static> for DynamicMessage {
    fn get_value<'a>(&'a self, field: &str) -> Option<CowValue<'a, 'static>>
    where
        'static: 'a,
    {
        let descriptor = self.descriptor_database.descriptor(&self.descriptor_name)?;
        let tag = descriptor.tags_by_name.get(field)?;
        Some(CowValue::from(self.values.get(tag)?.attr.as_ref()))
    }

    fn update<'a>(
        &'a mut self,
        update: &'a (dyn StructInstance<'static> + 'static),
        field_mask: Option<&looking_glass::FieldMask>,
        replace_repeated: bool,
    ) -> Result<(), looking_glass::Error> {
        let descriptor = self
            .descriptor_database
            .descriptor(&self.descriptor_name)
            .ok_or_else(|| looking_glass::Error::NotFound("descriptor".into()))?;
        for (key, update_value) in update.values() {
            let tag = descriptor
                .tags_by_name
                .get(&key)
                .ok_or_else(|| looking_glass::Error::NotFound("tag".into()))?;
            let new_mask = field_mask.and_then(|m| m.child(&key));
            if new_mask.is_some() || field_mask.is_none() {
                let field = self.values.get_mut(tag);
                let attr = field.map(|f| &mut f.attr);
                match attr {
                    Some(OwnedValue::Struct(inst)) => {
                        if let Some(update_inst) = update_value.as_ref().as_reflected_struct() {
                            inst.update(update_inst, new_mask, replace_repeated)?;
                        }
                    }
                    Some(OwnedValue::Vec(ref mut v)) => {
                        if let Some(update_vec) = update_value.as_ref().as_reflected_vec() {
                            v.update(update_vec, replace_repeated)?;
                        }
                    }
                    _ => {
                        let field = descriptor
                            .fields
                            .get(tag)
                            .ok_or_else(|| looking_glass::Error::NotFound("descriptor".into()))?;
                        let update_value = if let Some(view) =
                            update_value.as_ref().borrow::<&MessageView<Bytes>>()
                        {
                            OwnedValue::Option(Box::new(Some(DynamicMessage::new(view).map_err(
                                |_| looking_glass::Error::TypeError {
                                    expected: "valid message view".into(),
                                    found: "invalid message view".into(),
                                },
                            )?)))
                        } else {
                            update_value.to_owned()
                        };
                        let field = Field {
                            field_type: field.field_type.clone(),
                            attr: update_value,
                        };
                        self.values.insert(*tag, field);
                    }
                }
            }
        }
        Ok(())
    }

    fn values<'a>(&'a self) -> HashMap<SmolStr, CowValue<'a, 'static>> {
        if let Some(descriptor) = self.descriptor_database.descriptor(&self.descriptor_name) {
            self.values
                .iter()
                .filter_map(|(t, v)| {
                    let name = descriptor.fields.get(t)?.name.clone();
                    Some((name, CowValue::Ref(v.attr.as_ref())))
                })
                .collect()
        } else {
            HashMap::new()
        }
    }

    fn boxed_clone(&self) -> Box<dyn StructInstance<'static> + 'static> {
        Box::new(self.clone())
    }

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'static> + 'static> {
        self
    }
}

impl Typed<'static> for DynamicMessage {
    fn ty() -> looking_glass::ValueTy {
        ValueTy::Struct(TypeId::of::<Self>())
    }

    fn as_value<'a>(&'a self) -> looking_glass::Value<'a, 'static>
    where
        'static: 'a,
    {
        looking_glass::Value::from_struct(self)
    }
}

fn is_default_owned_value(value: &OwnedValue<'static>) -> bool {
    match value {
        OwnedValue::U64(u) => *u == 0,
        OwnedValue::U32(u) => *u == 0,
        OwnedValue::U16(u) => *u == 0,
        OwnedValue::U8(u) => *u == 0,
        OwnedValue::I64(u) => *u == 0,
        OwnedValue::I32(u) => *u == 0,
        OwnedValue::I16(u) => *u == 0,
        OwnedValue::I8(u) => *u == 0,
        OwnedValue::Bool(b) => !b,
        OwnedValue::String(s) => s.is_empty(),
        OwnedValue::Vec(v) => v.is_empty(),
        OwnedValue::Bytes(b) => b.is_empty(),
        OwnedValue::Struct(m) => {
            if let Some(msg) = m.as_inst().downcast_ref::<DynamicMessage>() {
                for field in msg.values.values() {
                    if !field.is_default() {
                        return false;
                    }
                }
                true
            } else {
                false
            }
        }
        OwnedValue::Option(option) => {
            if let Some(msg) = option.as_inst().downcast_ref::<Option<DynamicMessage>>() {
                if let Some(msg) = msg {
                    for field in msg.values.values() {
                        if !field.is_default() {
                            return false;
                        }
                    }
                    true
                } else {
                    true
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Field<A> {
    field_type: FieldType,
    attr: A,
}

impl Field<OwnedValue<'static>> {
    /// Checks if the field is a default value
    pub fn is_default(&self) -> bool {
        is_default_owned_value(&self.attr)
    }

    /// Encodes the tag for a field with the appropriate wire-type
    pub fn encode_key<B: BufMut>(&self, tag: u32, buf: &mut B) {
        if let OwnedValue::Vec(_) = self.attr {
            return;
        }
        match self.field_type {
            FieldType::Bool
            | FieldType::Int32
            | FieldType::Int64
            | FieldType::UInt32
            | FieldType::UInt64
            | FieldType::Enum(_) => encode_key(tag, WireType::Varint, buf),
            FieldType::Double | FieldType::Fixed64 | FieldType::SInt64 | FieldType::SFixed64 => {
                encode_key(tag, WireType::SixtyFourBit, buf)
            }
            FieldType::Float | FieldType::SInt32 | FieldType::Fixed32 | FieldType::SFixed32 => {
                encode_key(tag, WireType::ThirtyTwoBit, buf)
            }
            FieldType::String | FieldType::Message(_) | FieldType::Bytes => {
                encode_key(tag, WireType::LengthDelimited, buf)
            }
            FieldType::Group => {}
        };
    }

    /// Encodes just the contents of a field
    pub fn encode_raw<B: BufMut>(&self, buf: &mut B) {
        match (&self.field_type, &self.attr) {
            (FieldType::Bool, OwnedValue::Bool(b)) => {
                encode_varint(if *b { 1u64 } else { 0u64 }, buf)
            }
            (FieldType::Int32, OwnedValue::I32(i)) => encode_varint(*i as u64, buf),
            (FieldType::Int64, OwnedValue::I64(i)) => encode_varint(*i as u64, buf),
            (FieldType::UInt32, OwnedValue::U32(i)) => encode_varint(*i as u64, buf),
            (FieldType::UInt64, OwnedValue::U64(i)) => encode_varint(*i as u64, buf),
            (FieldType::SInt32, OwnedValue::I32(value)) => {
                encode_varint(((value << 1) ^ (value >> 31)) as u32 as u64, buf)
            }
            (FieldType::SInt64, OwnedValue::I64(value)) => {
                encode_varint(((value << 1) ^ (value >> 63)) as u64, buf)
            }
            (FieldType::Fixed64, OwnedValue::U64(i)) => buf.put_u64_le(*i),
            (FieldType::Fixed32, OwnedValue::U32(i)) => buf.put_u32_le(*i),
            (FieldType::String, OwnedValue::String(s)) => {
                let bytes: &[u8] = s.as_ref();
                encode_varint(bytes.len() as u64, buf);
                buf.put_slice(bytes)
            }
            (FieldType::Float, OwnedValue::F32(f)) => buf.put_f32_le(*f),
            (FieldType::Double, OwnedValue::F64(f)) => buf.put_f64_le(*f),
            (FieldType::Enum(_), OwnedValue::I32(i)) => encode_varint(*i as u64, buf),
            (FieldType::Message(_), OwnedValue::Option(m)) => {
                if let Some(v) = m.value() {
                    if let Some(msg) = v.borrow::<&DynamicMessage>() {
                        let n = msg.encoded_len();
                        encode_varint(n as u64, buf);
                        msg.encode(buf);
                    }
                }
                // For this method in the original implementation I used an extra Vec as the buffer,
                // and then wrote that buffer. I don't remember why I did that, but if there is bug look here
                // Also I don't like that I ignore the error here, but I also don't want to propogate errors throughout
                // -- SPHW
            }
            (FieldType::Message(_), OwnedValue::Struct(m)) => {
                if let Some(msg) = m.as_value().borrow::<&DynamicMessage>() {
                    let n = msg.encoded_len();
                    encode_varint(n as u64, buf);
                    msg.encode(buf);
                }
            }
            (FieldType::Bytes, OwnedValue::Bytes(b)) => {
                encode_varint(b.remaining() as u64, buf);
                buf.put_slice(b.chunk());
            }
            _ => {
                //TODO: Handle the type error
            }
        }
    }

    /// Encodes a the field with a given tag
    pub fn encode<B: BufMut>(&self, tag: u32, buf: &mut B) {
        match &self.attr {
            OwnedValue::Vec(r) if r.is_empty() => {}
            OwnedValue::Vec(r) => {
                let r: Vec<_> = r
                    .values()
                    .iter()
                    .map(|a| Field {
                        field_type: self.field_type.clone(),
                        attr: a.to_owned(),
                    })
                    .collect();
                match self.field_type {
                    FieldType::Bool
                    | FieldType::Int32
                    | FieldType::Int64
                    | FieldType::SInt32
                    | FieldType::SInt64
                    | FieldType::UInt32
                    | FieldType::UInt64
                    | FieldType::Float
                    | FieldType::Double
                    | FieldType::SFixed32
                    | FieldType::SFixed64
                    | FieldType::Fixed32
                    | FieldType::Fixed64
                    | FieldType::Enum(_) => {
                        encode_key(tag, WireType::LengthDelimited, buf);
                        let len: usize = r.iter().map(|value| value.encoded_len_raw()).sum();
                        encode_varint(len as u64, buf);
                        for value in r {
                            value.encode_raw(buf);
                        }
                    }
                    _ => {
                        for value in r {
                            value.encode_key(tag, buf);
                            value.encode_raw(buf);
                        }
                    }
                };
            }
            _ => {
                if !self.is_default() {
                    self.encode_key(tag, buf);
                    self.encode_raw(buf);
                }
            }
        }
    }

    /// Returns the encoded length of a field
    pub fn encoded_len(&self, tag: u32) -> usize {
        match &self.attr {
            OwnedValue::Vec(r) if r.is_empty() => 0,
            OwnedValue::Vec(r) => {
                let values = r.values();
                let iter = values.iter().map(|a| Field {
                    field_type: self.field_type.clone(),
                    attr: a.to_owned(),
                });
                let len = iter.map(|f| f.encoded_len_raw()).sum::<usize>();
                let key_len: usize = match self.field_type {
                    FieldType::Bool
                    | FieldType::Int32
                    | FieldType::Int64
                    | FieldType::SInt32
                    | FieldType::SInt64
                    | FieldType::UInt32
                    | FieldType::UInt64
                    | FieldType::Float
                    | FieldType::Double
                    | FieldType::SFixed32
                    | FieldType::SFixed64
                    | FieldType::Fixed32
                    | FieldType::Fixed64
                    | FieldType::Enum(_) => key_len(tag) + encoded_len_varint(len as u64),
                    _ => key_len(tag) * r.len(),
                };
                key_len + len
            }
            _ => {
                if !self.is_default() {
                    key_len(tag) + self.encoded_len_raw()
                } else {
                    0
                }
            }
        }
    }
    ///Returns the encoded length of a field, not taking into account compacted fields
    pub fn encoded_len_raw(&self) -> usize {
        match (&self.field_type, &self.attr) {
            (FieldType::Bool, OwnedValue::Bool(b)) => {
                encoded_len_varint(if *b { 1u64 } else { 0u64 })
            }
            (FieldType::Int32, OwnedValue::I32(i)) => encoded_len_varint(*i as u64),
            (FieldType::Int64, OwnedValue::I64(i)) => encoded_len_varint(*i as u64),
            (FieldType::UInt32, OwnedValue::U32(i)) => encoded_len_varint(*i as u64),
            (FieldType::UInt64, OwnedValue::U64(i)) => encoded_len_varint(*i as u64),
            (FieldType::SInt32, OwnedValue::I32(value)) => {
                encoded_len_varint(((value << 1) ^ (value >> 31)) as u32 as u64)
            }
            (FieldType::SInt64, OwnedValue::I64(value)) => {
                encoded_len_varint(((value << 1) ^ (value >> 63)) as u64)
            }
            (FieldType::Fixed64, OwnedValue::U64(_)) => 8,
            (FieldType::Fixed32, OwnedValue::U32(_)) => 4,
            (FieldType::String, OwnedValue::String(s)) => {
                let bytes: &[u8] = s.as_ref();
                encoded_len_varint(bytes.len() as u64) + bytes.len()
            }
            (FieldType::Float, OwnedValue::F32(_)) => 4,
            (FieldType::Double, OwnedValue::F64(_)) => 4,
            (FieldType::Enum(_), OwnedValue::I32(i)) => encoded_len_varint(*i as u64),
            (FieldType::Message(_), v @ OwnedValue::Struct(_)) => {
                if let Ok(msg) = IntoInner::<DynamicMessage>::into_inner(v.clone()) {
                    let len = msg.encoded_len();
                    encoded_len_varint(len as u64) + len
                } else {
                    0
                }
            }
            (FieldType::Message(_), v @ OwnedValue::Option(_)) => {
                if let Ok(Some(msg)) = IntoInner::<Option<DynamicMessage>>::into_inner(v.clone()) {
                    let len = msg.encoded_len();
                    encoded_len_varint(len as u64) + len
                } else {
                    0
                }
            }
            (FieldType::Bytes, OwnedValue::Bytes(b)) => {
                encoded_len_varint(b.remaining() as u64) + b.remaining()
            }
            _ => 0,
        }
    }
}
