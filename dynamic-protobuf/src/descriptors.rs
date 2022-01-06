use crate::{StrTranche, Tranche, ValueView};
use dynamic::SmolStr;
use prost_types::{
    field_descriptor_proto, DescriptorProto, FieldDescriptorProto, FileDescriptorProto,
};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, PartialEq)]
/// A parsed message descriptor
pub struct MessageDescriptor {
    pub name: SmolStr,
    pub fields: BTreeMap<u32, FieldDescriptor>,
    pub tags_by_name: HashMap<SmolStr, u32>,
}

impl MessageDescriptor {
    fn from_proto(path: &str, proto: &DescriptorProto) -> MessageDescriptor {
        let name = format!("{}.{}", path, proto.name());
        let fields = proto
            .field
            .iter()
            .map(|f| (f.number() as u32, FieldDescriptor::from(f)))
            .collect();
        let tags_by_name = proto
            .field
            .iter()
            .map(|f| (f.name().into(), f.number() as u32))
            .collect();
        MessageDescriptor {
            name: name.into(),
            fields,
            tags_by_name,
        }
    }

    pub fn field_by_name(&self, name: &str) -> Option<&FieldDescriptor> {
        let tag = self.tags_by_name.get(name)?;
        self.fields.get(tag)
    }
}

impl From<&MessageDescriptor> for DescriptorProto {
    fn from(desc: &MessageDescriptor) -> DescriptorProto {
        DescriptorProto {
            name: desc.name.split('.').last().map(|n| n.to_string()),
            field: desc.fields.iter().map(|(_, desc)| desc.into()).collect(),
            ..Default::default()
        }
    }
}

/// A database of message and enum descriptors.
///
/// Most structs will either take a reference to this, or an Arc wrapped version.
/// Because of this it is recommended to build the entire database ahead of time, and then
/// freeze it in an Arc.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct DescriptorDatabase {
    message_descriptors: HashMap<SmolStr, MessageDescriptor>,
    enum_descriptors: HashMap<SmolStr, EnumDescriptor>,
}

impl DescriptorDatabase {
    pub fn add_file_descriptor_proto(&mut self, file_descriptor_proto: &FileDescriptorProto) {
        for message in &file_descriptor_proto.message_type {
            self.add_descriptor_proto(&format!(".{}", file_descriptor_proto.package()), message)
        }
    }

    fn add_descriptor(&mut self, descriptor: MessageDescriptor) {
        self.message_descriptors
            .insert(descriptor.name.clone(), descriptor);
    }

    pub fn add_descriptor_proto(&mut self, path: &str, descriptor_proto: &DescriptorProto) {
        let descriptor = MessageDescriptor::from_proto(path, descriptor_proto);
        for nested_type in &descriptor_proto.nested_type {
            self.add_descriptor_proto(&descriptor.name, nested_type);
        }
        self.add_descriptor(descriptor)
    }

    pub fn descriptor(&self, name: &str) -> Option<&MessageDescriptor> {
        self.message_descriptors.get(name)
    }
}

impl From<&DescriptorDatabase> for Vec<FileDescriptorProto> {
    fn from(db: &DescriptorDatabase) -> Vec<FileDescriptorProto> {
        db.message_descriptors
            .iter()
            .map(|(name, desc)| {
                let parts = name.split('.').collect::<Vec<&str>>();
                FileDescriptorProto {
                    name: Some(parts[0..parts.len() - 1].join(".")),
                    package: Some(parts[1..parts.len() - 1].join(".")),
                    message_type: vec![desc.into()],
                    ..Default::default()
                }
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct FieldDescriptor {
    pub name: SmolStr,
    pub tag: u32,
    pub field_type: FieldType,
    pub repeated: bool,
}

impl From<&FieldDescriptorProto> for FieldDescriptor {
    fn from(proto: &FieldDescriptorProto) -> FieldDescriptor {
        FieldDescriptor {
            name: proto.name().into(),
            tag: proto.number() as u32,
            field_type: proto.into(),
            repeated: proto.label() == field_descriptor_proto::Label::Repeated,
        }
    }
}

impl From<&FieldDescriptorProto> for FieldType {
    fn from(proto: &FieldDescriptorProto) -> FieldType {
        match proto.r#type() {
            field_descriptor_proto::Type::Double => FieldType::Double,
            field_descriptor_proto::Type::Float => FieldType::Float,
            field_descriptor_proto::Type::Int64 => FieldType::Int64,
            field_descriptor_proto::Type::Uint64 => FieldType::UInt64,
            field_descriptor_proto::Type::Int32 => FieldType::Int32,
            field_descriptor_proto::Type::Fixed64 => FieldType::Fixed64,
            field_descriptor_proto::Type::Fixed32 => FieldType::Fixed32,
            field_descriptor_proto::Type::Bool => FieldType::Bool,
            field_descriptor_proto::Type::String => FieldType::String,
            field_descriptor_proto::Type::Group => FieldType::Group,
            field_descriptor_proto::Type::Bytes => FieldType::Bytes,
            field_descriptor_proto::Type::Uint32 => FieldType::UInt32,
            field_descriptor_proto::Type::Sfixed32 => FieldType::SFixed32,
            field_descriptor_proto::Type::Sfixed64 => FieldType::SFixed64,
            field_descriptor_proto::Type::Sint32 => FieldType::SInt32,
            field_descriptor_proto::Type::Sint64 => FieldType::SInt64,
            field_descriptor_proto::Type::Message => FieldType::Message(proto.type_name().into()),
            field_descriptor_proto::Type::Enum => FieldType::Enum(proto.type_name().into()),
        }
    }
}

impl From<&FieldType> for i32 {
    fn from(field_type: &FieldType) -> i32 {
        match field_type {
            FieldType::Double => field_descriptor_proto::Type::Double.into(),
            FieldType::Float => field_descriptor_proto::Type::Float.into(),
            FieldType::Int64 => field_descriptor_proto::Type::Int64.into(),
            FieldType::UInt64 => field_descriptor_proto::Type::Uint64.into(),
            FieldType::Int32 => field_descriptor_proto::Type::Int32.into(),
            FieldType::Fixed64 => field_descriptor_proto::Type::Fixed64.into(),
            FieldType::Fixed32 => field_descriptor_proto::Type::Fixed32.into(),
            FieldType::Bool => field_descriptor_proto::Type::Bool.into(),
            FieldType::String => field_descriptor_proto::Type::String.into(),
            FieldType::Group => field_descriptor_proto::Type::Group.into(),
            FieldType::Bytes => field_descriptor_proto::Type::Bytes.into(),
            FieldType::UInt32 => field_descriptor_proto::Type::Uint32.into(),
            FieldType::SFixed32 => field_descriptor_proto::Type::Sfixed32.into(),
            FieldType::SFixed64 => field_descriptor_proto::Type::Sfixed64.into(),
            FieldType::SInt32 => field_descriptor_proto::Type::Sint32.into(),
            FieldType::SInt64 => field_descriptor_proto::Type::Sint64.into(),
            FieldType::Message(_) => field_descriptor_proto::Type::Message.into(),
            FieldType::Enum(_) => field_descriptor_proto::Type::Enum.into(),
        }
    }
}
impl From<&FieldDescriptor> for FieldDescriptorProto {
    fn from(desc: &FieldDescriptor) -> FieldDescriptorProto {
        let type_name = match &desc.field_type {
            FieldType::Message(name) | FieldType::Enum(name) => Some(name.to_string()),
            _ => None,
        };
        FieldDescriptorProto {
            name: Some(desc.name.to_string()),
            number: Some(desc.tag as i32),
            type_name,
            r#type: Some((&desc.field_type).into()),
            label: Some(if desc.repeated {
                field_descriptor_proto::Label::Repeated.into()
            } else {
                field_descriptor_proto::Label::Required.into()
            }),
            ..Default::default()
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum FieldType {
    /// The `double` type.
    Double,
    /// The `float` type.
    Float,
    /// The `int64` type.
    Int64,
    /// The `uint64` type.
    UInt64,
    /// The `int32` type.
    Int32,
    /// The `fixed64` type.
    Fixed64,
    /// The `fixed32` type.
    Fixed32,
    /// The `bool` type.
    Bool,
    /// The `string` type.
    String,
    /// The `group` type.
    Group,
    /// The `bytes` type.
    Bytes,
    /// The `uint32` type.
    UInt32,
    /// The `sfixed32` type.
    SFixed32,
    /// The `sfixed64` type.
    SFixed64,
    /// The `sint32` type.
    SInt32,
    /// The `sint64` type.
    SInt64,
    /// A message that is yet to be resolved.
    Message(SmolStr),
    /// An enum that is yet to be resolved.
    Enum(SmolStr),
}

impl FieldType {
    pub fn default_value_view<T: Tranche>(&self) -> ValueView<T> {
        match self {
            FieldType::Double => ValueView::F64(0.0),
            FieldType::Float => ValueView::F32(0.0),
            FieldType::Int64 => ValueView::I64(0),
            FieldType::UInt64 => ValueView::U64(0),
            FieldType::Int32 => ValueView::I32(0),
            FieldType::Fixed64 => ValueView::Fixed64(0),
            FieldType::Fixed32 => ValueView::Fixed32(0),
            FieldType::Bool => ValueView::Bool(false),
            FieldType::String => ValueView::String(StrTranche::new(&mut T::default())),
            FieldType::Group => todo!(),
            FieldType::Bytes => ValueView::Bytes(T::default()),
            FieldType::UInt32 => ValueView::U32(0),
            FieldType::SFixed32 => ValueView::SFixed32(0),
            FieldType::SFixed64 => ValueView::SFixed64(0),
            FieldType::SInt32 => ValueView::S32(0),
            FieldType::SInt64 => ValueView::S64(0),
            FieldType::Message(_) => ValueView::Message(None),
            FieldType::Enum(_) => ValueView::Enum(0),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct EnumDescriptor {}
//TODO: Implement enums
