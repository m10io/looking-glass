use crate::*;
use bytes::BytesMut;
use looking_glass::{CowValue, FieldMask, StructInstance, Typed};
use test_protos::*;
use prost::Message;
use prost_types::FileDescriptorSet;
use std::default::Default;
use std::sync::Arc;

fn file_descriptor_set() -> FileDescriptorSet {
    let bytes = include_bytes!("test.pb");
    FileDescriptorSet::decode(&bytes[..]).expect("failed to decode protobufs")
}

fn tests_db() -> DescriptorDatabase {
    let set = file_descriptor_set();
    let file = set.file.first().expect("no file found");
    let mut db = DescriptorDatabase::default();
    db.add_file_descriptor_proto(&file);
    db
}

#[test]
fn test_file_descriptor_parse() {
    let db = tests_db();
    let msg = db
        .descriptor(".m10.tests.Test")
        .expect("failed to get message descriptor");
    assert_eq!(msg.name, ".m10.tests.Test");
}

#[test]
fn test_single_access() {
    let mut bytes = vec![];
    let test = Test {
        name: "test".to_string(),
        integer_32: -1,
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = tests_db();
    let view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let message = MessageView::new(view, ".m10.tests.Test".to_string(), Arc::new(db))
        .expect("msg parse failed");
    assert_eq!(
        message.view_tag(1).expect("failed to view tag"),
        &ValueView::String("test".into())
    );
    assert_eq!(
        message.view_tag(2).expect("failed to build raw view"),
        &ValueView::I32(-1)
    )
}

#[test]
fn test_embedded_access() {
    let mut bytes = vec![];
    let test = Test {
        name: "test".to_string(),
        integer_32: -1,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![1],
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = tests_db();
    let view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let message = MessageView::new(view, ".m10.tests.Test".to_string(), Arc::new(db))
        .expect("msg parse failed");
    let embedded = message.view_tag(3).expect("failed to view tag");
    if let ValueView::Message(Some(msg)) = embedded {
        assert_eq!(
            msg.view_tag(1).expect("failed to build raw view"),
            &ValueView::I32(1)
        )
    } else {
        unreachable!()
    }
}

#[test]
fn test_message_conversion() {
    let mut bytes = vec![];
    let test = Test {
        name: "test".to_string(),
        integer_32: -1,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![1, 2, 3],
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = tests_db();
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.Test".to_string(), Arc::new(db))
        .expect("msg parse failed");
    let message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let name_field = message.get_value("name").expect("field not found");
    assert_eq!(name_field, CowValue::Ref("test".as_value()));
    let int_field = message.get_value("integer_32").expect("field not found");
    assert_eq!(int_field, CowValue::Ref((-1i32).as_value()));
    let repeated_field = message.get_value("repeated_num").expect("field not found");
    assert_eq!(
        repeated_field,
        CowValue::Ref((vec![1, 2, 3] as Vec<i32>).as_value())
    )
}

#[test]
fn test_message_encode() {
    let mut bytes = BytesMut::new();
    let test = Test {
        name: "test".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = tests_db();
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.Test".to_string(), Arc::new(db))
        .expect("msg parse failed");
    let message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes_2 = BytesMut::new();
    message.encode(&mut bytes_2);
    assert_eq!(bytes, bytes_2);
}

#[test]
fn test_complex_message_encode() {
    let mut bytes = vec![];
    let test = ComplexTest {
        a: Some(ComplexTestEmbedded {
            a: vec![TestEnum::A.into(), TestEnum::B.into()],
        }),
        ..Default::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = tests_db();
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.ComplexTest".to_string(), Arc::new(db))
        .expect("msg parse failed");
    let message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes_2 = vec![];
    message.encode(&mut bytes_2);
    assert_eq!(bytes, bytes_2);
}

#[test]
fn test_message_merge() {
    let mut bytes = vec![];
    let test = Test {
        name: "test".to_string(),
        integer_32: -1,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![1, 2],
        a_payload: vec![],
        id: vec![],
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = Arc::new(tests_db());
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.Test".to_string(), Arc::clone(&db))
        .expect("msg parse failed");
    let mut message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes = vec![];
    let test = Test {
        id: vec![],
        name: "foo".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![3],
        a_payload: vec![],
    };
    test.encode(&mut bytes).expect("failed to encode");
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view =
        MessageView::new(raw_view, ".m10.tests.Test".to_string(), db).expect("msg parse failed");
    let update = DynamicMessage::new(&view).expect("failed to parse");
    message
        .update(&update, None, false)
        .expect("failed to merge");
    let int_field = message.get_value("integer_32").expect("field not found");
    assert_eq!(int_field, CowValue::Ref(5i32.as_value()));
    let repeated_field = message.get_value("repeated_num").expect("field not found");
    assert_eq!(
        repeated_field,
        CowValue::Ref((vec![1, 2, 3] as Vec<i32>).as_value())
    )
}

#[test]
fn test_message_merge_encode() {
    let mut bytes = BytesMut::new();
    let test = Test {
        name: "test".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = Arc::new(tests_db());
    let raw_view = RawMessageView::new(bytes.freeze()).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.Test".to_string(), Arc::clone(&db))
        .expect("msg parse failed");
    let mut message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes = BytesMut::new();
    let test = Test {
        name: "foo".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        ..Test::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let raw_view = RawMessageView::new(bytes.freeze()).expect("msg parse failed");
    let view =
        MessageView::new(raw_view, ".m10.tests.Test".to_string(), db).expect("msg parse failed");
    let update = DynamicMessage::new(&view).expect("failed to parse");
    message
        .update(&update, None, false)
        .expect("failed to merge");
    let mut bytes = BytesMut::new();
    message.encode(&mut bytes);
    let mut bytes_good = BytesMut::new();
    let test = Test {
        name: "foo".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        ..Test::default()
    };
    test.encode(&mut bytes_good).expect("failed to encode");
    assert_eq!(bytes_good.freeze(), bytes.freeze());
}

#[test]
fn test_message_masked() {
    let mut bytes = vec![];
    let test = Test {
        id: vec![],
        name: "test".to_string(),
        integer_32: -1,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![1, 2],
        a_payload: vec![],
    };
    test.encode(&mut bytes).expect("failed to encode");
    let db = Arc::new(tests_db());
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.Test".to_string(), Arc::clone(&db))
        .expect("msg parse failed");
    let mut message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes = vec![];
    let test = Test {
        id: vec![],
        name: "foo".to_string(),
        integer_32: 5,
        embedded: Some(TestEmbedded { number: 1 }),
        repeated_num: vec![3],
        a_payload: vec![],
    };
    test.encode(&mut bytes).expect("failed to encode");
    let raw_view = RawMessageView::new(&bytes[..]).expect("msg parse failed");
    let view =
        MessageView::new(raw_view, ".m10.tests.Test".to_string(), db).expect("msg parse failed");
    let update = DynamicMessage::new(&view).expect("failed to parse");
    message
        .update(&update, Some(&FieldMask::new(vec!["repeated_num"])), false)
        .expect("failed to merge");
    let int_field = message.get_value("integer_32").expect("field not found");
    assert_eq!(int_field, CowValue::Ref((-1i32).as_value()));
    let repeated_field = message.get_value("repeated_num").expect("field not found");
    assert_eq!(
        repeated_field,
        CowValue::Ref((vec![1, 2, 3] as Vec<i32>).as_value())
    )
}

#[test]
fn test_message_merge_encode_masked() {
    let mut bytes = BytesMut::new();
    let user = User {
        owner: vec![1, 2, 3, 4, 5, 6, 7, 8],
        name: "test".to_string(),
        id: vec![1, 2, 3, 4, 6, 9, 12, 22],
        accounts: vec![AccountRef {
            ledger_id: "test".to_string(),
            account_id: vec![1, 2, 3, 4, 6, 9, 12, 22],
        }],
        ..User::default()
    };
    user.encode(&mut bytes).expect("failed to encode");
    let db = Arc::new(tests_db());
    let raw_view = RawMessageView::new(bytes.freeze()).expect("msg parse failed");
    let view = MessageView::new(raw_view, ".m10.tests.User".to_string(), Arc::clone(&db))
        .expect("msg parse failed");
    let mut message = DynamicMessage::new(&view).expect("failed to build looking_glass message");
    let mut bytes = BytesMut::new();
    let test = User {
        notification_preferences: vec![1, 2, 3],
        ..User::default()
    };
    test.encode(&mut bytes).expect("failed to encode");
    let raw_view = RawMessageView::new(bytes.freeze()).expect("msg parse failed");
    let update = MessageView::new(raw_view, ".m10.tests.User".to_string(), db.clone())
        .expect("msg parse failed");
    let update = DynamicMessage::new(&update).unwrap();
    message
        .update(
            &update,
            Some(&FieldMask::new(vec!["notification_preferences"])),
            false,
        )
        .expect("failed to merge");
    let mut bytes = BytesMut::new();
    message.encode(&mut bytes);
    let doc = MessageView::new(
        RawMessageView::new(bytes.freeze()).unwrap(),
        ".m10.tests.User".to_string(),
        db,
    )
    .expect("decode failed");
}
