use crate::{HashMapInstance, Instance, IntoInner, Typed};
use std::ops::Deref;
use std::collections::HashMap;

#[test]
fn test_value_copy_types() {
    let i: u32 = 5;
    let val = i.as_value();
    assert_eq!(Some(i), val.borrow::<u32>())
}

#[test]
fn test_value_ref_types() {
    let string = "test";
    let val = string.as_value();
    assert_eq!("test", val.borrow::<&str>().unwrap().deref());
    let vec: Vec<u64> = vec![1, 2, 3];
    let val = vec.as_value();
    assert_eq!(&vec, val.borrow::<&Vec<u64>>().unwrap());
    let test = val.as_reflected_vec().unwrap();
    assert_eq!(test.get_value(0).unwrap().borrow::<u64>().unwrap(), 1);

    let vec: Vec<String> = vec!["test".to_string(), "abc".to_string()];
    let val = vec.as_value();
    assert_eq!(&vec, val.borrow::<&Vec<String>>().unwrap());
    let test = val.as_reflected_vec().unwrap();
    assert_eq!(
        test.get_value(0).unwrap().borrow::<&String>().unwrap(),
        &"test".to_string()
    );
    let map: HashMap<String, String> = HashMap::from([
        ("some_key_1".to_string(), "some_value_1".to_string()),
        ("some_key_2".to_string(), "some_value_2".to_string()),
        ("some_key_3".to_string(), "some_value_3".to_string()),
    ]);
    let val = map.as_value();
    assert_eq!(&map, val.borrow::<&HashMap<String, String>>().unwrap());
}

#[test]
fn test_into_inner() {
    let vec: Vec<u64> = vec![1, 2, 3];
    let val = vec.as_value();
    let owned = val.to_owned();
    let vecb: Vec<u64> = owned.into_inner().expect("into inner failed");
    assert_eq!(vec, vecb);
}

#[test]
fn test_hashmap_contains() {
    let map: HashMap<String, String> = HashMap::from([
        ("some_key_1".to_string(), "some_value_1".to_string()),
        ("some_key_2".to_string(), "some_value_2".to_string()),
        ("some_key_3".to_string(), "some_value_3".to_string()),
    ]);
    let inst = map.as_value().as_reflected_hashmap().unwrap();

    let submap: HashMap<String, String> = HashMap::from([
        ("some_key_1".to_string(), "some_value_1".to_string()),
        ("some_key_2".to_string(), "some_value_2".to_string()),
    ]);
    let sub_inst = submap.as_value().as_reflected_hashmap().unwrap();

    assert!(inst.contains(sub_inst));
}