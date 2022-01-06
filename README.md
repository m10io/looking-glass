Dynamic
==
Dynamic provides reflection for virtually any Rust type. It does this through a set of traits and type-erasing enums. 

This project was recently open-sourced and will have better documentation written up later. For now, the best way to check out the project is to clone it and look at the Rust docs. While this project was only recently open-sourced, it has been iterated on to a point of relative stability. We can't promise that the API won't change, especially for a good reason. But it currently suits all of M10's needs, and so is unlikely to change drastically. 


## Example

``` rust
use dynamic::Typed;
use dynamic_derive::Instance;

#[derive(Instance, Clone, PartialEq)]
struct Foo {
 text: String,
 int: i32,
}

let test = Foo { text: "Test".to_string(), int: -2 };
let val = test.as_value();
let inst = val.as_reflected_struct().unwrap();
let value  = inst.get_value("text").expect("field not found");
let text = value.as_ref().borrow::<&String>().expect("borrow failed");
assert_eq!(text, &test.text);
```

