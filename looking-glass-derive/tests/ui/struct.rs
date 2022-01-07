use looking_glass_derive::Instance;

#[derive(Instance, Clone, PartialEq)]
struct Test {
    test: i32,
    b: bool,
}

#[derive(Instance, Clone, PartialEq)]
struct Foo {
    test: Test,
    bar: i64,
    string: String,
    e: TestE,
    tuple: Tuple<'static, Test>,
    vec_test: Vec<Test>,
    vec_test2: Vec<TestE>,
}

#[derive(Instance, Clone, PartialEq)]
enum TestE {
    Foo(i32),
    StructTest { bar: i32, foo: String },
    Bar,
}

#[derive(Instance, Clone, PartialEq)]
struct Tuple<'a, T: Clone>(#[field(skip)] &'a T);

fn main() {}
