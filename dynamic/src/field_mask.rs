use std::collections::HashMap;

use smol_str::SmolStr;

/// As tree structure that repersents a set of nested fields.
///
/// This is based on the `FieldMaskTree` that is found in the C++ & Java protobuf libraries. It can be used for conditionally clearing or updating [`crate::Instance`]. A tree is used to simplify & speed up filtering fields
/// A field mask contains a series of paths to attributes such as `["foo.a", "foo.b", "bar"]`. Internally that would be repersented as a tree like below:
/// ```text
///     foo    bar
///    /   \
///   a     b
/// ```
#[derive(Default)]
pub struct FieldMask {
    children: HashMap<SmolStr, FieldMask>,
}

impl FieldMask {
    pub fn new<'a, I: IntoIterator<Item = &'a str>>(iter: I) -> FieldMask {
        let mut mask = FieldMask::default();
        for path in iter {
            let path = path.split('.');
            let mut new_mask = &mut mask;
            for p in path {
                new_mask = new_mask.children.entry(SmolStr::new(p)).or_default();
            }
        }
        mask
    }

    /// Returns a field mask for a specific field.
    pub fn child(&self, path: &SmolStr) -> Option<&FieldMask> {
        self.children.get(path)
    }
}
