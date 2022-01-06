use crate::*;
pub use bytes::Bytes;
pub use smol_str::SmolStr;
use std::collections::HashMap;

/// Any reflected type
pub trait Instance<'ty>: TypedObj + Send + Sync {
    /// Returns the name of a instance
    fn name(&self) -> SmolStr;

    fn as_inst(&self) -> &(dyn Instance<'ty> + 'ty);
}

impl<'ty> dyn Instance<'ty> + 'ty {
    /// Downcasts to a concere type
    #[inline]
    pub fn downcast_ref<'val, 't, T: Typed<'ty> + 'ty>(&'val self) -> Option<&'val T>
    where
        'ty: 'val,
    {
        if self.inst_ty() == T::ty() {
            // Safety: This is essentially a copy from `Any` and follows much the same logic.
            // The major difference is that we allow non-static casts.
            // The above check makes sure that the lifetime erased type T, and Self are the same.
            // However that does not ensure that the lifetimes match.
            // We ensure that saftey through the lifetime bounds. The lifetime bound `T: 'ty`
            // ensures that we only ever give out a lifetime that 'val (the lifetime of the parent struct) out lives.
            // Which is equivalent to a safe Rust cast (&'a () as &'b () where 'a: 'b).
            Some(unsafe { &*(self as *const dyn Instance<'ty> as *const T) })
        } else {
            None
        }
    }
}

/// A extension trait that provides downcasting
pub trait DowncastExt<'ty> {
    /// Downcasts to a boxed concrete type
    fn downcast<T: Typed<'ty> + 'ty>(self) -> Option<Box<T>>;
}
impl<'ty> DowncastExt<'ty> for Box<dyn Instance<'ty> + 'ty> {
    fn downcast<T: Typed<'ty> + 'ty>(self) -> Option<Box<T>> {
        if self.inst_ty() == T::ty() {
            unsafe {
                // Safety: This is also a copy from `Any`, and its lifetime saftey is guarenteed in
                // same way as [`Instance::downcast_ref`]
                let raw: *mut (dyn Instance<'ty> + 'ty) = Box::into_raw(self);
                Some(Box::from_raw(raw as *mut T))
            }
        } else {
            None
        }
    }
}

/// A reflected struct
pub trait StructInstance<'s>: Instance<'s> {
    /// Returns a reference to a field in a struct
    fn get_value<'a>(&'a self, field: &str) -> Option<CowValue<'a, 's>>
    where
        's: 'a;

    /// Updates an instance based on the instance passed in. If a field mask is specified only the fields passed with the mask will be updated.
    fn update<'a>(
        &'a mut self,
        update: &'a (dyn StructInstance<'s> + 's),
        field_mask: Option<&FieldMask>,
        replace_repeated: bool,
    ) -> Result<(), Error>;

    /// Returns a HashMap containing all the attributes of the instance.
    fn values<'a>(&'a self) -> HashMap<SmolStr, CowValue<'a, 's>>;

    /// Returns a clone of the instance in a [`Box`].
    fn boxed_clone(&self) -> Box<dyn StructInstance<'s> + 's>;

    /// Casts `Self` to a `Box<dyn Instance>`
    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s> + 's>;
}

impl<'s> std::fmt::Debug for dyn StructInstance<'s> + 's {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut builder = f.debug_struct(&self.name());
        for (name, val) in self.values() {
            builder.field(&name, &val);
        }
        builder.finish()
    }
}

impl<'s> PartialEq for dyn StructInstance<'s> + 's {
    fn eq(&self, other: &Self) -> bool {
        self.values() == other.values()
    }
}

impl<'s> Clone for Box<dyn StructInstance<'s> + 's> {
    fn clone(&self) -> Self {
        self.boxed_clone()
    }
}

/// A reflected enum
pub trait EnumInstance<'s>: Instance<'s> {
    /// Returns a clone of the instance in a [`Box`].
    fn boxed_clone(&self) -> Box<dyn EnumInstance<'s> + 's>;
    /// Returns the current value of the reflected enum.
    fn field<'a>(&'a self) -> EnumField<'a, 's>
    where
        's: 'a;

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s>>;
}

/// A reflected field of an enum
#[derive(PartialEq, Clone, Debug)]
pub enum EnumField<'a, 's> {
    Unit(SmolStr),
    Tuple {
        name: SmolStr,
        fields: Vec<CowValue<'a, 's>>,
    },
    Struct {
        name: SmolStr,
        fields: HashMap<SmolStr, CowValue<'a, 's>>,
    },
}

impl<'s> PartialEq for dyn EnumInstance<'s> + 's {
    fn eq(&self, other: &Self) -> bool {
        self.field() == other.field()
    }
}

impl<'s> std::fmt::Debug for dyn EnumInstance<'s> + 's {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.field() {
            EnumField::Unit(name) => f.write_str(name.as_str()),
            EnumField::Tuple { name, fields } => {
                let mut tuple = f.debug_tuple(name.as_str());
                for field in fields {
                    tuple.field(&field);
                }
                tuple.finish()
            }
            EnumField::Struct { name, fields } => {
                let mut s = f.debug_struct(&name);
                for (name, field) in fields {
                    s.field(&name, &field);
                }
                s.finish()
            }
        }
    }
}

impl<'s> Clone for Box<dyn EnumInstance<'s> + 's> {
    fn clone(&self) -> Self {
        self.boxed_clone()
    }
}

/// A reflected [`Vec`]
pub trait VecInstance<'s>: Instance<'s> + 's {
    /// Returns a reference to a field in a reflected vec
    fn get_value<'a>(&'a self, i: usize) -> Option<Value<'a, 's>>
    where
        's: 'a;

    /// Returns a Vec containing all the attributes of the instance.
    fn values<'a>(&'a self) -> Vec<CowValue<'a, 's>>
    where
        's: 'a;

    /// Returns a clone of the instance in a [`Box`].
    fn boxed_clone(&self) -> Box<dyn VecInstance<'s> + 's>;

    /// Updates an instance based on the instance passed in. If a field mask is specified only the fields passed with the mask will be updated.
    fn update<'a>(
        &'a mut self,
        update: &'a (dyn VecInstance<'s> + 's),
        replace_repeated: bool,
    ) -> Result<(), Error>;

    /// Returns whether the vec is empty
    fn is_empty(&self) -> bool;

    /// Returns whether the length of the vec;
    fn len(&self) -> usize;

    fn vec_eq(&self, inst: &(dyn VecInstance<'s> + 's)) -> bool;

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s> + 's>;
}

impl<'s> std::fmt::Debug for dyn VecInstance<'s> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.values().iter()).finish()
    }
}

impl<'s> PartialEq for dyn VecInstance<'s> + 's {
    fn eq(&self, other: &Self) -> bool {
        self.vec_eq(other)
    }
}

impl<'s> Clone for Box<dyn VecInstance<'s> + 's> {
    fn clone(&self) -> Self {
        self.boxed_clone()
    }
}

/// A reflected [`Option`]
pub trait OptionInstance<'s>: Instance<'s> {
    /// Returns a reference to a field in a reflected vec
    fn value<'a>(&'a self) -> Option<Value<'a, 's>>
    where
        's: 'a;

    /// Returns a clone of the instance in a [`Box`].
    fn boxed_clone(&self) -> Box<dyn OptionInstance<'s> + 's>;

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s> + 's>;
}

impl<'s> std::fmt::Debug for dyn OptionInstance<'s> + 's {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut build = f.debug_tuple(&self.name());
        if let Some(val) = self.value() {
            build.field(&val);
        }
        build.finish()
    }
}

impl<'s, T: Typed<'s> + Clone + 's> Typed<'s> for Option<T> {
    fn ty() -> ValueTy {
        ValueTy::Option(Box::new(T::ty()))
    }

    fn as_value<'a>(&'a self) -> Value<'a, 's>
    where
        's: 'a,
    {
        Value::from_option(self)
    }
}

impl<'s> PartialEq for dyn OptionInstance<'s> + 's {
    fn eq(&self, other: &Self) -> bool {
        self.value() == other.value()
    }
}

impl<'s> Clone for Box<dyn OptionInstance<'s> + 's> {
    fn clone(&self) -> Self {
        self.boxed_clone()
    }
}

impl<'a, T: Typed<'a> + Clone + PartialEq + 'a> Instance<'a> for Vec<T> {
    fn name(&self) -> SmolStr {
        format!("Vec<{:?}>", T::ty()).into()
    }

    fn as_inst(&self) -> &(dyn Instance<'a> + 'a) {
        self
    }
}

impl<'s, T: Typed<'s> + Clone + 's + PartialEq> VecInstance<'s> for Vec<T> {
    fn get_value<'a>(&'a self, i: usize) -> Option<Value<'a, 's>>
    where
        's: 'a,
    {
        let val = self.get(i)?.as_value();
        Some(val)
    }

    fn values<'a>(&'a self) -> Vec<CowValue<'a, 's>>
    where
        's: 'a,
    {
        self.iter().map(|e| CowValue::Ref(e.as_value())).collect()
    }

    fn boxed_clone(&self) -> Box<dyn VecInstance<'s> + 's> {
        Box::new(self.clone())
    }

    fn update<'a>(
        &'a mut self,
        update: &'a (dyn VecInstance<'s> + 's),
        replace_repeated: bool,
    ) -> Result<(), Error> {
        if let Some(vec) = Value::from_vec(update).borrow::<&Vec<T>>() {
            if replace_repeated {
                let vec = vec.clone();
                let _ = std::mem::replace(self as &mut Vec<T>, vec);
            } else {
                self.extend_from_slice(&vec[..]);
            }
        }
        Ok(())
    }

    fn is_empty(&self) -> bool {
        Vec::is_empty(self)
    }

    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn vec_eq(&self, inst: &(dyn VecInstance<'s> + 's)) -> bool {
        inst.as_inst().downcast_ref::<Self>() == Some(self)
    }

    fn into_boxed_instance(self: Box<Self>) -> Box<dyn Instance<'s> + 's> {
        self
    }
}

impl<'s, T: Typed<'s> + Clone + 's + PartialEq> Typed<'s> for Vec<T> {
    fn ty() -> ValueTy {
        ValueTy::Vec(Box::new(T::ty()))
    }

    fn as_value<'a>(&'a self) -> Value<'a, 's>
    where
        's: 'a,
    {
        Value::from_vec(self)
    }
}

impl<'s> Instance<'s> for String {
    fn name(&self) -> SmolStr {
        "String".into()
    }

    fn as_inst(&self) -> &(dyn Instance<'s> + 's) {
        self
    }
}

impl<'s> Instance<'s> for Bytes {
    fn name(&self) -> SmolStr {
        "Bytes".into()
    }

    fn as_inst(&self) -> &(dyn Instance<'s> + 's) {
        self
    }
}
