extern crate darling;
extern crate proc_macro;
extern crate syn;

use crate::proc_macro::TokenStream;
use darling::{ast, util, FromDeriveInput, FromField, FromVariant};
use quote::{format_ident, quote};
use syn::{DataEnum, DeriveInput, Ident, WhereClause};

#[derive(Debug, FromField)]
#[darling(attributes(field))]
struct StructField {
    ident: Option<Ident>,
    #[darling(default)]
    skip: bool,
}

#[derive(Debug, FromDeriveInput)]
#[darling(
    attributes(instance),
    supports(struct_named, enum_newtype, enum_unit, enum_newtype, struct_newtype)
)]
struct StructInstance {
    ident: Ident,
    generics: darling::ast::Generics<syn::GenericParam, WhereClause>,
    data: ast::Data<util::Ignored, StructField>,
    #[darling(default)]
    skip_generics: String,
}

#[proc_macro_derive(Instance, attributes(field, instance))]
pub fn derive(stream: TokenStream) -> TokenStream {
    let parsed: DeriveInput = syn::parse(stream).unwrap();
    let struct_name = parsed.ident.clone();
    let inst_impl = match parsed.data {
        syn::Data::Struct(_) => struct_derive(parsed),
        syn::Data::Enum(e) => enum_derive(e, struct_name),
        syn::Data::Union(_) => todo!(),
    };
    let gen = quote! {

        #inst_impl
    };
    gen.into()
}

fn struct_derive(parsed: DeriveInput) -> proc_macro2::TokenStream {
    let looking_glass = StructInstance::from_derive_input(&parsed).unwrap();
    let struct_name = looking_glass.ident;
    match looking_glass.data {
        ast::Data::Enum(_) => quote! {},
        ast::Data::Struct(ref s) => {
            let get_attr: Vec<_> = s
                .fields
                .iter()
                .enumerate()
                .filter(|(_, f)| !f.skip)
                .map(|(i, field)| {
                    let ident = field
                        .ident
                        .clone()
                        .map(|i| quote! { #i })
                        .unwrap_or_else(|| {
                            let i = syn::Index::from(i);
                            quote! { #i }
                        });
                    quote! {
                        stringify!(#ident) => Some(looking_glass::CowValue::Ref(self.#ident.as_value())),
                    }
                })
                .collect();
            let get_value_impl = quote! {
                match field {
                    #(#get_attr) *
                    _ => None
                }
            };
            let add_attrs: Vec<_> = s
                .fields
                .iter()
                .enumerate()
                .filter(|(_, f)| !f.skip)
                .map(|(i, field)| {
                    let ident = field.ident.clone().map(|i| quote!{ #i }).unwrap_or_else(|| { let i = syn::Index::from(i); quote! { #i } });
                    quote! {
                        map.insert(looking_glass::SmolStr::new(stringify!(#ident)), looking_glass::CowValue::Ref(self.#ident.as_value()));
                    }
                })
                .collect();
            let attributes_impl = quote! {
                let mut map = std::collections::HashMap::new();
                #(#add_attrs)*
                map
            };

            let merge_fields: Vec<_> = s
                .fields
                .iter()
                .enumerate()
                .filter(|(_, f)| {
                    !f.skip
                })
                .map(|(i, field)| {
                    let ident = field.ident.clone().map(|i| quote!{ #i }).unwrap_or_else(|| { let i = syn::Index::from(i); quote! { #i } });
                    quote! {
                        {
                            let attr_ident = looking_glass::SmolStr::new(stringify!(#ident));
                            let new_mask = field_mask.and_then(|m| m.child(&attr_ident));
                            if new_mask.is_some() || field_mask.is_none() {
                                let value = self.get_value(stringify!(#ident)).ok_or_else(|| looking_glass::Error::NotFound(attr_ident.clone()))?;
                                let mut update_attr = instance.get_value(stringify!(#ident)).ok_or_else(|| looking_glass::Error::NotFound(attr_ident.clone()))?.to_owned();
                                match (value.as_ref().as_reflected_struct(), &update_attr) {
                                  (Some(inst), looking_glass::OwnedValue::Struct(update_inst)) => {
                                    let mut inst = inst.boxed_clone();
                                    inst.update(update_inst.as_ref(), new_mask, replace_repeated)?;
                                    update_attr = looking_glass::OwnedValue::Struct(inst);
                                  }
                                  _ => {}
                                }
                                match (value.as_ref().as_reflected_vec(), &update_attr) {
                                  (Some(inst), looking_glass::OwnedValue::Vec(update_inst)) => {
                                    let mut inst = inst.boxed_clone();
                                    inst.update(update_inst.as_ref(), replace_repeated)?;
                                    update_attr = looking_glass::OwnedValue::Vec(inst);
                                  }
                                  _ => {}
                                }
                                self.#ident = update_attr.into_inner()?;
                            }
                        };
                    }
                })
                .collect();
            let update_impl = quote! {
                use looking_glass::IntoInner;
                #(#merge_fields)*
                Ok(())
            };
            let skip_generics = looking_glass.skip_generics.split(',').collect::<Vec<_>>();
            let generic_args = looking_glass
                .generics
                .params
                .iter()
                .map(|arg| {
                    quote! {
                        #arg
                    }
                })
                .collect::<Vec<_>>();
            let generic_args = quote! {
                #(#generic_args),*
            };
            let generic_struct_args = looking_glass
                .generics
                .params
                .iter()
                .map(|arg| match arg {
                    syn::GenericParam::Type(t) => {
                        let ident = &t.ident;
                        quote! { #ident }
                    }
                    syn::GenericParam::Lifetime(l) => {
                        let ident = &l.lifetime;
                        quote! { #ident }
                    }
                    _ => quote! {},
                })
                .collect::<Vec<_>>();
            let where_clauses = looking_glass
                .generics
                .params
                .iter()
                .map(|a| match a {
                    syn::GenericParam::Type(t) => {
                        let ident = &t.ident;
                        let a = ident.clone().to_string();
                        if skip_generics.iter().any(|g| g == &a) {
                            quote! {
                              #ident: 'static
                            }
                        } else {
                            quote! {
                                #ident: 'static + looking_glass::Typed<'s>
                            }
                        }
                    }
                    syn::GenericParam::Lifetime(l) => {
                        let lifetime = &l.lifetime;
                        quote! {
                            #lifetime: 's
                        }
                    }
                    _ => panic!("unsupported generic paramter"),
                })
                .collect::<Vec<_>>();
            let where_clause = if looking_glass.generics.params.is_empty() {
                quote! {}
            } else {
                quote! { where #(#where_clauses),* }
            };
            let static_types = looking_glass
                .generics
                .params
                .iter()
                .map(|arg| match arg {
                    syn::GenericParam::Type(t) => {
                        let ident = &t.ident;
                        quote! { #ident }
                    }
                    syn::GenericParam::Lifetime(_) => {
                        quote! { 'static }
                    }
                    _ => quote! {},
                })
                .collect::<Vec<_>>();
            let gen = quote! {
                impl<'s, #generic_args> looking_glass::Instance<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {
                    fn name(&self) -> looking_glass::SmolStr {
                        looking_glass::SmolStr::new(stringify!(#struct_name))
                    }

                    fn as_inst(&self) -> &(dyn looking_glass::Instance<'s> + 's) {
                        self
                    }
                }

                impl<'s, #generic_args> looking_glass::Typed<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {
                    fn ty() -> looking_glass::ValueTy {
                        looking_glass::ValueTy::Struct(std::any::TypeId::of::<#struct_name<#(#static_types),*>>())
                    }

                    fn as_value<'t>(&'t self) -> looking_glass::Value<'t, 's> where 's: 't {
                        looking_glass::Value::from_struct(self)
                    }
                }

                impl<'s, #generic_args> looking_glass::StructInstance<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {

                    fn get_value<'v>(&'v self, field: &str) -> Option<looking_glass::CowValue<'v, 's>>
                    where
                        's: 'v {

                        use looking_glass::Typed;
                        #get_value_impl
                    }

                    fn values<'v>(&'v self) -> std::collections::HashMap<looking_glass::SmolStr, looking_glass::CowValue<'v, 's>> {
                      use looking_glass::Typed;
                      #attributes_impl
                    }

                    fn update<'v>(
                        &'v mut self,
                        instance: &'v (dyn looking_glass::StructInstance<'s> + 's),
                        field_mask: Option<&looking_glass::FieldMask>,
                        replace_repeated: bool,
                    ) -> Result<(), looking_glass::Error> {
                        #update_impl
                    }

                    fn boxed_clone(&self) -> Box<dyn looking_glass::StructInstance<'s> + 's> {
                        Box::new(self.clone())
                    }

                    fn into_boxed_instance(self: Box<Self>) -> Box<dyn looking_glass::Instance<'s> + 's> {
                        self
                    }
                }
            };
            gen
        }
    }
}

#[derive(Debug, FromVariant)]
struct EnumVariant {
    ident: syn::Ident,
    fields: darling::ast::Fields<StructField>,
}

fn enum_derive(parsed: DataEnum, ident: Ident) -> proc_macro2::TokenStream {
    let matches = parsed
        .variants
        .iter()
        .filter_map(|e| EnumVariant::from_variant(e).ok())
        .map(|var| match var.fields.style {
            ast::Style::Tuple => {
                let fields: Vec<_> = var
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, _)| format_ident!("var{}", i))
                    .collect();
                let var_ident = var.ident;
                quote! {
                    #ident::#var_ident(#(#fields),*) => {
                        EnumField::Tuple {
                            name: looking_glass::SmolStr::new(stringify!(#var_ident)),
                            fields: vec![#(looking_glass::CowValue::Ref(#fields.as_value())),*]
                        }
                    }
                }
            }
            ast::Style::Struct => {
                let var_ident = var.ident;
                let fields: Vec<_> = var
                    .fields
                    .iter()
                    .map(|f| f.ident.clone().unwrap())
                    .collect();
                let inserts = fields.iter().map(|f| {
                    quote! {
                        fields.insert(looking_glass::SmolStr::new(stringify!(#f)), looking_glass::CowValue::Ref(#f.as_value()));
                    }
                });
                quote! {
                    #ident::#var_ident { #(#fields),* } => {
                        let mut fields = std::collections::HashMap::default();
                        #(#inserts)*
                        EnumField::Struct {
                            name: looking_glass::SmolStr::new(stringify!(#var_ident)),
                            fields,
                        }
                    }
                }
            }
            ast::Style::Unit => {
                let var_ident = var.ident;
                quote! {
                    #ident::#var_ident => {
                        EnumField::Unit(looking_glass::SmolStr::new(stringify!(#var_ident)))
                    },
                }
            }
        });

    quote! {
        impl<'s> looking_glass::Instance<'s> for #ident {
            fn name(&self) -> looking_glass::SmolStr {
                looking_glass::SmolStr::new(stringify!(#ident))
            }

            fn as_inst(&self) -> &(dyn looking_glass::Instance<'s> + 's) {
                self
            }
        }

        impl<'s> looking_glass::Typed<'s> for #ident {
            fn ty() -> looking_glass::ValueTy {
                looking_glass::ValueTy::Enum(std::any::TypeId::of::<Self>())
            }

            fn as_value<'a>(&'a self) -> looking_glass::Value<'a, 's> where 's: 'a {
                looking_glass::Value::from_enum(self)
            }
        }

        impl<'s> looking_glass::EnumInstance<'s> for #ident {
            fn boxed_clone(&self) -> Box<dyn looking_glass::EnumInstance<'s> + 's> {
                Box::new(self.clone())
            }


            fn field<'a>(&'a self) -> looking_glass::EnumField<'a, 's> where 's: 'a {
                use looking_glass::EnumField;
                use looking_glass::Typed;
                match self {
                    #(#matches)*
                }
            }

            fn into_boxed_instance(self: Box<Self>) -> Box<dyn looking_glass::Instance<'s> + 'static> {
                self
            }
        }

    }
}
