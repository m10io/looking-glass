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
    let dynamic = StructInstance::from_derive_input(&parsed).unwrap();
    let struct_name = dynamic.ident;
    match dynamic.data {
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
                        stringify!(#ident) => Some(dynamic::CowValue::Ref(self.#ident.as_value())),
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
                        map.insert(dynamic::SmolStr::new(stringify!(#ident)), dynamic::CowValue::Ref(self.#ident.as_value()));
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
                            let attr_ident = dynamic::SmolStr::new(stringify!(#ident));
                            let new_mask = field_mask.and_then(|m| m.child(&attr_ident));
                            if new_mask.is_some() || field_mask.is_none() {
                                let value = self.get_value(stringify!(#ident)).ok_or_else(|| dynamic::Error::NotFound(attr_ident.clone()))?;
                                let mut update_attr = instance.get_value(stringify!(#ident)).ok_or_else(|| dynamic::Error::NotFound(attr_ident.clone()))?.to_owned();
                                match (value.as_ref().as_reflected_struct(), &update_attr) {
                                  (Some(inst), dynamic::OwnedValue::Struct(update_inst)) => {
                                    let mut inst = inst.boxed_clone();
                                    inst.update(update_inst.as_ref(), new_mask, replace_repeated)?;
                                    update_attr = dynamic::OwnedValue::Struct(inst);
                                  }
                                  _ => {}
                                }
                                match (value.as_ref().as_reflected_vec(), &update_attr) {
                                  (Some(inst), dynamic::OwnedValue::Vec(update_inst)) => {
                                    let mut inst = inst.boxed_clone();
                                    inst.update(update_inst.as_ref(), replace_repeated)?;
                                    update_attr = dynamic::OwnedValue::Vec(inst);
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
                use dynamic::IntoInner;
                #(#merge_fields)*
                Ok(())
            };
            let skip_generics = dynamic.skip_generics.split(',').collect::<Vec<_>>();
            let generic_args = dynamic
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
            let generic_struct_args = dynamic
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
            let where_clauses = dynamic
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
                                #ident: 'static + dynamic::Typed<'s>
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
            let where_clause = if dynamic.generics.params.is_empty() {
                quote! {}
            } else {
                quote! { where #(#where_clauses),* }
            };
            let static_types = dynamic
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
                impl<'s, #generic_args> dynamic::Instance<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {
                    fn name(&self) -> dynamic::SmolStr {
                        dynamic::SmolStr::new(stringify!(#struct_name))
                    }

                    fn as_inst(&self) -> &(dyn dynamic::Instance<'s> + 's) {
                        self
                    }
                }

                impl<'s, #generic_args> dynamic::Typed<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {
                    fn ty() -> dynamic::ValueTy {
                        dynamic::ValueTy::Struct(std::any::TypeId::of::<#struct_name<#(#static_types),*>>())
                    }

                    fn as_value<'t>(&'t self) -> dynamic::Value<'t, 's> where 's: 't {
                        dynamic::Value::from_struct(self)
                    }
                }

                impl<'s, #generic_args> dynamic::StructInstance<'s> for #struct_name<#(#generic_struct_args),*> #where_clause {

                    fn get_value<'v>(&'v self, field: &str) -> Option<dynamic::CowValue<'v, 's>>
                    where
                        's: 'v {

                        use dynamic::Typed;
                        #get_value_impl
                    }

                    fn values<'v>(&'v self) -> std::collections::HashMap<dynamic::SmolStr, dynamic::CowValue<'v, 's>> {
                      use dynamic::Typed;
                      #attributes_impl
                    }

                    fn update<'v>(
                        &'v mut self,
                        instance: &'v (dyn dynamic::StructInstance<'s> + 's),
                        field_mask: Option<&dynamic::FieldMask>,
                        replace_repeated: bool,
                    ) -> Result<(), dynamic::Error> {
                        #update_impl
                    }

                    fn boxed_clone(&self) -> Box<dyn dynamic::StructInstance<'s> + 's> {
                        Box::new(self.clone())
                    }

                    fn into_boxed_instance(self: Box<Self>) -> Box<dyn dynamic::Instance<'s> + 's> {
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
                            name: dynamic::SmolStr::new(stringify!(#var_ident)),
                            fields: vec![#(dynamic::CowValue::Ref(#fields.as_value())),*]
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
                        fields.insert(dynamic::SmolStr::new(stringify!(#f)), dynamic::CowValue::Ref(#f.as_value()));
                    }
                });
                quote! {
                    #ident::#var_ident { #(#fields),* } => {
                        let mut fields = std::collections::HashMap::default();
                        #(#inserts)*
                        EnumField::Struct {
                            name: dynamic::SmolStr::new(stringify!(#var_ident)),
                            fields,
                        }
                    }
                }
            }
            ast::Style::Unit => {
                let var_ident = var.ident;
                quote! {
                    #ident::#var_ident => {
                        EnumField::Unit(dynamic::SmolStr::new(stringify!(#var_ident)))
                    },
                }
            }
        });

    quote! {
        impl<'s> dynamic::Instance<'s> for #ident {
            fn name(&self) -> dynamic::SmolStr {
                dynamic::SmolStr::new(stringify!(#ident))
            }

            fn as_inst(&self) -> &(dyn dynamic::Instance<'s> + 's) {
                self
            }
        }

        impl<'s> dynamic::Typed<'s> for #ident {
            fn ty() -> dynamic::ValueTy {
                dynamic::ValueTy::Enum(std::any::TypeId::of::<Self>())
            }

            fn as_value<'a>(&'a self) -> dynamic::Value<'a, 's> where 's: 'a {
                dynamic::Value::from_enum(self)
            }
        }

        impl<'s> dynamic::EnumInstance<'s> for #ident {
            fn boxed_clone(&self) -> Box<dyn dynamic::EnumInstance<'s> + 's> {
                Box::new(self.clone())
            }


            fn field<'a>(&'a self) -> dynamic::EnumField<'a, 's> where 's: 'a {
                use dynamic::EnumField;
                use dynamic::Typed;
                match self {
                    #(#matches)*
                }
            }

            fn into_boxed_instance(self: Box<Self>) -> Box<dyn dynamic::Instance<'s> + 'static> {
                self
            }
        }

    }
}
