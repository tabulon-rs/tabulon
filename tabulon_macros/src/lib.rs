use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, FnArg, ItemFn, Pat, PatType, Type, TypeReference};

// #[function]
// Supports numeric parameters (f64) and optionally a single context parameter
// of type &Ctx or &mut Ctx at any position in the parameter list. The context
// parameter is NOT counted toward arity and will be supplied via the hidden
// ctx pointer in the generated shim.
#[proc_macro_attribute]
pub fn function(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    let sig = &func.sig;
    let ident = &sig.ident;

    // Verify return type is f64
    let ret_ok = match &sig.output {
        syn::ReturnType::Type(_, ty) => matches!(**ty, Type::Path(ref tp) if tp.path.is_ident("f64")),
        syn::ReturnType::Default => false,
    };
    if !ret_ok {
        return syn::Error::new_spanned(&sig.output, "#[function] requires return type f64")
            .to_compile_error()
            .into();
    }

    // Parse parameters
    enum ParamKind {
        Num(PatType),               // f64 parameter (appears in expression)
        Ctx {                        // &Ctx or &mut Ctx (not counted in arity)
            name: syn::Ident,
            elem_ty: Box<Type>,
            is_mut: bool,
        },
    }

    let mut ordered: Vec<ParamKind> = Vec::new();
    let mut numeric_params: Vec<PatType> = Vec::new();
    let mut has_ctx = false;

    for input in &sig.inputs {
        match input {
            FnArg::Typed(pt) => {
                // Extract identifier
                let pat_ident = match &*pt.pat {
                    Pat::Ident(pi) => &pi.ident,
                    other => {
                        return syn::Error::new_spanned(
                            other,
                            "#[function] requires simple identifier parameters",
                        )
                        .to_compile_error()
                        .into()
                    }
                };

                // Classify type
                match &*pt.ty {
                    Type::Path(tp) if tp.path.is_ident("f64") => {
                        let pt_clone = pt.clone();
                        ordered.push(ParamKind::Num(pt_clone.clone()));
                        numeric_params.push(pt_clone);
                    }
                    Type::Reference(TypeReference { elem, mutability, .. }) => {
                        if has_ctx {
                            return syn::Error::new_spanned(
                                &pt.ty,
                                "#[function] supports at most one context parameter (&Ctx or &mut Ctx)",
                            )
                            .to_compile_error()
                            .into();
                        }
                        has_ctx = true;
                        ordered.push(ParamKind::Ctx {
                            name: pat_ident.clone(),
                            elem_ty: elem.clone(),
                            is_mut: mutability.is_some(),
                        });
                    }
                    other => {
                        return syn::Error::new_spanned(
                            other,
                            "#[function] only supports f64 parameters and at most one &Ctx/&mut Ctx context parameter",
                        )
                        .to_compile_error()
                        .into();
                    }
                }
            }
            _ => {
                return syn::Error::new_spanned(
                    input,
                    "#[function] does not support receiver parameters",
                )
                .to_compile_error()
                .into();
            }
        }
    }

    let arity = numeric_params.len();
    if arity > 3 {
        return syn::Error::new_spanned(
            &sig.inputs,
            "#[function] currently supports up to 3 numeric parameters",
        )
        .to_compile_error()
        .into();
    }

    let name_str = ident.to_string();
    let shim_ident = format_ident!("__tabulon_shim_{}", ident);

    // Shim arg list: only numeric params in their original order
    let shim_args = numeric_params
        .iter()
        .map(|pt| quote! { #pt })
        .collect::<Vec<_>>();

    // Call-site argument reconstruction in original order
    let mut call_args = Vec::with_capacity(ordered.len());
    let mut ctx_bind = None;
    let mut ctx_ty_tokens: Option<Box<Type>> = None;

    let ctx_param_ident = if has_ctx { format_ident!("ctx_ptr") } else { format_ident!("_ctx") };

    for p in &ordered {
        match p {
            ParamKind::Num(pt) => {
                // Use the original identifier name
                if let Pat::Ident(pi) = &*pt.pat {
                    let id = &pi.ident;
                    call_args.push(quote! { #id });
                }
            }
            ParamKind::Ctx { name, elem_ty, is_mut } => {
                // Bind context pointer to &Ctx or &mut Ctx variable with the original name
                let binding = if *is_mut {
                    quote! { let #name: &mut #elem_ty = unsafe { &mut *(#ctx_param_ident as *mut #elem_ty) }; }
                } else {
                    quote! { let #name: &#elem_ty = unsafe { &*(#ctx_param_ident as *const #elem_ty) }; }
                };
                ctx_bind = Some(binding);
                ctx_ty_tokens = Some(elem_ty.clone());
                call_args.push(quote! { #name });
            }
        }
    }

    let arity_lit = arity as u8;

    let ctx_bind_stmt = ctx_bind.unwrap_or_else(|| quote! {});

    let uses_ctx_lit = if has_ctx { quote! { true } } else { quote! { false } };

    // Compute ctx TypeId for runtime verification at registration time.
    let ctx_type_id_expr = if has_ctx {
        let ty = ctx_ty_tokens.as_ref().expect("ctx type tokens must exist when has_ctx");
        quote! { ::core::any::TypeId::of::<#ty>() }
    } else {
        quote! { ::core::any::TypeId::of::<()>() } // unused when uses_ctx=false
    };

    let ctx_id_fn_ident = format_ident!("__tabulon_ctx_of_{}", ident);

    let marker_ident = format_ident!("__tabulon_marker_{}", ident);

    // Conditional where-clause for compile-time context matching: only constrain when ctx is used
    let marker_where_clause = if has_ctx {
        let ty = ctx_ty_tokens.as_ref().expect("ctx type tokens must exist when has_ctx");
        quote! { where EngineCtx: ::tabulon::SameAs<#ty> }
    } else {
        quote! {}
    };

    let output = quote! {
        #func

        #[allow(non_snake_case)]
        extern "C" fn #shim_ident(#ctx_param_ident: *mut std::ffi::c_void, #( #shim_args ),* ) -> f64 {
            #ctx_bind_stmt
            #ident( #( #call_args ),* )
        }

        #[allow(non_snake_case)]
        fn #ctx_id_fn_ident() -> ::core::any::TypeId { #ctx_type_id_expr }

        // Public marker type for optional compile-time context matching
        #[allow(non_camel_case_types)]
        pub struct #marker_ident;

        impl<EngineCtx> ::tabulon::FunctionForEngineCtx<EngineCtx> for #marker_ident #marker_where_clause {
            const NAME: &'static str = #name_str;
            const ARITY: u8 = #arity_lit;
            const USES_CTX: bool = #uses_ctx_lit;
            fn addr() -> *const u8 { #shim_ident as *const u8 }
        }

        ::tabulon::inventory::submit! {
            ::tabulon::FnMeta { name: #name_str, arity: #arity_lit, addr: #shim_ident as *const u8, mod_path: module_path!(), uses_ctx: #uses_ctx_lit, ctx_type_id_fn: if #uses_ctx_lit { Some(#ctx_id_fn_ident as fn() -> ::core::any::TypeId) } else { None } }
        }
    };

    output.into()
}
