use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn function(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    let sig = &func.sig;
    let ident = &sig.ident;

    // Verify return type is f64
    let ret_ok = match &sig.output {
        syn::ReturnType::Type(_, ty) => matches!(**ty, syn::Type::Path(ref tp) if tp.path.is_ident("f64")),
        syn::ReturnType::Default => false,
    };
    if !ret_ok {
        return syn::Error::new_spanned(&sig.output, "#[function] requires return type f64").to_compile_error().into();
    }

    // Collect parameter idents and ensure all are f64
    let mut param_idents: Vec<syn::Ident> = Vec::new();
    let mut arity: usize = 0;
    for input in &sig.inputs {
        match input {
            syn::FnArg::Typed(pt) => {
                if let syn::Pat::Ident(pat_ident) = &*pt.pat {
                    if !matches!(*pt.ty, syn::Type::Path(ref tp) if tp.path.is_ident("f64")) {
                        return syn::Error::new_spanned(&pt.ty, "#[function] only supports f64 parameters").to_compile_error().into();
                    }
                    param_idents.push(pat_ident.ident.clone());
                    arity += 1;
                } else {
                    return syn::Error::new_spanned(&pt.pat, "#[function] requires simple identifier parameters").to_compile_error().into();
                }
            }
            _ => {
                return syn::Error::new_spanned(input, "#[function] does not support receiver parameters").to_compile_error().into();
            }
        }
    }
    if arity > 3 {
        return syn::Error::new_spanned(&sig.inputs, "#[function] currently supports up to 3 parameters").to_compile_error().into();
    }

    let name_str = ident.to_string();
    let shim_ident = format_ident!("__tabulon_shim_{}", ident);

    // Build shim argument list: reuse the original param idents and types (all f64)
    let shim_args = &sig.inputs;

    // Build call site: original_name(arg1, arg2, ...)
    let call_args = param_idents.iter();

    // Convert arity to u8 literal
    let arity_lit = arity as u8;

    let output = quote! {
        #func

        #[allow(non_snake_case)]
        extern "C" fn #shim_ident(#shim_args) -> f64 { #ident( #( #call_args ),* ) }

        ::tabulon::inventory::submit! {
            ::tabulon::FnMeta { name: #name_str, arity: #arity_lit, addr: #shim_ident as *const u8, mod_path: module_path!() }
        }
    };

    output.into()
}
