use crate::js::env::HostEnvInitError;
use crate::js::export::{Export, VMFunction};
use crate::js::exports::Exports;
use crate::js::externals::Extern;
use crate::js::module::Module;
use crate::js::resolver::Resolver;
use crate::js::store::Store;
use crate::js::trap::RuntimeError;
use js_sys::{WebAssembly, Reflect, Object, Promise};
use wasm_bindgen_futures::JsFuture;
use wasm_bindgen::JsValue;
use wasmer_types::ExternType;
use std::fmt;
#[cfg(feature = "std")]
use thiserror::Error;

/// A WebAssembly Instance is a stateful, executable
/// instance of a WebAssembly [`Module`].
///
/// Instance objects contain all the exported WebAssembly
/// functions, memories, tables and globals that allow
/// interacting with WebAssembly.
///
/// Spec: <https://webassembly.github.io/spec/core/exec/runtime.html#module-instances>
#[derive(Clone)]
pub struct Instance {
    instance: WebAssembly::Instance,
    module: Module,
    /// The exports for an instance.
    pub exports: Exports,
}

/// An error while instantiating a module.
///
/// This is not a common WebAssembly error, however
/// we need to differentiate from a `LinkError` (an error
/// that happens while linking, on instantiation), a
/// Trap that occurs when calling the WebAssembly module
/// start function, and an error when initializing the user's
/// host environments.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum InstantiationError {
    /// A linking ocurred during instantiation.
    #[cfg_attr(feature = "std", error("Link error: {0}"))]
    Link(String),

    /// A runtime error occured while invoking the start function
    #[cfg_attr(feature = "std", error(transparent))]
    Start(RuntimeError),

    /// Error occurred when initializing the host environment.
    #[cfg_attr(feature = "std", error(transparent))]
    HostEnvInitialization(HostEnvInitError),
}

#[cfg(feature = "core")]
impl std::fmt::Display for InstantiationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "InstantiationError")
    }
}

impl Instance {
    /// Creates a new `Instance` from a WebAssembly [`Module`] and a
    /// set of imports resolved by the [`Resolver`].
    ///
    /// The resolver can be anything that implements the [`Resolver`] trait,
    /// so you can plug custom resolution for the imports, if you wish not
    /// to use [`ImportObject`].
    ///
    /// The [`ImportObject`] is the easiest way to provide imports to the instance.
    ///
    /// [`ImportObject`]: crate::js::ImportObject
    ///
    /// ```
    /// # use wasmer::{imports, Store, Module, Global, Value, Instance};
    /// # fn main() -> anyhow::Result<()> {
    /// let store = Store::default();
    /// let module = Module::new(&store, "(module)")?;
    /// let imports = imports!{
    ///   "host" => {
    ///     "var" => Global::new(&store, Value::I32(2))
    ///   }
    /// };
    /// let instance = Instance::new(&module, &imports)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ## Errors
    ///
    /// The function can return [`InstantiationError`]s.
    ///
    /// Those are, as defined by the spec:
    ///  * Link errors that happen when plugging the imports into the instance
    ///  * Runtime errors that happen when running the module `start` function.
    pub fn new(module: &Module, resolver: &dyn Resolver) -> Result<Self, InstantiationError> 
    {
        let (instance, functions) = module
            .instantiate(resolver)
            .map_err(|e| InstantiationError::Start(e))?;
            
        Self::link_instance(module, instance, functions)
    }

    ///
    pub async fn from_promise(store: Store, promise: &Promise, resolver: &dyn Resolver, import_types: Vec<(u32, String, String)>) -> Result<(Self, Module), InstantiationError>
    {
        let (imports, functions): (Object, Vec<_>) = Module::resolve_imports(resolver, import_types).expect("failed to resolve imports.");

        let stream: Promise = WebAssembly::instantiate_streaming(promise, &imports);  // Promise { obj: Result { module: WebAssembly.Module, instance: WebAssemblyInstance } }

        let result: JsValue = JsFuture::from(stream) // Result { module: WebAssembly.Module, instance: WebAssemblyInstance }
            .await
            .expect("failed to await promise of Web Assembly module.");

        let wasm_instance: WebAssembly::Instance = Reflect::get(
            &result, 
            &"instance".into()
        )
        .expect("failed to get instance from result.")
        .into();

        let wasm_module: WebAssembly::Module = Reflect::get(
            &result,
            &"module".into()
        )
        .expect("failed to get module from result.")
        .into();

        let mut wasmer_module: Module = Module::from(wasm_module);

        wasmer_module.swap_store(store);

        let wasmer_instance: Instance = Self::link_instance(&wasmer_module, wasm_instance, functions)?;

        Ok((wasmer_instance, wasmer_module))
    }

    fn link_instance(module: &Module, instance: WebAssembly::Instance, functions: Vec<VMFunction>) -> Result<Self, InstantiationError>
    {
        let instance_exports: Object = instance.exports();

        let store: &Store = module.store();

        let module_exports: Exports = module
            .exports()
            .map(|export_type| 
            {
                let name: &str = export_type.name();

                let extern_type: ExternType = export_type.ty().clone();

                let js_export: JsValue = js_sys::Reflect::get(
                    &instance_exports, 
                    &name.into()
                ).expect("failed to get export from instance exports.");

                let export: Export = (js_export, extern_type).into();

                let extern_ = Extern::from_vm_export(store, export);

                (name.to_string(), extern_)
            })
            .collect();

        let wrapped_instance = Self {
            module: module.clone(),
            exports: module_exports,
            instance
        };

        for function in functions
        {
            function
                .init_envs(&wrapped_instance)
                .map_err(|error| 
                {
                    InstantiationError::HostEnvInitialization(error)
                })?
        }

        Ok(wrapped_instance)
    }

    /// Gets the [`Module`] associated with this instance.
    pub fn module(&self) -> &Module {
        &self.module
    }

    /// Returns the [`Store`] where the `Instance` belongs.
    pub fn store(&self) -> &Store {
        self.module.store()
    }
}

impl fmt::Debug for Instance {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Instance")
            .field("exports", &self.exports)
            .finish()
    }
}
