use include_dir::{include_dir, Dir};
use krypton_codegen_js::compile_modules_js;
use krypton_diagnostics::Diagnostic;
use krypton_modules::{
    module_resolver::ModuleResolver,
    stdlib_loader::StdlibLoader,
};
use krypton_parser::parser::parse;
use krypton_typechecker::infer::infer_module;
use serde::Serialize;
use wasm_bindgen::prelude::*;

static JS_RUNTIME_DIR: Dir<'_> = include_dir!("$CARGO_MANIFEST_DIR/../../runtime/js");

const ROOT_MODULE_NAME: &str = "main";
const ROOT_FILENAME: &str = "main.kr";
const RUNTIME_FILES: &[&str] = &[
    "actor.mjs",
    "array.mjs",
    "convert.mjs",
    "io.mjs",
    "json.mjs",
    "map.mjs",
    "panic.mjs",
    "prelude.mjs",
    "string.mjs",
];

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct CompiledJsFile {
    pub path: String,
    pub source: String,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct CompileToJsResult {
    pub success: bool,
    pub entry_module: String,
    pub files: Vec<CompiledJsFile>,
    pub warnings: Vec<String>,
    pub diagnostics: Vec<Diagnostic>,
}

impl CompileToJsResult {
    fn failure(diagnostics: Vec<Diagnostic>) -> Self {
        Self {
            success: false,
            entry_module: String::new(),
            files: Vec::new(),
            warnings: Vec::new(),
            diagnostics,
        }
    }
}

struct PlaygroundResolver {
    root_source: String,
}

impl ModuleResolver for PlaygroundResolver {
    fn resolve(&self, module_path: &str) -> Option<String> {
        if module_path == ROOT_MODULE_NAME {
            return Some(self.root_source.clone());
        }
        StdlibLoader::get_source(module_path).map(str::to_owned)
    }
}

fn package_runtime_files(files: &mut Vec<CompiledJsFile>) {
    for runtime_file in RUNTIME_FILES {
        let path = format!("runtime/js/{runtime_file}");
        let source = JS_RUNTIME_DIR
            .get_file(runtime_file)
            .unwrap_or_else(|| panic!("missing runtime file {runtime_file}"))
            .contents_utf8()
            .expect("runtime JS files must be valid UTF-8")
            .to_string();
        files.push(CompiledJsFile { path, source });
    }
    files.sort_by(|a, b| a.path.cmp(&b.path));
}

pub fn compile_to_js_result(source: &str) -> CompileToJsResult {
    let (module, parse_errors) = parse(source);
    if !parse_errors.is_empty() {
        let (diags, _srcs) = krypton_parser::diagnostics::lower_parse_errors(ROOT_FILENAME, source, &parse_errors);
        return CompileToJsResult::failure(diags);
    }

    let resolver = PlaygroundResolver {
        root_source: source.to_string(),
    };
    let typed_modules = match infer_module(&module, &resolver, ROOT_MODULE_NAME.to_string()) {
        Ok(typed_modules) => typed_modules,
        Err(err) => {
            let (diags, _srcs) = krypton_typechecker::diagnostics::lower_infer_error(ROOT_FILENAME, source, &err);
            return CompileToJsResult::failure(diags);
        }
    };

    let js_files = match compile_modules_js(&typed_modules, ROOT_MODULE_NAME, false) {
        Ok(files) => files,
        Err(err) => {
            let (diags, _srcs) = krypton_codegen_js::diagnostics::lower_js_codegen_error(ROOT_FILENAME, source, &err);
            return CompileToJsResult::failure(diags);
        }
    };

    let mut files: Vec<CompiledJsFile> = js_files
        .into_iter()
        .map(|(path, source)| CompiledJsFile { path, source })
        .collect();
    package_runtime_files(&mut files);

    CompileToJsResult {
        success: true,
        entry_module: format!("{ROOT_MODULE_NAME}.mjs"),
        files,
        warnings: Vec::new(),
        diagnostics: Vec::new(),
    }
}

#[wasm_bindgen]
pub fn compile_to_js(source: &str) -> Result<JsValue, JsValue> {
    serde_wasm_bindgen::to_value(&compile_to_js_result(source))
        .map_err(|err| JsValue::from_str(&err.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn compile_to_js_packages_runtime_files() {
        let result = compile_to_js_result(
            r#"
            fun main() = println("hello")
            "#,
        );

        assert!(result.success, "expected success: {result:?}");
        assert_eq!(result.entry_module, "main.mjs");
        assert!(
            result.files.iter().any(|file| file.path == "runtime/js/io.mjs"),
            "runtime io module should be packaged"
        );
        assert!(
            result.files.iter().any(|file| file.path == "main.mjs"),
            "compiled root module should be packaged"
        );
    }

    #[test]
    fn compile_to_js_reports_parse_errors() {
        let result = compile_to_js_result("fun main( = 1");
        assert!(!result.success, "expected failure: {result:?}");
        assert!(!result.diagnostics.is_empty(), "expected diagnostics");
        let diag = &result.diagnostics[0];
        assert_eq!(diag.severity, krypton_diagnostics::Severity::Error);
        assert!(!diag.code.is_empty(), "diagnostic should have a code");
        assert!(!diag.message.is_empty(), "diagnostic should have a message");
        assert!(result.files.is_empty(), "failed compile should not return files");
    }

    #[test]
    fn compile_to_js_diagnostics_have_structured_fields() {
        // Type error: applying Int to a non-function
        let result = compile_to_js_result("fun main() = (1)(2)");
        assert!(!result.success, "expected failure: {result:?}");
        assert!(!result.diagnostics.is_empty(), "expected diagnostics");
        let diag = &result.diagnostics[0];
        assert_eq!(diag.primary_file, "main.kr");
        assert!(diag.primary_span.is_some(), "diagnostic should have a span");
    }
}
