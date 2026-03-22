use std::collections::HashSet;
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};
use zip::write::SimpleFileOptions;
use zip::CompressionMethod;
use zip::ZipWriter;

/// Locate the krypton-runtime.jar.
///
/// Checks `KRYPTON_RUNTIME` env var first, then falls back to the
/// workspace-relative path `../../runtime/build/libs/krypton-runtime.jar`.
pub fn find_runtime_jar() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("KRYPTON_RUNTIME") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../runtime/build/libs/krypton-runtime.jar");
    if workspace_root.exists() {
        return Some(workspace_root);
    }
    None
}

/// Bundle compiled class files into a JAR (ZIP with manifest).
///
/// If `runtime_jar` is provided, all `.class` entries from that JAR are
/// copied into the output, producing a fat JAR that runs standalone.
pub fn write_jar(
    classes: &[(String, Vec<u8>)],
    main_class: &str,
    runtime_jar: Option<&Path>,
) -> Result<Vec<u8>, std::io::Error> {
    let buf = Cursor::new(Vec::new());
    let mut writer = ZipWriter::new(buf);

    let options = SimpleFileOptions::default().compression_method(CompressionMethod::Stored);

    // Write manifest
    writer.start_file("META-INF/MANIFEST.MF", options)?;
    write!(
        writer,
        "Manifest-Version: 1.0\r\nMain-Class: {main_class}\r\n\r\n"
    )?;

    // Write class files, tracking names to avoid duplicates
    let mut written: HashSet<String> = HashSet::new();
    for (name, bytes) in classes {
        let entry_name = format!("{name}.class");
        assert!(
            !written.contains(&entry_name),
            "duplicate class name in codegen output: {entry_name}"
        );
        writer.start_file(&entry_name, options)?;
        writer.write_all(bytes)?;
        written.insert(entry_name);
    }

    // Bundle runtime classes from the runtime JAR
    if let Some(path) = runtime_jar {
        let file = std::fs::File::open(path)?;
        let mut archive = zip::ZipArchive::new(file)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        for i in 0..archive.len() {
            let mut entry = archive
                .by_index(i)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
            let name = entry.name().to_string();
            // Skip META-INF/ entries, directories, and already-written classes
            if name.starts_with("META-INF/") || entry.is_dir() || written.contains(&name) {
                continue;
            }
            if name.ends_with(".class") {
                writer.start_file(&name, options)?;
                let mut buf = Vec::new();
                entry.read_to_end(&mut buf)?;
                writer.write_all(&buf)?;
                written.insert(name);
            }
        }
    }

    let cursor = writer.finish()?;
    Ok(cursor.into_inner())
}
