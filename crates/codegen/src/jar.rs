use std::io::{Cursor, Write};
use zip::write::SimpleFileOptions;
use zip::CompressionMethod;
use zip::ZipWriter;

/// Bundle compiled class files into a JAR (ZIP with manifest).
pub fn write_jar(classes: &[(String, Vec<u8>)], main_class: &str) -> Result<Vec<u8>, std::io::Error> {
    let buf = Cursor::new(Vec::new());
    let mut writer = ZipWriter::new(buf);

    let options = SimpleFileOptions::default().compression_method(CompressionMethod::Stored);

    // Write manifest
    writer.start_file("META-INF/MANIFEST.MF", options)?;
    write!(
        writer,
        "Manifest-Version: 1.0\r\nMain-Class: {main_class}\r\n\r\n"
    )?;

    // Write class files
    for (name, bytes) in classes {
        writer.start_file(format!("{name}.class"), options)?;
        writer.write_all(bytes)?;
    }

    let cursor = writer.finish()?;
    Ok(cursor.into_inner())
}
