package krypton.runtime;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Scanner;

public final class KryptonIO {
    // Used by codegen tests' direct println[a] extern
    public static void println(Object value) {
        System.out.println(value);
    }

    public static void print(Object value) {
        System.out.print(value);
    }

    public static void raw_println(String value) {
        System.out.println(value);
    }

    public static void raw_print(String value) {
        System.out.print(value);
    }

    public static String readLine() {
        return new Scanner(System.in).nextLine();
    }

    public static String read_file(String path) throws Exception {
        return Files.readString(Path.of(path));
    }

    public static void write_file(String path, String content) throws Exception {
        Files.writeString(Path.of(path), content);
    }

    private KryptonIO() {}
}
