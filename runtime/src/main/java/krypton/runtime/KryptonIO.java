package krypton.runtime;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Scanner;

public final class KryptonIO {
    public static void println(Object value) {
        System.out.println(value);
    }

    public static void print(Object value) {
        System.out.print(value);
    }

    public static String readLine() {
        return new Scanner(System.in).nextLine();
    }

    public static Object read_file(String path) {
        try {
            String content = Files.readString(Path.of(path));
            return wrapOk(content);
        } catch (Exception e) {
            return wrapErr(e.getMessage());
        }
    }

    public static Object write_file(String path, String content) {
        try {
            Files.writeString(Path.of(path), content);
            return wrapOk(Integer.valueOf(0));
        } catch (Exception e) {
            return wrapErr(e.getMessage());
        }
    }

    private static Object wrapOk(Object value) {
        try {
            Class<?> okClass = Class.forName("Result$Ok");
            return okClass.getDeclaredConstructor(Object.class).newInstance(value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Ok: " + e.getMessage(), e);
        }
    }

    private static Object wrapErr(Object value) {
        try {
            Class<?> errClass = Class.forName("Result$Err");
            return errClass.getDeclaredConstructor(Object.class).newInstance(value);
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct Err: " + e.getMessage(), e);
        }
    }

    private KryptonIO() {}
}
