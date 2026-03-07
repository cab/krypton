package krypton.runtime;

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

    private KryptonIO() {}
}
