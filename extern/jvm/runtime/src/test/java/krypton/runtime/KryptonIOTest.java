package krypton.runtime;

import org.junit.jupiter.api.Test;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import static org.junit.jupiter.api.Assertions.*;

class KryptonIOTest {
    @Test
    void printlnWritesWithNewline() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream original = System.out;
        try {
            System.setOut(new PrintStream(out));
            KryptonIO.println("hello");
            assertEquals("hello\n", out.toString());
        } finally {
            System.setOut(original);
        }
    }

    @Test
    void printWritesWithoutNewline() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream original = System.out;
        try {
            System.setOut(new PrintStream(out));
            KryptonIO.print("hello");
            assertEquals("hello", out.toString());
        } finally {
            System.setOut(original);
        }
    }

    @Test
    void readLineMethodExists() throws NoSuchMethodException {
        assertNotNull(KryptonIO.class.getMethod("readLine"));
    }
}
