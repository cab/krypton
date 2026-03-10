package krypton.runtime;

public final class KryptonString {
    public static String concat(String a, String b) { return a.concat(b); }
    public static long length(String s) { return (long) s.length(); }
    public static int codepointLength(String s) { return s.codePointCount(0, s.length()); }
    public static String codepointSlice(String s, int start, int end) {
        int startOffset = s.offsetByCodePoints(0, start);
        int endOffset = s.offsetByCodePoints(0, end);
        return s.substring(startOffset, endOffset);
    }
    public static Object split(String s, String delimiter) {
        String[] parts = s.split(delimiter, -1);
        KryptonArray arr = new KryptonArray(parts.length);
        for (int i = 0; i < parts.length; i++) {
            arr.set(i, parts[i]);
        }
        arr.freeze();
        return arr;
    }
    public static String trim(String s) { return s.trim(); }
    public static String substring(String s, long start, long end) {
        return s.substring((int) start, (int) end);
    }
    private KryptonString() {}
}
