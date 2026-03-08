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
        throw new UnsupportedOperationException("split not yet implemented");
    }
    private KryptonString() {}
}
