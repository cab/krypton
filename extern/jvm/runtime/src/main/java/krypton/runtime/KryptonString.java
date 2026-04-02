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
    public static KryptonArray split(String s, String delimiter) {
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
    public static Object parseIntSafe(String s) {
        try { return Long.parseLong(s); } catch (NumberFormatException e) { return null; }
    }
    public static Object parseFloatSafe(String s) {
        try { return Double.parseDouble(s); } catch (NumberFormatException e) { return null; }
    }
    public static boolean containsStr(String s, String substr) { return s.contains(substr); }
    public static boolean startsWith(String s, String prefix) { return s.startsWith(prefix); }
    public static boolean endsWith(String s, String suffix) { return s.endsWith(suffix); }
    public static long indexOf(String s, String substr) { return (long) s.indexOf(substr); }
    public static String toLower(String s) { return s.toLowerCase(); }
    public static String toUpper(String s) { return s.toUpperCase(); }
    public static String replaceStr(String s, String from, String to) { return s.replace(from, to); }
    public static Object charAt(String s, long index) {
        int i = (int) index;
        if (i < 0 || i >= s.length()) return null;
        return String.valueOf(s.charAt(i));
    }
    private KryptonString() {}
}
