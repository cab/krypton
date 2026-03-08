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
        try {
            Class<?> consClass = Class.forName("List$Cons");
            Class<?> nilClass = Class.forName("List$Nil");
            // Build linked list from right to left: Nil, then Cons(last, Nil), etc.
            Object list = nilClass.getDeclaredConstructor().newInstance();
            for (int i = parts.length - 1; i >= 0; i--) {
                list = consClass.getDeclaredConstructor(Object.class, Object.class)
                        .newInstance(parts[i], list);
            }
            return list;
        } catch (Exception e) {
            throw new RuntimeException("Failed to construct List: " + e.getMessage(), e);
        }
    }
    public static String trim(String s) { return s.trim(); }
    public static String substring(String s, long start, long end) {
        return s.substring((int) start, (int) end);
    }
    private KryptonString() {}
}
