package krypton.runtime;

public class KryptonString {
    private final String value;

    public KryptonString(String value) {
        this.value = value;
    }

    public int codepointLength() {
        return value.codePointCount(0, value.length());
    }

    public String codepointSlice(int start, int end) {
        int startOffset = value.offsetByCodePoints(0, start);
        int endOffset = value.offsetByCodePoints(0, end);
        return value.substring(startOffset, endOffset);
    }
}
