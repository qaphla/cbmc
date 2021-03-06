public class Test {
    public String det()
    {
        StringBuilder builder = new StringBuilder("abcdefghijklmnopqrstuvwxyz");
        builder.setCharAt(3, '!');
        builder.setCharAt(5, '!');
        builder.setCharAt(7, '!');
        builder.setCharAt(9, '!');
        builder.setCharAt(13, '!');
        builder.setCharAt(15, '!');
        builder.setCharAt(17, '!');
        builder.setCharAt(19, '!');
        builder.setCharAt(4, ':');
        builder.setCharAt(5, ':');
        builder.setCharAt(6, ':');
        builder.setCharAt(9, ':');
        builder.setCharAt(10, ':');
        builder.setCharAt(11, ':');
        builder.setCharAt(16, ':');
        builder.setCharAt(18, ':');
        return builder.toString();
    }

    public String nonDet(String s, char c, int i)
    {
        StringBuilder builder = new StringBuilder(s);
        if(i + 5 >= s.length() || 19 >= s.length() || i < 0)
            return "Out of bounds";
        builder.setCharAt(i, c);
        builder.setCharAt(i+5, 'x');
        builder.setCharAt(7, '!');
        builder.setCharAt(9, '!');
        builder.setCharAt(13, '!');
        builder.setCharAt(15, '!');
        builder.setCharAt(17, '!');
        builder.setCharAt(19, '!');
        builder.setCharAt(4, ':');
        builder.setCharAt(5, ':');
        builder.setCharAt(6, c);
        builder.setCharAt(9, ':');
        builder.setCharAt(10, ':');
        builder.setCharAt(11, ':');
        builder.setCharAt(16, ':');
        builder.setCharAt(18, ':');
        return builder.toString();
    }

    public String withDependency(boolean b)
    {
        StringBuilder builder = new StringBuilder("abcdefghijklmnopqrstuvwxyz");
        builder.setCharAt(3, '!');
        builder.setCharAt(5, '!');

        if(b) {
            assert builder.toString().startsWith("abc!");
        } else {
            assert !builder.toString().startsWith("abc!");
        }
        return builder.toString();
    }

}
