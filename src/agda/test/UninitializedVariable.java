public class UninitializedVariable {

    public static void f (int i) {
	int u;
	// Tautology that should be beyond the type checker.
	// if ((i + 1) * (i - 1) == i * i - 1) {
	// Simple tautology:
	if (i == i) {
	    u = 1;
	}
	System.out.println(u);  // rejected by javac
    }
    
    public static void main (String[] args) {
	f(5);
    }
}
