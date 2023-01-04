namespace ValiantProofVerifier;

public abstract record Term
{
    private Term()
    {
        
    }

    public sealed override string ToString()
    {
        return Printer.UniversalPrinter.PrintTerm(this);
    }

    internal sealed record Var(string Name, Type Type) : Term;

    internal sealed record Const(string Name, Type Type) : Term;

    internal sealed record Comb(Term Application, Term Argument) : Term;

    internal sealed record Abs(Term Parameter, Term Abstraction) : Term;
}