namespace ValiantProofVerifier;

public record Theorem
{
    private Theorem()
    {
        
    }

    internal sealed record Sequent(HashSet<Term> Premises, Term Conclusion) : Theorem
    {
        internal Sequent(Term term) : this(new HashSet<Term>(), term)
        {
            
        }
        
        internal Sequent(IEnumerable<Term> premises, Term conclusion) : this(premises.ToHashSet(), conclusion)
        {
            
        }
        
        internal Sequent(Term premise, Term conclusion) : this(new HashSet<Term> {premise}, conclusion)
        {
            
        }
    }

    public sealed override string ToString()
    {
        return Printer.UniversalPrinter.PrintTheorem(this);
    }
}