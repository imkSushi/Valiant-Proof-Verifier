namespace ValiantProofVerifier;

public abstract record Term
{
    private Term()
    {
        
    }

    internal sealed record Var(string Name, Type Type) : Term
    {
        public override string ToString()
        {
            return $"{Name}";
        }
    }
    internal sealed record Const(string Name, Type Type) : Term
    {
        public override string ToString()
        {
            return $"{Name}";
        }
    }
    internal sealed record Comb(Term Application, Term Argument) : Term
    {
        public override string ToString()
        {
            return $"({Application} {Argument})";
        }
    }
    internal sealed record Abs(Term Parameter, Term Abstraction) : Term
    {
        public override string ToString()
        {
            return $"(λ{Parameter}.{Abstraction})";
        }
    }
}