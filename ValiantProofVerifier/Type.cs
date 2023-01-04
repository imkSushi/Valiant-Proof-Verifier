namespace ValiantProofVerifier;

public abstract record Type
{
    private Type()
    {
        
    }

    public sealed override string ToString()
    {
        return Printer.UniversalPrinter.PrintType(this);
    }

    internal sealed record TyVar(string Name) : Type;

    internal sealed record TyApp(string Name, Type[] Args) : Type
    {
        public override int GetHashCode()
        {
            return HashCode.Combine(Name, Args.Aggregate(613, HashCode.Combine));
        }

        public bool Equals(TyApp? other)
        {
            if (other is null)
                return false;
            
            if (other.Name != Name)
                return false;

            if (other.Args.Length != Args.Length)
                return false;

            return !Args.Where((t, i) => t != other.Args[i]).Any();
        }
    }
}