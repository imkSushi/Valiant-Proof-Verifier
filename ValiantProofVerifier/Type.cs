namespace ValiantProofVerifier;

public abstract record Type
{
    private Type()
    {
        
    }

    internal sealed record TyVar(string Name) : Type
    {
        public override string ToString()
        {
            return Name;
        }
    }

    internal sealed record TyApp(string Name, Type[] Args) : Type
    {
        public override string ToString()
        {
            return $"{Name}<{string.Join(", ", Args.Select(type => type.ToString()))}>";
        }

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