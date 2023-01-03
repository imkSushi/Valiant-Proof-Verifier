namespace ValiantProofVerifier3;

public abstract record Type
{
    private Type()
    {
        
    }
    
    internal sealed record TyVar(string Name) : Type;
    internal sealed record TyApp(string Name, Type[] Args) : Type;
}