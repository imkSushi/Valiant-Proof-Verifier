using ValiantProofVerifier;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class ExistsUniqueTheorems
{
    public static void Load() { }

    static ExistsUniqueTheorems()
    {
        ExistsTheorems.Load();
        
        ExistsUnqiueDefinition = NewBasicDefinition(Parse(@"""?!"" = \ p . (? p) /\ ! x y . (p x /\ p y) -> (x = y)"));
        TryRegisterLambdaRule("?!", "?!", "∃!");
    }
    
    public static Theorem ExistsUnqiueDefinition { get; }
}