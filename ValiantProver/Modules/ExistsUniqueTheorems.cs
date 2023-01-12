using ValiantProofVerifier;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class ExistsUniqueTheorems
{
    public static void Load() { }

    static ExistsUniqueTheorems()
    {
        ExistsTheorems.Load();
        
        TryRegisterLambdaRule("?!", "?!", "∃!");
        ExistsUnqiueDefinition = NewDefinition(Parse(@"(?! p) = (? p) /\ ! x y . (p x /\ p y) -> (x = y)"));
    }
    
    public static Theorem ExistsUnqiueDefinition { get; }
}