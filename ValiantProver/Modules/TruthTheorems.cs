using ValiantProofVerifier;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class TruthTheorems
{
    public static void Load() { }

    static TruthTheorems()
    {
        CommutativityTheorems.Load();
        
        TruthDefinition = NewBasicDefinition(Parse(@"T = ((\ a: bool . a) = (\ a: bool . a))"));
        TryRegisterConst("T", "⊤");
        
        Truth = ConstructTruth();
    }
    public static Theorem TruthDefinition { get; }
    public static Theorem Truth { get; }

    private static Theorem ConstructTruth()
    {
        var a = Parse(@"\a: bool . a");
        var equality = Reflexivity(a);
        var commutativity = Commutativity(TruthDefinition);
        return ModusPonens(commutativity, equality);
    }
}