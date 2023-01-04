using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class TransitivityTheorems
{
    public static void Load() { }
    
    static TransitivityTheorems()
    {
        CommutativityTheorems.Load();
        BinaryUtilities.Load();
        
        Transitivity = ConstructTransitivity();
    }
    
    public static Theorem Transitivity { get; }
    

    private static Theorem ConstructTransitivity()
    {
        var pq = Assume(Parser.ParseTerm("p 'a = q")); // |- p = q
        var qr = Assume(Parser.ParseTerm("q 'a = r")); // |- q = r

        var dummyVariable = Parse("x 'a"); // x

        var eq = Parse(@"""="" :fun 'a :fun 'a :bool");
        var pEqQEq = Congruence(eq, pq); // |- "=" p = "=" q
        var qEqREq = Congruence(eq, qr); // |- "=" q = "=" r
        var pxQx = Congruence(pEqQEq, dummyVariable); // |- (p = x) = (q = x)
        var qxRx = Congruence(qEqREq, dummyVariable); // |- (q = x) = (r = x)
        var pEqX = Assume(Parse("p 'a = x"));
        var pEqQ = ModusPonens(pxQx, pEqX); // p = x |- q = x
        var pEqR = ModusPonens(qxRx, pEqQ); // p = x |- r = x

        var qxPx = Commutativity(pxQx); // |- (q = x) = (p = x)
        var rxQx = Commutativity(qxRx); // |- (r = x) = (q = x)
        
        var rEqX = Assume(Parse("r 'a = x"));
        var rEqQ = ModusPonens(rxQx, rEqX); // r = x |- q = x
        var rEqP = ModusPonens(qxPx, rEqQ); // r = x |- p = x

        var pxRx = AntiSymmetry(rEqP, pEqR); // (p = x) = (r = x)

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [dummyVariable] = Parse("p 'a")
        }, pxRx);
        
        var mp = ModusPonens(inst, Reflexivity(Parse("p 'a")));
        return Commutativity(mp);
    }

    public static Theorem ApplyTransitivity(Theorem left, Theorem right)
    {
        var type = TypeOf(BinaryLeft(left));
        
        var typed = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = type
        }, Transitivity);
        
        var substituted = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", type)] = BinaryLeft(left),
            [MakeVariable("q", type)] = BinaryRight(left),
            [MakeVariable("r", type)] = BinaryRight(right)
        }, typed);
        var eliminatedLeft = Elimination(left, substituted);
        return Elimination(right, eliminatedLeft);
    }
}