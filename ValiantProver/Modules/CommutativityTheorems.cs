using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class CommutativityTheorems
{
    public static void Load() { }
    
    static CommutativityTheorems()
    {
        Basic.Load();
        CommutativityTheorem = ConstructCommutativity();
        CommutativeEqualityTheorem = ConstructCommutativeEquality();
    }
    
    public static Theorem CommutativityTheorem { get; }
    public static Theorem CommutativeEqualityTheorem { get; }

    private static Theorem ConstructCommutativity()
    {
        var pEqQ = Assume(Parse("p 'a = q"));

        var pEqP = Reflexivity(Parse("p 'a"));

        var eq = Parse("= :fun 'a :fun 'a :bool");

        var pxEqQx = Congruence(eq, pEqQ);
        var ppEqQp = Congruence(pxEqQx, pEqP);
        
        return ModusPonens(ppEqQp, pEqP);
    }
    
    private static Theorem ConstructCommutativeEquality() // |- (p = q) = (q = p)
    {
        var pEqQ = Assume(Parse("p 'a = q")); // p = q |- p = q
        var qEqPComm = Commutativity(pEqQ); // p = q |- q = p
        
        var qEqP = Assume(Parse("q 'a = p")); // q = p |- q = p
        var pEqQComm = Commutativity(qEqP); // q = p |- p = q

        return AntiSymmetry(pEqQComm, qEqPComm);
    }

    public static Theorem IncreaseBeta(Theorem thm, Term variable) // t & x
    {
        var conclusion = thm.Deconstruct().conclusion; // t
        var beta = BetaReduction(MakeCombination(MakeAbstraction(variable, conclusion), variable)); // (\ x . t) x = t
        return ModusPonens(Commutativity(beta), thm);
    }

    public static Theorem Commutativity(Theorem theorem)
    {
        return (Theorem) TryCommutativity(theorem);
    }

    public static Result<Theorem> TryCommutativity(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem).Deconstruct(out var p, out var q, out var op, out _) ||
            !op.TryDeconstructConst().Deconstruct(out var opName, out _, out _) || opName != "=")
            return "Theorem is not an equality";

        var type = p.TypeOf();

        var typedCommutativity = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = type
        }, CommutativityTheorem);
        
        var commutativity = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", type)] = p,
            [MakeVariable("q", type)] = q
        }, typedCommutativity);
        
        return Elimination(commutativity, theorem);
    }

    public static Theorem CommutativityEquality(Term left, Term right)
    {
        var type = left.TypeOf();
        
        var typedCommutativeEquality = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = type
        }, CommutativeEqualityTheorem);

        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", type)] = left,
            [MakeVariable("q", type)] = right
        }, typedCommutativeEquality);
    }

    public static Result<Theorem> TryCommutativityEquality(Term left, Term right)
    {
        if (left.TypeOf() != right.TypeOf())
            return "Expected two terms of the same type";

        return CommutativityEquality(left, right);
    }
}