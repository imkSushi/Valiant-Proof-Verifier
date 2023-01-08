using ValiantBasics;
using ValiantProofVerifier;
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
    }
    
    public static Theorem CommutativityTheorem { get; }

    private static Theorem ConstructCommutativity()
    {
        var pEqQ = Assume(Parser.ParseTerm("p 'a = q"));

        var pEqP = Reflexivity(Parser.ParseTerm("p 'a"));

        var eq = Parser.ParseTerm("\"=\" :fun 'a :fun 'a :bool");

        var pxEqQx = Congruence(eq, pEqQ);
        var ppEqQp = Congruence(pxEqQx, pEqP);
        
        return ModusPonens(ppEqQp, pEqP);
    }

    public static Theorem IncreaseBeta(Theorem thm, Term variable) // t & x
    {
        var conclusion = thm.Deconstruct().conclusion; // t
        var beta = BetaReduction(MakeCombination(MakeAbstraction(variable, conclusion), variable)); // (\ x . t) x = t
        return ModusPonens(Commutativity(beta), thm);
    }

    public static Theorem Commutativity(Theorem theorem)
    {
        return TryCommutativity(theorem).ValueOrException();
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

    public static Theorem CommutativityEquality(Term term)
    {
        return TryCommutativityEquality(term).ValueOrException();
    }

    public static Result<Theorem> TryCommutativityEquality(Term term)
    {
        var assumption = Assume(term);
        if (!TryCommutativity(assumption).Deconstruct(out var commutativity, out var error))
            return error;
        var oppositeAssumption = Assume(commutativity.Deconstruct().conclusion);
        var oppositeCommutativity = Commutativity(oppositeAssumption);
        return AntiSymmetry(oppositeCommutativity, commutativity);
    }
}