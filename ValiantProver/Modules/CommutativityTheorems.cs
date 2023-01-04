using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
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

    public static Theorem IncreaseBeta(Theorem thm, Term variable) // t & x
    {
        var conclusion = DeconstructTheorem(thm).conclusion; // t
        var beta = BetaReduction(MakeCombination(MakeAbstraction(variable, conclusion), variable)); // (\ x . t) x = t
        return ModusPonens(Commutativity(beta), thm);
    }

    private static Theorem ConstructCommutativity()
    {
        var pEqQ = Assume(Parser.ParseTerm("p 'a = q"));

        var pEqP = Reflexivity(Parser.ParseTerm("p 'a"));

        var eq = Parser.ParseTerm("\"=\" :fun 'a :fun 'a :bool");

        var pxEqQx = Congruence(eq, pEqQ);
        var ppEqQp = Congruence(pxEqQx, pEqP);
        
        return ModusPonens(ppEqQp, pEqP);
    }

    public static Theorem Commutativity(Theorem theorem)
    {
        if (!Kernel.TryDeconstructEquality(Kernel.DeconstructTheorem(theorem).conclusion, out var p, out var q))
            throw new TheoremException("Theorem is not an equality");

        var typedCommutativity = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = Kernel.TypeOf(p)
        }, CommutativityTheorem);
        
        var commutativity = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", Kernel.TypeOf(p))] = p,
            [MakeVariable("q", Kernel.TypeOf(q))] = q
        }, typedCommutativity);
        
        return Elimination(theorem, commutativity);
    }

    public static Theorem CommutativityEquality(Term term)
    {
        var assumption = Assume(term);
        var commutativity = Commutativity(assumption);
        var oppositeAssumption = Assume(DeconstructTheorem(commutativity).conclusion);
        var oppositeCommutativity = Commutativity(oppositeAssumption);
        return AntiSymmetry(oppositeCommutativity, commutativity);
    }
}