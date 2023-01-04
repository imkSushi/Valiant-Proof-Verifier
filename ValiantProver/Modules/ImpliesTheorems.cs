using ValiantProofVerifier;
using static ValiantProver.Modules.AndTheorems;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class ImpliesTheorems
{
    public static void Load() { }

    static ImpliesTheorems()
    {
        AndTheorems.Load();
        
        ImpliesDefinition = NewBasicDefinition(Parse(@"-> = \ p q . p /\ q = p"));
        Parser.TryRegisterInfixRule("->", "->", 45, true);
        
        ImpliesModusPonens = ConstructImpliesModusPonens();
        ImpliesAssumption = ConstructImpliesAssumption();
    }
    
    public static Theorem ImpliesDefinition { get; }
    public static Theorem ImpliesModusPonens { get; }
    public static Theorem ImpliesAssumption { get; }

    private static Theorem ConstructImpliesAssumption()
    {
        //want: q |- p -> q
        var p = Parse("p :bool");
        var q = Parse("q :bool");
        var implies = ApplyBinaryDefinition(ImpliesDefinition, p, q); // p -> q = (p /\ q = p)
        var commutedImplies = Commutativity(implies); // q -> p = (p /\ q = p)
        
        var pQImpPAndQ = Conjugate(Assume(p), Assume(q)); // p, q |- p /\ q
        var pAndQImpP = DeconjugateLeft(Assume(Parse(@"p /\ q"))); // p /\ q |- p

        var antiSymmetry = AntiSymmetry(pQImpPAndQ, pAndQImpP); // q |- p /\ q = p
        return ModusPonens(commutedImplies, antiSymmetry); // q |- p -> q
    }
    
    public static Theorem AddImpliesAssumption(Theorem theorem, Term assumption)
    {
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = assumption,
            [MakeVariable("q", BoolTy)] = DeconstructTheorem(theorem).conclusion
        }, ImpliesAssumption);
        return Elimination(theorem, inst);
    }

    public static Theorem Discharge(Term premise, Theorem theorem)
    {
        // p |- q goes to |- p -> q
        var thmConclusion = DeconstructTheorem(theorem).conclusion;
        var p = Parse("p :bool");
        var implies = ApplyBinaryDefinition(ImpliesDefinition, Parse("p :bool"), Parse("q :bool")); // p -> q = (p /\ q = p)
        var commutedImplies = Commutativity(implies); // (p /\ q = p) = p -> q
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = premise,
            [Parse("q :bool")] = thmConclusion
        }, commutedImplies); // (p /\ q = p) = p -> q

        var pImpPAndQ = Conjugate(Assume(premise), theorem); // p |- p /\ q
        var pAndQImpP = DeconjugateLeft(Assume(ApplyBinaryFunction(@"/\", premise, thmConclusion))); // p /\ q |- p
        var antiSym = AntiSymmetry(pImpPAndQ, pAndQImpP); // |- p /\ q = p
        return ModusPonens(inst, antiSym);
    }

    public static Theorem Undischarge(Theorem theorem)
    {
        var (left, right, _) = BinaryDeconstruct(theorem);
        var assumption = Assume(left);
        return ApplyModusPonens(theorem, assumption);
    }

    public static Theorem ApplyAntiSymmetry(Theorem left, Theorem right)
    {
        var leftNormal = Undischarge(left);
        var rightNormal = Undischarge(right);

        return AntiSymmetry(leftNormal, rightNormal);
    }

    public static Theorem AddAssumption(Theorem theorem, Term assumption)
    {
        var discharged = AddImpliesAssumption(theorem, assumption);
        var assuming = Assume(assumption);
        
        return ApplyModusPonens(discharged, assuming);
    }

    public static Theorem DeconstructEqualityToImplies(Theorem theorem)
    {
        var (p, q, _) = BinaryDeconstruct(theorem); // p = q

        var pImpP = Assume(p); // p |- p
        
        var pImpQ = ModusPonens(theorem, pImpP); // p |- q
        return Discharge(p, pImpQ); // |- p -> q
    }

    public static (Theorem left, Theorem right) FullyDeconstructEqualityToImplies(Theorem theorem)
    {
        var left = DeconstructEqualityToImplies(theorem);
        var right = DeconstructEqualityToImplies(Commutativity(theorem));
        
        return (left, right);
    }

    public static Theorem ImpliesTransitivity(Theorem left, Theorem right)
    {
        var undischargedLeft = Undischarge(left);
        var undischargedRight = Undischarge(right);

        var transitivity = Elimination(undischargedLeft, undischargedRight);

        return Discharge(BinaryLeft(left), transitivity);
    }

    public static Theorem ApplyModusPonens(Theorem major, Theorem minor)
    {
        var (left, right, _) = BinaryDeconstruct(major);
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = left,
            [Parse("q :bool")] = right
        }, ImpliesModusPonens);

        return Elimination(new[] { major, minor }, inst);
    }

    private static Theorem ConstructImpliesModusPonens()
    {
        //want: p, p -> q |- q
        
        var simp = ApplyBinaryDefinition(ImpliesDefinition, Parse("p :bool"), Parse("q :bool")); // p -> q = (p /\ q = p)
        var major = Assume(Parse("p -> q")); // p -> q |- p -> q
        var minor = Assume(Parse("p :bool")); // p |- p
        var and = ModusPonens(simp, major); // p -> q |- p /\ q = p
        var commuted = Commutativity(and); // p -> q |- p = p /\ q
        var mp = ModusPonens(commuted, minor); // p -> q, p |- p /\ q
        return DeconjugateRight(mp);
    }
}