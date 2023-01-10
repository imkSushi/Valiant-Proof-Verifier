using ValiantBasics;
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
        TryRegisterInfixRule("->", "->", 45, true, "→");
        
        ImpliesModusPonens = ConstructImpliesModusPonens();
        ImpliesAssumption = ConstructImpliesAssumption();
        ImpliesItself = ConstructImpliesItself();
    }
    
    public static Theorem ImpliesDefinition { get; }
    public static Theorem ImpliesModusPonens { get; } // p, p -> q |- q
    public static Theorem ImpliesAssumption { get; } // q |- p -> q
    public static Theorem ImpliesItself { get; } // |- p -> p

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
    
    public static Theorem AddImpliesAssumption(Theorem theorem, Term assumption) // |- p & q goes to |- p -> q
    {
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = assumption,
            [MakeVariable("q", BoolTy)] = theorem.Deconstruct().conclusion
        }, ImpliesAssumption);
        return Elimination(inst, theorem);
    }
    
    public static Result<Theorem> TryAddImpliesAssumption(Theorem theorem, Term assumption)
    {
        if (assumption.TypeOf() != BoolTy)
            return $"Expected assumption to be of type bool, but was {assumption.TypeOf()}";
        
        return AddImpliesAssumption(theorem, assumption);
    }

    public static Theorem Discharge(Term premise, Theorem theorem)
    {
        // p |- q goes to |- p -> q
        var thmConclusion = theorem.Deconstruct().conclusion;
        var p = Parse("p :bool");
        var q = Parse("q :bool");
        var implies = ApplyBinaryDefinition(ImpliesDefinition, p, q); // p -> q = (p /\ q = p)
        var commutedImplies = Commutativity(implies); // (p /\ q = p) = p -> q
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [p] = premise,
            [q] = thmConclusion
        }, commutedImplies); // (p /\ q = p) = p -> q

        var pImpPAndQ = Conjugate(Assume(premise), theorem); // p |- p /\ q
        var pAndQImpP = DeconjugateLeft(Assume(ApplyBinaryFunction(@"/\", premise, thmConclusion))); // p /\ q |- p
        var antiSym = AntiSymmetry(pImpPAndQ, pAndQImpP); // |- p /\ q = p
        return ModusPonens(inst, antiSym);
    }

    public static Result<Theorem> TryDischarge(Term premise, Theorem theorem)
    {
        if (!theorem.Premises().Contains(premise))
            return $"Expected premise to be in the premises of the theorem, but it was not";

        return Discharge(premise, theorem);
    }

    public static Theorem Undischarge(Theorem theorem)
    {
        return TryUndischarge(theorem).ValueOrException();
    }
    
    public static Result<Theorem> TryUndischarge(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, "->").Deconstruct(out var left, out var right, out var error)) // |- p -> q
            return error;
        
        var assumption = Assume(left);
        return ApplyModusPonens(theorem, assumption); // p |- q
    }

    public static Theorem ApplyAntiSymmetry(Theorem left, Theorem right) // |- p -> q and |- q -> p goes to |- p = q
    {
        var leftNormal = Undischarge(left); // p |- q
        var rightNormal = Undischarge(right); // q |- p

        return AntiSymmetry(rightNormal, leftNormal); // |- p = q
    }
    
    public static Result<Theorem> TryApplyAntiSymmetry(Theorem left, Theorem right)
    {
        if (!TryUndischarge(left).Deconstruct(out var leftNormal, out var error))
            return error;
        
        if (!TryUndischarge(right).Deconstruct(out var rightNormal, out error))
            return error;

        return AntiSymmetry(leftNormal, rightNormal);
    }

    public static Theorem AddAssumption(Theorem theorem, Term assumption)
    {
        var discharged = AddImpliesAssumption(theorem, assumption);
        var assuming = Assume(assumption);
        
        return ApplyModusPonens(discharged, assuming);
    }
    
    public static Result<Theorem> TryAddAssumption(Theorem theorem, Term assumption)
    {
        if (assumption.TypeOf() != BoolTy)
            return $"Expected assumption to be of type bool, but was {assumption.TypeOf()}";
        
        return AddAssumption(theorem, assumption);
    }

    public static Theorem DeconstructEqualityToImplies(Theorem theorem)
    {
        return TryDeconstructEqualityToImplies(theorem).ValueOrException();
    }
    
    public static Result<Theorem> TryDeconstructEqualityToImplies(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, "=").Deconstruct(out var p, out var q, out var error))
            return error;

        var pImpP = Assume(p); // p |- p
        
        var pImpQ = ModusPonens(theorem, pImpP); // p |- q
        return Discharge(p, pImpQ); // |- p -> q
    }

    public static (Theorem left, Theorem right) FullyDeconstructEqualityToImplies(Theorem theorem)
    {
        return TryFullyDeconstructEqualityToImplies(theorem).ValueOrException();
    }
    
    public static Result<Theorem, Theorem> TryFullyDeconstructEqualityToImplies(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, "=").Deconstruct(out _, out _, out var error))
            return error;

        var left = DeconstructEqualityToImplies(theorem);
        var right = DeconstructEqualityToImplies(Commutativity(theorem));
        
        return (left, right);
    }

    public static Theorem ImpliesTransitivity(Theorem left, Theorem right)
    {
        return TryImpliesTransitivity(left, right).ValueOrException();
    }
    
    public static Result<Theorem> TryImpliesTransitivity(Theorem left, Theorem right)
    {
        if (!TryUndischarge(left).Deconstruct(out var undischargedLeft, out var error))
            return error;
        
        if (!TryUndischarge(right).Deconstruct(out var undischargedRight, out error))
            return error;

        if (!TryElimination(undischargedLeft, undischargedRight).Deconstruct(out var transitivity, out error))
            return error;
        

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

        return Elimination(inst, major, minor);
    }
    
    public static Result<Theorem> TryApplyModusPonens(Theorem major, Theorem minor)
    {
        if (!TryBinaryDeconstruct(major, "->").Deconstruct(out var left, out var right, out var error))
            return error;
        
        if (left != minor.Conclusion())
            return "Expected the minor to match the left side of the major";

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = left,
            [Parse("q :bool")] = right
        }, ImpliesModusPonens);

        return Elimination(inst, major, minor);
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

    private static Theorem ConstructImpliesItself()
    {
        var p = Parse("p :bool");
        var assumeP = Assume(p);
        var applied = ApplyBinaryDefinition(ImpliesDefinition, p, p); // p -> p = (p /\ p = p)
        var pImpPAndP = Conjugate(assumeP, assumeP); // p |- p /\ p
        var pAndPImpP = DeconjugateLeft(Assume(Parse(@"p /\ p"))); // p /\ p |- p
        var antiSym = AntiSymmetry(pImpPAndP, pAndPImpP); // |- p /\ p = p
        return ModusPonens(Commutativity(applied), antiSym);
    }

    public static Theorem SelfImplication(Term term)
    {
        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = term
        }, ImpliesItself);
    }
    
    public static Result<Theorem> TrySelfImplication(Term term)
    {
        if (term.TypeOf() != BoolTy)
            return $"Expected term to be of type bool, but was {term.TypeOf()}";
        
        return SelfImplication(term);
    }

    public static Theorem GivenTheoremImpliesAnythingThenAnything(Theorem theorem, Term term) // p and |- t goes to t -> p |- p
    {
        var conclusion = theorem.Deconstruct().conclusion; // t
        var implication = ApplyBinaryFunction("->", conclusion, term); // t -> p 
        var selfImplication = SelfImplication(implication); // |- (t -> p) -> (t -> p)
        var undischarged = Undischarge(selfImplication); // t -> p |- t -> p
        return ApplyModusPonens(undischarged, theorem); // t -> p |- p
    }
    
    public static Result<Theorem> TryGivenTheoremImpliesAnythingThenAnything(Theorem theorem, Term term)
    {
        if (term.TypeOf() != BoolTy)
            return $"Expected term to be of type bool, but was {term.TypeOf()}";
        
        return GivenTheoremImpliesAnythingThenAnything(theorem, term);
    }
}