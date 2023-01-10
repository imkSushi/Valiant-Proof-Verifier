using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.ImpliesTheorems;
using static ValiantProver.Modules.OrTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;
using static ValiantProver.Modules.TruthTheorems;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public static class FalseAndNotTheorems
{
    public static void Load() { }
    
    static FalseAndNotTheorems()
    {
        OrTheorems.Load();
        
        FalseDefinition = NewBasicDefinition(Parse("F = ! p . p"));
        TryRegisterConst("F", "⊥");
        
        NotDefinition = NewBasicDefinition(Parse(@"~ = \p . p -> F"));

        TryRegisterPrefixRule("~", "~", 1, "¬");
        
        FalseImpliesAnythingTheorem = ConstructFalseImpliesAnythingTheorem();
        NotEqualsFalseTheorem = ConstructNotEqualsFalseTheorem();

        TrueEqualsTrue = ConstructTrueEqualsTrue();
        TrueEqualsFalse = ConstructTrueEqualsFalse();
        FalseEqualsTrue = ConstructFalseEqualsTrue();
        FalseEqualsFalse = ConstructFalseEqualsFalse();
        
        TrueAndTrue = ConstructTrueAndTrue();
        TrueAndFalse = ConstructTrueAndFalse();
        FalseAndTrue = ConstructFalseAndTrue();
        FalseAndFalse = ConstructFalseAndFalse();
        TrueOrTrue = ConstructTrueOrTrue();
        TrueOrFalse = ConstructTrueOrFalse();
        FalseOrTrue = ConstructFalseOrTrue();
        FalseOrFalse = ConstructFalseOrFalse();
        TrueImpliesTrue = ConstructTrueImpliesTrue();
        TrueImpliesFalse = ConstructTrueImpliesFalse();
        FalseImpliesTrue = ConstructFalseImpliesTrue();
        FalseImpliesFalse = ConstructFalseImpliesFalse();
        NotTrue = ConstructNotTrue();
        NotFalse = ConstructNotFalse();

        PEqualsNotPTheorem = ConstructPEqualsNotPTheorem();
    }

    public static Theorem FalseDefinition { get; }
    public static Theorem NotDefinition { get; }
    public static Theorem FalseImpliesAnythingTheorem { get; } // F |-  p
    public static Theorem NotEqualsFalseTheorem { get; } // |- ~p = (p = F)
    
    public static Theorem TrueEqualsTrue { get; } // |- (T = T) = T
    public static Theorem TrueEqualsFalse { get; } // |- (T = F) = F
    public static Theorem FalseEqualsTrue { get; } // |- (F = T) = F
    public static Theorem FalseEqualsFalse { get; } // |- (F = F) = T
    
    public static Theorem TrueAndTrue { get; } // |- (T /\ T) = T
    public static Theorem TrueAndFalse { get; } // |- (T /\ F) = F
    public static Theorem FalseAndTrue { get; } // |- (F /\ T) = F
    public static Theorem FalseAndFalse { get; } // |- (F /\ F) = F
    public static Theorem TrueOrTrue { get; } // |- (T \/ T) = T
    public static Theorem TrueOrFalse { get; } // |- (T \/ F) = T
    public static Theorem FalseOrTrue { get; } // |- (F \/ T) = T
    public static Theorem FalseOrFalse { get; } // |- (F \/ F) = F
    public static Theorem TrueImpliesTrue { get; } // |- (T -> T) = T
    public static Theorem TrueImpliesFalse { get; } // |- (T -> F) = F
    public static Theorem FalseImpliesTrue { get; } // |- (F -> T) = T
    public static Theorem FalseImpliesFalse { get; } // |- (F -> F) = T
    public static Theorem NotTrue { get; } // |- ~T = F
    public static Theorem NotFalse { get; } // |- ~F = T
    
    public static Theorem PEqualsNotPTheorem { get; } // p = ~p |- F

    private static Theorem ConstructNotEqualsFalseTheorem()
    {
        var p = MakeVariable("p", BoolTy); // p
        
        var notP = ApplyUnaryDefinition(NotDefinition, p); // |- ~p = (p -> F)
        var pImpF = ModusPonens(notP, Assume(Parse("~p"))); // ~p |- p -> F
        var fImpP = Discharge(MakeConstant("F"), FalseImpliesAnything(p)); // |- F -> p
        var pEqF = ApplyAntiSymmetry(pImpF, fImpP); // ~p |- p = F

        var pEqFAssumption = Assume(Parse("p = F")); // p = F |- p = F
        var implies = DeconstructEqualityToImplies(pEqFAssumption); // p = F |- p -> F
        var notPThm = ModusPonens(Commutativity(notP), implies); // p = F |- ~p
        
        return AntiSymmetry(notPThm, pEqF);
    }

    private static Theorem ConstructFalseImpliesAnythingTheorem()
    {
        var f = Assume(MakeConstant("F")); // F |- F
        var mp = ModusPonens(FalseDefinition, f); // F |- ! p . p
        return Specialise(mp, MakeVariable("p", BoolTy)); // F |- p
    }

    private static Theorem ConstructTrueEqualsTrue()
    {
        return AntiSymmetry(Reflexivity(MakeConstant("T")), Truth);
    }
    
    private static Theorem ConstructTrueEqualsFalse()
    {
        var tf = Parse("T = F");
        
        var fImpTf = FalseImpliesAnything(tf); // F |- (T = F)

        var tfImpTf = Assume(tf); // T = F |- T = F
        var mp = ModusPonens(tfImpTf, Truth); // T = F |- F
        
        return AntiSymmetry(fImpTf, mp);
    }
    
    private static Theorem ConstructFalseEqualsTrue()
    {
        var ft = Parse("F = T");
        
        var tImpFt = FalseImpliesAnything(ft); // F |- (F = T)

        var ftImpFt = Assume(ft); // F = T |- F = T
        var mp = ModusPonens(Commutativity(ftImpFt), Truth); // F = T |- F
        
        return AntiSymmetry(tImpFt, mp);
    }
    
    private static Theorem ConstructFalseEqualsFalse()
    {
        return AntiSymmetry(Reflexivity(MakeConstant("F")), Truth);
    }

    private static Theorem ConstructTrueAndTrue()
    {
        var trueAndTrue = AndTheorems.Conjugate(Truth, Truth); // T |- T /\ T

        return AntiSymmetry(trueAndTrue, Truth); // |- T /\ T = T
    }
    
    private static Theorem ConstructTrueAndFalse()
    {
        var trueAndFalse = Parse(@"T /\ F");
        var fImpTf = FalseImpliesAnything(trueAndFalse); // F |- T /\ F
        var tfImpF = AndTheorems.DeconjugateRight(Assume(trueAndFalse)); // T /\ F |- F

        return AntiSymmetry(fImpTf, tfImpF); // |- T /\ F = F
    }
    
    private static Theorem ConstructFalseAndTrue()
    {
        var falseAndTrue = Parse(@"F /\ T");
        var fImpTf = FalseImpliesAnything(falseAndTrue); // F |- F /\ T
        var tfImpF = AndTheorems.DeconjugateLeft(Assume(falseAndTrue)); // F /\ T |- F

        return AntiSymmetry(fImpTf, tfImpF); // |- F /\ T = F
    }
    
    private static Theorem ConstructFalseAndFalse()
    {
        var falseAndFalse = Parse(@"F /\ F");
        var fImpTf = FalseImpliesAnything(falseAndFalse); // F |- F /\ F
        var tfImpF = AndTheorems.DeconjugateLeft(Assume(falseAndFalse)); // F /\ F |- F

        return AntiSymmetry(fImpTf, tfImpF); // |- F /\ F = F
    }
    
    private static Theorem ConstructTrueOrTrue()
    {
        var trueOrTrue = Disjunct(Truth, Truth); // T |- T \/ T

        return AntiSymmetry(trueOrTrue, Truth); // |- T \/ T = T
    }
    
    private static Theorem ConstructTrueOrFalse()
    {
        var trueOrFalse = Disjunct(Truth, MakeConstant("F")); // T |- T \/ F

        return AntiSymmetry(trueOrFalse, Truth); // |- T \/ F = T
    }
    
    private static Theorem ConstructFalseOrTrue()
    {
        var falseOrTrue = Disjunct(MakeConstant("F"), Truth); // T |- F \/ T

        return AntiSymmetry(falseOrTrue, Truth); // |- F \/ T = T
    }
    
    private static Theorem ConstructFalseOrFalse()
    {
        var f = MakeConstant("F");
        var fImpF = Assume(f);
        
        var falseOrFalse = Disjunct(fImpF, f); // F |- F \/ F
        
        var cased = DisjunctCases(Assume(Parse(@"F \/ F")), fImpF, fImpF); // F \/ F |- F

        return AntiSymmetry(falseOrFalse, cased); // |- F \/ F = F
    }
    
    private static Theorem ConstructTrueImpliesTrue()
    {
        var imp = AddImpliesAssumption(Truth, MakeConstant("T")); // |- T -> T
        return AntiSymmetry(imp, Truth);
    }
    
    private static Theorem ConstructTrueImpliesFalse()
    {
        var f = MakeConstant("F");
        
        var imp = AddImpliesAssumption(Assume(f), MakeConstant("T")); // F |- T -> F

        var truthImpThingy = GivenTheoremImpliesAnythingThenAnything(Truth, f); // T -> F |- F
        
        return AntiSymmetry(imp, truthImpThingy); // |- T -> F = F
    }
    
    private static Theorem ConstructFalseImpliesTrue()
    {
        var imp = AddImpliesAssumption(Truth, MakeConstant("F")); // |- F -> T
        
        return AntiSymmetry(imp, Truth); // |- F -> T = T
    }
    
    private static Theorem ConstructFalseImpliesFalse()
    {
        return AntiSymmetry(SelfImplication(MakeConstant("F")), Truth); // |- F -> F = T
    }
    
    private static Theorem ConstructNotTrue()
    {
        var notTrue = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = MakeConstant("T")
        }, NotEqualsFalseTheorem); // |- ~T = (T = F)

        return Transitivity(notTrue, TrueEqualsFalse); // |- ~T = F
    }
    
    private static Theorem ConstructNotFalse()
    {
        var notFalse = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = MakeConstant("F")
        }, NotEqualsFalseTheorem); // |- ~F = (F = F)

        return Transitivity(notFalse, FalseEqualsFalse); // |- ~F = T
    }

    private static Theorem ConstructPEqualsNotPTheorem()
    {
        var p = MakeVariable("p", BoolTy);
        
        var assumption = Assume(Parse("p = ~p")); // p = ~p |- p = ~p
        var mp = ModusPonens(assumption, Assume(p)); // p = ~p, p |- ~p
        var notDef = ApplyUnaryDefinition(NotDefinition, p); // ~p = p -> F
        var mp2 = ModusPonens(notDef, mp); // p = ~p, p |- p -> F
        var undischarge = Undischarge(mp2); // p = ~p, p |- F
        var discharge = Discharge(p, undischarge); // p = ~p |- p -> F
        var notP = ModusPonens(Commutativity(notDef), discharge); // p = ~p |- ~p
        var pTrue = ModusPonens(Commutativity(assumption), notP); // p = ~p |- p
        
        return ApplyModusPonens(discharge, pTrue); // p = ~p |- F
    }

    public static Result<Theorem> TryFalseImpliesAnything(Term term)
    {
        if (term.TypeOf() != BoolTy)
            return "Term is not a boolean expression";

        return FalseImpliesAnything(term);
    }
    
    public static Theorem FalseImpliesAnything(Term term) // F |- p
    {
        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = term
        }, FalseImpliesAnythingTheorem);
    }

    public static Theorem Contradiction(Theorem theorem, Term premise) // p |- F goes to |- ~p
    {
        var notPremise = Discharge(premise, theorem);
        var notThm = ApplyUnaryDefinition(NotDefinition, premise);
        
        return ModusPonens(Commutativity(notThm), notPremise);
    }
    
    public static Result<Theorem> TryContradiction(Theorem theorem, Term premise)
    {
        if (theorem.Conclusion() != MakeConstant("F"))
            return "Expected a theorem with a false conclusion";
        
        if (!theorem.Premises().Contains(premise))
            return "Expected a premise that is part of the theorem";
        
        return Contradiction(theorem, premise);
    }

    public static Result<Theorem> TryContradictionFromPEqNotP(Theorem theorem) // |- p = ~p goes to F
    {
        if (!TryBinaryDeconstruct(theorem, "=").Deconstruct(out var left, out var right, out var error))
            return error;

        if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg, out error) && left == rightArg)
        {
            var inst = InstantiateVariables(new Dictionary<Term, Term>
            {
                [MakeVariable("p", BoolTy)] = left
            }, PEqualsNotPTheorem); // p = ~p |- F

            return Elimination(inst, theorem); // |- F
        }
        
        if (!TryUnaryDeconstruct(left, "~").Deconstruct(out var leftArg, out error) || right != leftArg)
            return "Expected a theorem of the form p = ~p or ~p = p";
        
        var inst2 = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = right
        }, PEqualsNotPTheorem); // p = ~p |- F
        
        return Elimination(inst2, Commutativity(theorem)); // |- F
    }
    
    public static Theorem ContradictionFromPEqNotP(Theorem theorem) // |- p = ~p goes to F
    {
        return TryContradictionFromPEqNotP(theorem).ValueOrException();
    }
}