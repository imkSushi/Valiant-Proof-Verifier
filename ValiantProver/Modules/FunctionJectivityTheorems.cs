using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.ImpliesTheorems;
using static ValiantProver.Modules.TautologyEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;

namespace ValiantProver.Modules;

public static class FunctionJectivityTheorems
{
    public static void Load() { }

    static FunctionJectivityTheorems()
    {
        TautologyEvaluator.Load();
        
        InjectiveDefinition = NewDefinition(Parse("FUN_INJ f = !x y. (f x = f y) -> (x = y)"));
        InjectiveEqualityDefinition = ConstructInjectiveEqualityDefinition();
        
        SurjectiveDefinition = NewDefinition(Parse("FUN_SUR f = !y. ?x. f x = y"));
        SurjectivityConverse = ConstructSurjectivityConverse();
        
        BijectiveDefinition = NewDefinition(Parse(@"FUN_BIJ f = (FUN_INJ f /\ FUN_SUR f)"));
    }
    
    public static Theorem InjectiveDefinition { get; } // |- ! f . FUN_INJ f = !x y. (f x = f y) -> (x = y)
    public static Theorem InjectiveEqualityDefinition { get; } // |- ! f . FUN_INJ f = !x y. (f x = f y) = (x = y)
    public static Theorem SurjectiveDefinition { get; } // |- ! f . FUN_SUR f = !y. ?x. f x = y
    public static Theorem SurjectivityConverse { get; } // |- ! f . ~(FUN_SUR f) = ?y. !x. ~(f x = y)
    public static Theorem BijectiveDefinition { get; } // |- ! f . FUN_BIJ f = (FUN_INJ f /\ FUN_SUR f)

    private static Theorem ConstructInjectiveEqualityDefinition()
    {
        var f = Parse("f :fun 'a 'b");
        var x = Parse("x");
        var y = Parse("y");
        var spec = Specialise(InjectiveDefinition, f); // |- FUN_INJ f = !x y. (f x = f y) -> (x = y)
        
        var eq = Parse("x = y"); // |- x = y
        var assumption = Assume(eq); // x = y |- x = y
        var cong = Congruence(f, assumption); // x = y |- f x = f y
        var disch = Discharge(eq, cong); // |- (x = y) -> (f x = f y)
        
        var assumeInj = Assume(Parse("FUN_INJ f")); // FUN_INJ f |- FUN_INJ f
        var mpInj = ModusPonens(spec, assumeInj); // FUN_INJ f |- !x y. (f x = f y) -> (x = y)
        var specInj = Specialise(mpInj, x, y); // FUN_INJ f |- (f x = f y) -> (x = y)
        var impliesAntiSymmetry = ApplyAntiSymmetry(specInj, disch); // FUN_INJ f |- (f x = f y) = (x = y)
        var genInj = Generalise(impliesAntiSymmetry, x, y); // FUN_INJ f |- !x y. (f x = f y) = (x = y)

        var assumeWtp = Assume(Parse("! x y . (f x = f y) = (x = y)")); // ! x y . (f x = f y) = (x = y) |- ! x y . (f x = f y) = (x = y)
        var specWtp = Specialise(assumeWtp, x, y); // ! x y . (f x = f y) = (x = y) |- (f x = f y) = (x = y)
        var impliesWtp = DeconstructEqualityToImplies(specWtp); // ! x y . (f x = f y) = (x = y) |- (f x = f y) -> (x = y)
        var genWtp = Generalise(impliesWtp, x, y); // ! x y . (f x = f y) = (x = y) |- ! x y . (f x = f y) -> (x = y)
        var funInj = ModusPonens(Commutativity(spec), genWtp); // ! x y . (f x = f y) = (x = y) |- FUN_INJ f
        
        var antiSymmetry = AntiSymmetry(funInj, genInj); // |- FUN_INJ f = ! x y . (f x = f y) = (x = y)
        return Generalise(antiSymmetry, f); // |- ! f . FUN_INJ f = ! x y . (f x = f y) = (x = y)
    }

    private static Theorem ConstructSurjectivityConverse()
    {
        var f = Parse("f :fun 'a 'b");
        
        var tautEquivalent = TautologyEquivalent(Parse("~(!y 'b. ?x 'a. f x = y)"), Parse("?y 'b. !x 'a. ~(f x = y)")); // |- ~(!y. ?x. f x = y) = ?y. !x. ~(f x = y)
        
        var funSurj = Specialise(SurjectiveDefinition, f); // |- FUN_SUR f = !y. ?x. f x = y
        var inverted = InvertBothSidesOfEquals(funSurj); // |- ~(FUN_SUR f) = ~(!y. ?x. f x = y)
        
        var trans = Transitivity(inverted, tautEquivalent); // |- ~(FUN_SUR f) = ?y. !x. ~(f x = y)

        return Generalise(trans, f); // |- ! f . ~(FUN_SUR f) = ?y. !x. ~(f x = y)
    }
}