using ValiantProofVerifier;
using static ValiantProver.Modules.AndTheorems;
using static ValiantProver.Modules.ExistsTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.FunctionJectivityTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.SelectorTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public static class IndividualsTheorems
{
    public static void Load() { }

    static IndividualsTheorems()
    {
        FunctionJectivityTheorems.Load();
        
        DefineType("ind", 0);

        InfinityAxiom = NewAxiom(Parse(@"? f :fun :ind :ind . FUN_INJ f /\ ~FUN_SUR f"));

        IndSucAndInd0Exists = ConstructIndSucAndInd0Exists();
        IndSucDefinition =
            NewDefinition(Parse(@"IND_SUC = @ \f ind->ind ? z . (! x y . (f x = f y) = (x = y)) /\ ! x . ~(f x = z)"));
        Ind0Definition = NewDefinition(
            Parse(@"IND_0 = @ \z . (! x y . (IND_SUC x = IND_SUC y) = (x = y)) /\ ! x . ~(IND_SUC x = z)"));
    }
    
    public static Theorem InfinityAxiom { get; } // ? f ind->ind . FUN_INJ f /\ ~FUN_SUR f
    public static Theorem IndSucAndInd0Exists { get; } // ? f ind->ind z . (! x y . (f x = f y) = (x = y)) /\ ! x . ~(f x = z)
    public static Theorem IndSucDefinition { get; } // IND_SUC = @ \f ind->ind ? z . (! x y . (f x = f y) = (x = y)) /\ ! x . ~(f x = z)
    public static Theorem Ind0Definition { get; } // IND_0 = @ \z . (! x y . (IND_SUC x = IND_SUC y) = (x = y)) /\ ! x . ~(IND_SUC x = z)

    private static Theorem ConstructIndSucAndInd0Exists() // ? f ind->ind z . (! x y . (f x = f y) = (x = y)) /\ ! x . ~(f x = z)
    {
        // let inf be \ f . FUN_INJ f /\ ~FUN_SUR f
        var infinityThm = GetElementThatSatisfiesExistingFunction(InfinityAxiom); // |- inf @inf i.e. |-  // (\ f . FUN_INJ f /\ ~FUN_SUR f) @ (\ f . FUN_INJ f /\ ~FUN_SUR f)
        var infinityEval = EvaluateLambdas(infinityThm); // |- FUN_INJ @inf /\ ~(FUN_SUR @inf)
        var injective = DeconjugateLeft(infinityEval); // |- FUN_INJ @inf
        var surjective = DeconjugateRight(infinityEval); // |- ~(FUN_SUR @inf)

        var sInf = UnaryArgument(injective); // |- @inf

        var injEq = Specialise(InjectiveEqualityDefinition, sInf); // |-  FUN_INJ @inf = !x y. (@inf x = @inf y) = (x = y)
        var mpInj = ModusPonens(injEq, injective); // |- !x y. (@inf x = @inf y) = (x = y)

        var surjEq = Specialise(SurjectivityConverse, sInf); // |- ~(FUN_SUR @inf) = ?y. !x. ~(@inf x = y)
        var surjTrue = ModusPonens(surjEq, surjective); // |- ?y. !x. ~(@inf x = y)
        //var surjToSatisfy = BinaryRight(surjEq); // ? y . !x . ~(@inf x = y)
        var satistyElt = GetElementThatSatisfiesExistingFunction(surjTrue); // |- (\y . !x . ~(@inf x = y)) @func
        var satisfyEval = EvaluateLambdas(satistyElt); // |- !x . ~(@inf x = @func)
        var and = Conjugate(mpInj, satisfyEval); // |- (!x y. (@inf x = @inf y) = (x = y)) /\ (!x . ~(@inf x = @func))

        var inf = Parse(@"@ \ f :fun :ind :ind. FUN_INJ f /\ ~(FUN_SUR f)");
        AddTypedTermMacro("sInf", inf);
        var showExists = Parse(@"\ z . (! x y . (sInf x = sInf y) = (x = y)) /\ ! x . ~(sInf x = z)");
        RemoveMacro("sInf");

        var exists = Exists(showExists, and);
        return Exists(Parse(@"\ f :fun :ind :ind . ? z . (! x y . (f x = f y) = (x = y)) /\ ! x . ~(f x = z)"), exists);
    }
}