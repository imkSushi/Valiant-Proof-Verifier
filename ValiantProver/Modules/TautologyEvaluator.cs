using System.Runtime.Intrinsics.Arm;
using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.ExistsTheorems;
using static ValiantProver.Modules.FalseAndNotTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.ImpliesTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.SelectorTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;
using static ValiantProver.Modules.TruthTheorems;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public static class TautologyEvaluator
{
    public static void Load() { }

    static TautologyEvaluator()
    {
        SelectorTheorems.Load();
        
        EnumeratedBoolTheorem = ConstructEnumeratedBoolTheorem();
        DoubleEnumeratedBoolTheorem = ConstructDoubleEnumeratedBoolTheorem();
        
        TrueEqualsP = CheckTrivialBools(Parse(@"\ p . (T = p) = p"));
        PEqualsTrue = CheckTrivialBools(Parse(@"\ p . (p = T) = p"));
        FalseEqualsP = CheckTrivialBools(Parse(@"\ p . (F = p) = ~p"));
        FalseEqualsNotP = CheckTrivialBools(Parse(@"\ p . (F = ~p) = p"));
        PEqualsFalse = CheckTrivialBools(Parse(@"\ p . (p = F) = ~p"));
        NotPEqualsFalse = CheckTrivialBools(Parse(@"\ p . (~p = F) = p"));
        NotPEqualsNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p = ~q) = (p = q)"));
        NotPEqualsQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p = q) = ~(p = q)"));
        NotPEqualsQInversion = CheckTrivialDoubleBools(Parse(@"\ p q . (~p = q) = (p = ~q)"));
        NotPEqualsP = CheckTrivialBools(Parse(@"\ p . (~p = p) = F"));
        PEqualsNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (p = ~q) = ~(p = q)"));
        PEqualsNotP = CheckTrivialBools(Parse(@"\ p . (p = ~p) = F"));

        TrueAndP = CheckTrivialBools(Parse(@"\ p . (T /\ p) = p"));
        PAndTrue = CheckTrivialBools(Parse(@"\ p . (p /\ T) = p"));
        FalseAndP = CheckTrivialBools(Parse(@"\ p . (F /\ p) = F"));
        PAndFalse = CheckTrivialBools(Parse(@"\ p . (p /\ F) = F"));
        PAndP = CheckTrivialBools(Parse(@"\ p . (p /\ p) = p"));
        PAndNotP = CheckTrivialBools(Parse(@"\ p . (p /\ ~p) = F"));
        NotPAndP = CheckTrivialBools(Parse(@"\ p . (~p /\ p) = F"));
        NotPAndNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p /\ ~q) = ~(p \/ q)"));
        
        TrueOrP = CheckTrivialBools(Parse(@"\ p . (T \/ p) = T"));
        POrTrue = CheckTrivialBools(Parse(@"\ p . (p \/ T) = T"));
        FalseOrP = CheckTrivialBools(Parse(@"\ p . (F \/ p) = p"));
        POrFalse = CheckTrivialBools(Parse(@"\ p . (p \/ F) = p"));
        POrP = CheckTrivialBools(Parse(@"\ p . (p \/ p) = p"));
        POrNotP = CheckTrivialBools(Parse(@"\ p . (p \/ ~p) = T"));
        NotPOrP = CheckTrivialBools(Parse(@"\ p . (~p \/ p) = T"));
        POrNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (p \/ ~q) = (q -> p)"));
        NotPOrQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p \/ q) = (p -> q)"));
        NotPOrNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p \/ ~q) = ~(p /\ q)"));
        
        TrueImpliesP = CheckTrivialBools(Parse(@"\ p . (T -> p) = p"));
        PImpliesTrue = CheckTrivialBools(Parse(@"\ p . (p -> T) = T"));
        FalseImpliesP = CheckTrivialBools(Parse(@"\ p . (F -> p) = T"));
        PImpliesFalse = CheckTrivialBools(Parse(@"\ p . (p -> F) = ~p"));
        NotPImpliesFalse = CheckTrivialBools(Parse(@"\ p . (~p -> F) = p"));
        PImpliesNotP = CheckTrivialBools(Parse(@"\ p . (p -> ~p) = ~p"));
        NotPImpliesP = CheckTrivialBools(Parse(@"\ p . (~p -> p) = p"));
        NotPImpliesQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p -> q) = (p \/ q)"));
        NotPImpliesQInversion = CheckTrivialDoubleBools(Parse(@"\ p q . (~p -> q) = (~q -> p)"));
        PImpliesNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (p -> ~q) = ~(p /\ q)"));
        PImpliesNotQInversion = CheckTrivialDoubleBools(Parse(@"\ p q . (p -> ~q) = (q -> ~p)"));
        NotPImpliesNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p -> ~q) = (q -> p)"));
        
        ExistsAndForAllInversionTheorem = ConstructExistsAndForAllInversionTheorem();
        ForAllAndExistsInversionTheorem = ConstructForAllAndExistsInversionTheorem();
        TrueAndFalseEqualTheorem = ConstructTrueAndFalseEqualTheorem();
    }
    
    public static Theorem EnumeratedBoolTheorem { get; } // f T, f F |- !x . f x
    public static Theorem DoubleEnumeratedBoolTheorem { get; } // f T T, f T F, f F T, f F F |- !x y . f x y
    public static Theorem TrueAndFalseEqualTheorem { get; } // f T = k, f F = k |- ! x . f x = k
    
    public static Theorem TrueEqualsP { get; } // |- ! p . (T = p) = p
    public static Theorem PEqualsTrue { get; } // |- ! p . (p = T) = p
    public static Theorem FalseEqualsP { get; } // |- ! p . (F = p) = ! p
    public static Theorem FalseEqualsNotP { get; } // |- ! p . (F = ! p) = p
    public static Theorem PEqualsFalse { get; } // |- ! p . (p = F) = ! p
    public static Theorem NotPEqualsFalse { get; } // |- ! p . (! p = F) = p
    public static Theorem NotPEqualsNotQ { get; } // |- ! p q . (~p = ~q) = (p = q)
    public static Theorem NotPEqualsQ { get; } // |- ! p q . (~p = q) = ~(p = q)
    public static Theorem NotPEqualsQInversion { get; } // ! p q . (~p = q) = (p = ~q)
    public static Theorem NotPEqualsP { get; } // |- ! p . (~p = p) = F
    public static Theorem PEqualsNotQ { get; } // |- ! p q . (p = ~q) = ~(p = q)
    public static Theorem PEqualsNotP { get; } // |- ! p . (p = ~p) = F
    
    public static Theorem TrueAndP { get; } // |- ! p . (T /\ p) = p
    public static Theorem PAndTrue { get; } // |- ! p . (p /\ T) = p
    public static Theorem FalseAndP { get; } // |- ! p . (F /\ p) = F
    public static Theorem PAndFalse { get; } // |- ! p . (p /\ F) = F
    public static Theorem PAndP { get; } // |- ! p . (p /\ p) = p
    public static Theorem PAndNotP { get; } // |- ! p . (p /\ ~p) = F
    public static Theorem NotPAndP { get; } // |- ! p . (~p /\ p) = F
    public static Theorem NotPAndNotQ { get; } // |- ! p q . (~p /\ ~q) = ~(p \/ q)
    
    public static Theorem TrueOrP { get; } // |- ! p . (T \/ p) = T
    public static Theorem POrTrue { get; } // |- ! p . (p \/ T) = T
    public static Theorem FalseOrP { get; } // |- ! p . (F \/ p) = p
    public static Theorem POrFalse { get; } // |- ! p . (p \/ F) = p
    public static Theorem POrP { get; } // |- ! p . (p \/ p) = p
    public static Theorem POrNotP { get; } // |- ! p . (p \/ ~p) = T
    public static Theorem NotPOrP { get; } // |- ! p . (~p \/ p) = T
    public static Theorem POrNotQ { get; } // |- ! p q . (p \/ ~q) = (q -> p)
    public static Theorem NotPOrQ { get; } // |- ! p q . (~p \/ q) = (p -> q)
    public static Theorem NotPOrNotQ { get; } // |- ! p q . (~p \/ ~q) = ~(p /\ q)
    
    public static Theorem TrueImpliesP { get; } // |- ! p . (T -> p) = p
    public static Theorem PImpliesTrue { get; } // |- ! p . (p -> T) = T
    public static Theorem FalseImpliesP { get; } // |- ! p . (F -> p) = T
    public static Theorem PImpliesFalse { get; } // |- ! p . (p -> F) = ~p
    public static Theorem NotPImpliesFalse { get; } // |- ! p . (~p -> F) = p
    public static Theorem PImpliesNotP { get; } // |- ! p . (p -> ~p) = ~p
    public static Theorem NotPImpliesP { get; } // |- ! p . (~p -> p) = p
    public static Theorem NotPImpliesQ { get; } // |- ! p q . (~p -> q) = (p \/ q)
    public static Theorem NotPImpliesQInversion { get; } // |- ! p q . (~p -> q) = (~q -> p)
    public static Theorem PImpliesNotQ { get; } // |- ! p q . (p -> ~q) = ~(p /\ q)
    public static Theorem PImpliesNotQInversion { get; } // |- ! p q . (p -> ~q) = (~p \/ q)
    public static Theorem NotPImpliesNotQ { get; } // |- ! p q . (~p -> ~q) = (q -> p)
    public static Theorem ExistsAndForAllInversionTheorem { get; } // |- ! f . ~(? f) = (! x . ~(f x))
    public static Theorem ForAllAndExistsInversionTheorem { get; } // |- ! f . ~(! f) = (? x . ~(f x))

    private static Theorem ConstructEnumeratedBoolTheorem() // f T, f F |- !x . f x
    {
        var x = MakeVariable("x", BoolTy);
        var f = Parse("f :fun :bool :bool");

        var assumeX = Assume(x); // x |- x
        var trueEqX = AntiSymmetry(Truth, assumeX); // x |- T = x
        var ftEqFx = Congruence(f, trueEqX); // x |- f T = f x
        var xImpFx = ModusPonens(ftEqFx, Assume(MakeCombination(f, MakeConstant("T")))); // x, f T |- f x

        var assumeNotX = Assume(Parse("~x")); // ~x |- ~x
        var notEqualsFalseThm = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", BoolTy)] = x
        }, NotEqualsFalseTheorem); // |- ~x = (x = F)
        var falseEqNotX = ModusPonens(notEqualsFalseThm, assumeNotX); // ~x |- x = F
        var ffEqFx = Congruence(f, Commutativity(falseEqNotX)); // ~x |- f F = f ~x
        var notXImpFx = ModusPonens(ffEqFx, Assume(MakeCombination(f, MakeConstant("F")))); // ~x, f F |- f ~x
        
        var thm = CasesProof(xImpFx, notXImpFx, x); // f T, f F|- f x

        return Generalise(thm, x);
    }

    private static Theorem ConstructDoubleEnumeratedBoolTheorem() // f T T, f T F, f F T, f F F |- !x y . f x y
    {
        var tr = MakeConstant("T");
        var fal = MakeConstant("F");
        
        var f = Parse("f :fun :bool :fun :bool :bool"); // f
        var ft = MakeCombination(f, tr); // f T
        var ff = MakeCombination(f, fal); // f F
        var oldF = Parse("f :fun :bool :bool");
        var x = MakeVariable("x", BoolTy); // x
        var y = MakeVariable("y", BoolTy); // y
        
        var thmT = InstantiateVariables(new Dictionary<Term, Term>
        {
            [oldF] = ft
        }, EnumeratedBoolTheorem); // f T T, f T F |- !x . f T x
        var specT = Specialise(thmT, y); // f T T, f T F |- f T y
        
        var thmF = InstantiateVariables(new Dictionary<Term, Term>
        {
            [oldF] = ff
        }, EnumeratedBoolTheorem); // f F T, f F F |- !x . f F x
        var specF = Specialise(thmF, y); // f F T, f F F |- f F y

        var g = Parse(@"\x . f :fun :bool :fun :bool :bool x y");
        var gx = MakeCombination(g, x); // (\x . f x y) x
        var gxEval = EvaluateLambdas(gx); // |- (\x . f x y) x = f x y
        var gtEval = InstantiateVariables(new Dictionary<Term, Term>
        {
            [x] = tr
        }, gxEval); // |- g T = f T y
        var mpGt = ModusPonens(Commutativity(gtEval), specT); // f T T, f T F |- g T
        
        var gfEval = InstantiateVariables(new Dictionary<Term, Term>
        {
            [x] = fal,
        }, gxEval); // |- g F = f F y
        var mpGf = ModusPonens(Commutativity(gfEval), specF); // f F T, f F F |- g F

        var thmG = InstantiateVariables(new Dictionary<Term, Term>
        {
            [oldF] = g,
        }, EnumeratedBoolTheorem); // g F, g T |- !x . g x
        var spec = Specialise(thmG, x); // g F, g T |- g x
        var elim = Elimination(spec, mpGf, mpGt); // f T T, f T F, f F T, f F F |- g x
        var eval = EvaluateLambdas(elim); // f T T, f T F, f F T, f F F |- f x y

        return Generalise(eval, new []{x, y});
    }

    private static Theorem ConstructExistsAndForAllInversionTheorem() // |- ! f . ~(? f) = ! x . ~(f x)
    {
        var f = Parse("f :fun 'a :bool");
        var x = Parse("x 'a");
        var fx = MakeCombination(f, x);
        
        var assumeFx = Assume(fx); // f x |- f x
        var exists = Exists(Parse(@"\x . f :fun 'a :bool x"), assumeFx); // f x |- ? x . f x
        var inverted = InvertTheoremAndPremise(exists, fx); // ~(? x . f x) |- ~(f x)
        var generalised = Generalise(inverted, x); // ~(? x . f x) |- ! x . ~(f x)

        var assumeExists = Assume(Parse("? x 'a . f x")); // ? x . f x |- ? x . f x
        var existsExample = GetElementThatSatisfiesExistingFunction(assumeExists); // ? x . f x |- (\ x . f x) @(\ x . f x)
        var existsEval = EvaluateLambdas(existsExample); // ? x . f x |- f @f
        
        var assumeForAll = Assume(Parse("! x 'a . ~(f x)")); // ! x . ~(f x) |- ! x . ~(f x)
        var forAllExample = Specialise(assumeForAll, Parse(@"@f")); // ! x . ~(f x) |- ~(f @f)
        var contradiction = ContradictionFromPEqNotP(AntiSymmetry(existsEval, forAllExample)); // ! x . ~(f x), ? x . f x |- F
        var result = Contradiction(contradiction, Parse("? x 'a . f x")); // ! x . ~(f x) |- ~(? f)

        var antiSym = AntiSymmetry(result, generalised); // ~(? f) = ! x . ~(f x)

        return Generalise(antiSym, f); // |- ! f . ~(? f) = ! x . ~(f x)
    }

    private static Theorem ConstructForAllAndExistsInversionTheorem() // |- ! f . ~(! f) = (? x . ~(f x))
    {
        var f = Parse("f :fun 'a :bool");
        var arg = Parse(@"\x 'a . ~(f x)");

        var spec = Specialise(ExistsAndForAllInversionTheorem, arg); // |- ~(? ~(f x)) = ! x . ~~(f x)

        var notNot = Specialise(DoubleNotEliminationTheorem, Parse("f :fun 'a :bool x")); // |- ~~(f x) = f x
        var abs = Abstraction(Parse("x 'a"), notNot); // |- \x . ~~(f x) = \x . f x
        var forAllNotNot = Congruence(MakeConstant("!"), abs); // |- ! x . ~~(f x) = ! \x . f x
        
        var noNotSpec = Transitivity(spec, forAllNotNot); // |- ~(? ~(f x)) = ! \x . f x
        var simp = EvaluateLambdas(noNotSpec); // |- ~(? ~(f x)) = ! f

        var inverted = InvertBothSidesOfEquals(simp); // |- (? ~(f x)) = ~(! f)
        return Generalise(Commutativity(inverted), f); // |- ! f . ~(! f) = (? x . ~(f x))
    }

    private static Theorem ConstructTrueAndFalseEqualTheorem() // f T = k, f F = k |- ! x . f x = k
    {
        var assumptionT = Assume(Parse("f T = k 'a"));
        var assumptionF = Assume(Parse("f F = k 'a"));

        var enumerated = CasesEnumeratedBools(assumptionT, assumptionF, Parse(@"\ x :bool . f x = k 'a")); // f T = k, f F = k |- ! x . (\x .f x = k) x

        return EvaluateLambdas(enumerated); // f T = k, f F = k |- ! x . f x = k
    }

    public static Theorem CasesEnumeratedBools(Theorem ft, Theorem ff, Term f)
    {
        return (Theorem) TryCasesEnumeratedBools(ft, ff, f);
    }

    public static Result<Theorem> TryCasesEnumeratedBools(Theorem ft, Theorem ff, Term f)
    {
        var tr = MakeConstant("T");
        var fal = MakeConstant("F");

        if (!f.TypeOf().TryDeconstructFun().Deconstruct(out var from, out var to, out var error))
            return error;

        if (from != BoolTy || to != BoolTy)
            return "Expected a function from booleans to booleans";

        if (!TryLambdaEquivalence(ft.Conclusion(), MakeCombination(f, tr)).Deconstruct(out var evalTr, out error)) // |- ft = f T
            return error;

        var ftTrue = ModusPonens(evalTr, ft); // |- f T

        if (!TryLambdaEquivalence(ff.Conclusion(), MakeCombination(f, fal)).Deconstruct(out var evalFal, out error)) // |- ff = f F
            return error;
        
        var ffTrue = ModusPonens(evalFal, ff); // |- f F
        
        var etaLambdaEq = LambdaEquivalence(Parse("! x :bool . f x"), Parse(@"! f :fun :bool :bool")); // |- ! x . f x = ! f
        var ourDefn = ModusPonens(etaLambdaEq, EnumeratedBoolTheorem); // f T, f F |- ! f

        var subs = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("f :fun :bool :bool")] = f
        }, ourDefn); // f T, f F |- ! f

        return Elimination(subs, ftTrue, ffTrue); // |- ! f
    }

    public static Theorem CasesDoubleEnumeratedBools(Theorem ftt, Theorem ftf, Theorem fft, Theorem fff, Term f)
    {
        return (Theorem) TryCasesDoubleEnumeratedBools(ftt, ftf, fft, fff, f);
    }

    public static Result<Theorem> TryCasesDoubleEnumeratedBools(Theorem ftt, Theorem ftf, Theorem fft, Theorem fff, Term f)
    {
        var tr = MakeConstant("T");
        var fal = MakeConstant("F");
        
        if (!f.TryDeconstructAbs().Deconstruct(out var param1, out var abs1, out var error))
            return error;

        if (!abs1.TryDeconstructAbs().Deconstruct(out var param2, out var abs2, out error))
            return error;

        if (!f.TypeOf().TryDeconstructFun().Deconstruct(out var from, out var to, out error))
            return error;

        var (param1Name, param1Type) = param1.DeconstructVar();
        var (param2Name, param2Type) = param2.DeconstructVar();
        
        if (param1Type != BoolTy || param2Type != BoolTy || abs2.TypeOf() != BoolTy)
            return "Expected a function from two booleans to booleans";
        

        if (!TryLambdaEquivalence(ftt.Conclusion(), MakeCombination(MakeCombination(f, tr), tr)).Deconstruct(out var evalTt, out error)) // |- ftt = f T T
            return error;
        
        if (!TryLambdaEquivalence(ftf.Conclusion(), MakeCombination(MakeCombination(f, tr), fal)).Deconstruct(out var evalTf, out error)) // |- ftf = f T F
            return error;
        
        if (!TryLambdaEquivalence(fft.Conclusion(), MakeCombination(MakeCombination(f, fal), tr)).Deconstruct(out var evalFt, out error)) // |- fft = f F T
            return error;
        
        if (!TryLambdaEquivalence(fff.Conclusion(), MakeCombination(MakeCombination(f, fal), fal)).Deconstruct(out var evalFf, out error)) // |- fff = f F F
            return error;
        
        var ftTrue = ModusPonens(evalTt, ftt); // |- f T T
        var ftFalse = ModusPonens(evalTf, ftf); // |- f T F
        var ffTrue = ModusPonens(evalFt, fft); // |- f F T
        var ffFalse = ModusPonens(evalFf, fff); // |- f F F

        var unusedX = GetFreeVariableName(UsedNames(f).Append("f").ToHashSet(), "x");
        var unusedY = GetFreeVariableName(UsedNames(f).Append(unusedX).Append("f").ToHashSet(), "y");
        
        var etaLambdaEq = LambdaEquivalence(Parse("! x :bool y :bool . f x y"), Parse($@"! {unusedX} :bool {unusedY} :bool . f {unusedX} {unusedY}")); // |- ! x y . f x y = ! x' y' . f x' y'
        var ourDefn = ModusPonens(etaLambdaEq, DoubleEnumeratedBoolTheorem); // f T T, f T F, f F T, f F F |- ! x' y' . f x' y'
        
        
        var subs = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("f :fun :bool :fun :bool :bool")] = f
        }, ourDefn); // f T T, f T F, f F T, f F F |- ! x y . f x y

        var elim = Elimination(subs, ftTrue, ftFalse, ffTrue, ffFalse); // |- ! x y . (\ x y . t) x y

        var desiredRight = ApplyUnaryFunction("!", MakeAbstraction(param1, ApplyUnaryFunction("!", abs1))); // ! x y . t
        var desiredEqiv = LambdaEquivalence(elim.Conclusion(), desiredRight); // |- ! x y . (\ x y . t) x y = ! x y . t
        
        return ModusPonens(desiredEqiv, elim);
    }

    public static Theorem Tautology(Term term)
    {
        var lambdaEval = EvaluateLambdas(term);

        var taut = TautologyPostLambda(BinaryRight(lambdaEval));

        return Transitivity(lambdaEval, taut);
    }

    private static Theorem TautologyPostLambda(Term term)
    {
        if (term.IsConst() || term.IsVar())
            return Reflexivity(term);

        return SimplifyTruthsAndFalses(term);
    }

    public static Result<Theorem> TryTautologyEquivalent(Term left, Term right)
    {
        if (!TryTautology(left).Deconstruct(out var leftThm, out var error))
            return error;

        if (!TryTautology(right).Deconstruct(out var rightThm, out error))
            return error;

        return TryTransitivity(leftThm, Commutativity(rightThm));
    }

    public static Theorem TautologyEquivalent(Term left, Term right)
    {
        return (Theorem) TryTautologyEquivalent(left, right);
    }

    public static Result<Theorem> TryTautology(Term term)
    {
        if (term.TypeOf() != BoolTy)
            return "Term is not a boolean expression";
        
        return Tautology(term);
    }

    public static Theorem Tautology(Theorem theorem)
    {
        var taut = Tautology(theorem.Conclusion());

        return ModusPonens(taut, theorem);
    }

    public static Theorem SimplifyTruthsAndFalses(Term term)
    {
        if (term.IsVar() || term.IsConst())
            return Reflexivity(term);

        if (term.TryDeconstructAbs().IsSuccess(out var variable, out var abstraction))
            return SimplifyTruthsAndFalsesAbstractions(variable, abstraction);
        
        if (term.TryDeconstructComb().IsSuccess(out var application, out var argument))
            return SimplifyTruthsAndFalsesCombination(application, argument);
        
        throw new Exception("Invalid term");
    }

    private static Theorem SimplifyTruthsAndFalsesAbstractions(Term variable, Term abstraction)
    {
        return Abstraction(variable, SimplifyTruthsAndFalses(abstraction));
    }
    
    private static Theorem SimplifyTruthsAndFalsesCombination(Term application, Term argument)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");
        
        var evalApp = SimplifyTruthsAndFalses(application);
        var evalArg = SimplifyTruthsAndFalses(argument);
        
        var congruence = Congruence(evalApp, evalArg);
        
        var toDealWith = BinaryRight(congruence);
        
        if (!TryBinaryDeconstruct(toDealWith).IsSuccess(out var left, out var right, out var op))
        {
            if (!TryUnaryDeconstruct(toDealWith).IsSuccess(out var unaryOp, out var arg))
                return congruence;

            if (!unaryOp.TryDeconstructConst().IsSuccess(out var unaryName, out _))
                return congruence;

            return unaryName switch
            {
                "~" => Transitivity(congruence, SimplifyNot(arg)),
                "!" => Transitivity(congruence, SimplifyForAll(arg)),
                "?" => Transitivity(congruence, SimplifyExists(arg)),
                _   => congruence
            };
        }

        var eqn = congruence;

        if (op.TryDeconstructConst().Deconstruct(out var name, out _, out _))
        {
            eqn = name switch
            {
                "="   => Transitivity(congruence, SimplifyEquals(left, right)),
                @"/\" => Transitivity(congruence, SimplifyAnd(left, right)),
                @"\/" => Transitivity(congruence, SimplifyOr(left, right)),
                "->"  => Transitivity(congruence, SimplifyImplies(left, right)),
                _     => congruence
            };
        }

        var toDealWith2 = BinaryRight(eqn);
        if (!TryBinaryDeconstruct(toDealWith2).IsSuccess(out var leftEqn, out var rightEqn, out _))
            return eqn;

        var leftFrees = leftEqn.FreesIn().Where(v => v.TypeOf() == BoolTy);
        var rightFrees = rightEqn.FreesIn().Where(v => v.TypeOf() == BoolTy);
        var intersect = leftFrees.Intersect(rightFrees).ToList();

        for (var index = 0; index < intersect.Count; index++)
        {
            var freeVar = intersect[index];
            if (index > 0 && !IsVariableFree(freeVar, toDealWith2))
                continue;
            var newEqn = SimplifyFreeBoolVariable(toDealWith2, freeVar);
            if (newEqn == null)
                continue;
            eqn = Transitivity(eqn, newEqn);
            if (index == intersect.Count - 1)
                return eqn;
            
            toDealWith2 = BinaryRight(newEqn);
        }
        
        return eqn;
    }
    
    private static Theorem SimplifyForAll(Term term)
    {
        var forAllTerm = ApplyUnaryFunction("!", term);
        
        if (!term.TryDeconstructAbs().IsSuccess(out var variable, out var abstraction))
            return Reflexivity(forAllTerm);

        if (!IsVariableFree(variable, abstraction))
            return ForAllIndependentOfVar(forAllTerm);

        if (!TryUnaryDeconstruct(abstraction, "~").IsSuccess(out var abs)) // ! y . ~(g y = z) went to \ y . ~(g y = z) goes to g y = z
            return Reflexivity(forAllTerm);

        var unique = ChangeToUniqueVariables(ExistsAndForAllInversionTheorem, UsedNames(term), new Dictionary<string, string>
        {
            ["x"] = variable.DeconstructVar().name
        }); // |- ! f . ~(? f) = ! x . ~(f x)

        var (name, type) = variable.DeconstructVar();

        if (type != MakeType("a"))
        {
            unique = InstantiateTypes(new Dictionary<Type, Type>
            {
                [MakeType("a")] = type
            }, unique);
        }

        var thm = Commutativity(Specialise(unique, MakeAbstraction(variable, abs))); // |- (! y . ~((\y . g y = z) y) = ~(? (\ y . (g y = z)))

        var lambdaEquiv = LambdaEquivalence(forAllTerm, BinaryLeft(thm)); // |- (! y . ~(g y = z)) = (! y . ~((\y . g y = z) y)
        return Transitivity(lambdaEquiv, thm); // (! y . ~(g y = z)) = ~(? (\ y . (g y = z)))
    }

    private static Theorem SimplifyExists(Term term)
    {
        var existsTerm = ApplyUnaryFunction("?", term);

        if (!term.TryDeconstructAbs().IsSuccess(out var variable, out var abstraction))
            return Reflexivity(existsTerm);

        if (!IsVariableFree(variable, abstraction))
            return ExistsIndependentOfVar(existsTerm);

        if (!TryUnaryDeconstruct(abstraction, "~").IsSuccess(out var abs)) // ? x . ~(f x)
            return Reflexivity(existsTerm);

        var unique = ChangeToUniqueVariables(ForAllAndExistsInversionTheorem, UsedNames(term), new Dictionary<string, string>
        {
            ["x"] = variable.DeconstructVar().name
        }); // |- ! f . ~(! f) = ? x . ~(f x)

        var type = variable.DeconstructVar().type;

        if (type != MakeType("a"))
        {
            unique = InstantiateTypes(new Dictionary<Type, Type>
            {
                [MakeType("a")] = type
            }, unique);
        }

        var thm = Commutativity(Specialise(unique, MakeAbstraction(variable, abs)));

        var lambdaEquiv = LambdaEquivalence(existsTerm, BinaryLeft(thm));
        return Transitivity(lambdaEquiv, thm);
    }

    private static Theorem SimplifyNot(Term term)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");
        
        if (term == t)
            return NotTrue;

        if (term == f)
            return NotFalse;

        if (TryUnaryDeconstruct(term, "~").Deconstruct(out var notArg, out _))
            return Specialise(DoubleNotEliminationTheorem, notArg);
        
        return Reflexivity(ApplyUnaryFunction("~", term));
    }

    private static Theorem SimplifyEquals(Term left, Term right)
    {
        if (left == right) // p = p
            return AntiSymmetry(Reflexivity(left), Truth); // |- (p = p) = T
        
        var t = MakeConstant("T");
        var f = MakeConstant("F");

        if ((left == t || left == f) && (right == t || right == f))
        {
            return (left == t, right == t) switch
            {
                (true, true)   => TrueEqualsTrue,
                (true, false)  => TrueEqualsFalse,
                (false, true)  => FalseEqualsTrue,
                (false, false) => FalseEqualsFalse,
            };
        }

        if (left == t) // (T = p) = p
            return Specialise(TrueEqualsP, right);

        if (right == t) // (p = T) = p
            return Specialise(PEqualsTrue, left);

        if (left == f) // (F = p) = ~p and (F = ~p) = p
            return TryUnaryDeconstruct(right, "~").Deconstruct(out var arg, out _)
                ? Specialise(FalseEqualsNotP, arg)
                : Specialise(FalseEqualsP, right);

        if (right == f) // (p = F) = ~p and (~p = F) = p
            return TryUnaryDeconstruct(left, "~").Deconstruct(out var arg, out _)
                ? Specialise(NotPEqualsFalse, arg)
                : Specialise(PEqualsFalse, left);

        if (TryUnaryDeconstruct(left, "~").Deconstruct(out var leftArg, out _))
        {
            if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg, out _)) // (~p = ~q) = (p = q)
                return Specialise(NotPEqualsNotQ, new[] { leftArg, rightArg });

            if (leftArg == right) // (~p = p) = F
                return Specialise(NotPEqualsP, leftArg);

            // (~p = q) = ~(p = q)
            return Specialise(NotPEqualsQ, new[] { leftArg, right });
        }

        if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg1, out _))
        {
            if (rightArg1 == left) // (p = ~p) = F
                return Specialise(PEqualsNotP, rightArg1);

            return Specialise(PEqualsNotQ, new []{left, rightArg1}); // (p = ~q) = ~(p = q)
        }

        return Reflexivity(ApplyBinaryFunction("=", left, right)); // (p = q) = (p = q)
    }

    private static Theorem SimplifyAnd(Term left, Term right)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");

        if ((left == t || left == f) && (right == t || right == f))
        {
            return (left == t, right == t) switch
            {
                (true, true)   => TrueAndTrue,
                (true, false)  => TrueAndFalse,
                (false, true)  => FalseAndTrue,
                (false, false) => FalseAndFalse,
            };
        }
        
        if (left == t)
            return Specialise(TrueAndP, right);
        
        if (right == t)
            return Specialise(PAndTrue, left);
        
        if (left == f)
            return Specialise(FalseAndP, right);
        
        if (right == f)
            return Specialise(PAndFalse, left);
        
        if (left == right)
            return Specialise(PAndP, left);

        if (TryUnaryDeconstruct(left, "~").Deconstruct(out var leftArg, out _))
        {
            if (leftArg == right)
                return Specialise(NotPAndP, leftArg);
            
            if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg, out _))
                return Specialise(NotPAndNotQ, new[] { leftArg, rightArg });
        }
        
        if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg1, out _))
        {
            if (rightArg1 == left)
                return Specialise(PAndNotP, rightArg1);
        }
        
        return Reflexivity(ApplyBinaryFunction("/\\", left, right));
    }

    private static Theorem SimplifyOr(Term left, Term right)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");
        
        if ((left == t || left == f) && (right == t || right == f))
        {
            return (left == t, right == t) switch
            {
                (true, true)   => TrueOrTrue,
                (true, false)  => TrueOrFalse,
                (false, true)  => FalseOrTrue,
                (false, false) => FalseOrFalse,
            };
        }
        
        if (left == t)
            return Specialise(TrueOrP, right);
        
        if (right == t)
            return Specialise(POrTrue, left);
        
        if (left == f)
            return Specialise(FalseOrP, right);
        
        if (right == f)
            return Specialise(POrFalse, left);
        
        if (left == right)
            return Specialise(POrP, left);

        if (TryUnaryDeconstruct(left, "~").Deconstruct(out var leftArg, out _))
        {
            if (leftArg == right)
                return Specialise(NotPOrP, leftArg);
            
            if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg1, out _))
                return Specialise(NotPOrNotQ, new[] { leftArg, rightArg1 });
            
            return Specialise(NotPOrQ, new[] { leftArg, right });
        }
        
        if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg, out _))
        {
            if (rightArg == left)
                return Specialise(POrNotP, rightArg);
            
            return Specialise(POrNotQ, new[] { left, rightArg });
        }
        
        return Reflexivity(ApplyBinaryFunction("\\/", left, right));
    }

    private static Theorem SimplifyImplies(Term left, Term right)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");
        
        if ((left == t || left == f) && (right == t || right == f))
        {
            return (left == t, right == t) switch
            {
                (true, true)   => TrueImpliesTrue,
                (true, false)  => TrueImpliesFalse,
                (false, true)  => FalseImpliesTrue,
                (false, false) => FalseImpliesFalse,
            };
        }
        
        if (left == t)
            return Specialise(TrueImpliesP, right);
        
        if (right == t)
            return Specialise(PImpliesTrue, left);
        
        if (left == f)
            return Specialise(FalseImpliesP, right);

        if (TryUnaryDeconstruct(left, "~").Deconstruct(out var leftArg, out _))
        {
            if (right == f)
                return Specialise(NotPImpliesFalse, leftArg);

            if (leftArg == right)
                return Specialise(NotPImpliesP, leftArg);
            
            if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg1, out _))
                return Specialise(NotPImpliesNotQ, new[] { leftArg, rightArg1 });
            
            return Specialise(NotPImpliesQ, new[] { leftArg, right });
        }
        
        if (right == f)
            return Specialise(PImpliesFalse, left);

        if (TryUnaryDeconstruct(right, "~").Deconstruct(out var rightArg, out _))
        {
            if (rightArg == left)
                return Specialise(POrNotP, rightArg);
            
            return Specialise(PImpliesNotQ, new[] { left, rightArg });
        }
        
        return Reflexivity(ApplyBinaryFunction("->", left, right));
    }
    
    public static Theorem SimplifyTruthsAndFalses(Theorem theorem)
    {
        var simp = SimplifyTruthsAndFalses(theorem.Conclusion());

        return ModusPonens(simp, theorem);
    }

    private static Theorem? SimplifyFreeBoolVariable(Term term, Term variable) //returns null if no simpification possible
    {
        var ft = InstantiateVariables(new Dictionary<Term, Term>
        {
            [variable] = MakeConstant("T")
        }, term);
        
        var ff = InstantiateVariables(new Dictionary<Term, Term>
        {
            [variable] = MakeConstant("F")
        }, term);

        var evalFt = TautologyPostLambda(ft);
        var evalFf = TautologyPostLambda(ff);

        var right = BinaryRight(evalFt);

        if (right != BinaryRight(evalFf))
            return null;
        
        var cased = CasesEnumeratedBools(evalFt, evalFf, MakeAbstraction(variable, ApplyBinaryFunction("=", term, right))); // |- ! p . f p = k
        return Specialise(cased, variable);
    }

    public static Theorem EvaluateDeterminedTruthsAndFalses(Term term)
    {
        return (Theorem) TryEvaluateDeterminedTruthsAndFalses(term);
    }

    public static Result<Theorem> TryEvaluateDeterminedTruthsAndFalses(Term term)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");

        if (term == t || term == f)
            return Reflexivity(term);

        if (TryUnaryDeconstruct(term, "~").Deconstruct(out var innerTerm, out _))
        {
            if (!TryEvaluateDeterminedTruthsAndFalses(innerTerm).Deconstruct(out var innerValue, out var error)) // p = ?
                return error;
            
            var applyNot = Congruence(MakeConstant("~"), innerValue); // ~p = ~?

            return Transitivity(applyNot, BinaryRight(innerValue) == t ? NotTrue : NotFalse);
        }
        
        if (!TryBinaryDeconstruct(term).Deconstruct(out var left, out var right, out var op, out _))
            return "Not a determined truth or falsity";
        
        if (!op.TryDeconstructConst().Deconstruct(out var opName, out _, out _))
            return "Not a determined truth or falsity";

        switch (opName)
        {
            case "=":
                return TryEvaluteDeterminedEquality(left, right);
            case @"/\":
                return TryEvaluateDeterminedAnd(left, right);
            case @"\/":
                return TryEvaluateDeterminedOr(left, right);
            case "->":
                return TryEvaluateDeterminedImplies(left, right);
            default:
                return "Not a determined truth or falsity";
        }
    }

    private static Result<Theorem> TryEvaluteDeterminedEquality(Term left, Term right) // p = q
    {
        return TryEvaluateDeterminedBinary(left, right, Parse(@"= :fun :bool :fun :bool :bool"), (l, r) => (l, r) switch
        {
            (true, true)   => TrueEqualsTrue,
            (true, false)  => TrueEqualsFalse,
            (false, true)  => FalseEqualsTrue,
            (false, false) => FalseEqualsFalse
        });
    }
    
    private static Result<Theorem> TryEvaluateDeterminedAnd(Term left, Term right) // p /\ q
    {
        return TryEvaluateDeterminedBinary(left, right, MakeConstant(@"/\"), (l, r) => (l, r) switch
        {
            (true, true)   => TrueAndTrue,
            (true, false)  => TrueAndFalse,
            (false, true)  => FalseAndTrue,
            (false, false) => FalseAndFalse
        });
    }
    
    private static Result<Theorem> TryEvaluateDeterminedOr(Term left, Term right) // p \/ q
    {
        return TryEvaluateDeterminedBinary(left, right, MakeConstant(@"\/"), (l, r) => (l, r) switch
        {
            (true, true)   => TrueOrTrue,
            (true, false)  => TrueOrFalse,
            (false, true)  => FalseOrTrue,
            (false, false) => FalseOrFalse
        });
    }
    
    private static Result<Theorem> TryEvaluateDeterminedImplies(Term left, Term right) // p -> q
    {
        return TryEvaluateDeterminedBinary(left, right, MakeConstant("->"), (l, r) => (l, r) switch
        {
            (true, true)   => TrueImpliesTrue,
            (true, false)  => TrueImpliesFalse,
            (false, true)  => FalseImpliesTrue,
            (false, false) => FalseImpliesFalse
        });
    }

    private static Result<Theorem> TryEvaluateDeterminedBinary(Term left, Term right, Term op, Func<bool, bool, Theorem> solutions)
    {
        if (!TryEvaluateDeterminedTruthsAndFalses(left).Deconstruct(out var leftValue, out var error)) // p = ?
            return error;

        if (!TryEvaluateDeterminedTruthsAndFalses(right).Deconstruct(out var rightValue, out error)) // q = ?
            return error;

        var leftEq = Congruence(op, leftValue);
        var fullEq = Congruence(leftEq, rightValue); // (p op q) = (? op ?)

        var toSwitch = BinaryRight(fullEq);
        var (leftEval, rightEval, _) = BinaryDeconstruct(toSwitch);
        
        var t = MakeConstant("T");

        var thmToUse = solutions(leftEval == t, rightEval == t);

        return Transitivity(fullEq, thmToUse);
    }

    public static Result<Theorem> TryCheckTrivialDoubleBools(Term term)
    {
        if (term.TypeOf() != MakeType("fun", new[] { BoolTy, MakeType("fun", new[] { BoolTy, BoolTy }) }))
            return "Term has wrong type";
        
        var t = MakeConstant("T");
        var f = MakeConstant("F");

        var ftt = BinaryRight(EvaluateLambdas(MakeCombination(MakeCombination(term, t), t)));
        var ftf = BinaryRight(EvaluateLambdas(MakeCombination(MakeCombination(term, t), f)));
        var fft = BinaryRight(EvaluateLambdas(MakeCombination(MakeCombination(term, f), t)));
        var fff = BinaryRight(EvaluateLambdas(MakeCombination(MakeCombination(term, f), f)));
        
        if (!TryEvaluateDeterminedTruthsAndFalses(ftt).Deconstruct(out var evalFtt, out var error))
            return error;
        if (!TryModusPonens(Commutativity(evalFtt), Truth).Deconstruct(out var fttTrue, out error))
            return error;
        
        if (!TryEvaluateDeterminedTruthsAndFalses(ftf).Deconstruct(out var evalFtf, out error))
            return error;
        if (!TryModusPonens(Commutativity(evalFtf), Truth).Deconstruct(out var ftfTrue, out error))
            return error;
        
        if (!TryEvaluateDeterminedTruthsAndFalses(fft).Deconstruct(out var evalFft, out error))
            return error;
        if (!TryModusPonens(Commutativity(evalFft), Truth).Deconstruct(out var fftTrue, out error))
            return error;
        
        if (!TryEvaluateDeterminedTruthsAndFalses(fff).Deconstruct(out var evalFff, out error))
            return error;
        if (!TryModusPonens(Commutativity(evalFff), Truth).Deconstruct(out var fffTrue, out error))
            return error;
        
        return TryCasesDoubleEnumeratedBools(fttTrue, ftfTrue, fftTrue, fffTrue, term);
    }

    public static Theorem CheckTrivialDoubleBools(Term term)
    {
        return (Theorem) TryCheckTrivialDoubleBools(term);
    }

    public static Result<Theorem> TryChecktrivialBools(Term term)
    {
        if (term.TypeOf() != MakeType("fun", new[] { BoolTy, BoolTy }))
            return "Term has wrong type";
        
        var t = MakeConstant("T");
        var f = MakeConstant("F");

        var ft = BinaryRight(EvaluateLambdas(MakeCombination(term, t)));
        var ff = BinaryRight(EvaluateLambdas(MakeCombination(term, f)));
        
        if (!TryEvaluateDeterminedTruthsAndFalses(ft).Deconstruct(out var evalFt, out var error))
            return error;
        if (!TryModusPonens(Commutativity(evalFt), Truth).Deconstruct(out var ftTrue, out error))
            return error;
        
        if (!TryEvaluateDeterminedTruthsAndFalses(ff).Deconstruct(out var evalFf, out error))
            return error;
        if (!TryModusPonens(Commutativity(evalFf), Truth).Deconstruct(out var ffTrue, out error))
            return error;
        
        
        return TryCasesEnumeratedBools(ftTrue, ffTrue, term);
    }
    
    public static Theorem CheckTrivialBools(Term term)
    {
        return (Theorem) TryChecktrivialBools(term);
    }

    public static Result<Theorem> TryInvertTheoremAndPremise(Theorem theorem, Term premise) // p |- q to ~p |- ~q
    {
        if (!theorem.Premises().Contains(premise))
            return "Premise is not in theorem";

        var discharged = Discharge(premise, theorem);
        var (left, right, _) = BinaryDeconstruct(discharged);

        switch (TryUnaryDeconstruct(left, "~").IsSuccess(out var leftArg), TryUnaryDeconstruct(right, "~").IsSuccess(out var rightArg))
        {
            case (true, true): // |- ~p -> ~q
            {
                var thm = Specialise(NotPImpliesNotQ, leftArg!, rightArg!); // |- (~p -> ~q) = (q -> p)
                var mp = ModusPonens(thm, discharged); // |- q -> p
                return Undischarge(mp); // q |- p
            }
            case (true, false): // |- ~p -> q
            {
                var thm = Specialise(NotPImpliesQInversion, leftArg!, right); // |- (~p -> q) = (~q -> p)
                var mp = ModusPonens(thm, discharged); // |- ~q -> p
                return Undischarge(mp); // ~q |- p
            }
            case (false, true): // |- p -> ~q
            {
                var thm = Specialise(PImpliesNotQInversion, left, rightArg!); // |- (p -> ~q) = (q -> ~p)
                var mp = ModusPonens(thm, discharged); // |- q -> ~p
                return Undischarge(mp); // q |- ~p
            }
            case (false, false): // |- p -> q
            {
                var thm = Specialise(NotPImpliesNotQ, right, left); // |- (~q -> ~p) = (p -> q)
                var mp = ModusPonens(Commutativity(thm), discharged); // |- ~q -> ~p
                return Undischarge(mp); // ~q |- ~p
            }
        }
    }
    
    public static Theorem InvertTheoremAndPremise(Theorem theorem, Term premise)
    {
        return (Theorem) TryInvertTheoremAndPremise(theorem, premise);
    }

    public static Theorem InvertBothSidesOfEquals(Theorem theorem)
    {
        return (Theorem) TryInvertBothSidesOfEquals(theorem);
    }

    public static Result<Theorem> TryInvertBothSidesOfEquals(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, "=").Deconstruct(out var left, out var right, out var error))
            return error;
        

        switch (TryUnaryDeconstruct(left, "~").IsSuccess(out var leftArg), TryUnaryDeconstruct(right, "~").IsSuccess(out var rightArg))
        {
            case (true, true): // |- ~p = ~q
            {
                var thm = Specialise(NotPEqualsNotQ, leftArg!, rightArg!); // |- (~p = ~q) = (p = q)
                return ModusPonens(thm, theorem); // |- p = q
            }
            case (true, false): // |- ~p = q
            {
                var thm = Specialise(NotPEqualsQInversion, leftArg!, right); // |- (~p = q) = (p = ~q)
                return ModusPonens(thm, theorem); // |- p = ~q
            }
            case (false, true): // |- p = ~q
            {
                var thm = Specialise(NotPEqualsQInversion, left, rightArg!); // |- (~p = q) = (p = ~q)
                return ModusPonens(Commutativity(thm), theorem); // |- ~p = q
            }
            case (false, false): // |- p = q
            {
                var thm = Specialise(NotPEqualsNotQ, left, right); // |- (~p = ~q) = (p = q)
                return ModusPonens(Commutativity(thm), theorem); // |- ~p = ~q
            }
        }
    }

    public static Result<Theorem> TryTrueAndFalseEqual(Theorem ftEqFf, Term f, Term variable) // given |- f T = f F and f, return |- ! x . f x
    {
        if (!variable.TryDeconstructVar().Deconstruct(out var name, out var type, out var error))
            return error;
        
        if (!TryBinaryDeconstruct(ftEqFf, "=").Deconstruct(out var ft, out var ff, out error))
            return error;

        if (type != ft.TypeOf())
            return "Type of variable does not match type of term";
        
        if (MakeType("fun",new []{BoolTy, type}) != f.TypeOf())
            return "fT and fF do not match f";

        var ffEqFf = Reflexivity(ff); // |- f F = f F

        var uniqueTerms = ChangeToUniqueVariables(TrueAndFalseEqualTheorem, UsedNames(f), new Dictionary<string, string>
        {
            ["x"] = name
        }); // f T = k, f F = k |- ! x . f x

        var premise = uniqueTerms.Premises().First();
        var (premFt, premK, _) = BinaryDeconstruct(premise);

        var (kName, kType) = premK.DeconstructVar();
        var (fName, fType) = premFt.DeconstructComb().application.DeconstructVar();

        if (ft.TypeOf() != kType)
        {
            uniqueTerms = InstantiateTypes(new Dictionary<Type, Type>
            {
                [kType] = type
            }, uniqueTerms);
        }

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable(kName, type)] = ff,
            [MakeVariable(fName, f.TypeOf())] = f
        }, uniqueTerms); // f F = f F, f T = f F |- ! x . f x
        
        return TryElimination(inst, ffEqFf, ftEqFf); // |- ! x . f x
    }

    public static Theorem TrueAndFalseEqual(Theorem ftEqFf, Term f, Term variable)
    {
        return (Theorem) TryTrueAndFalseEqual(ftEqFf, f, variable);
    }
}