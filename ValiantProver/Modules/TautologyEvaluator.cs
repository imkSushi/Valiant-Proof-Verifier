using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.FalseAndNotTheorems;
using static ValiantProver.Modules.ForAllTheorems;
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
        PImpliesNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (p -> ~q) = ~(p /\ q)"));
        NotPImpliesNotQ = CheckTrivialDoubleBools(Parse(@"\ p q . (~p -> ~q) = (q -> p)"));
    }
    
    public static Theorem EnumeratedBoolTheorem { get; } // f T, f F |- !x . f x
    public static Theorem DoubleEnumeratedBoolTheorem { get; } // f T T, f T F, f F T, f F F |- !x y . f x y
    
    public static Theorem TrueEqualsP { get; } // |- ! p . (T = p) = p
    public static Theorem PEqualsTrue { get; } // |- ! p . (p = T) = p
    public static Theorem FalseEqualsP { get; } // |- ! p . (F = p) = ! p
    public static Theorem FalseEqualsNotP { get; } // |- ! p . (F = ! p) = p
    public static Theorem PEqualsFalse { get; } // |- ! p . (p = F) = ! p
    public static Theorem NotPEqualsFalse { get; } // |- ! p . (! p = F) = p
    public static Theorem NotPEqualsNotQ { get; } // |- ! p q . (~p = ~q) = (p = q)
    public static Theorem NotPEqualsQ { get; } // |- ! p q . (~p = q) = ~(p = q)
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
    public static Theorem PImpliesNotQ { get; } // |- ! p q . (p -> ~q) = ~(p /\ q)
    public static Theorem NotPImpliesNotQ { get; } // |- ! p q . (~p -> ~q) = (q -> p)

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
        return TryCasesDoubleEnumeratedBools(ftt, ftf, fft, fff, f).ValueOrException();
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

        var frees = term.FreesIn().Where(t => t.DeconstructVar().type == BoolTy).ToList();

        return SimplifyTruthsAndFalses(term);
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
                /*"!" => Transitivity(congruence, SimplifyForall(arg)),
                "?" => Transitivity(congruence, SimplifyExists(arg)),*/
                _   => congruence
            };
        }

        if (left != t && left != f && right != t && right != f)
            return congruence;

        if (!op.TryDeconstructConst().Deconstruct(out var name, out _, out _))
            return congruence;

        return name switch
        {
            "="   => Transitivity(congruence, SimplifyEquals(left, right)),
            @"/\" => Transitivity(congruence, SimplifyAnd(left, right)),
            @"\/" => Transitivity(congruence, SimplifyOr(left, right)),
            "->"  => Transitivity(congruence, SimplifyImplies(left, right)),
            _     => congruence
        };
    }

    private static Theorem SimplifyNot(Term term)
    {
        var t = MakeConstant("T");
        var f = MakeConstant("F");
        
        if (term == t)
            return NotTrue;

        if (term == f)
            return NotFalse;
        
        if (!TryUnaryDeconstruct(term, "~").Deconstruct(out var notArg, out _))
            return Reflexivity(term);
        
        return Specialise(DoubleNotEliminationTheorem, notArg);
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

    public static Theorem EvaluateDeterminedTruthsAndFalses(Term term)
    {
        return TryEvaluateDeterminedTruthsAndFalses(term).ValueOrException();
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
        return TryCheckTrivialDoubleBools(term).ValueOrException();
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
        return TryChecktrivialBools(term).ValueOrException();
    }
}