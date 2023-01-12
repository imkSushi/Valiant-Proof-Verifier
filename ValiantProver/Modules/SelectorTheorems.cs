using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.AndTheorems;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.ExistsTheorems;
using static ValiantProver.Modules.ExistsUniqueTheorems;
using static ValiantProver.Modules.FalseAndNotTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.ImpliesTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.OrTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;
using static ValiantProver.Modules.TruthTheorems;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public class SelectorTheorems
{
    public static void Load() { }

    static SelectorTheorems()
    {
        FalseAndNotTheorems.Load();
        ExistsUniqueTheorems.Load();
        
        DefineConstant("@", MakeType("fun", new []{MakeType("fun", new []{MakeType("a"), BoolTy}), MakeType("a")}));
        TryRegisterPrefixRule("@", "@", 1, "ε");
        SelectorAxiom = NewAxiom(Parse("!p . p x 'a -> p @ p"));

        ExistsTheorem = ConstructExistsTheorem();
        UniqueEqualsSelect = ConstructUniqueEqualsSelect();
        ExcludedMiddleTheorem = ConstructExcludedMiddleTheorem();
        DoubleNotEliminationTheorem = ConstructDoubleNotElimination();
    }
    
    public static Theorem SelectorAxiom { get; } // !p . p x 'a -> p @ p
    public static Theorem ExistsTheorem { get; } // ? p |- p @ p
    public static Theorem UniqueEqualsSelect { get; } // ?! p, p x |- @ p = x
    public static Theorem ExcludedMiddleTheorem { get; } // |- !p . p \/ ~p
    public static Theorem DoubleNotEliminationTheorem { get; } // |- !p . ~~p = p

    private static Theorem ConstructExistsTheorem()
    {
        var p = Parse("p :fun 'a :bool"); // p
        var existsP = Specialise(ExistsDefinition, p); // |- ? p = !q . (!x . p x -> q) -> q
        var mpElim = ModusPonens(existsP, Assume(Parse(@"(?) p :fun 'a :bool"))); // ?p |- !q . (!x . p x -> q) -> q
        var selector = Specialise(mpElim, Parse("p @ p :fun 'a :bool")); // ?p |- (!x . p x -> p @ p) -> p @ p

        var px = Specialise(SelectorAxiom, p); // p x -> p @ p
        var gen = Generalise(px, Parse("x 'a")); // |- !x . p x -> p @ p
        
        return ApplyModusPonens(selector, gen); // ?p |- p @ p
    }
    
    private static Theorem ConstructUniqueEqualsSelect()
    {
        var p = Parse("p :fun 'a :bool"); // p
        var uniqueP = Specialise(ExistsUnqiueDefinition, p); // |- ?! p = ? p /\ ! x y . (p x /\ p y) -> x = y
        var mpElim = ModusPonens(uniqueP, Assume(Parse(@"(?!) p :fun 'a :bool"))); // ?!p |- ? p /\ ! x y . (p x /\ p y) -> x = y
        var exists = DeconjugateLeft(mpElim); // ?!p |- ? p
        var pSelectP = Elimination(ExistsTheorem, exists); // ?!p |- p @ p
        var right = DeconjugateRight(mpElim); // ?!p |- ! x y . (p x /\ p y) -> x = y
        var equality = Specialise(right, new []{Parse("x 'a"), Parse("@ p")}); // ?!p |- p x /\ p @ p -> x = @ p
        var pxAndPSelectP = Conjugate(Assume(Parse("p :fun 'a :bool x")), pSelectP); // ?!p, p x |- p x /\ p @ p
        var impliesMp = ApplyModusPonens(equality, pxAndPSelectP); // ?!p, p x |- x = @ p
        return Commutativity(impliesMp); // ?!p, p x |- @ p = x
    }

    private static Theorem ConstructExcludedMiddleTheorem() // |- p \/ ~p
    {
        var p = Parse("p :bool"); // p
        var f = Parse(@"\x . (p /\ x) \/ ~x"); // f
        var g = Parse(@"\x . (p /\ ~x) \/ x"); // g
        
        AddTypedTermMacro("f", f); // set f = \x . (p /\ x) \/ ~x
        AddTypedTermMacro("g", g); // set g = \x . (p /\ ~x) \/ x

        var boolSelect = Parse(@"@ :fun :fun :bool :bool :bool"); // @
        var sf = Parse("@f"); // @f
        var sg = Parse("@g"); // @g
        var pAndSf = Parse(@"p /\ @f"); // p /\ @f
        var notSf = Parse("~@f"); // ~@f
        var fEqG = Parse("f = g"); // f = g
        var notP = Parse("~p"); // ~p
        var x = MakeVariable("x", BoolTy); // x
        var fx = Parse("f x"); // f x
        var gx = Parse("g x"); // g x
        var notX = Parse("~x"); // ~x
        var notSg = Parse("~@g"); // ~@g
        var pAndNotSg = Parse(@"p /\ ~@g"); // p /\ ~@g
        var pAndX = Parse(@"p /\ x");
        var pAndNotX = Parse(@"p /\ ~x"); // p /\ ~x
        
        RemoveMacro("f"); // remove f
        RemoveMacro("g"); // remove g
        
        var fFalse = EvaluateLambdas(MakeCombination(f, MakeConstant("F"))); // |- f F = (p /\ F) \/ ~F
        var notFalse = ModusPonens(Commutativity(NotFalse), Truth); // |- ~F
        var fFalseTrue = Disjunct(Parse(@"p /\ F"), notFalse); // |- (p /\ F) \/ ~F
        var fF = ModusPonens(Commutativity(fFalse), fFalseTrue); // |- f F

        var fsf = SelectorFromExample(fF, f); // |- f @ f
        var fsfEval = EvaluateLambdas(fsf); // |- (p /\ @f) \/ ~@f
        
        var gTrue = EvaluateLambdas(MakeCombination(g, MakeConstant("T"))); // |- g T = (p /\ ~T) \/ T
        var gTrueTrue = Disjunct(Parse(@"p /\ ~T"), Truth); // |- (p /\ ~T) \/ T
        var gT = ModusPonens(Commutativity(gTrue), gTrueTrue); // |- g T
        
        var gsg = SelectorFromExample(gT, g); // |- g @ g
        var gsgEval = EvaluateLambdas(gsg); // |- (p /\ ~@g) \/ @g

        var assumePAndSf = Assume(pAndSf); // p /\ @f |- p /\ @f
        var pAndSfImpliesP = DeconjugateLeft(assumePAndSf); // p /\ @f |- p
        var pAndSfImpliesThm = Disjunct(pAndSfImpliesP, notP); // p /\ @f |- p \/ ~p

        var assumeNotSf = Assume(notSf); // ~@f |- ~@f
        
        var assumePAndNotSg = Assume(pAndNotSg); // p /\ ~@g |- p /\ ~@g
        var pAndNotSgImpliesP = DeconjugateLeft(assumePAndNotSg); // p /\ ~@g |- p
        var pAndNotSgImpliesThm = Disjunct(pAndNotSgImpliesP, notP); // p /\ ~@g |- p \/ ~p
        
        var assumeSg = Assume(sg); // @g |- @g
        
        var assumeFEqG = Assume(fEqG); // f = g |- f = g
        var sfEqSg = Congruence(boolSelect, assumeFEqG); // f = g |- @f = @g
        var sFTrue = ModusPonens(Commutativity(sfEqSg), assumeSg); // @g, f = g |- @f
        var sfEqNotSf = AntiSymmetry(sFTrue, assumeNotSf); // ~@f, @g, f = g |- @f = ~@f
        var fEqGImpContra = ContradictionFromPEqNotP(sfEqNotSf); // ~@f, @g, f = g |- F
        var notFEqG = Contradiction(fEqGImpContra, fEqG); // ~@f, @g |- ~(f = g)

        var assumeP = Assume(p); // p |- p

        var assumeFx = Assume(fx); // f x |- f x
        var assumeFxEval = EvaluateLambdas(assumeFx); // f x |- (p /\ x) \/ ~x

        var assumeNotX = Assume(notX); // ~x |- ~x
        var notXImpliesPAndNotX = Conjugate(assumeP, assumeNotX); // p, ~x |- p /\ ~x
        var notXImpliesGxFunc = Disjunct(notXImpliesPAndNotX, x); // p, ~x |- (p /\ ~x) \/ x
        var gXEval = EvaluateLambdas(gx); // |- g x = (p /\ ~x) \/ x
        var notXImpliesGx = ModusPonens(Commutativity(gXEval), notXImpliesGxFunc); // p, ~x |- g x
        var notXImpliesGxEval = EvaluateLambdas(notXImpliesGx);

        var assumePAndX = Assume(pAndX); // p /\ x |- p /\ x
        var pAndXImpliesX = DeconjugateRight(assumePAndX); // p /\ x |- x
        var pAndXImpliesGxFunc = Disjunct(pAndNotX, pAndXImpliesX); // p /\ x |- (p /\ ~x) \/ x
        var pAndXImpliesGx = ModusPonens(Commutativity(gXEval), pAndXImpliesGxFunc); // p /\ x |- g x
        var pAndXImpliesGxEval = EvaluateLambdas(pAndXImpliesGx);
        
        var fxImpliesGx = DisjunctCases(assumeFxEval, pAndXImpliesGxEval, notXImpliesGxEval); // p, f x |- g x
        
        var assumeGx = Assume(gx); // g x |- g x
        var assumeGxEval = EvaluateLambdas(assumeGx); // g x |- (p /\ ~x) \/ x
        
        var assumePAndNotX = Assume(pAndNotX); // p /\ ~x |- p /\ ~x
        var pAndNotXImpliesNotX = DeconjugateRight(assumePAndNotX); // p /\ ~x |- ~x
        var pAndNotXImpliesFxFunc = Disjunct(pAndX, pAndNotXImpliesNotX); // p /\ ~x |- (p /\ x) \/ ~x
        var fxEval = EvaluateLambdas(fx); // |- f x = (p /\ x) \/ ~x
        var pAndNotXImpliesFx = ModusPonens(Commutativity(fxEval), pAndNotXImpliesFxFunc); // p /\ ~x |- f x
        var pAndNotXImpliesFxEval = EvaluateLambdas(pAndNotXImpliesFx);
        
        var assumeX = Assume(x); // x |- x
        var xImpliesPAndX = Conjugate(assumeP, assumeX); // p, x |- p /\ x
        var xImpliesFxFunc = Disjunct(xImpliesPAndX, notX); // p, x |- (p /\ x) \/ ~x
        var xImpliesFx = ModusPonens(Commutativity(fxEval), xImpliesFxFunc); // p, x |- f x
        var xImpliesFxEval = EvaluateLambdas(xImpliesFx);
        
        var gxImpliesFx = DisjunctCases(assumeGxEval, pAndNotXImpliesFxEval, xImpliesFxEval); // p, g x |- f x

        var fxEqGx = AntiSymmetry(IncreaseBeta(gxImpliesFx, x), IncreaseBeta(fxImpliesGx, x)); // p |- f x = g x
        var generalFxEqGx = Generalise(fxEqGx, x); // p |- !x . f x = g x
        var pImpFEqG = AllApplicationsImpliesEquality(generalFxEqGx); // p |- f = g
        var pAndSImpContradiction = ContradictionFromPEqNotP(AntiSymmetry(pImpFEqG, notFEqG)); // ~@f, @g, p |- F
        var notSfAndSgImpNotP = Contradiction(pAndSImpContradiction, p); // ~@f, @g |- ~p
        var notSfAndSgImpThm = Disjunct(p, notSfAndSgImpNotP); // ~@f, @g |- p \/ ~p
        
        var notSfImpThm = DisjunctCases(gsgEval, pAndNotSgImpliesThm, notSfAndSgImpThm); // ~@f |- p \/ ~p
        
        var pOrNotP = DisjunctCases(fsfEval, pAndSfImpliesThm, notSfImpThm); // |- p \/ ~p

        return Generalise(pOrNotP, p);
    }

    private static Theorem ConstructDoubleNotElimination() // |- ~~p = p
    {
        var p = MakeVariable("p", BoolTy);

        var assumeP = Assume(p); // p |- p
        var pEqTrue = AntiSymmetry(assumeP, Truth); // p |- p = T
        var notPEqNotTrue = Congruence(MakeConstant("~"), pEqTrue); // p |- ~p = ~T
        var notPEqFalse = Transitivity(notPEqNotTrue, NotTrue); // p |- ~p = F
        var notNotPEqNotFalse = Congruence(MakeConstant("~"), notPEqFalse); // p |- ~~p = ~F
        var notNotPEqTrue = Transitivity(notNotPEqNotFalse, NotFalse); // p |- ~~p = T
        var pImpThm = Transitivity(notNotPEqTrue, Commutativity(pEqTrue)); // p |- ~~p = p
        
        var assumeNotP = Assume(Parse("~p")); // ~p |- ~p
        var pEqFalse = ModusPonens(NotEqualsFalseTheorem, assumeNotP); // ~p |- p = F
        var notPEqNotFalse = Congruence(MakeConstant("~"), pEqFalse); // ~p |- ~p = ~F
        var notPEqTrue = Transitivity(notPEqNotFalse, NotFalse); // ~p |- ~p = T
        var notNotPEqNotTrue = Congruence(MakeConstant("~"), notPEqTrue); // ~p |- ~~p = ~T
        var notNotPEqFalse = Transitivity(notNotPEqNotTrue, NotTrue); // ~p |- ~~p = F
        var pImpNotThm = Transitivity(notNotPEqFalse, Commutativity(pEqFalse)); // ~p |- ~~p = ~p
        
        var elimination = CasesProof(pImpThm, pImpNotThm, p);

        return Generalise(elimination, p);
    }

    public static Theorem CasesProof(Theorem left, Theorem right, Term premise)
    {
        return (Theorem) TryCasesProof(left, right, premise);
    }

    public static Result<Theorem> TryCasesProof(Theorem left, Theorem right, Term premise) // p |- t and ~p |- t then |- t
    {
        if (premise.TypeOf() != BoolTy)
            return "Premise is not a boolean expression";
        
        if (left.Conclusion() != right.Conclusion())
            return "Left and right theorems do not have the same conclusion";
        
        var notPremise = ApplyUnaryFunction("~", premise);

        var hasPremise = left; // p |- t
        var hasNotPremise = right; // ~p |- t

        if (!left.Premises().Contains(premise) || !right.Premises().Contains(notPremise))
        {
            if (!left.Premises().Contains(notPremise) || !right.Premises().Contains(premise))
                return "Premise is not a premise of either theorem";
            hasPremise = right;
            hasNotPremise = left;
        }
        
        var premiseOrNotPremise = Specialise(ExcludedMiddleTheorem, premise); // |- p \/ ~p
        
        return DisjunctCases(premiseOrNotPremise, hasPremise, hasNotPremise);
    }
    
    public static Result<Theorem> TrySelectorFromExample(Theorem example, Term function)
    {
        if (!example.Conclusion().TryDeconstructComb().Deconstruct(out var application, out var argument, out _) || application != function)
            return "Theorem must be an application of the function";

        var specify = Specialise(SelectorAxiom, Parse("p :fun 'a :bool")); // |- p x -> p @ p
        var type = argument.TypeOf();

        var typed = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = type
        }, specify); // |- p x -> p @ p

        var ax = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", MakeType("fun", new[] { type, BoolTy }))] = application,
            [MakeVariable("x", type)] = argument
        }, typed); // |- p x -> p @ p
        
        return ApplyModusPonens(ax, example);
    }

    public static Theorem SelectorFromExample(Theorem example, Term function)
    {
        return (Theorem) TrySelectorFromExample(example, function);
    }

    public static Result<Theorem> TryDoubleNotElimination(Theorem theorem)
    {
        if (!TryUnaryDeconstruct(theorem, "~").Deconstruct(out var notArg, out var error))
            return error;

        if (!TryUnaryDeconstruct(notArg, "~").Deconstruct(out var arg, out error))
            return error;
        
        var specialised = Specialise(DoubleNotEliminationTheorem, arg); // ~~p = p

        return ModusPonens(specialised, theorem);
    }
    
    public static Theorem DoubleNotElimination(Theorem theorem)
    {
        return (Theorem) TryDoubleNotElimination(theorem);
    }

    public static Result<Theorem> TryGetElementThatSatisfiesExistingFunction(Theorem theorem) // ?p
    {
        if (!TryUnaryDeconstruct(theorem.Conclusion(), "?").Deconstruct(out var function, out var error))
            return error;

        var thm = ExistsTheorem; // ?p |- p @ p

        var fnType = function.TypeOf().DeconstructFun().from;

        if (fnType != MakeType("a"))
        {
            thm = InstantiateTypes(new Dictionary<Type, Type>
            {
                [MakeType("a")] = fnType
            }, thm);
        }
        
        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable("p", function.TypeOf())] = function
        }, thm); // ?p |- p @ p
        
        return Elimination(inst, theorem); // p @ p
    }

    public static Theorem GetElementThatSatisfiesExistingFunction(Theorem theorem)
    {
        return (Theorem) TryGetElementThatSatisfiesExistingFunction(theorem);
    }
}