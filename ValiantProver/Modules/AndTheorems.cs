using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TruthTheorems;

namespace ValiantProver.Modules;

public static class AndTheorems
{
    public static void Load() { }

    static AndTheorems()
    {
        LambdaEvaluator.Load();
        TruthTheorems.Load();
        
        AndDefinition = NewBasicDefinition(Parse(@"""/\"" = \ p q . ((\f:fun :bool :fun :bool :bool . f p q) = (\ f. f T T))"));
        TryRegisterInfixRule(@"/\", @"/\", 30, true, "∧");
        
        And = ConstructAnd();
        AndLeft = ConstructAndLeft();
        AndRight = ConstructAndRight();
    }
    
    public static Theorem AndDefinition { get; }
    public static Theorem AndLeft { get; }
    public static Theorem AndRight { get; }
    public static Theorem And { get; }

    private static Theorem ConstructAnd()
    {
        //want p, q |- p /\ q
        var f = Parse("f :fun :bool :fun :bool :bool");
        var p = Parse("p :bool");
        var q = Parse("q :bool");
        var pImpP = Assume(p); // p |- p
        var pEqP = Reflexivity(p); // p = p
        var qImpQ = Assume(q); // q |- q
        var qEqQ = Reflexivity(q); // q = q
        var pEqT = AntiSymmetry(pImpP, Truth); // p |- p = T
        var qEqT = AntiSymmetry(qImpQ, Truth); // q |- q = T
        var fpEqFt = Congruence(f, pEqT); // p |- f p = f T
        var fpqEqFtt = Congruence(fpEqFt, qEqT); // p, q |- f p q = f T T 
        var abstraction = Abstraction(f, fpqEqFtt); // p, q |- (\ f . f p q) = (\ f . f T T)
        var lambdaAbstraction = IncreaseBeta(abstraction, p); // p, q |- \ q . (\ f . f p q) = (\ f . f T T)
        var lambdaAbstraction2 = IncreaseBeta(lambdaAbstraction, q); // p, q |- \ p . \ q . (\ f . f p q) = (\ f . f T T)

        // /\ = \ p q . ((\f . f p q) = (\ f. f T T))
        var pand = Congruence(AndDefinition, pEqP); // /\ p = (\ p q . ((\f . f p q) = (\ f. f T T))) p
        var pandq = Congruence(pand, qEqQ); // /\ p q = (\ p q . ((\f . f p q) = (\ f. f T T))) p q
        var commutative = Commutativity(pandq);
        var leftTerm = lambdaAbstraction2.Conclusion();
        var rightTerm = BinaryLeft(commutative);
        var eqiv = LambdaEquivalence(leftTerm, rightTerm);
        var elimination = ModusPonens(eqiv, lambdaAbstraction2);
        return ModusPonens(commutative, elimination);
    }

    private static Theorem BaseAndConstruction()
    {
        
        //AndDefinition: /\ = \ p q . (\f . f p q) = (\f . f T T)
        var assumption = Assume(Parse(@"p /\ q")); // p /\ q |- p /\ q
        var pApp = Congruence(AndDefinition, Parse("p :bool"));
        var applied = Congruence(pApp, Parse("q :bool")); // p /\ q = (\f . f p q) = (\f . f T T)
        var appliedEliminated = ModusPonens(applied, assumption);
        var rightSimp = EvaluateLambdas(appliedEliminated.Conclusion());
        return ModusPonens(rightSimp, appliedEliminated); // p /\ q |- (\f . f p q) = (\f . f T T)
    }

    private static Theorem ConstructAndRight()
    {
        //want p /\ q |- q
        var baseConstruction = BaseAndConstruction(); // p /\ q |- (\f . f p q) = (\f . f T T)
        var combinated = Congruence(baseConstruction, Parse(@"\ p :bool q :bool . q")); // p /\ q |- (\f . f p q) (\p q . q) = (\f . f T T) (\p q . q)
        var simplified = EvaluateLambdas(combinated); // p /\ q |- q = T
        var commuted = Commutativity(simplified); // p /\ q |- T = q
        return ModusPonens(commuted, Truth);
    }

    private static Theorem ConstructAndLeft()
    {
        //want p /\ q |- p
        var baseConstruction = BaseAndConstruction(); // p /\ q |- (\f . f p q) = (\f . f T T)
        var combinated = Congruence(baseConstruction, Parse(@"\ p :bool q :bool . p")); // p /\ q |- (\f . f p q) (\p q . p) = (\f . f T T) (\p q . p)
        var simplified = EvaluateLambdas(combinated); // p /\ q |- p = T
        var commuted = Commutativity(simplified); // p /\ q |- T = p
        return ModusPonens(commuted, Truth);
    }

    public static Theorem Conjugate(Theorem left, Theorem right)
    {
        var and = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = left.Deconstruct().conclusion,
            [Parse("q :bool")] = right.Deconstruct().conclusion
        }, And);

        return Elimination(and, left, right);
    }

    public static (Theorem left, Theorem right) Deconjugate(Theorem theorem)
    {
        return (DeconjugateLeft(theorem), DeconjugateRight(theorem));
    }

    public static Result<Theorem, Theorem> TryDeconjugate(Theorem theorem)
    {
        return (TryDeconjugateLeft(theorem), TryDeconjugateRight(theorem));
    }

    public static Theorem DeconjugateLeft(Theorem theorem)
    {
        return TryDeconjugateLeft(theorem).ValueOrException();
    }

    public static Result<Theorem> TryDeconjugateLeft(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, @"/\").Deconstruct(out var left, out var right, out _))
            return "Expected theorem to be an 'and' operation";

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = left,
            [Parse("q :bool")] = right
        }, AndLeft);
        
        return Elimination(inst, theorem);
    }

    public static Theorem DeconjugateRight(Theorem theorem)
    {
        return TryDeconjugateRight(theorem).ValueOrException();
    }
    
    public static Result<Theorem> TryDeconjugateRight(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, @"/\").Deconstruct(out var left, out var right, out _))
            return "Expected theorem to be an 'and' operation";

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = left,
            [Parse("q :bool")] = right
        }, AndRight);
        
        return Elimination(inst, theorem);
    }
}