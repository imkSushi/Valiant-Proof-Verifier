using ValiantBasics;
using ValiantParser;
using ValiantProofVerifier;

namespace ValiantProver;

public sealed class UtilityTheorems
{
    public PrattParser Parser { get; }
    
    public UtilityTheorems(Kernel kernel, Utility utility, PrattParser parser)
    {
        Kernel = kernel;
        Utility = utility;
        Parser = parser;
        parser.TryRegisterInfixRule("=", "=", 0);
        Commutativity = ConstructCommutativity();
        TruthDefinition = Kernel.NewBasicDefinition(Parser.ParseTerm(@"T = ((\ a: bool . a) = (\ a: bool . a))"));
        Parser.TryRegisterInfixRule(@"/\", @"/\", 30);
        AndDefinition = Kernel.NewBasicDefinition(Parser.ParseTerm(@"""/\"" = \ p q . ((\f:fun :bool :fun :bool :bool . f p q) = (\ f. f T T))"));
        Truth = ConstructTruth();
        BetaIncrease = ConstructBetaIncrease();
        BetaReduction = ConstructBetaReduction();
        AbstractionAssociativity = ConstructAbstractionAssociativity();
        And = ConstructAnd();
        AndLeft = ConstructAndLeft();
        AndRight = ConstructAndRight();
    }

    private Theorem ConstructAbstractionAssociativity()
    {
        var p = Parser.ParseTerm("p 'a");
        var fpLambdaEqFp = Kernel.BetaReduction(Parser.ParseTerm(@"(\ x . f :fun 'a :fun 'b 'c p) x"));
        var fLambdaEqF = Kernel.BetaReduction(Parser.ParseTerm(@"(\ x . f :fun 'a :fun 'b 'c) x"));
        var fLambdaPEqFp = Kernel.Congruence(fLambdaEqF, Kernel.Reflexivity(p));
        var commuted = ApplyCommutativity(fLambdaPEqFp);
        return Kernel.Transitivity(fpLambdaEqFp, commuted);
    }

    private Theorem ConstructBetaReduction()
    {
        var beta = Kernel.BetaReduction(Parser.ParseTerm(@"(\ x . t :bool) x"));
        var assumed = Kernel.Assume(Parser.ParseTerm(@"(\ x . t :bool) x"));
        return Kernel.ModusPonens(beta, assumed);
    }

    private Theorem ConstructBetaIncrease()
    {
        var beta = Kernel.BetaReduction(Parser.ParseTerm(@"(\ x 'b . t :bool) x 'b"));
        var assumed = Kernel.Assume(Parser.ParseTerm(@"t :bool"));
        var commuted = ApplyCommutativity(beta);
        return Kernel.ModusPonens(commuted, assumed);
    }

    private Theorem IncreaseBeta(Term[] variables, Theorem theorem)
    {
        var body = Kernel.DeconstructTheorem(theorem).conclusion;
        foreach (var variable in variables)
        {
            body = Kernel.MakeCombination(Kernel.MakeAbstraction(variable, body), variable);
        }
        /*var betaThm = Kernel.BetaReduction(beta);
        var commute = ApplyCommutativity(betaThm);
        return Kernel.ModusPonens(commute, theorem);*/
        
        throw new NotImplementedException();
    }

    private Theorem ConstructAnd()
    {
        //want p, q |- p /\ q
        var f = Parser.ParseTerm("f :fun :bool :fun :bool :bool");
        var p = Parser.ParseTerm("p :bool");
        var q = Parser.ParseTerm("q :bool");
        var pImpP = Kernel.Assume(p);
        var pEqP = Kernel.Reflexivity(p);
        var qImpQ = Kernel.Assume(q);
        var qEqQ = Kernel.Reflexivity(q);
        var pEqT = Kernel.AntiSymmetry(pImpP, Truth);
        var qEqT = Kernel.AntiSymmetry(qImpQ, Truth);
        var fpEqFt = CongruenceTerms(f, pEqT);
        var fpqEqFtt = Kernel.Congruence(fpEqFt, qEqT); 
        var abstraction = Kernel.Abstraction(f, fpqEqFtt);
        /*var lambdaAbstraction = IncreaseBeta(q, abstraction);
        var lambdaAbstraction2 = IncreaseBeta(p, lambdaAbstraction);*/

        // /\ = \ p q . ((\f:fun :bool :fun :bool :bool . f p q) = (\ f. f T T))
        var pand = Kernel.Congruence(AndDefinition, qEqQ); // /\ p = (\ p q . ((\f:fun :bool :fun :bool :bool . f p q) = (\ f. f T T))) p
        var pandq = Kernel.Congruence(pand, pEqP); // /\ p q = (\ p q . ((\f:fun :bool :fun :bool :bool . f p q) = (\ f. f T T))) p q
        var commutative = ApplyCommutativity(pandq);
        //return Kernel.ModusPonens(commutative, lambdaAbstraction2);
        
        throw new NotImplementedException();
    }

    private Theorem ConstructAndRight()
    {
        //want p /\ q |- q
        throw new NotImplementedException();
    }

    private Theorem ConstructAndLeft()
    {
        //want p /\ q |- p
        throw new NotImplementedException();
    }

    public Kernel Kernel { get; }
    public Utility Utility { get; }
    public Theorem Commutativity { get; }
    public Theorem TruthDefinition { get; }
    public Theorem AndDefinition { get; }
    public Theorem AndLeft { get; }
    public Theorem AndRight { get; }
    public Theorem And { get; }
    public Theorem Truth { get; }
    public Theorem BetaIncrease { get; }
    public Theorem BetaReduction { get; }
    public Theorem AbstractionAssociativity { get; }

    private Theorem ConstructTruth()
    {
        var a = Parser.ParseTerm(@"\a: bool . a");
        var equality = Kernel.Reflexivity(a);
        var commutativity = ApplyCommutativity(TruthDefinition);
        return Kernel.ModusPonens(commutativity, equality);
    }

    public Theorem CongruenceTerms(Term application, Theorem argumentEquality)
    {
        var applicationEquality = Kernel.Reflexivity(application);
        return Kernel.Congruence(applicationEquality, argumentEquality);
    }

    private Theorem ConstructCommutativity()
    {
        var pEqQ = Kernel.Assume(Parser.ParseTerm("p 'a = q"));

        var pEqP = Kernel.Reflexivity(Parser.ParseTerm("p 'a"));

        var eq = Parser.ParseTerm("\"=\" :fun 'a :fun 'a :bool");

        var pxEqQx = CongruenceTerms(eq, pEqQ);
        var ppEqQp = Kernel.Congruence(pxEqQx, pEqP);
        
        return Kernel.ModusPonens(ppEqQp, pEqP);
    }

    public Theorem ApplyCommutativity(Theorem theorem)
    {
        if (!Kernel.TryDeconstructEquality(Kernel.DeconstructTheorem(theorem).conclusion, out var p, out var q))
            throw new TheoremException("Theorem is not an equality");

        var typedCommutativity = Kernel.InstantiateTypes(new Dictionary<Type, Type>
        {
            [Kernel.MakeType("a")] = Kernel.TypeOf(p)
        }, Commutativity);
        
        var commutativity = Kernel.InstantiateVariables(new Dictionary<Term, Term>
        {
            [Kernel.MakeVariable("p", Kernel.TypeOf(p))] = p,
            [Kernel.MakeVariable("q", Kernel.TypeOf(q))] = q
        }, typedCommutativity);
        
        return Elimination(theorem, commutativity);
    }

    public Theorem CommutativityEquality(Term term)
    {
        var assumption = Kernel.Assume(term);
        var commutativity = ApplyCommutativity(assumption);
        var oppositeAssumption = Kernel.Assume(Kernel.DeconstructTheorem(commutativity).conclusion);
        var oppositeCommutativity = ApplyCommutativity(oppositeAssumption);
        return Kernel.AntiSymmetry(oppositeCommutativity, commutativity);
    }

    public Theorem Elimination(Theorem toEliminate, Theorem theorem)
    {
        var equality = Kernel.AntiSymmetry(toEliminate, theorem);
        return Kernel.ModusPonens(equality, toEliminate);
    }

    public Theorem Eliminate(Theorem theorem)
    {
        var conclusion = Kernel.DeconstructTheorem(theorem).conclusion;
        var (left, _) = Kernel.DeconstructComb(conclusion);

        var assumption = Kernel.Assume(left);
        return Kernel.ModusPonens(theorem, assumption);
    }
    
    public Theorem EvaluateLambdas(Term term)
    {
        var currentTerm = EqualityLeft(EvaluateLambdasIteration(term));
        var output = EvaluateLambdasIteration(currentTerm);
        var newTerm = EqualityLeft(output);

        while (currentTerm != newTerm)
        {
            currentTerm = newTerm;
            output = EvaluateLambdasIteration(currentTerm);
            newTerm = EqualityLeft(output);
        }
        
        return output;
    }
    
    private Theorem EvaluateLambdasIteration(Term term)
    {
        if (Kernel.IsVar(term) || Kernel.IsConst(term))
            return Kernel.Reflexivity(term);
        if (Kernel.IsAbs(term))
        {
            var (parameter, abstraction) = Kernel.DeconstructAbs(term);
            var evaluatedAbstraction = EvaluateLambdas(abstraction);
            return Kernel.Abstraction(parameter, evaluatedAbstraction);
        }
        
        var (left, right) = Kernel.DeconstructComb(term);
        var evalApp = EvaluateLambdas(left);
        var evalArg = EvaluateLambdas(right);
        var (leftApp, rightApp) = DeconstuctEquality(evalApp);
        var (leftArg, rightArg) = DeconstuctEquality(evalArg);
        
        if (!Kernel.IsAbs(rightApp))
            return Kernel.Congruence(evalApp, evalArg);
        
        var (param, abs) = Kernel.DeconstructAbs(rightApp);
        var substitution = Kernel.InstantiateVariables(new Dictionary<Term, Term>
        {
            [param] = rightArg
        }, abs);
        throw new NotImplementedException();
    }

    private (Term left, Term right) DeconstuctEquality(Term term)
    {
        var (left, rightEquality) = Kernel.DeconstructComb(term);
        var (right, _) = Kernel.DeconstructComb(rightEquality);
        return (left, right);
    }

    private (Term left, Term right) DeconstuctEquality(Theorem thm)
    {
        return DeconstuctEquality(Kernel.DeconstructTheorem(thm).conclusion);
    }
    
    private Term EqualityLeft(Term term)
    {
        var (left, _) = Kernel.DeconstructComb(term);
        return left;
    }
    
    private Term EqualityRight(Term term)
    {
        var (_, rightEq) = Kernel.DeconstructComb(term);
        var (right, _) = Kernel.DeconstructComb(rightEq);
        return right;
    }
    
    private Term EqualityLeft(Theorem thm)
    {
        return EqualityLeft(Kernel.DeconstructTheorem(thm).conclusion);
    }
    
    private Term EqualityRight(Theorem thm)
    {
        return EqualityRight(Kernel.DeconstructTheorem(thm).conclusion);
    }

    public Theorem LambdaEquivalence(Term left, Term right)
    {
        throw new NotImplementedException();
        /* (\x . f) p q = (\y . f q) p
         * (\x . f) p   &  \y . f q
         *  \x . f      &       f q
         *       f      &       f
         */
    }
}