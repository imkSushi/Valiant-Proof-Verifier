using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.EtaReductionTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;
using static ValiantProver.Modules.TypeUtilities;

namespace ValiantProver.Modules;

public static class LambdaEvaluator
{
    public static void Load() { }

    static LambdaEvaluator()
    {
        EtaReductionTheorems.Load();
    }
    
    public static Theorem EvaluateLambdas(Term term)
    {
        var thm = Reflexivity(term);

        while (RequiresAnotherLambdaIteration(term))
        {
            var newThm = EvaluateLambdasIteration(term);
            thm = ApplyTransitivity(thm, newThm);
            term = BinaryRight(thm);
        }
        
        return thm;
    }

    public static Theorem EvaluateLambdas(Theorem theorem)
    {
        var equality = EvaluateLambdas(DeconstructTheorem(theorem).conclusion);
        
        return ModusPonens(equality, theorem);
    }
    
    public static bool RequiresAnotherLambdaIteration(Term term)
    {
        switch (TypeOfEnum(term))
        {
            case TermType.Var:
                return false;
            case TermType.Const:
                return false;
            case TermType.Abs:
            {
                var (param, abs) = DeconstructAbs(term);
                switch (TypeOfEnum(abs))
                {
                    case TermType.Var:
                        return false;
                    case TermType.Const:
                        return false;
                    case TermType.Abs:
                        return RequiresAnotherLambdaIteration(abs);
                    case TermType.Comb:
                    {
                        if (RequiresAnotherLambdaIteration(abs))
                            return true;
                        var (app, arg) = DeconstructComb(abs);
                        if (arg == param)
                            return true;

                        return false;
                    }
                    default:
                        throw new ArgumentOutOfRangeException();
                }
            }
            case TermType.Comb:
            {
                var (app, arg) = DeconstructComb(term);

                if (IsAbs(app) || RequiresAnotherLambdaIteration(app) || RequiresAnotherLambdaIteration(arg))
                    return true;
                
                return false;
            }
            default:
                throw new ArgumentOutOfRangeException();
        }
    }
    
    private static Theorem EvaluateLambdasIteration(Term term)
    {
        if (IsVar(term) || IsConst(term))
            return Reflexivity(term);
        if (IsAbs(term))
        {
            var (parameter, abstraction) = DeconstructAbs(term);
            var evaluatedAbstraction = EvaluateLambdas(abstraction);
            
            var evalAbsRight = BinaryRight(evaluatedAbstraction);

            var output = Abstraction(parameter, evaluatedAbstraction);

            if (!IsComb(evalAbsRight) || DeconstructComb(evalAbsRight).argument != parameter)
                return Abstraction(parameter, evaluatedAbstraction);
            
            var etaReduction = ApplyEtaReduction(BinaryRight(output));
            return ApplyTransitivity(output, etaReduction);
        }
        
        var (left, right) = DeconstructComb(term);
        var evalApp = EvaluateLambdas(left);
        var evalArg = EvaluateLambdas(right);
        var rightApp = BinaryRight(evalApp);
        var rightArg = BinaryRight(evalArg);

        var potentialOutput = Congruence(evalApp, evalArg);
        
        if (!IsAbs(rightApp))
            return potentialOutput;

        var param = DeconstructAbs(rightApp).parameter;
        var reduction = BetaReduction(MakeCombination(rightApp, param));
        var substitution = InstantiateVariables(new Dictionary<Term, Term>
        {
            [param] = rightArg
        }, reduction);
        return ApplyTransitivity(potentialOutput, substitution);
    }

    public static Theorem LambdaEquivalence(Term left, Term right)
    {
        var baseLeft = EvaluateLambdas(left);
        var baseRight = EvaluateLambdas(right);
        
        var newLeft = BinaryRight(baseLeft);
        var newRight = BinaryRight(baseRight);
        
        if (newLeft == newRight)
            return ApplyTransitivity(baseLeft, Commutativity(baseRight));

        if (!IsAbs(newLeft) || !IsAbs(newRight))
            throw new TheoremException("Terms are not equivalent");

        var (leftParam, leftAbs) = DeconstructAbs(BinaryRight(baseLeft));
        var (rightParam, rightAbs) = DeconstructAbs(BinaryRight(baseRight));

        var substituted = LambdaSubstitute(BinaryRight(baseLeft), rightParam);

        var transitive = ApplyTransitivity(baseLeft, substituted);

        return ApplyTransitivity(transitive, Commutativity(baseRight));
    }

    public static Theorem LambdaSubstitute(Term lambda, Term newVariable) // \x . f x & y
    {
        var (param, abstraction) = DeconstructAbs(lambda);
        if (newVariable == param)
            return Reflexivity(lambda); // (\x . f x) = (\x . f x)

        var desiredAbstraction = InstantiateVariables(new Dictionary<Term, Term>
        {
            [param] = newVariable
        }, abstraction); // f y
        var desiredAbs = MakeAbstraction(newVariable, desiredAbstraction); // \y . f y
        var appliedAbs = MakeCombination(desiredAbs, newVariable); // (\y . f y) y
        var reducedAbs = BetaReduction(appliedAbs); // (\y . f y) y = f y
        var substitutedAbs = InstantiateVariables(new Dictionary<Term, Term>
        {
            [newVariable] = param
        }, reducedAbs); // (\y . f y) x = f x
        var abstractedAbs = Abstraction(param, substitutedAbs); // (\x . (\y . f y) x) = (\x . f x)
        var commutedAbstractedAbs = Commutativity(abstractedAbs); // (\x . f x) = (\x . (\y . f y) x)
        var oldVariableName = DeconstructVar(param).name;
        var tempName = "f";
        if (oldVariableName == tempName)
            tempName = "g";
        
        var customEta = CustomEtaReduction(DeconstructVar(param).name, tempName); // ('x' . 'f' 'x') = 'f'

        var typedCustomEta = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = TypeOf(newVariable),
            [MakeType("b")] = TypeOf(abstraction)
        }, customEta); // typed as (\x . (\y . f y) x) = (\y . f y)
        
        var substitutedCustomEta = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable(tempName, TypeOf(desiredAbs))] = desiredAbs
        }, typedCustomEta); // (\x . (\y . f y) x) = (\y . f y)
        
        return ApplyTransitivity(commutedAbstractedAbs, substitutedCustomEta);
    }
    
    

    public static Theorem ApplyBinaryDefinition(Theorem definition, Term left, Term right)
    {
        var type = TypeOf(BinaryLeft(definition));
        var leftTypes = DeconstructTyApp(type).args;
        var templateRightType = leftTypes[0];
        var templateLeftType = DeconstructTyApp(leftTypes[1]).args[0];
        
        var leftType = TypeOf(left);
        var rightType = TypeOf(right);
        
        if (leftType != templateLeftType || rightType != templateRightType)
        {
            var dict = new Dictionary<Type, Type>();
            if (leftType != templateLeftType)
                dict[templateLeftType] = leftType;
            if (rightType != templateRightType)
                dict[templateRightType] = rightType;
            
            definition = InstantiateTypes(dict, definition);
        }

        var combLeft = Congruence(definition, left);
        var combRight = Congruence(combLeft, right);

        return EvaluateLambdas(combRight);
    }
}