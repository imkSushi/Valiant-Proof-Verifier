using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.EtaReductionTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;

namespace ValiantProver.Modules;

public static class LambdaEvaluator
{
    public static void Load() { }

    static LambdaEvaluator()
    {
        EtaReductionTheorems.Load();
    }

    public static Theorem EvaluateLambdas(Theorem theorem)
    {
        var equality = EvaluateLambdas(theorem.Deconstruct().conclusion);
        
        return ModusPonens(equality, theorem);
    }
    
    public static Theorem EvaluateLambdas(Term term)
    {
        if (term.IsVar() || term.IsConst())
            return Reflexivity(term);
        
        if (term.TryDeconstructAbs().IsSuccess(out var parameter, out var abstraction))
            return EvaluateLambdasAbstractionsIteration(parameter, abstraction);
        
        var combTuple = term.DeconstructComb();
        
        return EvaluateLambdasCombinationIteration(combTuple.application, combTuple.argument);
    }
    
    private static Theorem EvaluateLambdasAbstractionsIteration(Term parameter, Term abstraction)
    {
        var evaluatedAbstraction = EvaluateLambdas(abstraction);
            
        var evalAbsRight = BinaryRight(evaluatedAbstraction);

        var output = Abstraction(parameter, evaluatedAbstraction);

        if (!evalAbsRight.TryDeconstructComb().Deconstruct(out var app, out var arg, out _) || arg != parameter || IsVariableFree(parameter, app))
            return output;
            
        var etaReduction = ApplyEtaReduction(BinaryRight(output));
        return Transitivity(output, etaReduction);
    }

    private static Theorem EvaluateLambdasCombinationIteration(Term application, Term argument)
    {
        var evalApp = EvaluateLambdas(application); // f = g
        var evalArg = EvaluateLambdas(argument); // x = y
        var rightApp = BinaryRight(evalApp); // g
        var rightArg = BinaryRight(evalArg); // y

        var potentialOutput = Congruence(evalApp, evalArg); // f x = g y

        if (!rightApp.TryDeconstructAbs().IsSuccess(out var absTuple)) 
            return potentialOutput;
        
        // f x = (\z . t) y i.e. rightApp is \t . t
        var (param, abs) = absTuple;
        var reduction = BetaReduction(MakeCombination(rightApp, param)); // (\z . t) z = t
        var substitution = InstantiateVariables(new Dictionary<Term, Term>
        {
            [param] = rightArg
        }, reduction); // (\z . t) y = t[y/z]
            
        var transivity = Transitivity(potentialOutput, substitution);

        var eval = EvaluateLambdas(BinaryRight(transivity));

        return Transitivity(transivity, eval);
    }

    public static Theorem LambdaEquivalence(Term left, Term right)
    {
        return TryLambdaEquivalence(left, right).ValueOrException();
    }

    public static Result<Theorem> TryLambdaEquivalence(Term left, Term right)
    {
        var baseLeft = EvaluateLambdas(left);
        var baseRight = EvaluateLambdas(right);
        
        var newLeft = BinaryRight(baseLeft);
        var newRight = BinaryRight(baseRight);
        
        if (newLeft == newRight)
            return Transitivity(baseLeft, Commutativity(baseRight));

        if (newLeft.IsAbs() && newRight.IsAbs()) 
            return TryLambdaEquivalenceAbstraction(baseLeft, baseRight);

        if (newLeft.IsComb() && newRight.IsComb()) 
            return TryLambdaEquivalenceCombination(baseLeft, baseRight);
        
        return "Terms are not equivalent";
    }

    private static Result<Theorem> TryLambdaEquivalenceAbstraction(Theorem left, Theorem right)
    {
        var leftTerm = BinaryRight(left);
        var (rightParam, rightAbs) = BinaryRight(right).DeconstructAbs();
        var (leftParam, leftAbs) = leftTerm.DeconstructAbs();

        if (leftParam != rightParam)
        {
            if (!TryChangeLambdaVariable(leftTerm, rightParam).Deconstruct(out var substituted, out var error))
                return error;
            
            left = Transitivity(left, substituted);
            leftAbs = BinaryRight(left).DeconstructAbs().abstraction;
        }

        if (!TryLambdaEquivalence(leftAbs, rightAbs).Deconstruct(out var thm, out var err))
            return err;

        var abstracted = Abstraction(rightParam, thm);
        var transitivity = Transitivity(left, abstracted);

        return Transitivity(transitivity, Commutativity(right));
    }

    private static Result<Theorem> TryLambdaEquivalenceCombination(Theorem left, Theorem right)
    {
        var (leftApp, leftArg) = BinaryRight(left).DeconstructComb();
        var (rightApp, rightArg) = BinaryRight(right).DeconstructComb();

        if (!TryLambdaEquivalence(leftApp, rightApp).Deconstruct(out var appEq, out var error))
            return error;
        
        if (!TryLambdaEquivalence(leftArg, rightArg).Deconstruct(out var argEq, out error))
            return error;

        var evalEq = Congruence(appEq, argEq);
        
        var transitive = Transitivity(left, evalEq);
        
        return Transitivity(transitive, Commutativity(right));
    }/*

    public static Theorem ApplyBinaryDefinition(Theorem definition, Term left, Term right)
    {
        var type = BinaryLeft(definition).TypeOf();
        var leftTypes = type.DeconstructTyApp().args;
        var templateRightType = leftTypes[0];
        var templateLeftType = leftTypes[1].DeconstructTyApp().args[0];
        
        var leftType = left.TypeOf();
        var rightType = right.TypeOf();
        
        if (leftType != templateLeftType || rightType != templateRightType)
        {
            var dict = new Dictionary<Type, Type>();
            if (leftType != templateLeftType)
                GenerateTypeMap(templateLeftType, leftType, dict);
            if (rightType != templateRightType)
                GenerateTypeMap(templateRightType, rightType, dict);
            
            definition = InstantiateTypes(dict, definition);
        }

        var combLeft = Congruence(definition, left);
        var combRight = Congruence(combLeft, right);

        return EvaluateLambdas(combRight);
    }*/

    public static Theorem ApplyBinaryDefinition(Theorem definition, Term left, Term right)
    {
        return TryApplyBinaryDefinition(definition, left, right).ValueOrException();
    }

    public static Result<Theorem> TryApplyBinaryDefinition(Theorem definition, Term left, Term right)
    {
        if (!TryBinaryDeconstruct(definition, "=").Deconstruct(out var binaryTuple, out var error))
            return "Definition is not a binary definition";

        var (op, defn) = binaryTuple;
        
        var type = op.TypeOf();
        
        if (!type.TryDeconstructTyApp().Deconstruct(out var typeName, out var typeArgs, out error))
            return "Definition is not a binary definition";
        
        if (typeName != "fun")
            return "Definition is not a binary definition";
        
        var leftTemplateType = typeArgs[0];
        
        if (!typeArgs[1].TryDeconstructTyApp().Deconstruct(out typeName, out typeArgs, out error))
            return "Definition is not a binary definition";
        
        if (typeName != "fun")
            return "Definition is not a binary definition";
        
        var rightTemplateType = typeArgs[0];
        
        var leftType = left.TypeOf();
        var rightType = right.TypeOf();

        if (leftType != leftTemplateType || rightType != rightTemplateType)
        {
            var dict = new Dictionary<Type, Type>();
            if (leftType != leftTemplateType && TryGenerateTypeMap(leftTemplateType, leftType, dict).IsError(out error))
                return error;

            if (rightType != rightTemplateType &&
                TryGenerateTypeMap(rightTemplateType, rightType, dict).IsError(out error))
                return error;
            
            definition = InstantiateTypes(dict, definition);
        }
        
        var applied = Congruence(definition, left);
        applied = Congruence(applied, right);
        
        var evaluated = EvaluateLambdas(BinaryRight(applied));
        
        return Transitivity(applied, evaluated);
    }
}