using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;

namespace ValiantProver.Modules;

public static class UnaryUtilities
{
    public static void Load() { }
    
    static UnaryUtilities()
    {
        LambdaEvaluator.Load();
    }

    public static Term ApplyUnaryFunction(string name, Term arg)
    {
        var op = MakeConstant(name);
        var type = op.TypeOf();
        var templateArgType = type.DeconstructTyApp().args[0];
        
        var argType = arg.TypeOf();
        
        if (argType != templateArgType)
        {
            op = InstantiateTypes(GenerateTypeMap(templateArgType, argType), op);
        }
        
        return MakeCombination(op, arg);
    }

    public static Result<Term> TryApplyUnaryFunction(string name, Term arg)
    {
        if (!TryMakeConstant(name).Deconstruct(out var op, out _))
            return $"Could not find constant {name}";
        
        var type = op.TypeOf();
        
        if (!type.TryDeconstructTyApp().Deconstruct(out var typeName, out var args, out _))
            return $"Could not deconstruct type {type} as a type application";

        if (typeName != "fun")
            return $"{name} is not a function";
        
        var templateArgType = args[0];
        
        var argType = arg.TypeOf();
        
        if (argType != templateArgType)
        {
            if (!TryGenerateTypeMap(templateArgType, argType).Deconstruct(out var typeMap, out var error))
                return error;
            if (!TryInstantiateTypes(typeMap, op).Deconstruct(out op, out error))
                return error;
        }
        
        return MakeCombination(op, arg);
    }

    public static Term UnaryArgument(Term term)
    {
        return term.DeconstructComb().argument;
    }

    public static Result<Term> TryUnaryArgument(Term term)
    {
        return term.TryDeconstructComb().Item2;
    }

    public static (Term op, Term arg) UnaryDeconstruct(Term term)
    {
        return term.DeconstructComb();
    }

    public static Term UnaryDeconstruct(Term term, string expectedOp)
    {
        return (Term) TryUnaryDeconstruct(term, expectedOp);
    }
    
    public static Term UnaryDeconstruct(Theorem theorem, string expectedOp)
    {
        return (Term) TryUnaryDeconstruct(theorem, expectedOp);
    }
    
    public static Result<Term, Term> TryUnaryDeconstruct(Term term) //op & arg
    {
        return term.TryDeconstructComb();
    }
    
    public static Result<Term> TryUnaryDeconstruct(Term term, string expectedOp)
    {
        if (!TryUnaryDeconstruct(term).Deconstruct(out var op, out var arg, out var error))
            return error;
        
        if (!op.TryDeconstructConst().Deconstruct(out var opName, out _, out _) || opName != expectedOp)
            return $"{term} is not a binary function application of {expectedOp}";
        
        return arg;
    }
    
    public static Result<Term> TryUnaryDeconstruct(Theorem theorem, string expectedOp)
    {
        return TryUnaryDeconstruct(theorem.Conclusion(), expectedOp);
    }

    public static Term UnaryOperator(Term term)
    {
        return term.DeconstructComb().application;
    }
    
    public static Result<Term> TryUnaryOperator(Term term)
    {
        return term.TryDeconstructComb().Item1;
    }
    
    public static Term UnaryArgument(Theorem thm)
    {
        return UnaryArgument(thm.Conclusion());
    }
    
    public static Result<Term> TryUnaryArgument(Theorem thm)
    {
        return TryUnaryArgument(thm.Conclusion());
    }
    
    public static Term UnaryOperator(Theorem thm)
    {
        return UnaryOperator(thm.Conclusion());
    }
    
    public static Result<Term> TryUnaryOperator(Theorem thm)
    {
        return TryUnaryOperator(thm.Conclusion());
    }
    
    public static (Term op, Term arg) UnaryDeconstruct(Theorem thm)
    {
        return UnaryDeconstruct(thm.Conclusion());
    }
    
    public static Result<Term, Term> TryUnaryDeconstruct(Theorem thm)
    {
        return TryUnaryDeconstruct(thm.Conclusion());
    }
    
    public static Theorem ApplyUnaryDefinition(Theorem definition, Term arg)
    {
        var type = BinaryLeft(definition).TypeOf();
        var templateArgType = type.DeconstructTyApp().args[0];
        
        var argType = arg.TypeOf();

        if (templateArgType != argType)
        {
            definition = InstantiateTypes(GenerateTypeMap(templateArgType, argType), definition);
        }

        var outputThm = Congruence(definition, arg);

        return Transitivity(outputThm, EvaluateLambdas(BinaryRight(outputThm)));
    }
    
    public static Result<Theorem> TryApplyUnaryDefinition(Theorem definition, Term arg)
    {
        if (!TryBinaryLeft(definition).Deconstruct(out var definitionOp, out _))
            return $"{definition} is not a definition";
        
        var type = definitionOp.TypeOf();
        
        if (!type.TryDeconstructTyApp().Deconstruct(out var typeName, out var args, out _))
            return $"Could not deconstruct type {type} as a type application";

        if (typeName != "fun")
            return $"Definition {definition} is not a function";
        
        var templateArgType = args[0];
        
        var argType = arg.TypeOf();
        
        if (templateArgType != argType)
        {
            if (!TryGenerateTypeMap(templateArgType, argType).Deconstruct(out var typeMap, out var error))
                return error;
            if (!TryInstantiateTypes(typeMap, definition).Deconstruct(out var newDefinition, out error))
                return error;
            
            definition = newDefinition;
        }

        return EvaluateLambdas(Congruence(definition, arg));
    }
}