using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class BinaryUtilities
{
    public static void Load() { }
    
    static BinaryUtilities()
    {
        Basic.Load();
    }

    public static Term ApplyBinaryFunction(string name, Term left, Term right)
    {
        var op = MakeConstant(name);
        var type = op.TypeOf();
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
            
            op = InstantiateTypes(dict, op);
        }
        
        return MakeCombination(MakeCombination(op, left), right);
    }

    public static Result<Term> TryApplyBinaryFunction(string name, Term left, Term right)
    {
        if (!TryMakeConstant(name).Deconstruct(out var op, out var error))
            return error;
        var type = op.TypeOf();
        if (!type.TryDeconstructTyApp().Deconstruct(out var typeName, out var typeArgs, out _) || typeName != "fun")
            return $"{name} is not a binary function";
        var leftTypes = typeArgs;
        var templateLeftType = leftTypes[0];
        if (!leftTypes[1].TryDeconstructTyApp().Deconstruct(out typeName, out typeArgs, out _) || typeName != "fun")
            return $"{name} is not a binary function";
        var templateRightType = typeArgs[0];
        
        var leftType = left.TypeOf();
        var rightType = right.TypeOf();
        
        if (leftType != templateLeftType || rightType != templateRightType)
        {
            var dict = new Dictionary<Type, Type>();
            if (leftType != templateLeftType && TryGenerateTypeMap(templateLeftType, leftType, dict).IsError(out error))
                return error;
            if (rightType != templateRightType && TryGenerateTypeMap(templateRightType, rightType, dict).IsError(out error))
                return error;
            
            op = InstantiateTypes(dict, op);
        }
        
        return MakeCombination(MakeCombination(op, left), right);
    }
    
    public static Term BinaryRight(Term term)
    {
        var (_, right) = term.DeconstructComb();
        return right;
    }

    public static Result<Term> TryBinaryRight(Term term)
    {
        if (!term.TryDeconstructComb().Deconstruct(out var tuple, out _))
            return $"{term} is not a binary function application";
        var (leftEq, right) = tuple;
        
        if (!leftEq.IsComb())
            return $"{term} is not a binary function application";
        
        return right;
    }

    public static Term BinaryLeft(Term term)
    {
        var (leftEq, _) = term.DeconstructComb();
        var (_, left) = leftEq.DeconstructComb();
        return left;
    }

    public static Result<Term> TryBinaryLeft(Term term)
    {
        if (!term.TryDeconstructComb().Deconstruct(out var tuple, out _))
            return $"{term} is not a binary function application";
        var (leftEq, _) = tuple;

        if (!leftEq.TryDeconstructComb().Deconstruct(out tuple, out _))
            return $"{term} is not a binary function application";
        
        var (_, left) = tuple;
        return left;
    }

    public static (Term left, Term right, Term op) BinaryDeconstruct(Term term)
    {
        var (leftEq, right) = term.DeconstructComb();
        var (op, left) = leftEq.DeconstructComb();
        
        return (left, right, op);
    }
    
    public static Result<Term, Term, Term> TryBinaryDeconstruct(Term term) //left, right, op
    {
        if (!term.TryDeconstructComb().Deconstruct(out var tuple, out _))
            return $"{term} is not a binary function application";
        var (leftEq, right) = tuple;

        if (!leftEq.TryDeconstructComb().Deconstruct(out tuple, out _))
            return $"{term} is not a binary function application";
        
        var (op, left) = tuple;
        return (left, right, op);
    }

    public static Term BinaryOperator(Term term)
    {
        var (leftEq, _) = term.DeconstructComb();
        var (op, _) = leftEq.DeconstructComb();
        return op;
    }
    
    public static Result<Term> TryBinaryOperator(Term term)
    {
        if (!term.TryDeconstructComb().Deconstruct(out var tuple, out _))
            return $"{term} is not a binary function application";
        var (leftEq, _) = tuple;

        if (!leftEq.TryDeconstructComb().Deconstruct(out tuple, out _))
            return $"{term} is not a binary function application";
        
        var (op, _) = tuple;
        return op;
    }

    public static Term BinaryLeft(Theorem thm)
    {
        return BinaryLeft(thm.Conclusion());
    }
    
    public static Result<Term> TryBinaryLeft(Theorem thm)
    {
        return TryBinaryLeft(thm.Conclusion());
    }
    
    public static Term BinaryRight(Theorem thm)
    {
        return BinaryRight(thm.Deconstruct().conclusion);
    }
    
    public static Result<Term> TryBinaryRight(Theorem thm)
    {
        return TryBinaryRight(thm.Deconstruct().conclusion);
    }
    
    public static Term BinaryOperator(Theorem thm)
    {
        return BinaryOperator(thm.Deconstruct().conclusion);
    }
    
    public static Result<Term> TryBinaryOperator(Theorem thm)
    {
        return TryBinaryOperator(thm.Deconstruct().conclusion);
    }
    
    public static (Term left, Term right, Term op) BinaryDeconstruct(Theorem thm)
    {
        return BinaryDeconstruct(thm.Conclusion());
    }
    
    public static Result<Term, Term, Term> TryBinaryDeconstruct(Theorem thm) //left, right, op
    {
        return TryBinaryDeconstruct(thm.Conclusion());
    }

    public static Result<Term, Term> TryBinaryDeconstruct(Term term, string expectedMethod) //left, right
    {
        if (!TryBinaryDeconstruct(term).Deconstruct(out var tuple, out var error))
            return error;
        
        var (left, right, op) = tuple;
        
        if (!op.TryDeconstructConst().Deconstruct(out var opName, out _, out _) || opName != expectedMethod)
            return $"{term} is not a binary function application of {expectedMethod}";
        
        return (left, right);
    }
    
    public static Result<Term, Term> TryBinaryDeconstruct(Theorem thm, string expectedMethod) //left, right
    {
        return TryBinaryDeconstruct(thm.Conclusion(), expectedMethod);
    }
}