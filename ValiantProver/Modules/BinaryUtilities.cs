using ValiantProofVerifier;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class BinaryUtilities
{
    public static void Load() { }
    
    static BinaryUtilities()
    {
        Theory.Load();
    }

    public static Term ApplyBinaryFunction(string name, Term left, Term right)
    {
        var op = MakeConstant(name);
        var type = TypeOf(op);
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
            
            op = InstantiateTypes(dict, op);
        }
        
        return MakeCombination(MakeCombination(op, left), right);
    }

    public static Term ConstructEquality(Term left, Term right)
    {
        return MakeCombination(left, MakeCombination(right, MakeConstant("=", new Dictionary<Type, Type>
        {
            [Aty] = TypeOf(left)
        })));
    }

    public static (Term left, Term right) DeconstuctEquality(Term term)
    {
        var (left, rightEquality) = DeconstructComb(term);
        var (right, _) = DeconstructComb(rightEquality);
        return (left, right);
    }

    public static (Term left, Term right) DeconstuctEquality(Theorem thm)
    {
        return DeconstuctEquality(Theory.DeconstructTheorem(thm).conclusion);
    }
    
    public static Term BinaryRight(Term term)
    {
        var (_, right) = DeconstructComb(term);
        return right;
    }
    
    public static Term BinaryLeft(Term term)
    {
        var (leftEq, _) = DeconstructComb(term);
        var (_, left) = DeconstructComb(leftEq);
        return left;
    }

    public static (Term left, Term right, Term op) BinaryDeconstruct(Term term)
    {
        var (leftEq, right) = DeconstructComb(term);
        var (op, left) = DeconstructComb(leftEq);
        
        return (left, right, op);
    }

    public static Term BinaryOperator(Term term)
    {
        var (leftEq, _) = DeconstructComb(term);
        var (op, _) = DeconstructComb(leftEq);
        return op;
    }
    
    public static Term BinaryLeft(Theorem thm)
    {
        return BinaryLeft(DeconstructTheorem(thm).conclusion);
    }
    
    public static Term BinaryRight(Theorem thm)
    {
        return BinaryRight(DeconstructTheorem(thm).conclusion);
    }
    
    public static Term BinaryOperator(Theorem thm)
    {
        return BinaryOperator(DeconstructTheorem(thm).conclusion);
    }
    
    public static (Term left, Term right, Term op) BinaryDeconstruct(Theorem thm)
    {
        return BinaryDeconstruct(DeconstructTheorem(thm).conclusion);
    }
}