using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TruthTheorems;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public static class ForAllTheorems
{
    public static void Load() { }

    static ForAllTheorems()
    {
        LambdaEvaluator.Load();
        TruthTheorems.Load();
        
        ForAllDefinition = NewBasicDefinition(Parse(@"! = (\p . p = (\x . T))"));
        Parser.RegisterLambdaRule("!", "!");
    }
    
    public static Theorem ForAllDefinition { get; }
    
    public static Theorem Specialise(Theorem theorem, Term term) //! (x . t x) and y goes to t y
    {
        return TrySpecialise(theorem, term).ValueOrException();
    }

    public static Result<Theorem> TrySpecialise(Theorem theorem, Term term)
    {
        if (!TryUnaryDeconstruct(theorem, "!").Deconstruct(out var lambda, out _)) // \x . t x
            return "Expected theorem to be of the form \"! (x . t x)\"";
        var simp = ApplyUnaryDefinition(ForAllDefinition, lambda); // ! (\x . t x) = ((\x . t x) = (\x . T))
        var modusPonens = ModusPonens(simp, theorem); // (\x . t x) = (\x . T)

        if (!lambda.TypeOf().TryDeconstructFun().Deconstruct(out var thmType, out _, out var error))
            return error;
        
        var termType = term.TypeOf();
        var inst = modusPonens;
        if (thmType != termType)
        {
            if (!TryGenerateTypeMap(thmType, termType).Deconstruct(out var typeMap, out error))
                return error;
            
            inst = InstantiateTypes(typeMap, modusPonens);
        }
        
        var appliedTerm = Congruence(inst, term); // t y = T
        var simplifiedApplied = EvaluateLambdas(appliedTerm);
        var commuted = Commutativity(simplifiedApplied); // T = t y
        return ModusPonens(commuted, Truth); // t y
    }

    public static Theorem Specialise(Theorem theorem, Term[] parameters)
    {
        return parameters.Aggregate(theorem, Specialise);
    }
    
    public static Result<Theorem> TrySpecialise(Theorem theorem, Term[] parameters)
    {
        var output = theorem;
        
        foreach (var parameter in parameters)
        {
            if (!TrySpecialise(theorem, parameter).Deconstruct(out var newThm, out var error))
                return error;
            
            output = newThm;
        }
        
        return output;
    }

    public static Theorem Generalise(Theorem theorem, Term variable)
    {
        var antisymmetry = AntiSymmetry(theorem, Truth); // t x = T
        var abstraction = Abstraction(variable, antisymmetry); // \x . t x = \x . T
        var lambda = BinaryLeft(abstraction); // \x . t
        var applied = ApplyUnaryDefinition(ForAllDefinition, lambda); // ! (\x . t x) = ((\x . t x) = (\x . T))
        var lambdaEquivalent = LambdaEquivalence(abstraction.Conclusion(), BinaryRight(applied));
        var equivified = ModusPonens(lambdaEquivalent, abstraction);
        return ModusPonens(Commutativity(applied), equivified); // ! x . t x
    }
    
    public static Theorem Generalise(Theorem theorem, Term[] variables)
    {
        return variables.Reverse().Aggregate(theorem, Generalise);
    }
}