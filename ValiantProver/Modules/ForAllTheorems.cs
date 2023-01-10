using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.EtaReductionTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;
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
        TryRegisterLambdaRule("!", "!", "∀");

        AllApplicationsImpliesEqualityTheorem = ConstructAllApplicationsImpliesEqualityTheorem();
    }
    
    public static Theorem ForAllDefinition { get; }
    public static Theorem AllApplicationsImpliesEqualityTheorem { get; } // !x . f x = g x |- f = g

    private static Theorem ConstructAllApplicationsImpliesEqualityTheorem()
    {
        var etaF = CustomEtaReduction("x", "f"); // |- (\x . f x) = f
        var etaG = CustomEtaReduction("x", "g"); // |- (\x . g x) = g
        
        var fxEqGx = Assume(Parse("!x . f x = g x")); // !x . f x = g x |- !x . f x = g x
        var x = Parse("x 'a");
        var specialise = Specialise(fxEqGx, x); // !x . f x = g x |- f x = g x
        var abstracted = Abstraction(x, specialise); // !x . f x = g x |- (\x . f x) = (\x . g x)
        var transitivity = Transitivity(abstracted, etaG); // !x . f x = g x |- (\x . f x) = g
        
        return Transitivity(Commutativity(etaF), transitivity); // !x . f x = g x |- f = g
    }

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

    public static Result<Theorem> TryAllApplicationsImpliesEquality(Theorem theorem) // |- ! x . f x = g x
    {
        if (!TryUnaryDeconstruct(theorem, "!").Deconstruct(out var arg, out var error)) // \ y . fn y = gn y
            return error;

        if (!arg.TryDeconstructAbs().Deconstruct(out var param, out var abs, out error))
            return error;
        
        var (paramName, _) = param.DeconstructVar();

        if (!TryBinaryDeconstruct(abs, "=").Deconstruct(out var left, out var right, out error))
            return error;

        if (!left.TryDeconstructComb().Deconstruct(out var f, out var leftParam, out error))
            return error;
        
        if (leftParam != param)
            return "Expected left-hand side of equality to be of the form \"f x\"";

        if (!right.TryDeconstructComb().Deconstruct(out var g, out var rightParam, out error))
            return error;
        
        if (rightParam != param)
            return "Expected right-hand side of equality to be of the form \"g x\"";

        var fname = GetFreeVariableName(UsedNames(theorem).Append("x").ToHashSet(), "f"); // fn
        var gname = GetFreeVariableName(UsedNames(theorem).Append(fname).Append("x").ToHashSet(), "g"); // gn

        var thmDef = AllApplicationsImpliesEqualityTheorem;

        if (fname != "f" || gname != "g")
        {
            var dict = new Dictionary<Term, Term>();
            
            if (fname != "f")
                dict[Parse("f :fun 'a 'b")] = Parse($"{fname} :fun 'a 'b");
            
            if (gname != "g")
                dict[Parse("g :fun 'a 'b")] = Parse($"{gname} :fun 'a 'b");
            
            thmDef = InstantiateVariables(dict, thmDef);// !x . fn x = g x |- fn = gn
        }
        
        if (paramName != "x")
        {
            var subsTerm = Parse($"!{paramName} . {fname} {paramName} = {gname} {paramName}"); //!y . fn y = gn y
            
            var lambdaVariableChange = LambdaEquivalence(subsTerm, 
                Parse($"!x . {fname} x = {gname} x")); // |- (!y . fn y = gn y) = (!x . fn x = gn x)
            var mp = ModusPonens(lambdaVariableChange, Assume(subsTerm)); // !y . fn y = gn y |- (!x . fn x = gn x)
            
            thmDef = Elimination(thmDef, mp); // !y . fn y = gn y |- fn = gn
        }

        var type = f.TypeOf();
        
        var typeDict = GenerateTypeMap(MakeType("fun", new []{MakeType("a"), MakeType("b")}), type);
        
        var typed = InstantiateTypes(typeDict, thmDef); // !y . fn y = gn y |- fn = gn

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable(fname, type)] = f,
            [MakeVariable(gname, type)] = g
        }, typed); // !y . fn y = gn y |- fn = gn
        
        return Elimination(inst, theorem); // |- fn = gn
    }

    public static Theorem AllApplicationsImpliesEquality(Theorem theorem)
    {
        return TryAllApplicationsImpliesEquality(theorem).ValueOrException();
    }
}