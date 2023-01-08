using ValiantBasics;
using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TransitivityTheorems;

namespace ValiantProver.Modules;

public static class EtaReductionTheorems
{
    public static void Load() { }
    
    static EtaReductionTheorems()
    {
        TransitivityTheorems.Load();
        
        EtaReduction = NewAxiom(Parse(@"(\x . f x) = f"));
    }
    
    public static Theorem EtaReduction { get; }

    public static Theorem ApplyEtaReduction(Term term)
    {
        return TryApplyEtaReduction(term).ValueOrException();
    }
    
    public static Result<Theorem> TryApplyEtaReduction(Term term) // \y . g y
    {
        if (!term.TryDeconstructAbs().Deconstruct(out var termTuple, out var error))
            return error;
        var (param, abstraction) = termTuple;
        
        if (!abstraction.TryDeconstructComb().Deconstruct(out termTuple, out error))
            return error;
        
        var (g, y) = termTuple;
        
        if (y != param)
            return $"Term is not in eta normal form: {y} and {param} are not equal";
        
        var (paramName, _) = param.DeconstructVar();

        var fName = GetFreeVariableName(term);
        
        var customEta = CustomEtaReduction(paramName, fName, abstraction.TypeOf()); // (\ y . f y) = f

        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable(fName, g.TypeOf())] = g
        }, customEta);
    }

    public static Theorem CustomEtaReduction(string variableName, string applicationName)
    {
        return TryCustomEtaReduction(variableName, applicationName).ValueOrException();
    }

    public static Result<Theorem> TryCustomEtaReduction(string variableName, string applicationName)
    {
        if (applicationName == variableName)
            return "variableName and applicationName must be different";
        
        if (variableName.Length == 0 || applicationName.Length == 0)
            return "variableName and applicationName must be non-empty";

        var y = variableName;
        var g = applicationName;
        
        var f = "f";

        if (variableName == "f")
            f = "g";

        var reduction = Substitute(EtaReduction, Parse($@"(\x . {f} x) = {f} :fun 'a 'b")); // (\x . f x) = f

        var yBetaReduction = BetaReduction(Parse($@"(\{y} . {f} :fun 'a 'b {y}) {y}")); // ((\y . f y) y) = f y
        var substitution = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse($"{y} 'a")] = Parse("x 'a")
        }, yBetaReduction); // ((\y . f y) x) = f x
        var abstracted = Abstraction(Parse("x 'a"), substitution); // (\x . ((\y . f y) x)) = (\x . f x)
        var transitivity = Transitivity(abstracted, reduction); // (\x . ((\y . f y) x)) = f
        
        var otherEq = Substitute(EtaReduction, Parse(@$"(\x . (\{y} . {f} {y}) x) = (\{y} . {f} :fun 'a 'b {y})")); // (\x . (\y . f y) x) = (\y . f y)
        
        var output = Transitivity(Commutativity(otherEq), transitivity); // (\y . f y) = f

        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse($"{f} :fun 'a 'b")] = Parse($"{g} :fun 'a 'b")
        }, output); // (\y . g y) = g
    }

    public static Result<Theorem> TryCustomEtaReduction(string variableName, string applicationName, Type type)
    {
        if (!type.TryDeconstructTyApp().Deconstruct(out var tyApp, out var error))
            return "Expected function type";
        
        var (typeName, args) = tyApp;
        
        if (typeName != "fun")
            return "Expected function type";
        
        if (!TryCustomEtaReduction(variableName, applicationName).Deconstruct(out var theorem, out error))
            return error;
        
        return InstantiateTypes(GenerateTypeMap(MakeType("fun", new []{MakeType("a"), MakeType("b")}), type), theorem);
    }
    
    public static Theorem CustomEtaReduction(string variableName, string applicationName, Type type)
    {
        return TryCustomEtaReduction(variableName, applicationName, type).ValueOrException();
    }

    public static Result<Theorem> TryChangeLambdaVariable(Term term, Term variable) // \z . t and y
    {
        if (!term.TryDeconstructAbs().Deconstruct(out var param, out var abs, out var error)) // z & t
            return error;
        

        if (param == variable)
            return Reflexivity(term);

        if (!variable.TryDeconstructVar().Deconstruct(out var varName, out var type, out error))
            return error;
        
        
        var (_, paramType) = param.DeconstructVar();
        
        if (type != paramType)
            return "Types of variable and lambda parameter are not equal";

        var etaFunctionName = GetFreeVariableName(new[] { term, variable }); // f
        var etaFunctionVariable = MakeVariable(etaFunctionName, term.TypeOf());
        var customEtaReduction = CustomEtaReduction(varName, etaFunctionName, etaFunctionVariable.TypeOf()); // \ y . f y = f

        if (!TryInstantiateVariables(new Dictionary<Term, Term>
            {
                [etaFunctionVariable] = term
            }, customEtaReduction).Deconstruct(out var subs, out error)) // \ y . (\z . t) y = \z . t
            return error;

        var betaReduction = BetaReduction(MakeCombination(term, param)); // (\z . t) z = t
        if (!TryInstantiateVariables(new Dictionary<Term, Term>
        {
            [param] = variable
        }, betaReduction).Deconstruct(out var subbedBetaReduction, out error)) // (\z . t) y = t
            return error;
        var abstracted = Abstraction(variable, subbedBetaReduction); // \y . (\z . t) y = \y . t

        return TryTransitivity(Commutativity(subs), abstracted); // \z . t = \y . t
    }
    
    public static Theorem ChangeLambdaVariable(Term term, Term variable)
    {
        return TryChangeLambdaVariable(term, variable).ValueOrException();
    }
}