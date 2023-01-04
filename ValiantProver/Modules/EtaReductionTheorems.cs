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
        var (param, abstraction) = DeconstructAbs(term);
        var f = DeconstructComb(abstraction).application;
        
        var paramName = DeconstructVar(param).name;
        var fName = paramName == "f" ? "g" : "f";
        
        var customEta = CustomEtaReduction(paramName, fName); // (\ 'x' . 'f' 'x') = 'f'
        var types = DeconstructTyApp(TypeOf(abstraction)).args;
        var typedCustomEta = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = types[0],
            [MakeType("b")] = types[1]
        }, customEta); // typed correctly

        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [MakeVariable(fName, TypeOf(f))] = f
        }, typedCustomEta);
    }

    public static Theorem CustomEtaReduction(string variableName, string applicationName)
    {
        if (applicationName == variableName)
            throw new TheoremException("variableName and applicationName must be different");
        
        if (variableName.Length == 0 || applicationName.Length == 0)
            throw new TheoremException("variableName and applicationName must be non-empty");

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
        var transitivity = ApplyTransitivity(abstracted, reduction); // (\x . ((\y . f y) x)) = f
        
        var otherEq = Substitute(EtaReduction, Parse(@$"(\x . (\{y} . {f} {y}) x) = (\{y} . {f} :fun 'a 'b {y})")); // (\x . (\y . f y) x) = (\y . f y)
        
        var output = ApplyTransitivity(Commutativity(otherEq), transitivity); // (\y . f y) = f

        return InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse($"{f} :fun 'a 'b")] = Parse($"{g} :fun 'a 'b")
        }, output); // (\y . g y) = g
    }
}