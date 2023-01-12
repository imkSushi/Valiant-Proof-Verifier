using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.BinaryUtilities;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.ForAllTheorems;
using static ValiantProver.Modules.ImpliesTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.UnaryUtilities;

namespace ValiantProver.Modules;

public static class ExistsTheorems
{
    public static void Load() { }

    static ExistsTheorems()
    {
        ImpliesTheorems.Load();
        ForAllTheorems.Load();
        
        TryRegisterLambdaRule("?", "?", "∃");
        ExistsDefinition = NewDefinition(Parse(@"(? p) = !q . (!x . p x -> q) -> q")); //:fun :fun 'a :bool    :bool
        
        ExistsWitnessTheorem = ConstructExistsWitnessTheorem();
        ExistsIndependentOfVariableTheorem = ConstructExistsIndependentOfVariableTheorem();
    }
    
    public static Theorem ExistsDefinition { get; } // ! p . (? p) = !q . (!x . p x -> q) -> q
    public static Theorem ExistsWitnessTheorem { get; } // f t |- ? x . f x
    public static Theorem ExistsIndependentOfVariableTheorem { get; } // |- ! t . (? x . t) = t

    private static Theorem ConstructExistsWitnessTheorem()
    {
        var ft = Parse(@"f :fun 'a :bool t"); // f t
        var witness = Assume(ft); // f t |- f t
        
        var param = Parse(@"x 'a"); // x
        var abs = Parse(@"f :fun 'a :bool x"); // f x
        var existsLambda = MakeAbstraction(param, abs); // \x . f x

        var q = MakeVariable("q", BoolTy); // q

        var ftImpQ = GivenTheoremImpliesAnythingThenAnything(witness, q); //f t, f t -> q |- q
        
        var discharged = Discharge(Parse("f t 'a -> q"), ftImpQ); // f t |- (f t -> q) -> q

        var forAllLambda = Parse("! x 'a . f x -> q"); // ! x . f x -> q

        var assumption = Assume(forAllLambda); // ! x . f x -> q |- ! x . f x -> q
        var specialise = Specialise(assumption, Parse("t 'a")); // ! x . f x -> q |- f t -> q
        var mp = ApplyModusPonens(discharged, specialise); // f t, ! x . f x -> q |- q
        var dischargedAgain = Discharge(forAllLambda, mp); // f t |- (! x . f x -> q) -> q
        var generalised = Generalise(dischargedAgain, q); // f t |- ! q .(! x . f x -> q) -> q

        var wtp = Specialise(ExistsDefinition, existsLambda); // |- ? x . f x = ...
        return ModusPonens(Commutativity(wtp), generalised); // f t |- ? x . f x
    }

    private static Theorem ConstructExistsIndependentOfVariableTheorem() // |- ! t . (? x . t) = t
    {
        var t = Parse("t :bool"); // t
        
        var assumeT = Assume(t); // t |- t
        var witnessed = Exists(Parse(@"\x 'a . t :bool"), assumeT); // t |- ? x . t
        
        var assumeExists = Assume(Parse("? x 'a . t")); // ? x . t |- ? x . t
        var appliedDefn = Specialise(ExistsDefinition, Parse(@"\x 'a . t :bool")); // |- ? x . t = !q . (!x . t -> q) -> q
        var mp = ModusPonens(appliedDefn, assumeExists); // ? x . t |- !q . (!x . t -> q) -> q
        var specMp = Specialise(mp, t); // ? x . t |- (!x . t -> t) -> t

        var forAllThm = ForAllIndependentOfVar(Parse("!x . t -> t")); // |- (! x . t -> t) = t -> t
        var selfImplication = SelfImplication(t); // |- t -> t
        var mp2 = ModusPonens(Commutativity(forAllThm), selfImplication); // |- (! x . t -> t)
        var appMp = ApplyModusPonens(specMp, mp2); // ? x . t |- t
        
        var antisym = AntiSymmetry(witnessed, appMp); // |- (? x . t) = t
        return Generalise(antisym, t); // |- ! t . (? x . t) = t
    }

    public static Result<Theorem> TryExists(Term existsLambda, Theorem witness) // given |- f ((g x) a) then |- ? y . f (y a)
    {
        if (!existsLambda.TryDeconstructAbs().Deconstruct(out var param, out var abs, out var error)) // y and f (y a)
            return error;
        
        if (!TryGenerateMaps(abs, witness.Conclusion()).Deconstruct(out var typeMap, out var termMap, out error)) //maps from f (y a) to f ((g x) a)
            return "Witness is not an example of the lambda";
        
        if (typeMap.Any()) 
            return "Type mismatch";
        
        if (termMap.Count > 2 || (termMap.Count == 1 && termMap.First().Key != param))
            return "Witness is not an example of the lambda";

        var qName = GetFreeVariableName(new[] { existsLambda, witness.Conclusion() }, "q");
        
        var q = MakeVariable(qName, BoolTy);
        if (!TryApplyBinaryFunction("->", abs, q).Deconstruct(out var lambdaImpliesQ, out error)) //f x -> q
            return error;

        var ftImpQ = GivenTheoremImpliesAnythingThenAnything(witness, q); //f t -> q |- q
        var discharged = Discharge(ApplyBinaryFunction("->", witness.Conclusion(), q), ftImpQ); // |- (f t -> q) -> q

        var forAllLambda = ApplyUnaryFunction("!", MakeAbstraction(param, lambdaImpliesQ)); // ! x . f x -> q

        var assumption = Assume(forAllLambda); // ! x . f x -> q |- ! x . f x -> q
        var specialise = Specialise(assumption, termMap.TryGetValue(param, out var subs) ? subs : param); // ! x . f x -> q |- f t -> q
        var mp = ApplyModusPonens(discharged, specialise); // ! x . f x -> q |- q
        var dischargedAgain = Discharge(forAllLambda, mp); // |- (! x . f x -> q) -> q
        var generalised = Generalise(dischargedAgain, q); // |- ! q .(! x . f x -> q) -> q

        //var pName = GetFreeVariableName(new []{existsLambda, witness.Conclusion(), q});

        var newExistsEq = ChangeToUniqueVariables(ExistsDefinition,
            UsedNames(new[] { existsLambda, witness.Conclusion() }), new Dictionary<string, string>
            {
                ["x"] = param.DeconstructVar().name,
                ["q"] = qName
            }); // ! p . (? p) = !q . (!y . p y -> q) -> q
        
        /*var applicationExists = Specialise(newExistsEq, existsLambda); // |- ? x . f x = ...
        
        var existsEq = LambdaEquivalence(ExistsDefinition.Conclusion(), Parse(@$"! {pName} . ((?) {pName}) = !{qName} . (!{param} . {pName} {param} -> {qName}) -> {qName}"));
        var existsDefinition = ModusPonens(existsEq, ExistsDefinition); // |- ? x . f x = \x . f x
        var wtp = ApplyUnaryDefinition(existsDefinition, existsLambda); // |- ? x . f x = ...*/
        return ModusPonens(Commutativity(Specialise(newExistsEq, existsLambda)), generalised);
    }

    public static Theorem Exists(Term existsLambda, Theorem witness)//given \x . f x & |- f t then ? x . f x
    {
        return (Theorem) TryExists(existsLambda, witness);
    }

    public static Result<Theorem> TryExistsIndependentOfVar(Term term) // |- (? y . s) = s
    {
        if (!TryUnaryDeconstruct(term, "?").Deconstruct(out var arg, out var error))
            return error;
        
        if (!arg.TryDeconstructAbs().Deconstruct(out var param, out var abs, out error))
            return error;

        var uniqueThm = ChangeToUniqueVariables(ExistsIndependentOfVariableTheorem, UsedNames(term),
            new Dictionary<string, string>
            {
                ["x"] = param.DeconstructVar().name
            }); // |- ! s . (? y . s) = s
        
        return TrySpecialise(uniqueThm, abs); // |- (? y . s) = s
    }
    
    public static Theorem ExistsIndependentOfVar(Term term)
    {
        return (Theorem) TryExistsIndependentOfVar(term);
    }
}