using ValiantBasics;
using ValiantProofVerifier;
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
        
        ExistsDefinition = NewBasicDefinition(Parse(@"? = \p . !q . (!x . p x -> q) -> q")); //:fun :fun 'a :bool    :bool
        Parser.RegisterLambdaRule("?", "?");
        
        ExistsWitnessTheorem = ConstructExistsWitnessTheorem();
    }
    
    public static Theorem ExistsDefinition { get; }
    public static Theorem ExistsWitnessTheorem { get; } // f t |- ? x . f x

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

        var wtp = ApplyUnaryDefinition(ExistsDefinition, existsLambda); // |- ? x . f x = ...
        return ModusPonens(Commutativity(wtp), generalised); // f t |- ? x . f x
    }

    /*public static Result<Theorem> TryExists2(Term existsLambda, Theorem witness)
    {
        if (!existsLambda.TryDeconstructAbs().Deconstruct(out var param, out var abs, out var error))
            return error;
        
        if (abs.TypeOf() != BoolTy)
            return "exists lambda must return type bool";
        
        var (paramName, paramTy) = param.DeconstructVar();

        var defn = ExistsWitnessTheorem;
        
        var fName = "f";

        if (paramName == fName)
        {
            fName = "g";
            defn = InstantiateVariables(new Dictionary<Term, Term>
            {
                [Parse("f :fun 'a :bool")] = Parse("g :fun 'a :bool")
            }, defn);
        }

        var typed = InstantiateTypes(new Dictionary<Type, Type>
        {
            [MakeType("a")] = paramTy
        }, defn); // f t |- ? x . f x

        var lambda = UnaryArgument(typed); // \ x . f x
        var lambdaType = lambda.TypeOf();

        if (paramName != "x")
        {
            var changedVar = EtaReductionTheorems.ChangeLambdaVariable(lambda, param); // \ x . f x = \y . f y
            var forAll = Congruence(Reflexivity(MakeConstant("?", new Dictionary<Type, Type>
            {
                [MakeType("a")] = lambdaType
            })), changedVar); // ? x . f x = ? y . f y
            
            typed = ModusPonens(forAll, typed); // f t |- ? y . f y
        }
        
        if (!TryInstantiateVariables(new Dictionary<Term, Term>
            {
                [MakeVariable(fName, lambdaType)] = abs,
                [MakeVariable("t", paramTy)] = witness
            }))
    }*/

    public static Result<Theorem> TryExists(Term existsLambda, Theorem witness)
    {
        if (!existsLambda.TryDeconstructAbs().Deconstruct(out var param, out var abs, out var error))
            return error;
        
        if (!TryGenerateMaps(abs, witness.Conclusion()).Deconstruct(out var typeMap, out var termMap, out error))
            return "Witness is not an example of the lambda";
        
        if (typeMap.Any())
            return "Type mismatch";
        
        if (termMap.Count > 2 || (termMap.Count == 1 && termMap.First().Key != param))
            return "Witness is not an example of the lambda";

        var qName = GetFreeVariableName(new[] { existsLambda, witness.Conclusion() });
        
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

        var pName = GetFreeVariableName(new []{existsLambda, witness.Conclusion(), q});
        
        var existsEq = LambdaEquivalence(ExistsDefinition.Conclusion(), Parse(@$"""?"" = \{pName} . !{qName} . (!{param} . {pName} {param} -> {qName}) -> {qName}"));
        var existsDefinition = ModusPonens(existsEq, ExistsDefinition); // |- ? x . f x = \x . f x
        var wtp = ApplyUnaryDefinition(existsDefinition, existsLambda); // |- ? x . f x = ...
        return ModusPonens(Commutativity(wtp), generalised);
    }

    public static Theorem Exists(Term existsLambda, Theorem witness)//given \x . f x & |- f t then ? x . f x
    {
        return TryExists(existsLambda, witness).ValueOrException();
    }
}