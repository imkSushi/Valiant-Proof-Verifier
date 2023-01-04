using ValiantProofVerifier;
using static ValiantProver.Modules.Basic;
using static ValiantProver.Modules.CommutativityTheorems;
using static ValiantProver.Modules.LambdaEvaluator;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TruthTheorems;
using static ValiantProver.Modules.TypeUtilities;

namespace ValiantProver.Modules;

public static class ForAllTheorems
{
    public static void Load() { }

    static ForAllTheorems()
    {
        LambdaEvaluator.Load();
        TruthTheorems.Load();
        
        ForAllDefinition = NewBasicDefinition(Parse(@"! = \p . p = (\x . T)"));
        Parser.RegisterLambdaRule("!", "!");
    }
    
    public static Theorem ForAllDefinition { get; }
    
    public static Theorem Specialise(Theorem theorem, Term term) //! (x . t x) and y goes to t y
    {
        var lambda = DeconstructComb(theorem).argument; // \x . t x
        var applied = Congruence(ForAllDefinition, lambda);
        var simp = EvaluateLambdas(applied); // ! (\x . t x) = ((\x . t x) = (\x . T))
        var modusPonens = ModusPonens(simp, theorem); // (\x . t x) = (\x . T)
        var inst = InstantiateTypes(new Dictionary<Type, Type>
        {
            [DeconstructTyApp(TypeOf(lambda)).args[0]] = TypeOf(term)
        }, modusPonens);
        var appliedTerm = Congruence(inst, term); // t y = T
        var commuted = Commutativity(appliedTerm); // T = t y
        return ModusPonens(commuted, Truth); // t y
    }
}