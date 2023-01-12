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

namespace ValiantProver.Modules;

public static class OrTheorems
{
    public static void Load() { }

    static OrTheorems()
    {
        ImpliesTheorems.Load();
        ForAllTheorems.Load();
        
        TryRegisterInfixRule(@"\/", @"\/", 37, true, "∨");
        OrDefinition = NewDefinition(Parse(@"(p \/ q) = ! r . (p -> r) -> ((q -> r) -> r)"));

        OrLeft = ConstructOrLeft();
        OrRight = ConstructOrRight();
        OrCommutativityTheorem = ConstructOrCommutativityTheorem();
    }
    
    public static Theorem OrDefinition { get; }
    public static Theorem OrLeft { get; } // p |- p \/ q
    public static Theorem OrRight { get; } // q |- p \/ q
    public static Theorem OrCommutativityTheorem { get; } // ! p q . (p \/ q) = (q \/ p)

    private static Theorem ConstructOrLeft()
    {
        var p = Parse("p :bool"); // p
        var q = Parse("q :bool"); // q
        var r = Parse("r :bool"); // r

        var stuffImpliesR = GivenTheoremImpliesAnythingThenAnything(Assume(p), r); // p, p -> r |- r

        var qrr = AddImpliesAssumption(Assume(r), Parse("q -> r")); // r |- (q -> r) -> r
        
        var stuffImpliesQrr = Elimination(qrr, stuffImpliesR); // p, p -> r |- (q -> r) -> r
        
        var prqrr = Discharge(Parse("p -> r"), stuffImpliesQrr); // p |- (p -> r) -> ((q -> r) -> r)
        var generalised = Generalise(prqrr, r); // |- ! r . (p -> r) -> ((q -> r) -> r)

        return ModusPonens(Commutativity(Specialise(OrDefinition, p, q)), generalised);
    }

    private static Theorem ConstructOrRight()
    {
        var p = Parse("p :bool"); // p
        var q = Parse("q :bool"); // q
        var r = Parse("r :bool"); // r

        var stuffImpliesR = GivenTheoremImpliesAnythingThenAnything(Assume(q), r); // q, q -> r |- r
        var qrr = Discharge(Parse("q -> r"), stuffImpliesR); // q |- (q -> r) -> r
        
        var prqrr = AddImpliesAssumption(qrr, Parse("p -> r")); // q |- (p -> r) -> ((q -> r) -> r)
        var generalised = Generalise(prqrr, r); // |- ! r . (p -> r) -> ((q -> r) -> r)
        
        return ModusPonens(Commutativity(Specialise(OrDefinition, p, q)), generalised);
    }

    private static Theorem ConstructOrCommutativityTheorem()
    {
        var p = MakeVariable("p", BoolTy); // p
        var q = MakeVariable("q", BoolTy); // q

        var pImplies = Disjunct(q, Assume(p)); // p |- q \/ p
        var qImplies = Disjunct(Assume(q), p); // q |- q \/ p
        
        var disj = DisjunctCases(Assume(Parse(@"p \/ q")), pImplies, qImplies); // p \/ q |- q \/ p
        
        var disj2 = DisjunctCases(Assume(Parse(@"q \/ p")), OrRight, OrLeft); // q \/ p |- p \/ q

        var antisym = AntiSymmetry(disj2, disj); // |- p \/ q = q \/ p

        return Generalise(antisym, p, q);
    }

    public static Result<Theorem> TryDisjunct(Theorem theorem, Term term)
    {
        if (term.TypeOf() != BoolTy)
            return "Term is not a boolean";

        var conc = theorem.Conclusion();

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = conc,
            [Parse("q :bool")] = term
        }, OrLeft);

        return Elimination(inst, theorem);
    }
    
    public static Theorem Disjunct(Theorem theorem, Term term)
    {
        return (Theorem) TryDisjunct(theorem, term);
    }

    public static Result<Theorem> TryDisjunct(Term term, Theorem theorem)
    {
        if (term.TypeOf() != BoolTy)
            return "Term is not a boolean";

        var conc = theorem.Conclusion();

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = term,
            [Parse("q :bool")] = conc
        }, OrRight);

        return Elimination(inst, theorem);
    }
    
    public static Theorem Disjunct(Term term, Theorem theorem)
    {
        return (Theorem) TryDisjunct(term, theorem);
    }
    
    public static Theorem Disjunct(Theorem left, Theorem right)
    {
        var leftConc = left.Conclusion();
        var rightConc = right.Conclusion();

        var inst = InstantiateVariables(new Dictionary<Term, Term>
        {
            [Parse("p :bool")] = leftConc,
            [Parse("q :bool")] = rightConc
        }, OrLeft);

        return Elimination(inst, left, right);
    }

    public static Result<Theorem> TryDisjunctCases(Theorem orThm, Theorem thm1, Theorem thm2) // A |- t1 \/ t2, A1 |- t, A2 |- t 
    {
        var conc = thm1.Conclusion(); // t
        
        if (conc != thm2.Conclusion())
            return "The two theorems have different conclusions";
        
        if (!TryBinaryDeconstruct(orThm, @"\/").Deconstruct(out var left, out var right, out var error)) // t1, t2
            return error;

        var leftImpThm = Discharge(left, thm1); // A1 - t1 |- t1 -> t
        var rightImpThm = Discharge(right, thm2); // A2 - t2 |- t2 -> t

        var r = MakeVariable("r", BoolTy);
        var rName = "r";
        var orDefn = OrDefinition;
        if (IsVariableFree(r, left) || IsVariableFree(r, right))
        {
            rName = GetFreeVariableName(new []{left, right, MakeVariable("p", BoolTy), MakeVariable("q", BoolTy)});
            var subs = LambdaEquivalence(OrDefinition.Conclusion(),
                Parse(@$"! p q . p \/ q = ! {rName} . (p -> {rName}) -> ((q -> {rName}) -> {rName})"));
            
            orDefn = ModusPonens(subs, OrDefinition);
        }
        
        var orDefnInst = Specialise(orDefn, left, right); // |- t1 \/ t2 = ! r . (t1 -> r) -> ((t2 -> r) -> r)

        var orDefnUsage = ModusPonens(orDefnInst, orThm); // A |- ! r . (t1 -> r) -> ((t2 -> r) -> r)
        
        if (!TrySpecialise(orDefnUsage, conc).Deconstruct(out var specialised, out error)) // A |- (t1 -> t) -> ((t2 -> t) -> t)
            return error;

        var mp = ApplyModusPonens(specialised, leftImpThm); // A + (A1 - t1) |- (t2 -> t) -> t

        return ApplyModusPonens(mp, rightImpThm); // A + (A1 - t1) + (A2 - t2) |- t
    }
    
    public static Theorem DisjunctCases(Theorem orThm, Theorem thm1, Theorem thm2) // A |- t1 \/ t2, A1 |- t, A2 |- t 
    {
        return (Theorem) TryDisjunctCases(orThm, thm1, thm2);
    }

    public static Result<Theorem> TryOrCommutativity(Theorem theorem)
    {
        if (!TryBinaryDeconstruct(theorem, @"/\").Deconstruct(out var left, out var right, out var error))
            return error;
        
        var com = Specialise(OrCommutativityTheorem, left, right); // |- p \/ q = q \/ p
        
        return ModusPonens(com, theorem);
    }
    
    public static Theorem OrCommutativity(Theorem theorem)
    {
        return (Theorem) TryOrCommutativity(theorem);
    }
}