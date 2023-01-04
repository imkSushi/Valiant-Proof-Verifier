using System.Diagnostics.CodeAnalysis;
using ValiantBasics;
using ValiantParser;
using ValiantProofVerifier;

namespace ValiantProver.Modules;

public static class Theory
{
    public static void Load() { }
    private static Kernel Kernel { get; }
    public static Parser Parser { get; }

    static Theory()
    {
        Kernel = new Kernel();
        Parser = new Parser(Kernel);
    }
    
    public static Term Parse(string term)
    {
        return Parser.ParseTerm(term);
    }
    
    public static Result<Term> TryParse(string term)
    {
        return Parser.TryParseTerm(term);
    }
    
    public static Type BoolTy => Kernel.BoolTy;
    public static Type Aty => Kernel.Aty;

    public static void DefineType(string name, int arity)
    {
        Kernel.DefineType(name, arity);
    }
    
    public static bool TryDefineType(string name, int arity)
    {
        return Kernel.TryDefineType(name, arity);
    }
    
    public static bool TryGetArity(string name, [MaybeNullWhen(false)] out int arity)
    {
        return Kernel.TryGetArity(name, out arity);
    }
    
    public static void DefineConstant(string name, Type type)
    {
        Kernel.DefineConstant(name, type);
    }
    
    public static bool TryDefineConstant(string name, Type type)
    {
        return Kernel.TryDefineConstant(name, type);
    }
    
    public static bool ConstantExists(string name)
    {
        return Kernel.ConstantExists(name);
    }

    public static Theorem Reflexivity(Term term) //Replaceable by |- x = x given INST & INST_TYPE
    {
        return Kernel.Reflexivity(term);
    }

    public static Theorem Congruence(Theorem applications, Theorem arguments) //Replaceable by f = g, x = y |- f x = g y given INST & INST_TYPE
    {
        return Kernel.Congruence(applications, arguments);
    }

    public static Theorem Abstraction(Term variable, Theorem theorem) // s = t |- (\x . s) = (\x . t)
    {
        return Kernel.Abstraction(variable, theorem);
    }
    
    public static Theorem BetaReduction(Term term) // (\x . t) x = t
    {
        return Kernel.BetaReduction(term);
    }

    public static Theorem Assume(Term term) //Replaceable by x |- x given INST
    {
        return Kernel.Assume(term);
    }

    public static Theorem ModusPonens(Theorem major, Theorem minor) //Replaceable by x = y, x |- y given INST
    {
        return Kernel.ModusPonens(major, minor);
    }

    public static Theorem AntiSymmetry(Theorem left, Theorem right)
    {
        return Kernel.AntiSymmetry(left, right);
    }

    public static Theorem InstantiateVariables(Dictionary<Term, Term> map, Theorem theorem)
    {
        return Kernel.InstantiateVariables(map, theorem);
    }
    
    public static Theorem InstantiateTypes(Dictionary<Type, Type> map, Theorem theorem)
    {
        return Kernel.InstantiateTypes(map, theorem);
    }
    
    public static Term InstantiateVariables(Dictionary<Term, Term> map, Term term)
    {
        return Kernel.InstantiateVariables(map, term);
    }
    
    public static Term InstantiateTypes(Dictionary<Type, Type> map, Term term)
    {
        return Kernel.InstantiateTypes(map, term);
    }
    
    public static Type InstantiateTypes(Dictionary<Type, Type> map, Type type)
    {
        return Kernel.InstantiateTypes(map, type);
    }

    public static Term Variant(Term variable, Term[] avoid)
    {
        return Kernel.Variant(variable, avoid);
    }

    public static bool IsVariableFree(Term variable, Term term)
    {
        return Kernel.IsVariableFree(variable, term);
    }

    public static bool TryDeconstructEquality(Term term,
        [MaybeNullWhen(false)] out Term left,
        [MaybeNullWhen(false)] out Term right)
    {
        return Kernel.TryDeconstructEquality(term, out left, out right);
    }

    public static Type TypeOf(Term term)
    {
        return Kernel.TypeOf(term);
    }
    
    public static Type MakeType(string name, Type[] args)
    {
        return Kernel.MakeType(name, args);
    }
    
    public static bool TryMakeType(string name, Type[] args, [MaybeNullWhen(false)] out Type type, [MaybeNullWhen(true)] out string error)
    {
        return Kernel.TryMakeType(name, args, out type, out error);
    }

    public static Type MakeType(string name)
    {
        return Kernel.MakeType(name);
    }
    
    public static Term MakeVariable(string name, Type type)
    {
        return Kernel.MakeVariable(name, type);
    }
    
    public static Term MakeConstant(string name, Dictionary<Type, Type> map)
    {
        return Kernel.MakeConstant(name, map);
    }

    public static Term MakeConstant(string name)
    {
        return Kernel.MakeConstant(name);
    }
    
    public static Term MakeCombination(Term application, Term argument)
    {
        return Kernel.MakeCombination(application, argument);
    }
    
    public static bool TryMakeCombination(Term application, Term argument, [MaybeNullWhen(false)] out Term result, [MaybeNullWhen(true)] out string error)
    {
        return Kernel.TryMakeCombination(application, argument, out result, out error);
    }

    public static Term MakeAbstraction(Term parameter, Term abstraction)
    {
        return Kernel.MakeAbstraction(parameter, abstraction);
    }
    
    public static (string name, Type[] args) DeconstructTyApp(Type type)
    {
        return Kernel.DeconstructTyApp(type);
    }
    
    public static string DeconstructTyVar(Type type)
    {
        return Kernel.DeconstructTyVar(type);
    }
    
    public static (string name, Type type) DeconstructVar(Term term)
    {
        return Kernel.DeconstructVar(term);
    }
    
    public static (string name, Type type) DeconstructConst(Term term)
    {
        return Kernel.DeconstructConst(term);
    }
    
    public static (Term application, Term argument) DeconstructComb(Term term)
    {
        return Kernel.DeconstructComb(term);
    }
    
    public static (Term parameter, Term abstraction) DeconstructAbs(Term term)
    {
        return Kernel.DeconstructAbs(term);
    }

    public static Theorem NewAxiom(Term term)
    {
        return Kernel.NewAxiom(term);
    }
    
    public static Theorem[] Axioms => Kernel.Axioms;
    
    public static Theorem[] Definitions => Kernel.Definitions;

    public static Theorem NewBasicDefinition(Term term)
    {
        return Kernel.NewBasicDefinition(term);
    }

    public static (Theorem constructor, Theorem deconstructor) NewBasicTypeDefinition(string name,
        string constructorName,
        string deconstructorName,
        Theorem basis)
    {
        return Kernel.NewBasicTypeDefinition(name, constructorName, deconstructorName, basis);
    }

    public static bool AllFreesIn(HashSet<Term> allowableFrees, Term term)
    {
        return Kernel.AllFreesIn(allowableFrees, term);
    }

    public static IEnumerable<Type> TypesIn(Type type)
    {
        return Kernel.TypesIn(type);
    }

    public static IEnumerable<Type> TypesIn(Term term)
    {
        return Kernel.TypesIn(term);
    }
    
    public static Type GetConstantType(string name)
    {
        return Kernel.GetConstantType(name);
    }
    
    public static bool TryGetConstantType(string name, [MaybeNullWhen(false)] out Type type)
    {
        return Kernel.TryGetConstantType(name, out type);
    }
    
    public static (HashSet<Term> premises, Term conclusion) DeconstructTheorem(Theorem theorem)
    {
        return Kernel.DeconstructTheorem(theorem);
    }
    
    public static bool IsTyVar(Type type)
    {
        return Kernel.IsTyVar(type);
    }
    
    public static bool IsTyApp(Type type)
    {
        return Kernel.IsTyApp(type);
    }
    
    public static bool IsVar(Term term)
    {
        return Kernel.IsVar(term);
    }
    
    public static bool IsConst(Term term)
    {
        return Kernel.IsConst(term);
    }
    
    public static bool IsComb(Term term)
    {
        return Kernel.IsComb(term);
    }
    
    public static bool IsAbs(Term term)
    {
        return Kernel.IsAbs(term);
    }
}