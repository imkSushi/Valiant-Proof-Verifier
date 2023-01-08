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
    
    public static Result TryDefineType(string name, int arity)
    {
        return Kernel.TryDefineType(name, arity) ? Result.Success : $"Type {name} already exists";
    }
    
    public static Result<int> TryGetArity(string name, [MaybeNullWhen(false)] out int arity)
    {
        return Kernel.TryGetArity(name, out arity) ? arity : $"Type {name} does not exist";
    }
    
    public static void DefineConstant(string name, Type type)
    {
        Kernel.DefineConstant(name, type);
    }
    
    public static Result TryDefineConstant(string name, Type type)
    {
        return Kernel.TryDefineConstant(name, type) ? Result.Success: $"Constant {name} already exists";
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

    public static Result<Theorem> TryCongruence(Theorem applications, Theorem arguments)
    {
        try
        {
            return Kernel.Congruence(applications, arguments);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem Abstraction(Term variable, Theorem theorem) // s = t |- (\x . s) = (\x . t)
    {
        return Kernel.Abstraction(variable, theorem);
    }
    
    public static Result<Theorem> TryAbstraction(Term variable, Theorem theorem)
    {
        try
        {
            return Kernel.Abstraction(variable, theorem);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem BetaReduction(Term term) // (\x . t) x = t
    {
        return Kernel.BetaReduction(term);
    }
    
    public static Result<Theorem> TryBetaReduction(Term term)
    {
        try
        {
            return Kernel.BetaReduction(term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem Assume(Term term) //Replaceable by x |- x given INST
    {
        return Kernel.Assume(term);
    }
    
    public static Result<Theorem> TryAssume(Term term)
    {
        try
        {
            return Kernel.Assume(term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem ModusPonens(Theorem major, Theorem minor) //Replaceable by x = y, x |- y given INST
    {
        return Kernel.ModusPonens(major, minor);
    }
    
    public static Result<Theorem> TryModusPonens(Theorem major, Theorem minor)
    {
        try
        {
            return Kernel.ModusPonens(major, minor);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem AntiSymmetry(Theorem left, Theorem right)
    {
        return Kernel.AntiSymmetry(left, right);
    }
    
    public static Result<Theorem> TryAntiSymmetry(Theorem left, Theorem right)
    {
        try
        {
            return Kernel.AntiSymmetry(left, right);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Theorem InstantiateVariables(Dictionary<Term, Term> map, Theorem theorem)
    {
        return Kernel.InstantiateVariables(map, theorem);
    }
    
    public static Result<Theorem> TryInstantiateVariables(Dictionary<Term, Term> map, Theorem theorem)
    {
        try
        {
            return Kernel.InstantiateVariables(map, theorem);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Theorem InstantiateTypes(Dictionary<Type, Type> map, Theorem theorem)
    {
        return Kernel.InstantiateTypes(map, theorem);
    }
    
    public static Result<Theorem> TryInstantiateTypes(Dictionary<Type, Type> map, Theorem theorem)
    {
        try
        {
            return Kernel.InstantiateTypes(map, theorem);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Term InstantiateVariables(Dictionary<Term, Term> map, Term term)
    {
        return Kernel.InstantiateVariables(map, term);
    }
    
    public static Result<Term> TryInstantiateVariables(Dictionary<Term, Term> map, Term term)
    {
        try
        {
            return Kernel.InstantiateVariables(map, term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Term InstantiateTypes(Dictionary<Type, Type> map, Term term)
    {
        return Kernel.InstantiateTypes(map, term);
    }
    
    public static Result<Term> TryInstantiateTypes(Dictionary<Type, Type> map, Term term)
    {
        try
        {
            return Kernel.InstantiateTypes(map, term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Type InstantiateTypes(Dictionary<Type, Type> map, Type type)
    {
        return Kernel.InstantiateTypes(map, type);
    }
    
    public static Result<Type> TryInstantiateTypes(Dictionary<Type, Type> map, Type type)
    {
        try
        {
            return Kernel.InstantiateTypes(map, type);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Term Variant(Term variable, Term[] avoid)
    {
        return Kernel.Variant(variable, avoid);
    }
    
    public static Result<Term> TryVariant(Term variable, Term[] avoid)
    {
        try
        {
            return Kernel.Variant(variable, avoid);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static bool IsVariableFree(Term variable, Term term)
    {
        return Kernel.IsVariableFree(variable, term);
    }

    public static Result<Term, Term> TryDeconstructEquality(Term term) //left, right
    {
        return Kernel.TryDeconstructEquality(term, out var left, out var right) ? (left, right) : $"Term is not an equality: {term}";
    }

    public static Type TypeOf(this Term term)
    {
        return Kernel.TypeOf(term);
    }
    
    public static Type MakeType(string name, Type[] args)
    {
        return Kernel.MakeType(name, args);
    }
    
    public static Result<Type> TryMakeType(string name, Type[] args)
    {
        return Kernel.TryMakeType(name, args, out var type, out var error) ? type : error;
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
    
    public static Result<Term> TryMakeConstant(string name, Dictionary<Type, Type> map)
    {
        try 
        {
            return Kernel.MakeConstant(name, map);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Term MakeConstant(string name)
    {
        return Kernel.MakeConstant(name);
    }
    
    public static Result<Term> TryMakeConstant(string name)
    {
        try 
        {
            return Kernel.MakeConstant(name);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static Term MakeCombination(Term application, Term argument)
    {
        return Kernel.MakeCombination(application, argument);
    }
    
    public static Result<Term> TryMakeCombination(Term application, Term argument)
    {
        return Kernel.TryMakeCombination(application, argument, out var result, out var error) ? result : error;
    }

    public static Term MakeAbstraction(Term parameter, Term abstraction)
    {
        return Kernel.MakeAbstraction(parameter, abstraction);
    }
    
    public static Result<Term> TryMakeAbstraction(Term parameter, Term abstraction)
    {
        try 
        {
            return Kernel.MakeAbstraction(parameter, abstraction);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static (string name, Type[] args) DeconstructTyApp(this Type type)
    {
        return Kernel.DeconstructTyApp(type);
    }

    public static Type[] DeconstructTyApp(this Type type, string expectedName)
    {
        return type.TryDeconstructTyApp(expectedName).ValueOrException();
    }
    
    public static Result<string, Type[]> TryDeconstructTyApp(this Type type) // name & args
    {
        if (type.IsTyApp())
            return Kernel.DeconstructTyApp(type);
        
        return $"Type is not a type application: {type}";
    }

    public static Result<Type[]> TryDeconstructTyApp(this Type type, string expectedName)
    {
        if (!type.TryDeconstructTyApp().Deconstruct(out var name, out var args, out var error))
            return error;
        
        if (name != expectedName)
            return $"Expected type application of {expectedName}, but got {name}";
        
        return args;
    }

    public static string DeconstructTyVar(this Type type)
    {
        return Kernel.DeconstructTyVar(type);
    }
    
    public static StringResult TryDeconstructTyVar(this Type type)
    {
        if (type.IsTyVar())
            return (true, Kernel.DeconstructTyVar(type));
        
        return (false, $"Type is not a type variable: {type}");
    }
    
    public static (string name, Type type) DeconstructVar(this Term term)
    {
        return Kernel.DeconstructVar(term);
    }
    
    public static Result<string, Type> TryDeconstructVar(this Term term) //name & type
    {
        if (term.IsVar())
            return Kernel.DeconstructVar(term);
        
        return $"Term is not a variable: {term}";
    }
    
    public static (string name, Type type) DeconstructConst(this Term term)
    {
        return Kernel.DeconstructConst(term);
    }
    
    public static Result<string, Type> TryDeconstructConst(this Term term) //name & type
    {
        if (term.IsConst())
            return Kernel.DeconstructConst(term);
        
        return $"Term is not a constant: {term}";
    }
    
    public static (Term application, Term argument) DeconstructComb(this Term term)
    {
        return Kernel.DeconstructComb(term);
    }
    
    public static Result<Term, Term> TryDeconstructComb(this Term term) //application & argument
    {
        if (term.IsComb())
            return Kernel.DeconstructComb(term);
        
        return $"Term is not a combination: {term}";
    }
    
    public static (Term parameter, Term abstraction) DeconstructAbs(this Term term)
    {
        return Kernel.DeconstructAbs(term);
    }
    
    public static Result<Term, Term> TryDeconstructAbs(this Term term) //parameter & abstraction
    {
        if (term.IsAbs())
            return Kernel.DeconstructAbs(term);
        
        return $"Term is not an abstraction: {term}";
    }

    public static Theorem NewAxiom(Term term)
    {
        return Kernel.NewAxiom(term);
    }
    
    public static Result<Theorem> TryNewAxiom(Term term)
    {
        try
        {
            return Kernel.NewAxiom(term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Theorem[] Axioms => Kernel.Axioms;
    
    public static Theorem[] Definitions => Kernel.Definitions;

    public static Theorem NewBasicDefinition(Term term)
    {
        return Kernel.NewBasicDefinition(term);
    }
    
    public static Result<Theorem> TryNewBasicDefinition(Term term)
    {
        try
        {
            return Kernel.NewBasicDefinition(term);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static (Theorem constructor, Theorem deconstructor) NewBasicTypeDefinition(string name,
        string constructorName,
        string deconstructorName,
        Theorem basis)
    {
        return Kernel.NewBasicTypeDefinition(name, constructorName, deconstructorName, basis);
    }
    
    public static Result<Theorem, Theorem> TryNewBasicTypeDefinition(string name,
        string constructorName,
        string deconstructorName,
        Theorem basis) //constructor & deconstructor
    {
        try
        {
            return Kernel.NewBasicTypeDefinition(name, constructorName, deconstructorName, basis);
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public static bool AllFreesIn(HashSet<Term> allowableFrees, Term term)
    {
        return Kernel.AllFreesIn(allowableFrees, term);
    }
    
    public static HashSet<string> GetConstantsList() => Kernel.GetConstantsList();

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
    
    public static Result<Type> TryGetConstantType(string name)
    {
        return Kernel.TryGetConstantType(name, out var type) ? type : $"Constant {name} not found";
    }
    
    public static (HashSet<Term> premises, Term conclusion) Deconstruct(this Theorem theorem)
    {
        return Kernel.DeconstructTheorem(theorem);
    }

    public static HashSet<Term> Premises(this Theorem theorem)
    {
        return theorem.Deconstruct().premises;
    }
    
    public static Term Conclusion(this Theorem theorem)
    {
        return theorem.Deconstruct().conclusion;
    }

    public static bool IsTyVar(this Type type)
    {
        return Kernel.IsTyVar(type);
    }
    
    public static bool IsTyApp(this Type type)
    {
        return Kernel.IsTyApp(type);
    }
    
    public static bool IsVar(this Term term)
    {
        return Kernel.IsVar(term);
    }
    
    public static bool IsConst(this Term term)
    {
        return Kernel.IsConst(term);
    }
    
    public static bool IsComb(this Term term)
    {
        return Kernel.IsComb(term);
    }
    
    public static bool IsAbs(this Term term)
    {
        return Kernel.IsAbs(term);
    }
}