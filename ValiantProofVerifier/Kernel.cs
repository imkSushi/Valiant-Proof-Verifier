using System.Diagnostics.CodeAnalysis;
using static ValiantProofVerifier.Term;
using static ValiantProofVerifier.Theorem;
using static ValiantProofVerifier.Type;

namespace ValiantProofVerifier;

public sealed class Kernel
{
    private Dictionary<string, int> _types; //name & arity
    private Dictionary<string, Type> _constants ; //name & term
    private HashSet<Theorem> _axioms;
    private HashSet<Theorem> _definitions;

    public Kernel()
    {
        _types = new Dictionary<string, int>
        {
            ["bool"] = 0,
            ["fun"] = 2
        };
        _constants = new Dictionary<string, Type>
        {
            ["="] = new TyApp("fun", new[] {Aty, new TyApp("fun", new[] {Aty, BoolTy})})
        };

        _axioms = new HashSet<Theorem>();
        _definitions = new HashSet<Theorem>();
    }
    
    public static Type BoolTy => new TyApp("bool", Array.Empty<Type>());
    public static Type Aty => new TyVar("A");
    
    public HashSet<string> GetConstantsList() => new(_constants.Keys);

    public void DefineType(string name, int arity)
    {
        if (_types.ContainsKey(name))
            throw new TheoremException($"Type {name} already defined");
        _types.Add(name, arity);
    }

    public bool TryDefineType(string name, int arity)
    {
        if (_types.ContainsKey(name))
            return false;
        _types.Add(name, arity);
        return true;
    }
    
    public bool TryGetArity(string name, [MaybeNullWhen(false)] out int arity)
    {
        return _types.TryGetValue(name, out arity);
    }
    
    public void DefineConstant(string name, Type type)
    {
        if (_constants.ContainsKey(name))
            throw new TheoremException($"Constant {name} already defined");
        _constants.Add(name, type);
    }
    
    public bool TryDefineConstant(string name, Type type)
    {
        if (_constants.ContainsKey(name))
            return false;
        _constants.Add(name, type);
        return true;
    }
    
    public bool ConstantExists(string name)
    {
        return _constants.ContainsKey(name);
    }

    public Theorem Reflexivity(Term term) //Replaceable by |- x = x given INST & INST_TYPE
    {
        return new Sequent(SafeMakeEquality(term, term));
    }

    public Theorem Congruence(Theorem applications, Theorem arguments) //Replaceable by f = g, x = y |- f x = g y given INST & INST_TYPE
    {
        var applicationsSeq = (Sequent) applications;
        var argumentsSeq = (Sequent) arguments;
        
        if (!TryDeconstructEquality(applicationsSeq.Conclusion, out var leftApp, out var rightApp))
            throw new TheoremException("Applications theorem is not an equality");
        if (!TryDeconstructEquality(argumentsSeq.Conclusion, out var leftArg, out var rightArg))
            throw new TheoremException("Arguments theorem is not an equality");
        
        var appType = TypeOf(leftApp);
        if (appType is not TyApp("fun", [var desiredArgType, _]))
            throw new TheoremException("Applications are not a function");
        var argType = TypeOf(leftArg);
        if (argType != desiredArgType)
            throw new TheoremException("Arguments do not match the functions' argument type");
        
        return new Sequent(applicationsSeq.Premises.Concat(argumentsSeq.Premises), SafeMakeEquality(new Comb(leftApp, leftArg), new Comb(rightApp, rightArg)));
    }

    public Theorem Abstraction(Term variable, Theorem theorem) // s = t |- (\x . s) = (\x . t)
    {
        var seq = (Sequent) theorem;
        if (variable is not Var)
            throw new TheoremException("Variable is not a variable");
        if (!TryDeconstructEquality(seq.Conclusion, out var left, out var right))
            throw new TheoremException("Theorem is not an equality");
        if (seq.Premises.Any(premise => IsVariableFree(variable, premise)))
            throw new TheoremException("Variable is free in premises");
        return new Sequent(seq.Premises, SafeMakeEquality(new Abs(variable, left), new Abs(variable, right)));
    }
    
    public Theorem BetaReduction(Term term) // (\x . t) x = t
    {
        if (term is not Comb {Application: Abs {Parameter: var parameter, Abstraction: var abstraction}, Argument: var argument} || parameter != argument)
            throw new TheoremException("Term is not a beta reduction");
        
        return new Sequent(Array.Empty<Term>(), SafeMakeEquality(term, abstraction));
    }

    public Theorem Assume(Term term) //Replaceable by x |- x given INST
    {
        if (TypeOf(term) != BoolTy)
            throw new TheoremException("Term is not a boolean");
        
        return new Sequent(term, term);
    }

    public Theorem ModusPonens(Theorem major, Theorem minor) //Replaceable by x = y, x |- y given INST
    {
        var majorSeq = (Sequent) major;
        var minorSeq = (Sequent) minor;
        
        if (!TryDeconstructEquality(majorSeq.Conclusion, out var left, out var right))
            throw new TheoremException("Major theorem is not an equality");
        
        if (left != minorSeq.Conclusion)
            throw new TheoremException("Minor theorem does not match the major theorem's left side");
        
        return new Sequent(majorSeq.Premises.Concat(minorSeq.Premises), right);
    }

    public Theorem AntiSymmetry(Theorem left, Theorem right)
    {
        var leftSeq = (Sequent) left;
        var rightSeq = (Sequent) right;

        var leftPremises = leftSeq.Premises.Where(premise => premise != rightSeq.Conclusion);
        var rightPremises = rightSeq.Premises.Where(premise => premise != leftSeq.Conclusion);
        
        return new Sequent(leftPremises.Concat(rightPremises), SafeMakeEquality(leftSeq.Conclusion, rightSeq.Conclusion));
    }

    public Theorem InstantiateVariables(Dictionary<Term, Term> map, Theorem theorem)
    {
        var seq = (Sequent) theorem;
        
        return new Sequent(seq.Premises.Select(premise => InstantiateVariables(map, premise)), InstantiateVariables(map, seq.Conclusion));
    }
    
    public Theorem InstantiateTypes(Dictionary<Type, Type> map, Theorem theorem)
    {
        var seq = (Sequent) theorem;
        
        return new Sequent(seq.Premises.Select(premise => InstantiateTypes(map, premise)), InstantiateTypes(map, seq.Conclusion));
    }
    
    public static Term InstantiateVariables(Dictionary<Term, Term> map, Term term)
    {
        foreach (var (variable, value) in map)
        {
            if (variable is not Var {Type: var type})
                throw new TheoremException("Bad substitution map: invalid variable");
            
            if (type != TypeOf(value))
                throw new TheoremException("Bad substitution map: variable and value types do not match");
        }

        return SafeInstantiateVariables(map, term);
    }
    
    public static Term InstantiateTypes(Dictionary<Type, Type> map, Term term)
    {
        foreach (var (varType, _) in map)
        {
            if (varType is not TyVar)
                throw new TheoremException("Bad substitution map: invalid type variable");
        }
        
        return SafeInstantiateTypes(map, term);
    }
    
    public static Type InstantiateTypes(Dictionary<Type, Type> map, Type type)
    {
        return type switch
        {
            TyVar varType => map.TryGetValue(varType, out var result) ? result : varType,
            TyApp { Name: var name, Args: var arguments } => new TyApp(name,
                arguments.Select(arg => InstantiateTypes(map, arg)).ToArray()),
            _ => throw new TheoremException("Bad substitution map: invalid type")
        };
    }

    private static Term SafeInstantiateTypes(Dictionary<Type, Type> map, Term term)
    {
        switch (term)
        {
            case Var { Name: var name, Type: var type }:
                return new Var(name, SafeTypeSubstitution(map, type));
            case Const { Name: var name, Type: var type }:
                return new Const(name, SafeTypeSubstitution(map, type));
            case Comb { Application: var application, Argument: var argument }:
                return new Comb(SafeInstantiateTypes(map, application), SafeInstantiateTypes(map, argument));
            case Abs { Parameter: var parameter, Abstraction: var abstraction }:
            {
                /*
                var frees = FreesIn(term).ToArray();
                var mappedFrees = frees.Select(free => SafeInstantiateTypes(map, free)).Concat(frees).Distinct().ToArray();
                var potentialNewParameter = SafeInstantiateTypes(map, parameter);
                var newParameter = Variant(potentialNewParameter, mappedFrees);
                var subbedAbstraction = SafeInstantiateVariables(new Dictionary<Term, Term>
                {
                    [parameter] = newParameter
                }, abstraction);
                return new Abs(newParameter, SafeInstantiateTypes(map, subbedAbstraction));*/
                return new Abs(SafeInstantiateTypes(map, parameter), SafeInstantiateTypes(map, abstraction));
            }
            default:
                throw new TheoremException("Bad term");
        }
    }

    private static IEnumerable<Term> FreesIn(Term term)
    {
        return term switch
        {
            Var   => new[] { term },
            Const => Array.Empty<Term>(),
            Comb { Application: var application, Argument: var argument } => FreesIn(application)
                .Concat(FreesIn(argument)).Distinct(),
            Abs { Parameter: var parameter, Abstraction: var abstraction } => FreesIn(abstraction)
                .Where(free => free != parameter),
            _ => throw new TheoremException("Bad term")
        };
    }

    private static Type SafeTypeSubstitution(Dictionary<Type, Type> map, Type type)
    {
        return type switch
        {
            TyVar varType => map.TryGetValue(varType, out var result) ? result : varType,
            TyApp appType => new TyApp(appType.Name, appType.Args.Select(arg => SafeTypeSubstitution(map, arg)).ToArray()),
            _             => throw new TheoremException("Bad type")
        };
    }
    
    private static Term SafeInstantiateVariables(Dictionary<Term, Term> map, Term term)
    {
        switch (term)
        {
            case Var:
                return map.TryGetValue(term, out var value) ? value : term;
            case Const:
                return term;
            case Comb {Application: var application, Argument: var argument}:
                return new Comb(SafeInstantiateVariables(map, application), SafeInstantiateVariables(map, argument));
            case Abs { Parameter: var parameter, Abstraction: var abstraction }:
            {
                var newMap = map.ToDictionary(kv => kv.Key, kv => kv.Value);
                newMap.Remove(parameter);

                var newAbstraction = SafeInstantiateVariables(newMap, abstraction);
                if (!newMap.Any(tuple =>
                        IsVariableFree(parameter, tuple.Value) && IsVariableFree(tuple.Key, abstraction)))
                    return new Abs(parameter, newAbstraction);
                
                var newParameter = Variant(parameter, new []{newAbstraction});
                newMap[parameter] = newParameter;
                return new Abs(newParameter, SafeInstantiateVariables(newMap, newAbstraction));
            }
            default:
                throw new TheoremException("Invalid term");
        }
    }

    public static Term Variant(Term variable, Term[] avoid)
    {
        if (variable is not Var {Name: var name, Type: var type})
            throw new TheoremException("Variable is not a variable");
        return avoid.Any(term => IsVariableFree(variable, term)) ? Variant(new Var($"{name}'", type), avoid) : variable;
    }

    public static bool IsVariableFree(Term variable, Term term)
    {
        return term switch
        {
            Abs { Abstraction: var abstraction, Parameter: var parameter } => parameter != variable &&
                IsVariableFree(variable, abstraction),
            Comb { Application: var application, Argument: var argument } => IsVariableFree(variable, application) ||
                IsVariableFree(variable, argument),
            Var   => variable == term,
            Const => false,
            _     => throw new TheoremException("Term is invalid")
        };
    }

    public static bool TryDeconstructEquality(Term term,
        [MaybeNullWhen(false)] out Term left,
        [MaybeNullWhen(false)] out Term right)
    {
        if (term is Comb {Application: Comb {Application: Const {Name: "="}, Argument: var leftOutput}, Argument: var rightOutput})
        {
            left = leftOutput;
            right = rightOutput;
            return true;
        }
        
        left = null;
        right = null;
        return false;
    }

    private Term SafeMakeEquality(Term left, Term right)
    {
        var type = TypeOf(left);
        return new Comb(new Comb(new Const("=", new TyApp("fun", new []{type, new TyApp("fun", new []{type, BoolTy})})), left), right);
    }

    public static Type TypeOf(Term term)
    {
        return term switch
        {
            Var { Type: var type }   => type,
            Const { Type: var type } => type,
            Abs { Abstraction: var abstraction, Parameter: Var { Type: var parameterType } } => new TyApp("fun",
                new[] { parameterType, TypeOf(abstraction) }),
            Comb { Application: var application } when TypeOf(application) is TyApp { Name: "fun", Args: [_, var type] }
                => type,
            _ => throw new TheoremException("Invalid term")
        };
    }
    
    public Type MakeType(string name, Type[] args)
    {
        if (!_types.TryGetValue(name, out var arity))
            throw new TheoremException("Type does not exist");
        if (args.Length != arity)
            throw new TheoremException("Invalid number of arguments");
        return new TyApp(name, args);
    }
    
    public bool TryMakeType(string name, Type[] args, [MaybeNullWhen(false)] out Type type, [MaybeNullWhen(true)] out string error)
    {
        if (!_types.TryGetValue(name, out var arity))
        {
            type = null;
            error = "Type does not exist";
            return false;
        }
        if (args.Length != arity)
        {
            type = null;
            error = "Invalid number of arguments";
            return false;
        }
        type = new TyApp(name, args);
        error = null;
        return true;
    }

    public Type MakeType(string name)
    {
        return new TyVar(name);
    }
    
    public Term MakeVariable(string name, Type type)
    {
        return new Var(name, type);
    }
    
    public Term MakeConstant(string name, Dictionary<Type, Type> map)
    {
        if (!_constants.TryGetValue(name, out var type))
            throw new TheoremException("Constant does not exist");
        return new Const(name, SafeTypeSubstitution(map, type));
    }

    public Term MakeConstant(string name)
    {
        return MakeConstant(name, new Dictionary<Type, Type>());
    }
    
    public Term MakeCombination(Term application, Term argument)
    {
        if (!TryMakeCombination(application, argument, out var result, out var error))
            throw new TheoremException(error);
        
        return result;
    }
    
    public bool TryMakeCombination(Term application, Term argument, [MaybeNullWhen(false)] out Term result, [MaybeNullWhen(true)] out string error)
    {
        if (TypeOf(application) is not TyApp {Name: "fun", Args: [var argumentType, _]})
        {
            error = "Application is not a function";
            result = null;
            return false;
        }

        if (argumentType != TypeOf(argument))
        {
            error = "Argument type does not match function argument type";
            result = null;
            return false;
        }
        result = new Comb(application, argument);
        error = null;
        return true;
    }

    public Term MakeAbstraction(Term parameter, Term abstraction)
    {
        if (parameter is not Var)
            throw new TheoremException("Parameter is not a variable");
        return new Abs(parameter, abstraction);
    }
    
    public static (string name, Type[] args) DeconstructTyApp(Type type)
    {
        if (type is TyApp {Name: var name, Args: var args})
            return (name, args);
        throw new TheoremException("Type is not a type application");
    }
    
    public static string DeconstructTyVar(Type type)
    {
        if (type is TyVar {Name: var name})
            return name;
        throw new TheoremException("Type is not a type variable");
    }
    
    public static (string name, Type type) DeconstructVar(Term term)
    {
        if (term is Var {Name: var name, Type: var type})
            return (name, type);
        throw new TheoremException("Term is not a variable");
    }
    
    public static (string name, Type type) DeconstructConst(Term term)
    {
        if (term is Const {Name: var name, Type: var type})
            return (name, type);
        throw new TheoremException("Term is not a constant");
    }
    
    public static (Term application, Term argument) DeconstructComb(Term term)
    {
        if (term is Comb {Application: var application, Argument: var argument})
            return (application, argument);
        throw new TheoremException("Term is not a combination");
    }
    
    public static (Term parameter, Term abstraction) DeconstructAbs(Term term)
    {
        if (term is Abs {Parameter: var parameter, Abstraction: var abstraction})
            return (parameter, abstraction);
        throw new TheoremException("Term is not an abstraction");
    }

    public Theorem NewAxiom(Term term)
    {
        if (TypeOf(term) != BoolTy)
            throw new TheoremException("Term is not a proposition");

        var thm = new Sequent(term);
        _axioms.Add(thm);
        return thm;
    }
    
    public Theorem[] Axioms => _axioms.ToArray();
    
    public Theorem[] Definitions => _definitions.ToArray();

    public Theorem NewBasicDefinition(Term term)
    {
        if (term is not Comb {Application: Comb {Application: Const {Name: "="}, Argument: Var {Name: var name, Type: var type}}, Argument: var right})
            throw new TheoremException("Term is not an equality");
        if (!AllFreesIn(new HashSet<Term>(), right))
            throw new TheoremException("Term is not closed");
        var leftTypes = TypesIn(type).ToHashSet();
        var rightTypes = TypesIn(right);
        if (rightTypes.Any(t => !leftTypes.Contains(t)))
            throw new TheoremException("Term is not fully-typed");
        
        DefineConstant(name, type);
        var c = new Const(name, type);
        var thm = new Sequent(SafeMakeEquality(c, right));
        _definitions.Add(thm);
        return thm;
    }

    public (Theorem constructor, Theorem deconstructor) NewBasicTypeDefinition(string name,
        string constructorName,
        string deconstructorName,
        Theorem basis)
    {
        if (_constants.ContainsKey(constructorName) || _constants.ContainsKey(deconstructorName))
            throw new TheoremException("Constant(s) already is use");
        
        var seq = (Sequent) basis;
        if (seq.Premises.Any())
            throw new TheoremException("Basis has premises");
        
        var (app, arg) = DeconstructComb(seq.Conclusion);
        if (!AllFreesIn(new HashSet<Term>(), app))
            throw new TheoremException("Basis is not closed");
        
        var types = TypesIn(arg).OrderBy(type => type.ToString()).ToArray();
        if (!TryDefineType(name, types.Length))
            throw new TheoremException("Type already defined");

        var aty = new TyApp(name, types);
        var rty = TypeOf(arg);

        var conType = new TyApp("fun", new[] { rty, aty });
        var decType = new TyApp("fun", new[] { aty, rty });
        
        DefineConstant(constructorName, conType);
        DefineConstant(deconstructorName, decType);
        
        var con = new Const(constructorName, conType);
        var dec = new Const(deconstructorName, decType);
        var a = new Var("a", aty);
        var r = new Var("r", rty);
        
        var constructor = new Sequent(SafeMakeEquality(MakeCombination(con, MakeCombination(dec, a)), a));
        var deconstructor = new Sequent(SafeMakeEquality(new Comb(app, r),
            SafeMakeEquality(MakeCombination(dec, MakeCombination(con, r)), r)));

        return (constructor, deconstructor);
    }

    public static bool AllFreesIn(HashSet<Term> allowableFrees, Term term)
    {
        switch (term)
        {
            case Var:
                return allowableFrees.Contains(term);
            case Const:
                return true;
            case Comb {Application: var application, Argument: var argument}:
                return AllFreesIn(allowableFrees, application) && AllFreesIn(allowableFrees, argument);
            case Abs {Parameter: var parameter, Abstraction: var abstraction}:
                var newAllowableFrees = new HashSet<Term>(allowableFrees) { parameter };
                return AllFreesIn(newAllowableFrees, abstraction);
            default:
                throw new TheoremException("Term is invalid");
        }
    }

    public static IEnumerable<Type> TypesIn(Type type)
    {
        return type switch
        {
            TyVar                    => new[] { type },
            TyApp { Args: var args } => args.SelectMany(TypesIn).Distinct(),
            _                        => throw new TheoremException("Type is invalid")
        };
    }

    public static IEnumerable<Type> TypesIn(Term term)
    {
        return term switch
        {
            Const { Type: var type } => TypesIn(type),
            Var { Type: var type }   => TypesIn(type),
            Comb { Application: var application, Argument: var argument } => TypesIn(application)
                .Concat(TypesIn(argument)).Distinct(),
            Abs { Parameter: Var { Type: var parameterType }, Abstraction: var abstraction } => TypesIn(parameterType)
                .Concat(TypesIn(abstraction)).Distinct(),
            _ => throw new TheoremException("Term is invalid")
        };
    }
    
    public Type GetConstantType(string name)
    {
        if (!_constants.TryGetValue(name, out var type))
            throw new TheoremException("Constant does not exist");
        return type;
    }
    
    public bool TryGetConstantType(string name, [MaybeNullWhen(false)] out Type type)
    {
        return _constants.TryGetValue(name, out type);
    }
    
    public static (HashSet<Term> premises, Term conclusion) DeconstructTheorem(Theorem theorem)
    {
        var seq = (Sequent) theorem;
        return (seq.Premises, seq.Conclusion);
    }
    
    public static bool IsTyVar(Type type)
    {
        return type is TyVar;
    }
    
    public static bool IsTyApp(Type type)
    {
        return type is TyApp;
    }
    
    public static bool IsVar(Term term)
    {
        return term is Var;
    }
    
    public static bool IsConst(Term term)
    {
        return term is Const;
    }
    
    public static bool IsComb(Term term)
    {
        return term is Comb;
    }
    
    public static bool IsAbs(Term term)
    {
        return term is Abs;
    }
}