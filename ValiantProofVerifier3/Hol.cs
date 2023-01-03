/*using static ValiantProofVerifier3.Term;
using static ValiantProofVerifier3.Type;

namespace ValiantProofVerifier3;

public sealed class Hol : Kernel<Type, Term, Theorem>
{
    private Dictionary<string, int> _theTypeConstants = new Dictionary<string, int>
    {
        ["bool"] = 0,
        ["fun"] = 2
    };
    
    public override Dictionary<string, int> Types()
    {
        return _theTypeConstants.ToDictionary(kv => kv.Key, kv => kv.Value);
    }

    public override int GetTypeArity(string type)
    {
        return _theTypeConstants[type];
    }

    public override void NewType(string name, int arity)
    {
        if (_theTypeConstants.ContainsKey(name))
            throw new Exception($"Type {name} has already been declared");
        
        _theTypeConstants[name] = arity;
    }

    public override Type MakeType(string name, Type[] args)
    {
        if (!_theTypeConstants.TryGetValue(name, out var arity))
            throw new Exception($"Type {name} has not been defined");
        if (arity != args.Length)
            throw new Exception($"Type {name} has arity {arity}, but {args.Length} arguments were given");
        return new TyApp(name, args);
    }

    public override Type MakeVarType(string name)
    {
        return new TyVar(name);
    }

    public override (string name, Type[] args) DestructType(Type type)
    {
        if (type is TyApp tyApp)
            return (tyApp.Name, tyApp.Args);
        
        throw new Exception("Type is not a type application");
    }

    public override string DestructVarType(Type type)
    {
        if (type is TyVar tyVar)
            return tyVar.Name;
        
        throw new Exception("Type is not a type variable");
    }

    public override bool IsType(Type type)
    {
        return type is TyApp;
    }

    public override bool IsVarType(Type type)
    {
        return type is TyVar;
    }

    public override Type[] TyVars(Type type)
    {
        return type switch
        {
            TyApp { Args: var args } => args.SelectMany(TyVars).Distinct().ToArray(),
            TyVar                    => new[] { type },
            _                             => throw new InvalidOperationException()
        };
    }

    public override Func<Type, Type> TypeSubst(Dictionary<Type, Type> map)
    {
        Type Subst(Type type)
        {
            return type switch
            {
                TyApp tyApp => new TyApp(tyApp.Name, tyApp.Args.Select(Subst).ToArray()),
                _           => map.ContainsValue(type) ? map.First(kv => kv.Value == type).Key : type
            };
        }
        
        return Subst;
    }

    public override Type BoolTy { get; set; } = new TyApp("bool", Array.Empty<Type>());

    public override Type Aty { get; set; } = new TyVar("A");

    private Dictionary<string, Type> _theTermConstants;

    public Hol()
    {
        _theTermConstants = new Dictionary<string, Type>
        {
            ["="] = new TyApp("fun", new []{Aty, new TyApp("fun", new []{Aty, BoolTy})})
        };
    }

    public override Dictionary<string, Type> Constants()
    {
        return _theTermConstants.ToDictionary(kv => kv.Key, kv => kv.Value);
    }

    public override Type GetConstType(string name)
    {
        return _theTermConstants[name];
    }

    public override void NewConst(string name, Type type)
    {
        if (_theTermConstants.ContainsKey(name))
            throw new Exception($"Constant {name} has already been declared");
        
        _theTermConstants[name] = type;
    }

    public override Type TypeOf(Term term)
    {
        return term switch
        {
            Var { Type: var type }                                           => type,
            Const { Type: var type }                                         => type,
            Comb { Application: var application } when TypeOf(application) is TyApp { Name: "fun", Args: [_, var type] } => type,
            Abs { Parameter: var parameter, Abstraction: Var { Type: var type } } => new TyApp("fun",
                new[] { type, TypeOf(parameter) }),
            _ => throw new InvalidOperationException()
        };
    }

    public override Func<Term, int> AlphaOrder(Term term)
    {
        throw new NotImplementedException();
    }

    public override bool IsVar(Term term)
    {
        return term is Var;
    }

    public override bool IsConst(Term term)
    {
        return term is Const;
    }

    public override bool IsAbs(Term term)
    {
        return term is Abs;
    }

    public override bool IsComb(Term term)
    {
        return term is Comb;
    }

    public override Term MakeVar(string name, Type type)
    {
        return new Var(name, type);
    }

    public override Term MakeConst(string name, Dictionary<Type, Type> map)
    {
        if (!_theTermConstants.TryGetValue(name, out var type))
            throw new Exception($"Constant {name} has not been defined");

        return new Const(name, TypeSubst(map)(type));
    }

    public override Term MakeAbs(Term parameter, Term abstraction)
    {
        if (parameter is not Var)
            throw new Exception("Parameter is not a variable");
        
        return new Abs(parameter, abstraction);
    }

    public override Term MakeComb(Term application, Term argument)
    {
        if (TypeOf(application) is not TyApp {Name: "fun", Args: [var ty, _]} || ty != TypeOf(argument))
            throw new Exception("Type mismatch");

        return new Comb(application, argument);
    }

    public override (string name, Type type) DestructVar(Term term)
    {
        if (term is not Var var)
            throw new Exception("Term is not a variable");
        
        return (var.Name, var.Type);
    }

    public override (string name, Type type) DestructConst(Term term)
    {
        if (term is not Const @const)
            throw new Exception("Term is not a constant");
        
        return (@const.Name, @const.Type);
    }

    public override (Term application, Term argument) DestructComb(Term term)
    {
        if (term is not Comb comb)
            throw new Exception("Term is not a combination");
        
        return (comb.Application, comb.Argument);
    }

    public override (Term parameter, Term abstraction) DestructAbs(Term term)
    {
        if (term is not Abs abs)
            throw new Exception("Term is not an abstraction");
        
        return (abs.Parameter, abs.Abstraction);
    }

    public override Term[] Frees(Term term)
    {
        return term switch
        {
            Var   => new[] { term },
            Const => Array.Empty<Term>(),
            Abs { Parameter: var parameter, Abstraction: var abstraction } => Frees(abstraction)
                .Where(t => t != parameter).ToArray(),
            Comb { Application: var application, Argument: var argument } => Frees(application)
                .Union(Frees(argument)).ToArray(),
            _ => throw new InvalidOperationException()
        };
    }

    public override Term[] Freesl(Term[] terms)
    {
        return terms.SelectMany(Frees).Distinct().ToArray();
    }

    public override Func<Term, bool> Freesin(Term[] terms)
    {
        bool AllFreesIn(Term term)
        {
            return term switch
            {
                Var   => terms.Contains(term),
                Const => true,
                Abs { Parameter: var parameter, Abstraction: var abstraction } => Freesin(terms.Append(parameter)
                    .ToArray())(abstraction),
                Comb { Application: var application, Argument: var argument } => AllFreesIn(application) &&
                    AllFreesIn(argument),
                _ => throw new InvalidOperationException()
            };
        }
        
        return AllFreesIn;
    }

    public override Func<Term, bool> VfreeIn(Term variable)
    {
        bool IsFree(Term termToCheck)
        {
            return termToCheck switch
            {
                Abs { Parameter: var parameter, Abstraction: var abstraction } => parameter != variable && IsFree(abstraction),
                Comb { Application: var application, Argument: var argument } => IsFree(application) && IsFree(argument),
                _ => termToCheck == variable
            };
        }
        
        return IsFree;
    }

    public override Type[] TypeVarsInTerm(Term term)
    {
        return term switch
        {
            Var { Type: var type }        => TyVars(type),
            Const { Type: var type } => TyVars(type),
            Comb { Application: var application, Argument: var argument } => TypeVarsInTerm(application)
                .Union(TypeVarsInTerm(argument)).ToArray(),
            Abs { Parameter: Var { Type: var type }, Abstraction: var abstraction } => TypeVarsInTerm(
                    abstraction)
                .Union(TyVars(type)).ToArray(),
            _ => throw new InvalidOperationException()
        };
    }

    public override Func<Term, Term> Variant(Term[] terms)
    {
        Term CheckAvoidance(Term term)
        {
            if (!terms.Any(VfreeIn(term)))
                return term;
            if (term is not Var { Name: var name, Type: var type })
                throw new Exception("Term is not a variable");
            return CheckAvoidance(new Var($"{name}'", type));
        }

        return CheckAvoidance;
    }

    public override Func<Term, Term> Vsubst(Dictionary<Term, Term> map)
    {
        Term Substitute(Term term)
        {
            return term switch
            {
                Var when map.ContainsValue(term) => map.First(kv => kv.Value == term).Key,
                Var => term,
                Const => term,
                Comb { Application: var application, Argument: var argument } => MakeComb(Substitute(application),
                    Substitute(argument)),
                Abs { Parameter: var parameter, Abstraction: var abstraction } => MakeAbs(parameter,
                    Substitute(map.Where(kv => kv.Key != parameter).ToDictionary(kv => kv.Key, kv => kv.Value))),
                _ => throw new InvalidOperationException()
            };
        }
        
        return Substitute;
    }

    private Term TmpSubAbs(Dictionary<Term, Term> map, Term term)
    {
        var (application, argument) = DestructAbs(term);
        var imap = map.Where(kv => kv.Value != application).ToDictionary(kv => kv.Key, kv => kv.Value);
        if (!imap.Any())
            return term;
        var argPrime = Vsubst(imap)(argument);
        if (argPrime == argument)
            return term;
        
    }

    public override Func<Term, Term> Inst(Dictionary<Type, Type> map)
    {
        throw new NotImplementedException();
    }

    public override Term Rand(Term term)
    {
        throw new NotImplementedException();
    }

    public override Term Rator(Term term)
    {
        throw new NotImplementedException();
    }

    public override (Term, Term) DestEq(Term term)
    {
        throw new NotImplementedException();
    }
}*/