/*using static ValiantKernel.Term;
using static ValiantKernel.Theorem;
using static ValiantKernel.Type;

namespace ValiantKernel;

public sealed class Hol : Kernel<Type, Term, Theorem>
{
    private Dictionary<string, int> _types;
    private Dictionary<string, Type> _constants;

    public Hol()
    {
        _types = new Dictionary<string, int>
        {
            ["bool"] = 0,
            ["fun"] = 2
        };
        _constants = new Dictionary<string, Type>
        {
            ["="] = new TyApp("fun", new[] { ATy, new TyApp("fun", new []{ATy, BoolType})})
        };
    }
    
    private static Term[] TermUnion(IEnumerable<Term> a, IEnumerable<Term> b)
    {
        return a.Union(b).ToArray();
    }

    public override Theorem ProofTransitivity(Theorem thm1, Theorem thm2)
    {
        var seq1 = (Sequent) thm1;
        var seq2 = (Sequent) thm2;

        var (left, leftMiddle) = DecomposeEquality(seq1.Conclusion) ?? throw new Exception("ProofTransitivity: not both equations");
        var (rightMiddle, right) = DecomposeEquality(seq2.Conclusion) ?? throw new Exception("ProofTransitivity: not both equations");
        
        if (leftMiddle != rightMiddle)
            throw new Exception("ProofTransitivity: not equal");
        return new Sequent(TermUnion(seq1.Premises, seq2.Premises), SafeMakeEquality(left, right));
    }

    public override Theorem ProofCongruence(Theorem thm1, Theorem thm2)
    {
        var seq1 = (Sequent) thm1;
        var seq2 = (Sequent) thm2;
        
        var (funLeft, funRight) = DecomposeEquality(seq1.Conclusion) ?? throw new Exception("ProofCongruence: not both equations");
        var (argLeft, argRight) = DecomposeEquality(seq2.Conclusion) ?? throw new Exception("ProofCongruence: not both equations");
        
        if (TypeOf(funLeft) is not TyApp { Name: "fun", Args: [var inputType, _] })
            throw new Exception("ProofCongruence: not a function");
        
        if (inputType != TypeOf(argLeft))
            throw new Exception("ProofCongruence: types do not agree");
        
        return new Sequent(TermUnion(seq1.Premises, seq2.Premises), SafeMakeEquality(new Comb(funLeft, argLeft), new Comb(funRight, argRight)));
    }

    public override Theorem ProofAbstraction(Term term, Theorem thm)
    {
        var seq = (Sequent) thm;
        if (term is not Var v)
            throw new Exception("ProofAbstraction: not a variable");
        if (seq.Premises.Any(premise => !VarFreeIn(v, premise)))
            throw new Exception("ProofAbstraction: variable not free in premises");
        var (left, right) = DecomposeEquality(seq.Conclusion) ?? throw new Exception("ProofAbstraction: not an equation");
        
        return new Sequent(seq.Premises, SafeMakeEquality(new Abs(v, left), new Abs(v, right)));
    }

    public override Theorem ProofBetaReduction(Term term)
    {
        if (term is not Comb { Application: Abs { Parameter: var parameter, Abstraction: var abstraction} , Argument: var argument} || parameter != argument)
            throw new Exception("ProofBetaReduction: not a trivial abstraction and application");

        return new Sequent(Array.Empty<Term>(), SafeMakeEquality(term, abstraction));
    }

    public override Theorem ProofAssume(Term thm)
    {
        if (TypeOf(thm) != BoolType)
            throw new Exception("ProofAssume: not a proposition");
        
        return new Sequent(new[] {thm}, thm);
    }

    public override Theorem ProofModusPonens(Theorem maj, Theorem min)
    {
        var eq = (Sequent) maj;
        var (left, right) = DecomposeEquality(eq.Conclusion) ?? throw new Exception("ProofModusPonens: not an equation");
        
        var seq = (Sequent) min;
        
        if (seq.Conclusion != left)
            throw new Exception("ProofModusPonens: not equal");
        
        return new Sequent(TermUnion(seq.Premises, eq.Premises), right);
    }

    public override Theorem ProofDeductAntisymmetryRule(Theorem thm1, Theorem thm2)
    {
        var seq1 = (Sequent) thm1;
        var seq2 = (Sequent) thm2;
        
        var premises1 = seq1.Premises.Where(premise => premise != seq2.Conclusion);
        var premises2 = seq2.Premises.Where(premise => premise != seq1.Conclusion);
        
        return new Sequent(TermUnion(premises1, premises2), SafeMakeEquality(seq1.Conclusion, seq2.Conclusion));
    }

    private (Term left, Term right)? DecomposeEquality(Term t)
    {
        if (t is Comb {Application: Comb {Application: Const {Name: "="}, Argument: var left}, Argument: var right})
        {
            return (left, right);
        }
        return null;
    }

    public override Dictionary<string, int> GetTypes()
    {
        return _types.ToDictionary(kv => kv.Key, kv => kv.Value);
    }

    public override void NewType(string name, int arity)
    {
        if (_types.ContainsKey(name))
            throw new Exception($"Type {name} already exists");
        _types[name] = arity;
    }

    public override Type MakeType(string name, Type[] args)
    {
        if (!_types.TryGetValue(name, out var arity))
            throw new Exception($"Type {name} does not exist");
        
        if (arity != args.Length)
            throw new Exception($"Type {name} expects {arity} arguments, but {args.Length} were given");
        
        return new TyApp(name, args);
    }

    public override Type MakeVarType(string name)
    {
        return new TyVar(name);
    }

    public override (string name, Type[] args) DestType(Type type)
    {
        if (type is TyApp tyApp)
            return (tyApp.Name, tyApp.Args);
        
        throw new Exception($"Type {type} is not a type application");
    }

    public override string DestVarType(Type type)
    {
        if (type is TyVar tyVar)
            return tyVar.Name;
        
        throw new Exception($"Type {type} is not a type variable");
    }

    public override bool IsType(Type type)
    {
        return type is TyApp;
    }

    public override bool IsVarType(Type type)
    {
        return type is TyVar;
    }

    public override Type TypeOf(Term term)
    {
        return term switch {
            Abs {Parameter: Var {Type: var parameterType}, Abstraction: var abstraction}      => new TyApp("fun", new []{parameterType, TypeOf(abstraction)}),
            Comb {Application: var application} when TypeOf(application) is TyApp {Name: "fun", Args: [_, var rty]}    => rty,
            Const {Type: var type} => type,
            Var { Type: var type }      => type,
            _            => throw new InvalidOperationException()
        };
    }

    public override Type BoolType { get; } = new TyApp("bool", Array.Empty<Type>());

    public override Type ATy { get; } = new TyVar("A");
    public override Term MakeVar(string name, Type type)
    {
        return new Var(name, type);
    }

    public override Term MakeConst(string name, Dictionary<Type, Type> map)
    {
        if (!_constants.TryGetValue(name, out var type))
            throw new Exception($"Constant {name} does not exist");

        return new Const(name, SubstituteTypes(map)(type));
    }

    public override Term MakeComb(Term application, Term argument)
    {
        if (TypeOf(application) is not TyApp {Name: "fun", Args: [var inputType, _]})
            throw new Exception($"Application {application} is not a function");
        
        if (inputType != TypeOf(argument))
            throw new Exception($"Argument {argument} does not match the type of the application {application}");
        
        return new Comb(application, argument);
    }

    public override Term MakeAbs(Term parameter, Term abstraction)
    {
        if (parameter is not Var)
            throw new Exception($"Parameter {parameter} is not a variable");
        
        return new Abs(parameter, abstraction);
    }

    public override Dictionary<string, Type> GetConstants()
    {
        return _constants.ToDictionary(kv => kv.Key, kv => kv.Value);
    }

    public override void NewConstant(string name, Type type)
    {
        if (_constants.ContainsKey(name))
            throw new Exception($"Constant {name} already exists");
        
        _constants[name] = type;
    }

    public override Func<Type, Type> SubstituteTypes(Dictionary<Type, Type> map)
    {
        Type Substitute(Type type)
        {
            return type switch
            {
                TyApp { Name: var name, Args: var args } => new TyApp(name,
                    args.Select(Substitute).ToArray()),
                TyVar tyVar => map.TryGetValue(tyVar, out var output) ? output : tyVar,
                _           => throw new InvalidOperationException()
            };
        }
        
        return Substitute;
    }

    public override Term[] Frees(Term term)
    {
        return term switch
        {
            Var   => new[] { term },
            Const => Array.Empty<Term>(),
            Comb { Application: var application, Argument: var argument } => TermUnion(Frees(application),
                Frees(argument)),
            Abs { Parameter: var parameter, Abstraction: var abstraction } => Frees(abstraction)
                .Where(t => t != parameter).ToArray(),
            _ => throw new InvalidOperationException()
        };
    }

    public override Term[] Frees(Term[] terms)
    {
        return terms.SelectMany(Frees).Distinct().ToArray();
    }

    public override Func<Term, bool> FreesIn(Term[] terms)
    {
        bool IsIn(Term term)
        {
            return term switch
            {
                Var   => terms.Contains(term),
                Const => true,
                Abs { Parameter: var parameter, Abstraction: var abstraction } => FreesIn(terms.Append(parameter)
                    .ToArray())(abstraction),
                Comb { Application: var application, Argument: var argument } => IsIn(application) &&
                    IsIn(argument),
                _ => throw new InvalidOperationException()
            };
        }
        
        return IsIn;
    }

    public override bool VarFreeIn(Term variable, Term term)
    {
        return term switch
        {
            Abs { Parameter: var parameter, Abstraction: var abstraction } => parameter != variable &&
                VarFreeIn(variable, abstraction),
            Comb { Application: var application, Argument: var argument } => VarFreeIn(variable, application) ||
                VarFreeIn(variable, argument),
            _ => variable != term
        };
    }

    /*public override Func<Term, Term> Instance(Dictionary<Type, Type> map)
    {
        Term Instancer(Term term)
        {
            var substitution = SubstituteTypes(map);
            
            switch (term)
            {
                case Var { Name: var name, Type: var type}:
                    return new Var(name, substitution(type));
                case Const {Name: var name, Type: var type}:
                    return new Const(name, substitution(type));
                case Comb {Application: var application, Argument: var argument}:
                    return new Comb(Instancer(application), Instancer(argument));
                case Abs { Parameter: var parameter, Abstraction: var abstraction }:
                {
                    var newParameter = Instancer(parameter);
                }
                default:
                    throw new ArgumentOutOfRangeException(nameof(term));
            }
        }
        
        return Instancer;
    }#1#
    
    private class ClashException : Exception
    {
        public Term Term;
        
        public ClashException(Term term)
        {
            Term = term;
        }
    }

    public override Func<Term, Term> Instance(Dictionary<Type, Type> map)
    {
        Term Instancer(Term term)
        {
            switch (term)
            {
                case Var {Name: var name, Type: var type}:
                    
            }
        }

        return Instancer;
    }

    private Func<Dictionary<Type, Type>, Func<Term, Term>> RecursiveInstance(Dictionary<Term, Term> inverseEnv)
    {
        Func<Term, Term> Iteration(Dictionary<Type, Type> map)
        {
            var substitution = SubstituteTypes(map);
                
            Term Instancer(Term term)
            {
                switch (term)
                {
                    case Var { Name: var name, Type: var type}:
                    {
                        var substitutedType = substitution(type);
                        var output = new Var(name, substitutedType);
                        if (!inverseEnv.TryGetValue(output, out var originalTerm) || term == originalTerm)
                            return new Var(name, substitutedType);
                        throw new ClashException(output);
                    }
                    case Const {Name: var name, Type: var type}:
                        return new Const(name, substitution(type));
                    case Comb {Application: var application, Argument: var argument}:
                        return new Comb(Instancer(application), Instancer(argument));
                    case Abs { Parameter: var parameter, Abstraction: var abstraction }:
                    {
                        var emptyRecursiveInstance = RecursiveInstance(new Dictionary<Term, Term>())(map);
                        var newParameter = emptyRecursiveInstance(parameter);
                        var newEnv = inverseEnv.ToDictionary(kv => kv.Key, kv => kv.Value);
                        newEnv[newParameter] = parameter;
                        try
                        {
                            var newAbstraction = RecursiveInstance(newEnv)(map)(abstraction);
                            return new Abs(newParameter, newAbstraction);
                        }
                        catch (ClashException clash)
                        {
                            if (clash.Term != newParameter)
                                throw;
                            var ifrees = Frees(abstraction).Select(emptyRecursiveInstance).ToArray();
                            var parameterVariant = Variant(ifrees)(newParameter);
                            var anotherVariable = new Var(DestVar(parameterVariant).name, DestVar(parameter).type);
                            return Instancer(new Abs(anotherVariable,
                                VarSubstitution(anotherVariable, parameter)(abstraction)));
                        }
                    }
                    default:
                        throw new ArgumentOutOfRangeException(nameof(term));
                }
            }
            
            return Instancer;
        }
        
        return Iteration;
    }

    public override Func<Term, Term> Variant(Term[] avoid)
    {
        Term CreateVariant(Term term)
        {
            if (!avoid.Any(aTerm => VarFreeIn(term, aTerm)))
                return term;
            if (term is not Var {Name: var name, Type: var type})
                throw new Exception("Term is not a variable");
            return CreateVariant(new Var($"{name}'", type));
        }
        
        return CreateVariant;
    }

    private Term SafeMakeEquality(Term left, Term right)
    {
        var type = TypeOf(left);
        var eqType = new TyApp("fun", new[] { type, new TyApp("fun", new[] { type, BoolType }) });
        var eq = new Const("=", eqType);
        return new Comb(new Comb(eq, left), right);
    }

    public override Theorem ProofReflexivity(Term term)
    {
        return new Sequent(Array.Empty<Term>(), SafeMakeEquality(term, term));
    }
}*/