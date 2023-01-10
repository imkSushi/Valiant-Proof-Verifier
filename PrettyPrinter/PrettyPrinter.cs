using System.Text;
using ValiantParser;
using ValiantProofVerifier;
using Type = ValiantProofVerifier.Type;

namespace PrettyPrinter;

public class PrettyPrinter : Printer
{
    private Parser _parser;
    private Kernel _kernel;
    private Dictionary<string, string> _prefixes = new();
    private Dictionary<string, string> _lambdas = new();
    private Dictionary<string, string> _infixes = new();
    private Dictionary<string, string> _consts = new();
    public PrettyPrinter(Parser parser, Kernel kernel)
    {
        _parser = parser;
        _kernel = kernel;
    }

    public bool TryRegisterPrefix(string prefix, string display)
    {
        if (_prefixes.ContainsKey(prefix))
            return false;

        _prefixes[prefix] = display;
        return true;
    }
    
    public bool TryRegisterLambda(string lambda, string display)
    {
        if (_lambdas.ContainsKey(lambda))
            return false;

        _lambdas[lambda] = display;
        return true;
    }
    
    public bool TryRegisterInfix(string infix, string display)
    {
        if (_infixes.ContainsKey(infix))
            return false;

        _infixes[infix] = display;
        return true;
    }
    
    public bool TryRegisterConst(string constant, string display)
    {
        if (_consts.ContainsKey(constant))
            return false;

        _consts[constant] = display;
        return true;
    }

    public override string PrintTyApp(string name, Type[] args)
    {
        if (name != "fun")
        {
            return args.Length == 0 ? name : base.PrintTyApp(name, args);
        }

        if (Kernel.IsTyApp(args[0]) && Kernel.DeconstructTyApp(args[0]).name == "fun")
        {
            return $"({PrintType(args[0])}) → {PrintType(args[1])}";
        }
        
        return $"{PrintType(args[0])} → {PrintType(args[1])}";
    }

    public override string PrintAbs(Term parameter, Term abstraction)
    {
        return PrintAbs(parameter, abstraction, null);
    }

    protected virtual string PrintAbs(Term parameter, Term abstraction, string? modifier)
    {
        var paramList = new List<Term> {parameter};

        while (true)
        {
            if (modifier != null)
            {
                if (!Kernel.IsComb(abstraction))
                    break;
                
                var (app, arg) = Kernel.DeconstructComb(abstraction);
                if (!Kernel.IsConst(app))
                    break;
                
                if (Kernel.DeconstructConst(app).name != modifier)
                    break;
                
                abstraction = arg;
            }

            if (!Kernel.IsAbs(abstraction))
                break;

            var (param, abs) = Kernel.DeconstructAbs(abstraction);
            paramList.Add(param);
            abstraction = abs;
        }
        
        return $"{(modifier == null ? "λ" : _lambdas[modifier])} {string.Join(" ", paramList.Select(PrintTerm))}. {PrintTerm(abstraction)}";
    }
    
    public override string PrintComb(Term application, Term argument)
    {
        if (Kernel.IsConst(application))
        {
            var constInfo = Kernel.DeconstructConst(application);
            if (_lambdas.ContainsKey(constInfo.name) && Kernel.IsAbs(argument))
            {
                var (param, abs) = Kernel.DeconstructAbs(argument);
                return PrintAbs(param, abs, constInfo.name);
            }
            
            if (_prefixes.TryGetValue(constInfo.name, out var prefixSymbol))
            {
                if (ShouldPrefixBracketArgument(argument))
                    return $"{prefixSymbol}({PrintTerm(argument)})";
                
                return $"{prefixSymbol}{PrintTerm(argument)}";
            }

            if (_infixes.TryGetValue(constInfo.name, out prefixSymbol))
            {
                if (ShouldPrefixBracketArgument(argument))
                    return $"({prefixSymbol})({PrintTerm(argument)})";
                
                return $"({prefixSymbol}){PrintTerm(argument)}";
            }
        }
        
        if (Kernel.IsComb(application))
        {
            var (app, arg) = Kernel.DeconstructComb(application);
            if (Kernel.IsConst(app))
            {
                var (name, _) = Kernel.DeconstructConst(app);
                if (_infixes.TryGetValue(name, out var infixSymbol))
                    return
                        $"{(ShouldInfixBracketArgument(arg, true) ? $"({PrintTerm(arg)})" : PrintTerm(arg))} {infixSymbol} {(ShouldInfixBracketArgument(argument, false) ? $"({PrintTerm(argument)})" : PrintTerm(argument))}";
            }
        }

        if (!Kernel.IsComb(argument))
        {
            if (Kernel.IsAbs(application))
                return $"({PrintTerm(application)}) {PrintTerm(argument)}";
            
            return $"{PrintTerm(application)} {PrintTerm(argument)}";
        }
        
        var (app2, arg2) = Kernel.DeconstructComb(argument);
        
        if (Kernel.IsConst(app2))
        {
            var (name, _) = Kernel.DeconstructConst(app2);
            if (_prefixes.ContainsKey(name))
            {
                if (Kernel.IsAbs(application))
                    return $"({PrintTerm(application)}) {PrintTerm(argument)}";
            
                return $"{PrintTerm(application)} {PrintTerm(argument)}";
            }
        }
        
        if (Kernel.IsAbs(application))
            return $"({PrintTerm(application)}) ({PrintTerm(argument)})";
            
        return $"{PrintTerm(application)} ({PrintTerm(argument)})";
    }

    protected virtual bool ShouldPrefixBracketArgument(Term argument)
    {
        if (!Kernel.IsComb(argument))
            return false;
                
        var (app, _) = Kernel.DeconstructComb(argument);
        return !Kernel.IsConst(app) || !_prefixes.ContainsKey(Kernel.DeconstructConst(app).name);
    }

    protected virtual bool ShouldInfixBracketArgument(Term argument, bool left)
    {
        if (!Kernel.IsComb(argument))
            return left && Kernel.IsAbs(argument);
        
        var (app, arg) = Kernel.DeconstructComb(argument);

        if (Kernel.IsConst(app))
            return _infixes.ContainsKey(Kernel.DeconstructConst(app).name);

        if (!Kernel.IsComb(app)) 
            return false;
        
        var (app2, _) = Kernel.DeconstructComb(app);

        return Kernel.IsConst(app2) && _infixes.ContainsKey(Kernel.DeconstructConst(app2).name);
    }
    
    public override string PrintConst(string name, Type type)
    {
        return _consts.TryGetValue(name, out var display) ? display : name;
    }

    public override string PrintSequent(HashSet<Term> premises, Term conclusion)
    {
        return $"{string.Join(", ", premises.Select(PrintTerm))} ⊢ {PrintTerm(conclusion)}";
    }
}