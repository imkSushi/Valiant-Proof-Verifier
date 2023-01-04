using System.Text;
using ValiantParser;
using ValiantProofVerifier;
using Type = ValiantProofVerifier.Type;

namespace PrettyPrinter;

public class PrettyPrinter : Printer
{
    private Parser _parser;
    private Kernel _kernel;
    public PrettyPrinter(Parser parser, Kernel kernel)
    {
        _parser = parser;
        _kernel = kernel;
    }

    public override string PrintTyApp(string name, Type[] args)
    {
        if (name != "fun")
        {
            return args.Length == 0 ? name : base.PrintTyApp(name, args);
        }

        if (Kernel.IsTyApp(args[0]) && Kernel.DeconstructTyApp(args[0]).name == "fun")
        {
            return $"({PrintType(args[0])}) -> {PrintType(args[1])}";
        }
        
        return $"{PrintType(args[0])} -> {PrintType(args[1])}";
    }

    public override string PrintAbs(Term parameter, Term abstraction)
    {
        var paramList = new List<Term> {parameter};

        while (Kernel.IsAbs(abstraction))
        {
            var (param, abs) = Kernel.DeconstructAbs(abstraction);
            paramList.Add(param);
            abstraction = abs;
        }
        
        return $"λ {string.Join(" ", paramList.Select(PrintTerm))}. {PrintTerm(abstraction)}";
    }
}