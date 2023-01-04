using static ValiantProofVerifier.Term;
using static ValiantProofVerifier.Type;

namespace ValiantProofVerifier;

public class Printer
{
    public virtual string PrintTerm(Term term)
    {
        return term switch
        {
            Var(var name, var type)   => PrintVar(name, type),
            Const(var name, var type) => PrintConst(name, type),
            Comb(var app, var arg)    => PrintComb(app, arg),
            Abs(var param, var abs)   => PrintAbs(param, abs),
            _                         => throw new ArgumentOutOfRangeException()
        };
    }

    public virtual string PrintVar(string name, Type type)
    {
        return name;
    }
    
    public virtual string PrintConst(string name, Type type)
    {
        return name;
    }
    
    public virtual string PrintComb(Term app, Term arg)
    {
        return $"{PrintTerm(app)} {PrintTerm(arg)}";
    }
    
    public virtual string PrintAbs(Term parameter, Term abstraction)
    {
        return $"λ {PrintTerm(parameter)} . {PrintTerm(abstraction)}";
    }
    
    public virtual string PrintType(Type type)
    {
        return type switch
        {
            TyVar(var name)           => PrintTyVar(name),
            TyApp(var name, var args) => PrintTyApp(name, args),
            _                         => throw new ArgumentOutOfRangeException()
        };
    }

    public virtual string PrintTyVar(string name)
    {
        return name;
    }

    public virtual string PrintTyApp(string name, Type[] args)
    {
        return $"{name}<{string.Join(", ", args.Select(PrintType))}>";
    }

    public virtual string PrintTheorem(Theorem theorem)
    {
        var (premises, conclusion) = (Theorem.Sequent)theorem;

        return PrintSequent(premises, conclusion);
    }
    
    public virtual string PrintSequent(HashSet<Term> premises, Term conclusion)
    {
        return $"{string.Join(", ", premises.Select(PrintTerm))} |- {PrintTerm(conclusion)}";
    }

    public static Printer UniversalPrinter { get; private set; } = new();

    public Printer Activate()
    {
        var oldPrinter = UniversalPrinter;
        UniversalPrinter = this;
        return oldPrinter;
    }

    public void Deactivate()
    {
        UniversalPrinter = new Printer();
    }
    
    public void Deactivate(Printer newPrinter)
    {
        UniversalPrinter = newPrinter;
    }
}