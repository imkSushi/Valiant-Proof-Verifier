using ValiantProofVerifier;
using static ValiantProofVerifier.Kernel;

namespace ValiantBasics;

public abstract record FakeTerm
{
    public virtual Term ToTerm(Kernel kernel)
    {
        if (!TryMakeTerm(kernel).Deconstruct(out var output, out var error))
            throw new TheoremException(error);
        
        return output;
    }
    
    public abstract Result<Term> TryMakeTerm(Kernel kernel);

    public static FakeTerm FromTerm(Term term)
    {
        if (IsVar(term))
        {
            var (name, type) = DeconstructVar(term);
            return new Var(name, FakeType.FromType(type));
        }

        if (IsConst(term))
        {
            var (name, type) = DeconstructConst(term);
            return new Const(name, FakeType.FromType(type));
        }
        
        if (IsComb(term))
        {
            var (app, arg) = DeconstructComb(term);
            if (!Comb.TryMakeComb(FromTerm(app), FromTerm(arg)).Deconstruct(out var output, out var error))
                throw new TheoremException(error);
            return output;
        }
        
        var (param, abs) = DeconstructAbs(term);
        return new Abs((Var) FromTerm(param), FromTerm(abs));
    }

    public abstract FakeType TypeOf();
}

public record Var(string Name, FakeType Type) : FakeTerm
{
    public override Result<Term> TryMakeTerm(Kernel kernel)
    {
        try
        {
            return kernel.MakeVariable(Name, Type.ToType(kernel));
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public override FakeType TypeOf()
    {
        return Type;
    }

    public override string ToString()
    {
        return $"{Name}:{Type}";
    }
}

public record Const(string Name, FakeType Type) : FakeTerm
{
    public override Result<Term> TryMakeTerm(Kernel kernel)
    {
        try
        {
            var type = Type.ToType(kernel);
            if (!kernel.TryGenerateConstant(Name, type, out var constant, out var error))
                throw new TheoremException(error);

            return constant;
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public override FakeType TypeOf()
    {
        return Type;
    }

    public override string ToString()
    {
        return $"{Name}:{Type}";
    }
}

public record Comb : FakeTerm
{
    private Comb(FakeTerm application, FakeTerm argument)
    {
        Application = application;
        Argument = argument;
    }

    public static Result<Comb> TryMakeComb(FakeTerm application, FakeTerm argument)
    {
        if (application.TypeOf() is not TyApp { Name: "fun", Args: [_, _] })
            return "Application is not a function";

        return new Comb(application, argument);
    }

    public override Result<Term> TryMakeTerm(Kernel kernel)
    {
        try
        {
            return kernel.MakeCombination(Application.ToTerm(kernel), Argument.ToTerm(kernel));
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }
    
    public static Comb MakeComb(FakeTerm application, FakeTerm argument)
    {
        if (!TryMakeComb(application, argument).Deconstruct(out var output, out var error))
            throw new TheoremException(error);
        
        return output;
    }

    public override FakeType TypeOf()
    {
        if (Application.TypeOf() is not TyApp { Name: "fun", Args:[_, var output] })
            throw new TheoremException("Application is not a function");
        
        return output;
    }

    public override string ToString()
    {
        return $"({Application} {Argument})";
    }

    public FakeTerm Application { get; init; }
    public FakeTerm Argument { get; init; }
    public void Deconstruct(out FakeTerm application, out FakeTerm argument)
    {
        application = Application;
        argument = Argument;
    }
}

public record Abs(Var Parameter, FakeTerm Abstraction) : FakeTerm
{
    public override Result<Term> TryMakeTerm(Kernel kernel)
    {
        try
        {
            return kernel.MakeAbstraction(Parameter.ToTerm(kernel), Abstraction.ToTerm(kernel));
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public override FakeType TypeOf()
    {
        return new TyApp("fun", new []{Parameter.TypeOf(), Abstraction.TypeOf()});
    }

    public override string ToString()
    {
        return $"λ{Parameter}.{Abstraction}";
    }
}