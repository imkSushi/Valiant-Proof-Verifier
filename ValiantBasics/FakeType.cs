using ValiantProofVerifier;

namespace ValiantBasics;

public abstract record FakeType
{
    public virtual Type ToType(Kernel kernel)
    {
        if (!TryMakeType(kernel).Deconstruct(out var output, out var error))
            throw new TheoremException(error);
        
        return output;
    }
    
    public abstract Result<Type> TryMakeType(Kernel kernel);

    public static FakeType FromType(Type type)
    {
        if (Kernel.IsTyVar(type))
        {
            return new TyVar(Kernel.DeconstructTyVar(type));
        }
        var (name, args) = Kernel.DeconstructTyApp(type);
        return new TyApp(name, args.Select(FromType).ToArray());
    }
}

public record TyVar(string Name) : FakeType
{

    public override Result<Type> TryMakeType(Kernel kernel)
    {
        return kernel.MakeType(Name);
    }

    public override string ToString()
    {
        return $"{Name}";
    }
}

public record TyApp(string Name, FakeType[] Args) : FakeType
{

    public override Result<Type> TryMakeType(Kernel kernel)
    {
        try
        {
            return kernel.MakeType(Name, Args.Select(a => a.ToType(kernel)).ToArray());
        }
        catch (TheoremException e)
        {
            return e.Message;
        }
    }

    public override string ToString()
    {
        return $"{Name}<{string.Join(", ", Args.Select(type => type.ToString()))}>";
    }
}