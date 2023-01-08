using ValiantProofVerifier;
using Type = ValiantProofVerifier.Type;

namespace PrettyPrinter;

public class DetailedPrinter : Printer
{
    public override string PrintConst(string name, Type type)
    {
        return $"{name} {PrintType(type)}";
    }
    
    public override string PrintVar(string name, Type type)
    {
        return $"{name} {PrintType(type)}";
    }
}