using System.Diagnostics.CodeAnalysis;
using ValiantProofVerifier;

namespace ValiantBasics;

public static class KernelExtension
{
    public static bool TryGenerateConstant(this Kernel kernel, string name, Type type, [MaybeNullWhen(false)] out Term constant, [MaybeNullWhen(true)] out string error)
    {
        constant = default;
        if (!kernel.ConstantExists(name))
            return ReturnError($"No constant with name {name} exists.", out error);
        
        var baseType = kernel.GetConstantType(name);
        var map = new Dictionary<Type, Type>();

        if (!kernel.TryGenerateSubstitution(baseType, type, map, out error))
            return false;

        constant = kernel.MakeConstant(name, map);
        error = null;
        return true;
    }

    private static bool TryGenerateSubstitution(this Kernel kernel,
        Type basic,
        Type desired,
        Dictionary<Type, Type> map,
        [MaybeNullWhen(true)] out string error)
    {
        if (Kernel.IsTyVar(basic))
        {
            if (map.TryGetValue(basic, out var existing))
            {
                if (existing != desired)
                    return ReturnError($"Type variable {basic} maps to both {existing} and {desired}.", out error);
            }
            else
            {
                map[basic] = desired;
            }
            error = null;
            return true;
        }

        if (Kernel.IsTyVar(desired))
            return ReturnError($"Type application {basic} maps to type variable {desired}.", out error);

        var (basicName, basicArgs) = Kernel.DeconstructTyApp(basic);
        var (desiredName, desiredArgs) = Kernel.DeconstructTyApp(desired);
        
        if (basicName != desiredName)
            return ReturnError($"Type application {basic} maps to type application {desired}.", out error);
        
        foreach (var (basicArg, desiredArg) in basicArgs.Zip(desiredArgs))
        {
            if (!kernel.TryGenerateSubstitution(basicArg, desiredArg, map, out error))
                return false;
        }
        
        error = null;
        return true;
    }
    
    private static bool ReturnError(string error, [MaybeNullWhen(true)] out string errorOut)
    {
        errorOut = error;
        return false;
    }
}