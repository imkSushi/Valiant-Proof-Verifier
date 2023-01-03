using ValiantBasics;
using ValiantProofVerifier;
using static ValiantBasics.Utilities;

namespace ValiantParser.Inference;

internal abstract record InfType
{
    internal static InfType FromType(Type type, bool bound) => FromType(FakeType.FromType(type), bound);

    internal static InfType FromType(FakeType type, bool bound)
    {
        return type switch
        {
            TyVar { Name: var name } => (bound ? new InfTypeVar(name) : new InfUnboundVar(name)),
            TyApp { Name: var name, Args: var args } => new InfTypeApp(name,
                args.Select(arg => FromType(arg, bound)).ToArray()),
            _ => throw new ArgumentOutOfRangeException(nameof(type))
        };
    }

    internal abstract IEnumerable<string> UnboundTypeNamesIn();
    
    internal abstract IEnumerable<string> BoundTypeNamesIn();
    internal abstract InfType MakeUnboundTypeNamesUnique(HashSet<string> avoid, Dictionary<string, string> newlyBound);

    internal virtual InfType MakeUnboundTypeNamesUnique(HashSet<string> avoid)
    {
        var newlyBound = new Dictionary<string, string>();
        var output = MakeUnboundTypeNamesUnique(avoid, newlyBound);
        avoid.UnionWith(newlyBound.Values);
        return output;
    }

    internal abstract InfType ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map);

    internal virtual FakeType FixTypes()
    {
        var avoid = BoundTypeNamesIn().ToHashSet();
        using var newNameGenerator = new NewNameTypeGenerator();
        return FixTypes(new Dictionary<InfUnboundVar, FakeType>(), avoid, newNameGenerator);
    }

    internal abstract FakeType FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, NewNameTypeGenerator newNameGenerator);

    internal abstract bool IsUnboundVarIn(InfUnboundVar var);

    internal abstract InfType ConvertTypeToFn(string oldName);
}