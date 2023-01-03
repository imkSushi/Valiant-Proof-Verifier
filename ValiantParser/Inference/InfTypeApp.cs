using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfTypeApp(string Name, InfType[] Args) : InfType
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        return Args.SelectMany(arg => arg.UnboundTypeNamesIn());
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        return Args.SelectMany(arg => arg.BoundTypeNamesIn());
    }

    internal override InfType MakeUnboundTypeNamesUnique(HashSet<string> avoid, Dictionary<string, string> newlyBound)
    {
        return new InfTypeApp(Name, Args.Select(arg => arg.MakeUnboundTypeNamesUnique(avoid, newlyBound)).ToArray());
    }

    internal override InfType ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return new InfTypeApp(Name, Args.Select(arg => arg.ApplySubstitutions(map)).ToArray());
    }

    internal override TyApp FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        return new TyApp(Name, Args.Select(arg => arg.FixTypes(map, avoid, newNameGenerator)).ToArray());
    }

    internal override bool IsUnboundVarIn(InfUnboundVar var)
    {
        return Args.Any(arg => arg.IsUnboundVarIn(var));
    }

    internal override InfType ConvertTypeToFn(string oldName)
    {
        return new InfTypeApp(Name, Args.Select(arg => arg.ConvertTypeToFn(oldName)).ToArray());
    }

    public override string ToString()
    {
        return $"{Name}<{string.Join(", ", Args.Select(arg => arg.ToString()))}>";
    }
}