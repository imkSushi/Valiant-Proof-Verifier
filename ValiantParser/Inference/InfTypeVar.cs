using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfTypeVar(string Name) : InfType
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        yield break;
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        yield return Name;
    }

    internal override InfType MakeUnboundTypeNamesUnique(HashSet<string> avoid, Dictionary<string, string> newlyBound)
    {
        return this;
    }

    internal override InfType ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return this;
    }

    internal override TyVar FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        return new TyVar(Name);
    }

    internal override bool IsUnboundVarIn(InfUnboundVar var)
    {
        return false;
    }

    internal override InfType ConvertTypeToFn(string oldName)
    {
        return this;
    }

    public override string ToString()
    {
        return $"'{Name}";
    }
}