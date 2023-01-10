using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfVar(string Name, InfType Type) : InfTerm
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        return Type.UnboundTypeNamesIn();
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        return Type.BoundTypeNamesIn();
    }

    internal override InfVar MakeUnboundTypeNamesUnique(HashSet<string> avoid)
    {
        return new InfVar(Name, Type.MakeUnboundTypeNamesUnique(avoid));
    }

    internal override InfVar ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return new InfVar(Name, Type.ApplySubstitutions(map));
    }

    internal override Var FixTypes(Dictionary<InfUnboundVar, FakeType> map,
        HashSet<string> avoid,
        Utilities.NewNameTypeGenerator newNameGenerator)
    {
        return new Var(Name, Type.FixTypes(map, avoid, newNameGenerator));
    }

    internal override IEnumerable<(InfType, InfType)> GetMappings()
    {
        yield break;
    }

    internal override IEnumerable<InfType> GetAllMappingsOf(string boundVarName)
    {
        if (Name == boundVarName)
            yield return Type;
    }

    internal override InfType TypeOf()
    {
        return Type;
    }

    internal override Result<InfTerm> FixCombTypes()
    {
        return this;
    }

    internal override InfVar ConvertTypeToFn(string oldName)
    {
        return new InfVar(Name, Type.ConvertTypeToFn(oldName));
    }

    internal override IEnumerable<InfVar> FreesIn()
    {
        yield return this;
    }

    public override string ToString()
    {
        return $"{Name}:{Type}";
    }
}