using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfConst(string Name, InfType Type) : InfTerm
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        return Type.UnboundTypeNamesIn();
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        return Type.BoundTypeNamesIn();
    }

    internal override InfTerm MakeUnboundTypeNamesUnique(HashSet<string> avoid)
    {
        return new InfConst(Name, Type.MakeUnboundTypeNamesUnique(avoid));
    }

    internal override InfTerm ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return new InfConst(Name, Type.ApplySubstitutions(map));
    }

    internal override Const FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        return new Const(Name, Type.FixTypes(map, avoid, newNameGenerator));
    }

    internal override IEnumerable<(InfType, InfType)> GetMappings()
    {
        yield break;
    }

    internal override IEnumerable<InfType> GetAllMappingsOf(string boundVarName)
    {
        yield break;
    }

    internal override InfType TypeOf()
    {
        return Type;
    }

    internal override Result<InfTerm> FixCombTypes()
    {
        return this;
    }

    internal override InfTerm ConvertTypeToFn(string oldName)
    {
        return new InfConst(Name, Type.ConvertTypeToFn(oldName));
    }

    public override string ToString()
    {
        return $"{Name}:{Type}";
    }
}