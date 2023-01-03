using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfAbs(InfVar Parameter, InfTerm Abstraction) : InfTerm
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        return Parameter.UnboundTypeNamesIn().Concat(Abstraction.UnboundTypeNamesIn());
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        return Parameter.BoundTypeNamesIn().Concat(Abstraction.BoundTypeNamesIn());
    }

    internal override InfTerm MakeUnboundTypeNamesUnique(HashSet<string> avoid)
    {
        return new InfAbs(Parameter.MakeUnboundTypeNamesUnique(avoid), Abstraction.MakeUnboundTypeNamesUnique(avoid));
    }

    internal override InfTerm ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return new InfAbs(Parameter.ApplySubstitutions(map), Abstraction.ApplySubstitutions(map));
    }

    internal override Abs FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        // ReSharper disable PossibleMultipleEnumeration
        return new Abs(Parameter.FixTypes(map, avoid, newNameGenerator), Abstraction.FixTypes(map, avoid, newNameGenerator));
    }

    internal override IEnumerable<(InfType, InfType)> GetMappings()
    {
        return Abstraction.GetAllMappingsOf(Parameter.Name).Select(type => (Parameter.Type, type)).Concat(Abstraction.GetMappings());
    }

    internal override IEnumerable<InfType> GetAllMappingsOf(string boundVarName)
    {
        return Parameter.Name == boundVarName ? Enumerable.Empty<InfType>() : Abstraction.GetAllMappingsOf(boundVarName);
    }

    internal override InfType TypeOf()
    {
        return new InfTypeApp("fun", new []{Parameter.Type, Abstraction.TypeOf()});
    }

    internal override Result<InfTerm> FixCombTypes()
    {
        if (!Abstraction.FixCombTypes().Deconstruct(out var newAbs, out var err))
            return err;
        
        return new InfAbs(Parameter, newAbs);
    }

    internal override InfAbs ConvertTypeToFn(string oldName)
    {
        return new InfAbs(Parameter.ConvertTypeToFn(oldName), Abstraction.ConvertTypeToFn(oldName));
    }

    public override string ToString()
    {
        return $"(λ{Parameter.Name}.{Abstraction})";
    }
}