using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfComb : InfTerm
{
    internal InfComb(InfTerm application, InfTerm argument)
    {
        Application = application;
        Argument = argument;
    }

    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        return Application.UnboundTypeNamesIn().Concat(Argument.UnboundTypeNamesIn());
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        return Application.BoundTypeNamesIn().Concat(Argument.BoundTypeNamesIn());
    }

    internal override InfTerm MakeUnboundTypeNamesUnique(HashSet<string> avoid)
    {
        return new InfComb(Application.MakeUnboundTypeNamesUnique(avoid), Argument.MakeUnboundTypeNamesUnique(avoid));
    }

    internal override InfTerm ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return new InfComb(Application.ApplySubstitutions(map), Argument.ApplySubstitutions(map));
    }

    internal override Comb FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        // ReSharper disable PossibleMultipleEnumeration
        return Comb.MakeComb(Application.FixTypes(map, avoid, newNameGenerator), Argument.FixTypes(map, avoid, newNameGenerator));
    }

    internal override IEnumerable<(InfType, InfType)> GetMappings()
    {
        var inputType = ((InfTypeApp)Application.TypeOf()).Args[0];
        return new[] { (inputType, Argument.TypeOf()) }.Concat(Application.GetMappings())
            .Concat(Argument.GetMappings());
    }

    internal override IEnumerable<InfType> GetAllMappingsOf(string boundVarName)
    {
        return Application.GetAllMappingsOf(boundVarName).Concat(Argument.GetAllMappingsOf(boundVarName));
    }

    internal override InfType TypeOf()
    {
        return ((InfTypeApp)Application.TypeOf()).Args[1];
    }

    internal override Result<InfTerm> FixCombTypes()
    {
        if (!Application.FixCombTypes().Deconstruct(out var newApp, out var error) || !Argument.FixCombTypes().Deconstruct(out var newArg, out error))
            return error;

        return newApp.TypeOf() switch
        {
            InfTypeApp { Name: "fun" } => new InfComb(newApp, newArg),
            InfTypeApp { Name: var name } =>
                $"Application could not be applied to argument because the type of the application is not a function type. The type of the application is {name}.",
            InfTypeVar { Name: var name } =>
                $"Application could not be applied to argument because the type of the application is not a function type. The type of the application is {name}.",
            InfUnboundVar { Name: var name } => new InfComb(newApp.ConvertTypeToFn(name), newArg),
            _                                => throw new ArgumentOutOfRangeException()
        };
    }

    internal override InfComb ConvertTypeToFn(string oldName)
    {
        return new InfComb(Application.ConvertTypeToFn(oldName), Argument);
    }

    internal override IEnumerable<InfVar> FreesIn()
    {
        return Application.FreesIn().Concat(Argument.FreesIn());
    }

    public InfTerm Application { get; init; }
    public InfTerm Argument { get; init; }
    public void Deconstruct(out InfTerm application, out InfTerm argument)
    {
        application = Application;
        argument = Argument;
    }
    
    public override string ToString()
    {
        return $"({Application} {Argument})";
    }
}