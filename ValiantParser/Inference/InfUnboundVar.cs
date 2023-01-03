using ValiantBasics;

namespace ValiantParser.Inference;

internal record InfUnboundVar(string Name) : InfType
{
    internal override IEnumerable<string> UnboundTypeNamesIn()
    {
        yield return Name;
    }

    internal override IEnumerable<string> BoundTypeNamesIn()
    {
        yield break;
    }

    internal override InfType MakeUnboundTypeNamesUnique(HashSet<string> avoid, Dictionary<string, string> newlyBound)
    {
        if (newlyBound.TryGetValue(Name, out var newName))
            return new InfUnboundVar(newName);
        newName = Name;
        while (avoid.Contains(newName))
        {
            newName = $"'{newName}";
        }
        newlyBound[Name] = newName;
        return new InfUnboundVar(newName);
    }

    internal override InfType ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map)
    {
        return map.TryGetValue(this, out var output) ? output : this;
    }

    internal override FakeType FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, Utilities.NewNameTypeGenerator newNameGenerator)
    {
        if (map.TryGetValue(this, out var output))
            return output;

        var newName = newNameGenerator.Next();

        while (avoid.Contains(newName))
        {
            newName = newNameGenerator.Next();
        }
        
        avoid.Add(newName);
        output = new TyVar(newName);
        map[this] = output;
        return output;
    }

    internal override bool IsUnboundVarIn(InfUnboundVar var)
    {
        return this == var;
    }

    internal override InfType ConvertTypeToFn(string oldName)
    {
        if (Name == oldName)
            return new InfTypeApp("fun", new InfType[]{new InfUnboundVar(")a"), new InfUnboundVar(")b")});

        return this;
    }

    public override string ToString()
    {
        return $"~{Name}";
    }
}