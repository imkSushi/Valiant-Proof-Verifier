﻿using ValiantBasics;
using ValiantProofVerifier;
using static ValiantBasics.Utilities;

namespace ValiantParser.Inference;

internal abstract record InfTerm
{
    internal static InfTerm FromTerm(Term term, bool bound) => FromTerm(FakeTerm.FromTerm(term), bound);
    
    internal static InfTerm FromTerm(FakeTerm term, bool bound)
    {
        return term switch
        {
            Var {Name: var name, Type: var type} => new InfVar(name, InfType.FromType(type, bound)),
            Const {Name: var name, Type: var type} => new InfConst(name, InfType.FromType(type, bound)),
            Comb {Application: var application, Argument: var argument} => new InfComb(FromTerm(application, bound), FromTerm(argument, bound)),
            Abs {Parameter: var parameter, Abstraction: var abstraction} => new InfAbs((InfVar) FromTerm(parameter, bound), FromTerm(abstraction, bound)),
            _ => throw new ArgumentOutOfRangeException(nameof(term))
        };
    }

    internal abstract IEnumerable<string> UnboundTypeNamesIn();
    
    internal abstract IEnumerable<string> BoundTypeNamesIn();
    internal abstract InfTerm MakeUnboundTypeNamesUnique(HashSet<string> avoid);

    internal virtual InfTerm MakeUnboundTypeNamesUnique()
    {
        return MakeUnboundTypeNamesUnique(new HashSet<string>());
    }

    internal abstract InfTerm ApplySubstitutions(Dictionary<InfUnboundVar, InfType> map);

    internal virtual FakeTerm FixTypes()
    {
        var avoid = BoundTypeNamesIn().ToHashSet();
        using var newNameGenerator = new NewNameTypeGenerator();
        return FixTypes(new Dictionary<InfUnboundVar, FakeType>(), avoid, newNameGenerator);
    }

    internal abstract FakeTerm FixTypes(Dictionary<InfUnboundVar, FakeType> map, HashSet<string> avoid, NewNameTypeGenerator newNameGenerator);

    internal abstract IEnumerable<(InfType, InfType)> GetMappings();

    internal abstract IEnumerable<InfType> GetAllMappingsOf(string boundVarName);

    internal abstract InfType TypeOf();
    
    internal abstract Result<InfTerm> FixCombTypes();

    internal abstract InfTerm ConvertTypeToFn(string oldName);
}