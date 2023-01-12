using ValiantBasics;
using ValiantResults;

namespace ValiantParser.Inference;

internal class TypeInferer
{
    internal Result<FakeTerm> InferType(InfTerm input)
    {
        if (!input.FixCombTypes().Deconstruct(out var fixedCombInput, out var error))
            return error;
        var uniqueTerm = fixedCombInput.MakeUnboundTypeNamesUnique();
        var mappings = uniqueTerm.GetAllMappings().ToHashSet();

        while (mappings.Any())
        {
            var (left, right) = mappings.First();
            mappings.Remove((left, right));
            if (left == right)
                continue;

            switch (left, right)
            {
                case (InfUnboundVar leftUnbound, InfUnboundVar rightUnbound):
                {
                    var substitution = new Dictionary<InfUnboundVar, InfType>
                    {
                        [leftUnbound] = rightUnbound
                    };
                    uniqueTerm = uniqueTerm.ApplySubstitutions(substitution);
                    mappings = mappings.Select(m => (m.Item1.ApplySubstitutions(substitution), m.Item2.ApplySubstitutions(substitution))).ToHashSet();
                    break;
                }
                case (InfUnboundVar leftUnbound, _):
                {
                    if (right.IsUnboundVarIn(leftUnbound))
                        return "Type error: recursion type";
                    var substitution = new Dictionary<InfUnboundVar, InfType>
                    {
                        [leftUnbound] = right
                    };
                    uniqueTerm = uniqueTerm.ApplySubstitutions(substitution);
                    mappings = mappings.Select(m => (m.Item1.ApplySubstitutions(substitution), m.Item2.ApplySubstitutions(substitution))).ToHashSet();
                    break;
                }
                case (_, InfUnboundVar rightUnbound):
                {
                    if (left.IsUnboundVarIn(rightUnbound))
                        return "Type error: recursion type";
                    var substitution = new Dictionary<InfUnboundVar, InfType>
                    {
                        [rightUnbound] = left
                    };
                    uniqueTerm = uniqueTerm.ApplySubstitutions(substitution);
                    mappings = mappings.Select(m => (m.Item1.ApplySubstitutions(substitution), m.Item2.ApplySubstitutions(substitution))).ToHashSet();
                    break;
                }
                case (InfTypeApp leftApp, InfTypeApp rightApp):
                {
                    if (leftApp.Name != rightApp.Name)
                        return "Type error: type mismatch";
                    if (leftApp.Args.Length != rightApp.Args.Length)
                        return "Type error: type mismatch";
                    for (var i = 0; i < leftApp.Args.Length; i++)
                    {
                        mappings.Add((leftApp.Args[i], rightApp.Args[i]));
                    }
                    break;
                }
                default:
                    return "Type error: type mismatch";
            }
        }

        return uniqueTerm.FixTypes();
    }
}