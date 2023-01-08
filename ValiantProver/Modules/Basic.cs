using ValiantBasics;
using ValiantProofVerifier;
using static ValiantBasics.Utilities;
using static ValiantProver.Modules.Theory;
using static ValiantProver.Modules.TypeUtilities;

namespace ValiantProver.Modules;

public static class Basic
{
    public static void Load() { }

    static Basic()
    {
        TypeUtilities.Load();

        Parser.TryRegisterInfixRule("=", "=", 0, true);
    }

    public static Theorem Congruence(Theorem application, Term argument)
    {
        return Theory.Congruence(application, Reflexivity(argument));
    }
    
    public static Result<Theorem> TryCongruence(Theorem application, Term argument)
    {
        return Theory.TryCongruence(application, Reflexivity(argument));
    }

    public static Theorem Congruence(Term application, Theorem argument)
    {
        return Theory.Congruence(Reflexivity(application), argument);
    }
    
    public static Result<Theorem> TryCongruence(Term application, Theorem argument)
    {
        return Theory.TryCongruence(Reflexivity(application), argument);
    }

    public static Theorem Congruence(Term application, Term argument)
    {
        return Theory.Congruence(Reflexivity(application), Reflexivity(argument));
    }
    
    public static Result<Theorem> TryCongruence(Term application, Term argument)
    {
        return Theory.TryCongruence(Reflexivity(application), Reflexivity(argument));
    }

    private static Theorem Elimination(Theorem toEliminate, Theorem theorem)
    {
        var equality = AntiSymmetry(toEliminate, theorem);
        return ModusPonens(equality, toEliminate);
    }
    
    private static Result<Theorem> TryElimination(Theorem toEliminate, Theorem theorem)
    {
        var premise = toEliminate.Conclusion();
        if (!theorem.Premises().Contains(premise))
            return $"Premise {premise} not found in {theorem}";
        
        var equality = AntiSymmetry(toEliminate, theorem);
        return ModusPonens(equality, toEliminate);
    }

    public static Theorem Elimination(Theorem theorem, params Theorem[] toEliminate)
    {
        return toEliminate.Aggregate(theorem, (current, thm) => Elimination(thm, current));
    }
    
    public static Result<Theorem> TryElimination(Theorem theorem, params Theorem[] toEliminate)
    {
        foreach (var elim in toEliminate)
        {
            if (!TryElimination(elim, theorem).Deconstruct(out var newTheorem, out var error))
                return error;
            
            theorem = newTheorem;
        }
        
        return theorem;
    }

    public static Theorem Substitute(Theorem theorem, Term desired)
    {
        var (typeMap, termMap) = GenerateMaps(theorem.Conclusion(), desired);
        var typedTheorem = InstantiateTypes(typeMap, theorem);
        return InstantiateVariables(termMap, typedTheorem);
    }
    
    public static Result<Theorem> TrySubstitute(Theorem theorem, Term desired)
    {
        if (!TryGenerateMaps(theorem.Conclusion(), desired).Deconstruct(out var maps, out var error))
            return error;
        var (typeMap, termMap) = maps;
        
        if (!TryInstantiateTypes(typeMap, theorem).Deconstruct(out var typedTheorem, out error))
            return error;
        
        return TryInstantiateVariables(termMap, typedTheorem);
    }

    public static (Dictionary<Type, Type> typeMap, Dictionary<Term, Term> termMap) GenerateMaps(Term template,
        Term term)
    {
        var typeMap = new Dictionary<Type, Type>();
        var termMap = new Dictionary<Term, Term>();

        GenerateMaps(template, term, typeMap, termMap);

        return (typeMap, termMap);
    }
    
    public static Result<Dictionary<Type, Type>, Dictionary<Term, Term>> TryGenerateMaps(Term template,
        Term term) //typeMap & termMap
    {
        var typeMap = new Dictionary<Type, Type>();
        var termMap = new Dictionary<Term, Term>();

        return TryGenerateMaps(template, term, typeMap, termMap).Deconstruct(out var error)
            ? (typeMap, termMap)
            : error;
    }

    public static void GenerateMaps(Term template,
        Term term,
        Dictionary<Type, Type> typeMap,
        Dictionary<Term, Term> termMap)
    {
        if (TryGenerateMaps(template, term, typeMap, termMap).IsError(out var error))
            throw new TheoremException(error);
    }

    public static Result TryGenerateMaps(Term template,
        Term term,
        Dictionary<Type, Type> typeMap,
        Dictionary<Term, Term> termMap)
    {
        switch (TypeOfEnum(template))
        {
            case TermType.Const:
            {
                if (!term.IsConst())
                    return "Terms are not convertible";

                var (templateConst, templateType) = template.DeconstructConst();
                var (termConst, termType) = term.DeconstructConst();

                if (templateConst != termConst)
                    return "Terms are not convertible";

                return TryGenerateTypeMap(templateType, termType, typeMap);
            }
            case TermType.Abs:
            {
                if (!term.IsAbs())
                    return "Terms are not convertible";

                var (templateParam, templateAbs) = template.DeconstructAbs();
                var (termParam, termAbs) = term.DeconstructAbs();

                var (templateParamName, templateParamType) = templateParam.DeconstructVar();
                var (termParamName, termParamType) = termParam.DeconstructVar();

                if (templateParamName != termParamName)
                    return "Terms are not convertible";

                
                return TryGenerateMaps(templateAbs, termAbs, typeMap, termMap) && TryGenerateTypeMap(templateParamType, termParamType, typeMap);
            }
            case TermType.Comb:
            {
                if (!term.IsComb())
                    return "Terms are not convertible";

                var (templateApplication, templateArgument) = template.DeconstructComb();
                var (termApplication, termArgument) = term.DeconstructComb();

                return TryGenerateMaps(templateApplication, termApplication, typeMap, termMap) && TryGenerateMaps(templateArgument, termArgument, typeMap, termMap);
            }
            case TermType.Var:
            {
                var termType = term.TypeOf();
                var templateName = template.DeconstructVar().name;
                var newVariable = MakeVariable(templateName, termType);


                if (TryGenerateTypeMap(template.TypeOf(), termType, typeMap).IsError(out var error))
                    return error;

                if (term.IsVar() && templateName == term.DeconstructVar().name)
                    return Result.Success;

                if (!termMap.TryGetValue(newVariable, out var subs))
                    termMap[newVariable] = term;
                else if (subs != term)
                    return "Terms are not convertible";

                return Result.Success;
            }
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    public static Dictionary<Type, Type> GenerateTypeMap(Type template, Type type)
    {
        var output = new Dictionary<Type, Type>();
        GenerateTypeMap(template, type, output);
        return output;
    }

    public static Result<Dictionary<Type, Type>> TryGenerateTypeMap(Type template, Type type)
    {
        var output = new Dictionary<Type, Type>();
        return TryGenerateTypeMap(template, type, output).Deconstruct(out var error) ? output : error;
    }

    public static void GenerateTypeMap(Type template, Type type, Dictionary<Type, Type> map)
    {
        if (!TryGenerateTypeMap(template, type, map).Deconstruct(out var error))
            throw new TheoremException(error);
    }

    public static Result TryGenerateTypeMap(Type template, Type type, Dictionary<Type, Type> map)
    {
        if (template == type)
            return Result.Success;

        if (template.IsTyVar())
        {
            if (!map.TryGetValue(template, out var subs))
                map[template] = type;
            else if (subs != type)
                return "Types are not convertable";
            
            return Result.Success;
        }

        if (!type.IsTyApp())
            return "Types are not convertable";

        var (templateName, templateArgs) = template.DeconstructTyApp();
        var (typeName, typeArgs) = type.DeconstructTyApp();

        if (templateName != typeName)
            return "Types are not convertable";

        for (var i = 0; i < templateArgs.Length; i++)
        {
            if (TryGenerateTypeMap(templateArgs[i], typeArgs[i], map).IsError(out var error))
                return error;
        }
        
        return Result.Success;
    }

    public static string GetFreeVariableName(Term term)
    {
        var nameGen = new NewNameTypeGenerator();
        var name = nameGen.Next();
        var usedNames = UsedNames(term);
        while (usedNames.Contains(name))
        {
            name = nameGen.Next();
        }
        
        return name;
    }

    public static string GetFreeVariableName(Theorem theorem)
    {
        var nameGen = new NewNameTypeGenerator();
        var name = nameGen.Next();
        var usedNames = UsedNames(theorem);
        while (usedNames.Contains(name))
        {
            name = nameGen.Next();
        }
        
        return name;
    }

    public static string GetFreeVariableName(Term[] terms)
    {
        var nameGen = new NewNameTypeGenerator();
        var name = nameGen.Next();
        var usedNames = UsedNames(terms);
        while (usedNames.Contains(name))
        {
            name = nameGen.Next();
        }
        
        return name;
    }

    public static HashSet<string> UsedNames(Theorem theorem)
    {
        var (premises, conclusion) = theorem.Deconstruct();
        return UsedNames(premises.Append(conclusion).ToArray());
    }

    public static HashSet<string> UsedNames(Term[] terms)
    {
        var output = new HashSet<string>();
        foreach (var t in terms)
        {
            UsedNames(t, output);
        }

        return output;
    }

    public static HashSet<string> UsedNames(Term term)
    {
        var output = new HashSet<string>();
        UsedNames(term, output);
        return output;
    }

    private static void UsedNames(Term term, HashSet<string> used)
    {
        switch (TypeOfEnum(term))
        {
            case TermType.Var:
            {
                used.Add(term.DeconstructVar().name);
                break;
            }
            case TermType.Const:
                break;
            case TermType.Abs:
            {
                var (param, abs) = term.DeconstructAbs();
                UsedNames(param, used);
                UsedNames(abs, used);
                break;
            }
            case TermType.Comb:
            {
                var (application, argument) = term.DeconstructComb();
                UsedNames(application, used);
                UsedNames(argument, used);
                break;
            }
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    public static Result<Type, Type> TryDeconstructFun(this Type type)
    {
        if (!type.TryDeconstructTyApp("fun").Deconstruct(out var args, out var error))
            return error;
        
        return (args[0], args[1]);
    }
    
    public static (Type from, Type to) DeconstructFun(this Type type)
    {
        return type.TryDeconstructFun().ValueOrException();
    }
}