using ValiantProofVerifier;
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
    
    public static Theorem Congruence(Term application, Theorem argument)
    {
        return Theory.Congruence(Reflexivity(application), argument);
    }
    
    public static Theorem Congruence(Term application, Term argument)
    {
        return Theory.Congruence(Reflexivity(application), Reflexivity(argument));
    }

    public static Theorem Elimination(Theorem toEliminate, Theorem theorem)
    {
        var equality = AntiSymmetry(toEliminate, theorem);
        return ModusPonens(equality, toEliminate);
    }
    
    public static Theorem Elimination(Theorem[] toEliminate, Theorem theorem)
    {
        return toEliminate.Aggregate(theorem, (current, thm) => Elimination(thm, current));
    }

    public static Theorem Substitute(Theorem theorem, Term desired)
    {
        var (typeMap, termMap) = GenerateMaps(DeconstructTheorem(theorem).conclusion, desired);
        var typedTheorem = InstantiateTypes(typeMap, theorem);
        return InstantiateVariables(termMap, typedTheorem);
    }

    public static (Dictionary<Type, Type> typeMap, Dictionary<Term, Term> termMap) GenerateMaps(Term template, Term term)
    {
        var typeMap = new Dictionary<Type, Type>();
        var termMap = new Dictionary<Term, Term>();

        GenerateMaps(template, term, typeMap, termMap);

        return (typeMap, termMap);
    }

    public static void GenerateMaps(Term template, Term term, Dictionary<Type, Type> typeMap, Dictionary<Term, Term> termMap)
    {
        switch (TypeOfEnum(template))
        {
            case TermType.Const:
            {
                if (!IsConst(term))
                    throw new TheoremException("Terms are not convertible");
                
                var (templateConst, templateType) = DeconstructConst(template);
                var (termConst, termType) = DeconstructConst(term);

                if (templateConst != termConst)
                    throw new TheoremException("Terms are not convertible");
                
                GenerateTypeMap(templateType, termType, typeMap);
                break;
            }
            case TermType.Abs:
            {
                if (!IsAbs(term))
                    throw new TheoremException("Terms are not convertible");
                
                var (templateParam, templateAbs) = DeconstructAbs(template);
                var (termParam, termAbs) = DeconstructAbs(term);
                
                var (templateParamName, templateParamType) = DeconstructVar(templateParam);
                var (termParamName, termParamType) = DeconstructVar(termParam);
                
                if (templateParamName != termParamName)
                    throw new TheoremException("Terms are not convertible");
                
                GenerateMaps(templateAbs, termAbs, typeMap, termMap);
                GenerateTypeMap(templateParamType, termParamType, typeMap);
                break;
            }
            case TermType.Comb:
            {
                if (!IsComb(term))
                    throw new TheoremException("Terms are not convertible");
                
                var (templateApplication, templateArgument) = DeconstructComb(template);
                var (termApplication, termArgument) = DeconstructComb(term);
                
                GenerateMaps(templateApplication, termApplication, typeMap, termMap);
                GenerateMaps(templateArgument, termArgument, typeMap, termMap);
                break;
            }
            case TermType.Var:
            {
                var termType = TypeOf(term);
                var templateName = DeconstructVar(template).name;
                var newVariable = MakeVariable(templateName, termType);
                
                GenerateTypeMap(TypeOf(template), termType, typeMap);

                if (IsVar(term) && templateName == DeconstructVar(term).name)
                    break;

                if (!termMap.TryGetValue(newVariable, out var subs))
                    termMap[newVariable] = term;
                else if (subs != term)
                    throw new TheoremException("Terms are not convertible");
                
                break;
            }
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    public static void GenerateTypeMap(Type template, Type type, Dictionary<Type, Type> map)
    {
        if (template == type)
            return;
        
        if (IsTyVar(template))
        {
            if (!map.TryGetValue(template, out var subs))
                map[template] = type;
            else if (subs != type)
                throw new TheoremException("Types are not convertable");
        }
        else
        {
            if (!IsTyApp(type))
                throw new TheoremException("Types are not convertable");

            var (templateName, templateArgs) = DeconstructTyApp(template);
            var (typeName, typeArgs) = DeconstructTyApp(type);

            if (templateName != typeName)
                throw new TheoremException("Types are not convertable");
            
            for (var i = 0; i < templateArgs.Length; i++)
            {
                GenerateTypeMap(templateArgs[i], typeArgs[i], map);
            }
        }
    }
}