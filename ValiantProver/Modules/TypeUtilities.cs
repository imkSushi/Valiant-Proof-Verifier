using ValiantProofVerifier;
using static ValiantProver.Modules.Theory;

namespace ValiantProver.Modules;

public static class TypeUtilities
{
    public static void Load() { }

    static TypeUtilities()
    {
        Theory.Load();
    }

    public static TermType TypeOfEnum(Term term)
    {
        if (Theory.IsVar(term))
            return TermType.Var;
        if (Theory.IsConst(term))
            return TermType.Const;
        if (Theory.IsComb(term))
            return TermType.Comb;
        return TermType.Abs;
    }

    public enum TermType
    {
        Var,
        Const,
        Abs,
        Comb
    }

    public static bool IsAbs(Theorem thm)
    {
        return Theory.IsAbs(DeconstructTheorem(thm).conclusion);
    }

    public static bool IsComb(Theorem thm)
    {
        return Theory.IsComb(DeconstructTheorem(thm).conclusion);
    }

    public static bool IsConst(Theorem thm)
    {
        return Theory.IsConst(DeconstructTheorem(thm).conclusion);
    }

    public static bool IsVar(Theorem thm)
    {
        return Theory.IsVar(DeconstructTheorem(thm).conclusion);
    }

    public static (Term parameter, Term abstraction) DeconstructAbs(Theorem thm)
    {
        return Theory.DeconstructAbs(DeconstructTheorem(thm).conclusion);
    }

    public static (Term application, Term argument) DeconstructComb(Theorem thm)
    {
        return Theory.DeconstructComb(DeconstructTheorem(thm).conclusion);
    }
}