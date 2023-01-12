using ValiantBasics;
using ValiantProofVerifier;
using ValiantResults;

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
        if (term.IsVar())
            return TermType.Var;
        if (term.IsConst())
            return TermType.Const;
        if (term.IsComb())
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
        return thm.Conclusion().IsAbs();
    }

    public static bool IsComb(Theorem thm)
    {
        return thm.Conclusion().IsComb();
    }

    public static bool IsConst(Theorem thm)
    {
        return thm.Conclusion().IsConst();
    }

    public static bool IsVar(Theorem thm)
    {
        return thm.Conclusion().IsVar();
    }

    public static (Term parameter, Term abstraction) DeconstructAbs(Theorem thm)
    {
        return thm.Conclusion().DeconstructAbs();
    }
    
    public static Result<Term, Term> TryDeconstructAbs(Theorem thm) //parameter & abstraction
    {
        return thm.Conclusion().TryDeconstructAbs();
    }

    public static (Term application, Term argument) DeconstructComb(Theorem thm)
    {
        return thm.Conclusion().DeconstructComb();
    }
    
    public static Result<Term, Term> TryDeconstructComb(Theorem thm) //application & argument
    {
        return thm.Conclusion().TryDeconstructComb();
    }
}