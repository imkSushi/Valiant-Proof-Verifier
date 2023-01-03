namespace ValiantKernel;

public abstract class Kernel<TType, TTerm, TThm> where TType : notnull
{
    public abstract TThm ProofReflexivity(TTerm term);
    public abstract TThm ProofTransitivity(TThm thm1, TThm thm2);
    public abstract TThm ProofCongruence(TThm thm1, TThm thm2);
    public abstract TThm ProofAbstraction(TTerm term, TThm thm);
    public abstract TThm ProofBetaReduction(TTerm term);
    public abstract TThm ProofAssume(TTerm thm);
    public abstract TThm ProofModusPonens(TThm maj, TThm min);
    public abstract TThm ProofDeductAntisymmetryRule(TThm thm1, TThm thm2);
    /*
    public abstract TThm ProofInstanceType((TType, TType)[] types, TThm thm);
    public abstract TThm ProofInstance((TTerm, TTerm)[] terms, TThm thm);*/

    public abstract Dictionary<string, int> GetTypes();
    public abstract void NewType(string name, int arity);
    public abstract TType MakeType(string name, TType[] args);
    public abstract TType MakeVarType(string name);
    public abstract (string name, TType[] args) DestType(TType type);
    public abstract string DestVarType(TType type);
    public abstract bool IsType(TType type);
    public abstract bool IsVarType(TType type);
    
    public abstract TType TypeOf(TTerm term);
    public abstract TType BoolType { get; }
    public abstract TType ATy { get; }
    
    public abstract TTerm MakeVar(string name, TType type);
    public abstract TTerm MakeConst(string name, Dictionary<TType, TType> map);
    public abstract TTerm MakeComb(TTerm application, TTerm argument);
    public abstract TTerm MakeAbs(TTerm parameter, TTerm abstraction);
    public abstract Dictionary<string, TType> GetConstants();
    public abstract void NewConstant(string name, TType type);
    public abstract Func<TType, TType> SubstituteTypes(Dictionary<TType, TType> map);
    public abstract TTerm[] Frees(TTerm term);
    public abstract TTerm[] Frees(TTerm[] terms);
    public abstract Func<TTerm, bool> FreesIn(TTerm[] terms);
    public abstract bool VarFreeIn(TTerm variable, TTerm term);
    public abstract Func<TTerm, TTerm> Instance(Dictionary<TType, TType> map);
    public abstract Func<TTerm, TTerm> Variant(TTerm[] avoid);
    public abstract (string name, TType type) DestVar(TTerm term);
    public abstract (string name, TType type) DestConst(TTerm term);
    public abstract (TTerm application, TTerm argument) DestComb(TTerm term);
    public abstract (TTerm parameter, TTerm abstraction) DestAbs(TTerm term);
    public abstract Func<Term, Term> VarSubstitution(Term variable, Term term);
}