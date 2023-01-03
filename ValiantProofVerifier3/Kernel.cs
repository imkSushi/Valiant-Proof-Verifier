namespace ValiantProofVerifier3;

public abstract class Kernel<TType, TTerm, TThm> where TType : notnull where TTerm : notnull
{
    public abstract Dictionary<string, int> Types();
    public abstract int GetTypeArity(string type);
    public abstract void NewType(string name, int arity);
    public abstract TType MakeType(string name, TType[] args);
    public abstract TType MakeVarType(string name);
    public abstract (string name, TType[] args) DestructType(TType type);
    public abstract string DestructVarType(TType type);
    public abstract bool IsType(TType type);
    public abstract bool IsVarType(TType type);
    public abstract TType[] TyVars(TType type);
    public abstract Func<TType, TType> TypeSubst(Dictionary<TType, TType> map);
    public abstract TType BoolTy { get; set; }
    public abstract TType Aty { get; set; }
    
    public abstract Dictionary<string, TType> Constants();
    public abstract TType GetConstType(string name);
    public abstract void NewConst(string name, TType type);
    public abstract TType TypeOf(TTerm term);
    public abstract Func<TTerm, int> AlphaOrder(TTerm term);
    public abstract bool IsVar(TTerm term);
    public abstract bool IsConst(TTerm term);
    public abstract bool IsAbs(TTerm term);
    public abstract bool IsComb(TTerm term);
    public abstract TTerm MakeVar(string name, TType type);
    public abstract TTerm MakeConst(string name, Dictionary<TType, TType> map);
    public abstract TTerm MakeAbs(TTerm parameter, TTerm abstraction);
    public abstract TTerm MakeComb(TTerm application, TTerm argument);
    public abstract (string name, TType type) DestructVar(TTerm term);
    public abstract (string name, TType type) DestructConst(TTerm term);
    public abstract (TTerm application, TTerm argument) DestructComb(TTerm term);
    public abstract (TTerm parameter, TTerm abstraction) DestructAbs(TTerm term);
    public abstract TTerm[] Frees(TTerm term);
    public abstract TTerm[] Freesl(TTerm[] terms);
    public abstract Func<TTerm, bool> Freesin(TTerm[] terms);
    public abstract Func<TTerm, bool> VfreeIn(TTerm variable);
    public abstract TType[] TypeVarsInTerm(TTerm term);
    public abstract Func<TTerm, TTerm> Variant(TTerm[] terms);
    public abstract Func<TTerm, TTerm> Vsubst(Dictionary<TTerm, TTerm> map);
    public abstract Func<TTerm, TTerm> Inst(Dictionary<TType, TType> map);
    public abstract TTerm Rand(TTerm term);
    public abstract TTerm Rator(TTerm term);
    public abstract (TTerm, TTerm) DestEq(TTerm term);
}