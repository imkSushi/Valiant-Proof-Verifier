using ValiantProofVerifier;

namespace ValiantProver;

public struct FourwayTheorem
{
    public FourwayTheorem(Theorem theorem, UtilityTheorems utilityTheorems)
    {
        Standard = theorem;
        Converse = utilityTheorems.ApplyCommutativity(theorem);
        StandardElimination = utilityTheorems.Eliminate(theorem);
        ConverseElimination = utilityTheorems.Eliminate(Converse);
    }

    public Theorem Standard;
    public Theorem Converse;
    public Theorem StandardElimination;
    public Theorem ConverseElimination;
}