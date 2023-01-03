using ValiantProofVerifier;

namespace ValiantProver;

public class PeanoAxioms
{
    public PeanoAxioms(Kernel kernel)
    {
        Kernel = kernel;
        kernel.DefineType("nat", 0);
        var nat = kernel.MakeType("nat", Array.Empty<Type>());
        kernel.DefineConstant("0", nat);
        kernel.DefineConstant("Suc", kernel.MakeType("fun", new []{nat, nat}));
    }
    public Kernel Kernel { get; }
}