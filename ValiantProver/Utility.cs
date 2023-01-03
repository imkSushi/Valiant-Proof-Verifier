using ValiantProofVerifier;

namespace ValiantProver;

public class Utility
{
    public Utility(Kernel kernel)
    {
        Kernel = kernel;
    }
    public Kernel Kernel { get; }

    public Term MakeEquality(Term left, Term right)
    {
        var type = Kernel.TypeOf(left);

        var equality = Kernel.MakeConstant("=", new Dictionary<Type, Type>
        {
            [Kernel.MakeType("A")] = type
        });

        return ApplyBinaryFunction(equality, left, right);
    }

    public Term ApplyBinaryFunction(Term function, Term left, Term right)
    {
        var leftComb = Kernel.MakeCombination(function, left);
        return Kernel.MakeCombination(leftComb, right);
    }
}