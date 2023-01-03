﻿namespace ValiantProofVerifier3;

public record Theorem
{
    private Theorem()
    {
        
    }
    
    internal sealed record Sequent(Term[] Premises, Term Conclusion) : Theorem;
}