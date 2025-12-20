# Lean proofs for the OEIS

## Sum over divisors

The sequence [A281487](https://oeis.org/A281487) is defined by the relation $a(n+1) = -\sum_{d|n} a(d)$, with $a(1)=1$. The file [SumOverDivisors.lean](Oeis/SumOverDivisors.lean) contains the proof that $a(n) \geqslant 0$ if $n$ is odd and $a(n) \leqslant 0$ if $n$ is even.

The proof has been found by [Harmonic](https://harmonic.fun)'s mathematical AI [Aristotle](https://aristotle.harmonic.fun). Initially, I only wrote the definition of `a`, the formulation of `theorem signs`, and a few lines of the theorem body (which didn't survive my subsequent editing anyway). The rest of the proof was written by Aristotle, including the comments. I edited the proof, reducing some redundancy and removing the non-terminal `simp`s and `aesop`s.

In fact, the proof that Aristotle returned didn't work for me: some tactics calls failed with timeout. This repository is pinned to a newer version of Lean and Mathlib than those that Aristotle uses; however, the proof also didn't work with Mathlib 4.24, producing the same errors. I had to change the parts of the proof where this happened.
