# Lean proofs for the OEIS

## Sum over divisors

The sequence [A281487](https://oeis.org/A281487) is defined by the relation $a(n+1) = -\sum_{d|n} a(d)$, with $a(1)=1$. The file [SumOverDivisors.lean](Oeis/SumOverDivisors.lean) ([docs](https://zabolotskii.github.io/oeis-lean/docs/Oeis/SumOverDivisors.html)) contains the proof that $a(n) \geqslant 0$ if $n$ is odd and $a(n) \leqslant 0$ if $n$ is even.

The proof has been found by [Harmonic](https://harmonic.fun)'s mathematical AI [Aristotle](https://aristotle.harmonic.fun). Initially, I only wrote the definition of `a`, the formulation of `theorem signs`, and a few lines of the proof (which didn't survive my subsequent editing anyway). The rest of the proof was written by Aristotle, including the comments. I edited the proof, reducing some redundancy and removing the non-terminal `simp`s and `aesop`s.

In fact, the Lean file that Aristotle returned only worked for me after increasing `maxHeartbeats`. I changed the parts of the proof that required this. Also, this repository is pinned to a newer version of Lean and Mathlib than those that Aristotle uses, but this has not been an issue.
