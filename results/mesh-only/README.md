# Mesh-only Dirichlet convergence

The accompanying Lean result is **qualitative Dirichlet convergence from vanishing mesh**, including uniformity over bounded C² families on a fixed common harmonic neighborhood.

- [Exact statement](../../MeshOnly/MeshOnlyStatement.lean): `BouRabeeGwynne.MeshOnlyTheorem11Statement`.
- [Proof](../../MeshOnly/MeshOnlyConvergence.lean): `BouRabeeGwynne.meshOnly_theorem11_proved`.
- [AI research paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/mesh-only-tilings-and-rates.pdf).

For d ≥ 2, the global mesh of orthogonal tilings tends to zero. On every bounded open set compactly contained in the open tiling domain, sampled harmonic boundary data have an eventually well-posed discrete Dirichlet problem and the discrete solutions converge uniformly to the harmonic function. The conductance is facet surface volume divided by distance between marked vertices. No geometric alternatives I, II, or III are imposed.

The family version fixes one common harmonic neighborhood and bounds the function, its first derivative, and its second derivative there before selecting the eventual index. Uniqueness is on the closed graph region; it makes no claim about values at unrelated ambient vertices.

## Scope in the combined paper

This formalization was written for Theorem 1.1 of the earlier nine-page volume-notation draft. It covers the convergence statement retained in the combined paper. It **does not formalize the sharper ε^(4/(d+4)) error rate or the random-walk corollary**. These should not be inferred from the presence of the Lean link.

## Source and verification

The 64 `MeshOnly` modules are unchanged source from development commit `ec3738f9c8df2e584e35ad8ef816b581cf217160`. Their 81 shared `BouRabeeGwynne` dependencies were already included here and are byte-identical to that source. The [source manifest](../../source-manifest.json) records the exact import closure and hashes.

Use the pinned toolchain and dependencies in this repository:

```sh
lake exe cache get
lake build MeshOnly
lake env lean results/mesh-only/Check.lean
```

The check verifies the exact theorem type, absence of `sorry`, and axiom dependencies. The standard foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. These checks concern the encoded statement; the mathematical scope is specified above.
