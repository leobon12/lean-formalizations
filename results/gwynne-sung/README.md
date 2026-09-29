# Random walk reflected off of infinity

Lean formalization of **Theorem 1.6 with a documented correction** from Ewain Gwynne and Jinwoo Sung, [*Random walk reflected off of infinity, with applications to uniform spanning forests and supercritical Liouville quantum gravity*, arXiv:2506.18827v2](https://arxiv.org/abs/2506.18827v2).

The result constructs a continuous-time random walk reflected off of infinity on a countably infinite connected conductance graph and proves uniqueness in law. Vertex degrees may be infinite; total conductance at each vertex is finite. The theorem chooses a positive rate threshold and applies to every rate function above it.

## Exact statement and proof

| | Lean source |
| --- | --- |
| Statement and process properties | [`Theorem16Statement`, `IsReflectedWalk`](../../ReflectedWalk/Theorem16Statement.lean) |
| Main proof | [`ReflectedWalk.theorem16_closed`](../../ReflectedWalk/Theorem16Closed.lean) |
| Energy-minimizer construction | [`Proposition13.lean`](../../ReflectedWalk/Proposition13.lean) |

```lean
theorem theorem16_closed (G : ConductanceGraph V) (hmin : G.EnergyMinimizer) :
    Theorem16Statement G hmin
```

The energy-minimizer bundle is supplied by the accompanying proved construction. It is displayed in the signature rather than hidden from the statement.

## The correction: right continuity at infinity

The printed property (ii) constrains paths at vertex-valued times. The formalized process class additionally requires right continuity at times when the process is at infinity: for every vertex, the path avoids that vertex for a sufficiently short interval immediately afterward.

This distinction changes the scope:

- **Existence:** the constructed process satisfies the additional regularity clause.
- **Uniqueness:** uniqueness in law is proved among processes satisfying the additional clause.
- Uniqueness over the paper's literally printed, larger class is **not claimed** by this release.

The theorem is numbered 1.6 in v2 and 1.5 in v1. This release concerns that theorem and its dependencies, not the paper's spanning-forest or LQG applications. It also makes no claim to formalize every subsidiary statement in Sections 2–3. For example, the second, cycle-space half of Lemma 2.1 is outside the selected proof's scope.

The energy formalization uses real-valued sums and compares the minimizer against finite-energy competitors; infinite-energy competitors are not represented by a valid finite real-valued energy comparison.

## Check this result

See [verification instructions](../../VERIFICATION.md) and the [certificate](../../Certificate.lean), which checks the main declaration for proof placeholders and nonstandard axiom dependencies. The pinned toolchain and all local dependencies are included in this public snapshot.

[All released formalizations](../../README.md)
