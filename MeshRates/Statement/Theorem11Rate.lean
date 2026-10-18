import MeshOnly.MeshOnlyStatement

/-!
# MR Theorem 1.1 (mesh-only Dirichlet convergence, with the rate (10)) — DRAFT statements

Source: MR = "Mesh-only convergence and sharper rates on orthogonal tilings", p. 3,
Theorem 1.1, equations (9) and (10); the constant form is MR (81), p. 15.
See `STATEMENT_SPEC.md` for the line-by-line comparison and the proposed deviation rows.

All objects are reused: `OrthogonalTiling`, `TilingSequence`, `mesh`, `interiorVertices`,
`closedVertices`, `SolvesDirichlet`, `DirichletError`, `HasUniqueDirichletExtension`,
`DirichletApproximationTarget`, `HarmonicNearClosure`, `HasAmbientCollar` (BouRabeeGwynne) and
`C2BoundOn`, `TilingSequence.MeshConverges` (MeshOnly). These are target definitions only;
nothing is proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology ENNReal

namespace BouRabeeGwynne.MeshRates

/-- MR (10): the exponent `β_d = 4/(d+4)`. -/
noncomputable def meshRateExponent (d : ℕ) : ℝ := 4 / ((d : ℝ) + 4)

/-- MR Theorem 1.1, equation (9) (qualitative part).

`d ≥ 2`; `U` bounded with `closure U ⊆ interior D` (MR: `U ⋐ D`, `D` open); the tilings `G n`
of the common set `D` have mesh tending to `0`; `h` is `C²` and harmonic on an open neighbourhood
of `closure U`. Conclusion: eventual finiteness and unique solvability of (7), and uniform
convergence over `V_n[U]` for every solution `h_{D,n}` of (7). `U` is NOT assumed open: MR does
not assume it, and MR §7 applies Theorem 1.1 to the non-open set `B_r(x) ∩ B_δ(D₀)`. -/
def MeshRatesTheorem11QualitativeStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (G : TilingSequence d) (U : Set (Euc d)),
    Bornology.IsBounded U → HasAmbientCollar U G.domain → G.MeshConverges →
    ∀ h : Euc d → ℝ, HarmonicNearClosure h U →
      DirichletApproximationTarget G U h (fun n v => h ((G.tiling n).pos v))

/-- MR Theorem 1.1, equation (10) with the constant form (81), in single-tiling form.

For `d ≥ 2`, bounded `U` and bounded open `K` with `closure U ⊆ K`, there are a mesh threshold
`ε₀ > 0` and a constant `C ≥ 0` — chosen after `d, U, K` only, hence before the tiled set `D`, the
tiling, `h_C` and `h_D` — such that for EVERY orthogonal tiling `T` of EVERY set `D` with
`closure K ⊆ interior D` (MR: `K ⋐ D`) and mesh `ε ≤ ε₀`:
* the Dirichlet problem (7) on `V[U]` is well posed (finite closed region, unique solution for
  every boundary datum; MR p. 3), and
* for every `h_C` that is `C²` and harmonic on an open neighbourhood of `closure K`, every
  `M` bounding `|h_C|, ‖Dh_C‖, ‖D²h_C‖` on `K` (i.e. `M ≥ ‖h_C‖_{C²(K)}`), and every solution
  `h_D` of (7): `|h_D(v) - h_C(v)| ≤ C · M · ε^{4/(d+4)}` for all `v ∈ V[U]`. -/
def MeshRatesTheorem11RateStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (U K : Set (Euc d)),
    Bornology.IsBounded U → IsOpen K → Bornology.IsBounded K → closure U ⊆ K →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ T : OrthogonalTiling d,
        HasAmbientCollar K T.domain → T.mesh ≤ ENNReal.ofReal ε₀ →
        ((T.closedVertices U).Finite ∧
          ∀ g : T.V → ℝ, T.HasUniqueDirichletExtension U g) ∧
        ∀ h : Euc d → ℝ, HarmonicNearClosure h K →
          ∀ M : ℝ, C2BoundOn h K M →
            ∀ hD : T.V → ℝ, T.SolvesDirichlet U (fun v => h (T.pos v)) hD →
              T.DirichletError U h hD (C * M * T.mesh.toReal ^ meshRateExponent d)

/-- MR Theorem 1.1 in full: (9) and (10). The final sentence of the theorem ("uniform over
families for which these quantities are uniformly bounded") is an immediate reading of the
rate statement, whose `ε₀` and `C` depend only on `d, U, K` and whose bound is linear in `M`. -/
def MeshRatesTheorem11Statement : Prop :=
  MeshRatesTheorem11QualitativeStatement ∧ MeshRatesTheorem11RateStatement

end BouRabeeGwynne.MeshRates
