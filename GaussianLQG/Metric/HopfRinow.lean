import LQGMetric.Papers.GM.S2.Geodesics

/-!
# Existence of constant-speed geodesics (blueprint Lemma `lem:hopf-rinow`)

Blueprint Lemma `lem:hopf-rinow`: let `d` be a length metric on `ℂ` inducing the Euclidean
topology whose closed balls `{x : d(z, x) ≤ ρ}` are compact. Then any `z, w ∈ ℂ` are joined by a
constant-speed `d`-geodesic, which is a Euclidean-continuous path.

Here `d` is a `LQGMetric.ContMetric` (a continuous metric inducing the Euclidean topology) with
`ContMetric.IsLength`, and the geodesic is `η : C([0,1], ℂ)` with
`LQGMetric.Blueprint.IsGeod01 D z w η` (`D(η s, η t) = |t - s| D(z, w)`); being an element of
`C([0,1], ℂ)`, it is Euclidean-continuous. The statement is a wrapper around
`LQGMetric.GM.exists_isGeod01_of_bcpt` (GM S1.1, deterministic form, via BBI Cor. 2.5.20),
whose bounded-compactness hypothesis follows from compactness of closed `D`-balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace GaussianLQG

open LQGMetric LQGMetric.Blueprint

/-- Compact closed `D`-balls make every closed `D`-bounded set compact. -/
theorem isCompact_of_isClosed_of_bounded (D : ContMetric)
    (hc : ∀ (z : ℂ) (ρ : ℝ), IsCompact {x : ℂ | D.1 (z, x) ≤ ρ}) {A : Set ℂ} (hA : IsClosed A)
    (hb : ∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, D.1 (u, v) ≤ M) : IsCompact A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
  · exact isCompact_empty
  obtain ⟨M, hM⟩ := hb
  exact (hc u M).of_isClosed_subset hA fun v hv => hM u hu v hv

/-- **Blueprint Lemma `lem:hopf-rinow`.** If `D` is a continuous length metric on `ℂ` whose
closed balls are compact, then any two points are joined by a constant-speed `D`-geodesic
`η : C([0,1], ℂ)`. -/
theorem exists_isGeod01_of_isCompact_closedBall (D : ContMetric) (hL : D.IsLength)
    (hc : ∀ (z : ℂ) (ρ : ℝ), IsCompact {x : ℂ | D.1 (z, x) ≤ ρ}) (z w : ℂ) :
    ∃ η : C(unitInterval, ℂ), IsGeod01 D z w η :=
  GM.exists_isGeod01_of_bcpt D hL (fun _ hA hb => isCompact_of_isClosed_of_bounded D hc hA hb) z w

end GaussianLQG
