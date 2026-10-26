import HigherDimLQGMetric.Proper.Proper
import HigherDimLQGMetric.Sec10.Lemma101

/-!
# Properness and geodesics for strong assignments

Lemma 2.2 is an immediate consequence of the general-parameter properness and geodesic
theorems for sharp weak assignments, together with the conversion from strong to sharp weak
assignments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

/-- In a proper continuous metric inducing the Euclidean topology, a compact Euclidean set has
uniformly diverging distance from the complement of sufficiently large Euclidean balls. -/
theorem proper_compact_escape {d : ℕ} (D : ContMetric d) [ProperSpace D.Space]
    {K : Set (Rd d)} (hK : IsCompact K) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d, R ≤ ‖y‖ → M < D.1 (x, y) := by
  intro M
  by_cases hM : M < 0
  · refine ⟨0, fun x hx y hy => ?_⟩
    exact hM.trans_le (D.nonneg x y)
  · by_cases hKne : K.Nonempty
    · have hKD : IsCompact (D.pt '' K) := D.isCompact_image_pt hK
      obtain ⟨C, hC⟩ := hKD.isBounded.subset_closedBall (D.pt 0)
      let C' : ℝ := max C 0
      have hKbound : D.pt '' K ⊆ Metric.closedBall (D.pt 0) C' := by
        exact hC.trans (Metric.closedBall_subset_closedBall (le_max_left C 0))
      have hBallCompact : IsCompact (Metric.closedBall (D.pt 0) (C' + M)) :=
        ProperSpace.isCompact_closedBall (D.pt 0) (C' + M)
      have hEuclideanCompact : IsCompact
          (D.unpt '' Metric.closedBall (D.pt 0) (C' + M)) :=
        hBallCompact.image D.continuous_unpt
      obtain ⟨R₀, hR₀⟩ := hEuclideanCompact.isBounded.subset_closedBall (0 : Rd d)
      refine ⟨max R₀ 0 + 1, fun x hx y hy => ?_⟩
      by_contra hxy
      have hxy' : D.1 (x, y) ≤ M := le_of_not_gt hxy
      have hx0 : dist (D.pt 0) (D.pt x) ≤ C' := by
        have hmem := Metric.mem_closedBall.mp (hKbound ⟨x, hx, rfl⟩)
        simpa only [dist_comm] using hmem
      have hxyDist : dist (D.pt x) (D.pt y) ≤ M := by
        simpa only [D.dist_pt] using hxy'
      have h0y : dist (D.pt 0) (D.pt y) ≤ C' + M := by
        calc
          dist (D.pt 0) (D.pt y) ≤
              dist (D.pt 0) (D.pt x) + dist (D.pt x) (D.pt y) := dist_triangle _ _ _
          _ ≤ C' + M := add_le_add hx0 hxyDist
      have hyBall : D.pt y ∈ Metric.closedBall (D.pt 0) (C' + M) := by
        apply Metric.mem_closedBall.mpr
        simpa only [dist_comm] using h0y
      have hyImage : y ∈ D.unpt '' Metric.closedBall (D.pt 0) (C' + M) := by
        exact ⟨D.pt y, hyBall, by simp⟩
      have hyR₀ : ‖y‖ ≤ R₀ := by
        have hmem := Metric.mem_closedBall.mp (hR₀ hyImage)
        simpa only [dist_zero_right] using hmem
      have hR₀lt : R₀ < max R₀ 0 + 1 := by
        have hle := le_max_left R₀ 0
        linarith
      exact (not_le_of_gt hR₀lt) (hy.trans hyR₀)
    · refine ⟨0, fun x hx y hy => (hKne ⟨x, hx⟩).elim⟩

/-- Almost surely, a strong exponential metric assignment is proper and every pair of points is
joined by a geodesic. This is Lemma 2.2, with the normalized whole-space LGF hypothesis made
explicit on an arbitrary probability space. -/
theorem lemma22_ae_proper_and_geodesic {d : ℕ} (hd : 3 ≤ d) {ξ Q : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (D : DistRd d → ContMetric d) (hD : IsStrongExpMetric d ξ Q D) :
    ∀ᵐ ω ∂P, ProperSpace (D (h ω)).Space ∧
      (∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ,
        ∀ x ∈ K, ∀ y : Rd d, R ≤ ‖y‖ → M < (D (h ω)).1 (x, y)) ∧
      ∀ x y : Rd d, ∃ (γ : ℝ → Rd d) (T : ℝ),
        γ 0 = x ∧ γ T = y ∧ IsGeodesicCurve ((D (h ω)).pt ∘ γ) 0 T := by
  have hhWhole : IsWholeSpaceLGF h P := hh.1
  have hSharp : IsSharpWeakExpMetric d ξ Q D :=
    lemma101 (show 2 ≤ d by omega) hξ hD
  have hproper := lemma27_proper hd hξ hQ hSharp P h hhWhole
  have hgeodesic := lemma27_geodesic hd hξ hQ hSharp P h hhWhole
  filter_upwards [hproper, hgeodesic] with ω hωproper hωgeodesic
  exact ⟨hωproper, fun K hK => proper_compact_escape (D (h ω)) hK, hωgeodesic⟩

end HigherDimLFPPAS
