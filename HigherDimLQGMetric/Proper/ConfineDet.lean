import HigherDimLQGMetric.Proper.HighSphere
import LQGMetric.Metric.Geodesic

/-!
# Deterministic confinement of geodesics by a distant sphere

Only triangle inequalities, continuity, and the length-minimizing property of a geodesic are used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- A sphere farther than twice the endpoint-ball diameter cannot be reached by a geodesic
whose endpoints are in that ball. -/
theorem proper_no_geodesic_escape (D : ContMetric d)
    {L A R m : ℝ} (hR : 0 < R) (hLA : L < A)
    (hS : ∀ v : Rd d, ‖v‖ = A * R → 2 * m < D.1 (0, v))
    (hU : ∀ x y : Rd d, ‖x‖ < L * R → ‖y‖ < L * R → D.1 (x, y) < m) :
    ¬ ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧
      IsGeodesicCurve (D.pt ∘ γ) 0 T ∧ ‖γ 0‖ < L * R ∧ ‖γ T‖ < L * R ∧
      ∃ t ∈ Icc (0 : ℝ) T, A * R ≤ ‖γ t‖ := by
  rintro ⟨γ, T, hT, hgeo, hx, hy, t, ht, htbig⟩
  have hstart : ‖γ 0‖ < A * R := hx.trans (mul_lt_mul_of_pos_right hLA hR)
  have hcont : ContinuousOn (fun s : ℝ => ‖γ s‖) (Icc 0 t) := by
    have hγ : ContinuousOn γ (Icc 0 T) := by
      have := D.continuous_unpt.comp_continuousOn hgeo.2.1
      simpa only [Function.comp_def, D.unpt_pt] using this
    exact hγ.norm.mono (Icc_subset_Icc le_rfl ht.2)
  obtain ⟨s, hs, hsR⟩ := intermediate_value_Icc ht.1 hcont
    (show A * R ∈ Icc (‖γ 0‖) (‖γ t‖) from ⟨hstart.le, htbig⟩)
  have hsT : s ≤ T := hs.2.trans ht.2
  have hshort : D.1 (γ 0, γ s) ≤ D.1 (γ 0, γ T) := by
    have hlen : edist ((D.pt ∘ γ) 0) ((D.pt ∘ γ) s) ≤
        edist ((D.pt ∘ γ) 0) ((D.pt ∘ γ) T) := by
      calc
        edist ((D.pt ∘ γ) 0) ((D.pt ∘ γ) s)
            ≤ curveLength (D.pt ∘ γ) 0 s := edist_le_curveLength _ hs.1
        _ ≤ curveLength (D.pt ∘ γ) 0 T := curveLength_mono _ le_rfl hsT
        _ = edist ((D.pt ∘ γ) 0) ((D.pt ∘ γ) T) := hgeo.2.2
    have hlen' : ENNReal.ofReal (D.1 (γ 0, γ s)) ≤
        ENNReal.ofReal (D.1 (γ 0, γ T)) := by
      simpa only [Function.comp_apply, D.edist_pt] using hlen
    exact (ENNReal.ofReal_le_ofReal_iff (D.nonneg _ _)).1 hlen'
  have hLR : 0 < L * R := (norm_nonneg (γ 0)).trans_lt hx
  have h0 := hU 0 (γ 0) (by simpa only [norm_zero] using hLR) hx
  have hxy := hU (γ 0) (γ T) hx hy
  have htri := D.apply_triangle 0 (γ 0) (γ s)
  have hbad : D.1 (0, γ s) < 2 * m := by linarith
  exact (not_lt_of_ge (hS (γ s) hsR).le) hbad

end HigherDimLQGMetric
