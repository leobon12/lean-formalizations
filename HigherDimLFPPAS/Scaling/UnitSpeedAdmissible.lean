import HigherDimLFPPAS.Core.Interfaces

/-!
# Unit-speed geodesics are admissible internal geodesics

The global metric is bounded above by every internal metric, while the length of a
unit-speed segment bounds the internal metric from above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Scaling

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

theorem unitSpeedAdmissible_holds (d : ℕ) : Core.UnitSpeedAdmissible d := by
  intro G R γ T hT hcont hmap hspeed
  have hEdist : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      edist (G.pt (γ s)) (G.pt (γ t)) = edist s t := by
    intro s hs t ht
    rw [G.edist_pt, hspeed s hs t ht, edist_dist, Real.dist_eq]
    congr 1
    rw [abs_sub_comm]
  obtain ⟨_, hUnit⟩ := isGeodesicCurve_of_edist_eq hT hEdist
  have hball : ball (0 : Rd d) R ⊆ ball 0 (R + 1) :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨hT, hcont, ?_, ?_, ?_⟩
  · intro t ht
    exact hball (hmap ht)
  · intro s hs t ht
    by_cases hst : s ≤ t
    · have hlen : G.len γ s t = ENNReal.ofReal (t - s) := by
        rw [G.len_def]
        change curveLength (fun q => G.pt (γ q)) s t = _
        exact curveLength_of_hasUnitSpeedOn hUnit hs ht
      apply le_antisymm
      · calc
          G.internal (ball (0 : Rd d) (R + 1)) (γ s) (γ t) ≤ G.len γ s t :=
            G.internal_le_len hst (hcont.mono (Icc_subset_Icc hs.1 ht.2))
              ((hmap.mono_right hball).mono_left (Icc_subset_Icc hs.1 ht.2))
          _ = ENNReal.ofReal |t - s| := by rw [hlen, abs_of_nonneg (sub_nonneg.mpr hst)]
      · calc
          ENNReal.ofReal |t - s| = ENNReal.ofReal (G.1 (γ s, γ t)) := by
            rw [hspeed s hs t ht]
          _ ≤ G.internal (ball (0 : Rd d) (R + 1)) (γ s) (γ t) :=
            G.ofReal_le_internal (ball (0 : Rd d) (R + 1)) (γ s) (γ t)
    · rw [G.internal_comm]
      have hrev : G.internal (ball (0 : Rd d) (R + 1)) (γ t) (γ s) =
          ENNReal.ofReal |s - t| := by
        have hlen : G.len γ t s = ENNReal.ofReal (s - t) := by
          rw [G.len_def]
          change curveLength (fun q => G.pt (γ q)) t s = _
          exact curveLength_of_hasUnitSpeedOn hUnit ht hs
        apply le_antisymm
        · calc
            G.internal (ball (0 : Rd d) (R + 1)) (γ t) (γ s) ≤ G.len γ t s :=
              G.internal_le_len (le_of_not_ge hst) (hcont.mono (Icc_subset_Icc ht.1 hs.2))
                ((hmap.mono_right hball).mono_left (Icc_subset_Icc ht.1 hs.2))
            _ = ENNReal.ofReal |s - t| := by rw [hlen, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hst))]
        · calc
            ENNReal.ofReal |s - t| = ENNReal.ofReal (G.1 (γ t, γ s)) := by
              rw [hspeed t ht s hs]
            _ ≤ G.internal (ball (0 : Rd d) (R + 1)) (γ t) (γ s) :=
              G.ofReal_le_internal (ball (0 : Rd d) (R + 1)) (γ t) (γ s)
      rw [hrev, abs_sub_comm]
  · intro s hs t ht hst
    rw [G.len_def]
    change curveLength (fun q => G.pt (γ q)) s t = _
    exact curveLength_of_hasUnitSpeedOn hUnit hs ht

end HigherDimLFPPAS.Scaling
