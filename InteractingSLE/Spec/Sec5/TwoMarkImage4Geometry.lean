/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Trace
import InteractingSLE.Spec.Sec5.CrossRestartTrace

/-!
# Clearance of the original target before separation

The canonical image hull is bounded at every time before target separation.
The identity `ψ(z)+1=a/(a-z)` therefore gives positive clearance between the
original hull and the pole `a`. This construction uses the existing image-hull
identity and does not assume an image trace.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.TwoMark.Image4

open Zhan.Retarget

variable {a : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The target has positive distance from each hull before separation. -/
theorem exists_ball_disjoint_originalHull (hd : PullData w vk a T)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ∃ r > 0, Disjoint (ball (a : ℂ) r) (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨R, hR⟩ := (hd.isHPHull_newHull ht).2.1.subset_closedBall 0
  rw [hd.fwdHull_newDrv_eq ht] at hR
  set M := max R 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨a / (M + 1), div_pos hd.pos (by positivity), ?_⟩
  rw [Set.disjoint_left]
  intro z hz hzK
  have hzH : z ∈ H := (QuantumZipper.fwdHull_mono.2 _) hzK
  have hne : (a : ℂ) - z ≠ 0 := sub_ne_zero.2 (Sec7.ne_ofReal_of_mem_H hzH a).symm
  have hbound : ‖Sec7.targetChange a z‖ ≤ M := by
    have h := hR ⟨z, hzK, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  have hdiv : a / ‖(a : ℂ) - z‖ ≤ M + 1 := by
    calc a / ‖(a : ℂ) - z‖ = ‖Sec7.targetChange a z + 1‖ := by
          rw [targetChange_add_one hne, norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hd.pos]
      _ ≤ ‖Sec7.targetChange a z‖ + 1 := by simpa only [norm_one] using norm_add_le (Sec7.targetChange a z) 1
      _ ≤ M + 1 := by linarith only [hbound]
  have hge : a / (M + 1) ≤ ‖(a : ℂ) - z‖ := by
    apply (div_le_iff₀ (by positivity : 0 < M + 1)).2
    have h := (div_le_iff₀ (norm_pos_iff.2 hne)).1 hdiv
    simpa only [mul_comm] using h
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
  exact (not_lt_of_ge hge) hz

/-- The given original trace cannot visit the new target before separation. -/
theorem trace_ne_target (hd : PullData w vk a T) (hη : IsGeneratingTrace w T η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) : η t ≠ (a : ℂ) := by
  intro he
  rcases eq_zero_or_pos t with rfl | ht0
  · rw [hη.1] at he
    exact hd.pos.ne' (Complex.ofReal_injective he.symm)
  obtain ⟨r, hr, hdisj⟩ := exists_ball_disjoint_originalHull hd ht
  have hlim : Tendsto η (𝓝[<] t) (𝓝 (η t)) :=
    ((hη.2.1 t ht.le).mono fun s (hs : s < t) =>
      (ENNReal.coe_lt_coe.2 hs).le.trans ht.le).tendsto
  have hev : ∀ᶠ s in 𝓝[<] t, η s ∈ ball (a : ℂ) r := by
    apply hlim.eventually
    rw [he]
    exact ball_mem_nhds _ hr
  obtain ⟨s, hst, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' ht0).1 hev
  obtain ⟨q, hq, hH⟩ := Restart.IsGeneratingTrace.exists_mem_H hη
    (Local2.continuousOn_driver hd) hd.w_zero hst ht.le
  have hqK : η q ∈ fwdHull (fun s : ℝ => w s.toNNReal) t :=
    CrossRestart.inter_H_subset_of_isFilling (hη.2.2 t ht) ⟨⟨q, ⟨zero_le, hq.2.le⟩, rfl⟩, hH⟩
  exact Set.disjoint_left.1 hdisj (hsub hq) hqK

end InteractingSLE.Sec5.TwoMark.Image4
