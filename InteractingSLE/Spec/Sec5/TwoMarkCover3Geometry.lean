/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Path
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.G11Trace

/-!
# Swallowed right intervals for local paths

The centred-coordinate comparison from GB7a applies to stopped paths without
maximality. A collision of a right coordinate swallows every smaller positive
real point. The hull-stability argument then excludes later visits to points
off the existing trace prefix, including visits at the terminal time.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull IsForwardSol)

namespace InteractingSLE.Sec5.TwoMark.Cover3

variable {κ : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ}
  {xR ρR : Fin nR → ℝ} {w β : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- A collided right coordinate leaves no alive positive point below its seed. -/
theorem not_exists_isForwardSol_of_right_collision
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR β T)
    {j : Fin nR} {y : ℝ} (hy : 0 < y) (hyj : y < xR j)
    {R u : ℝ≥0} (hRT : (R : ℝ≥0∞) ≤ T) (huR : u < R)
    (hcol : vR j u = w u) {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (hUw : ∀ s : ℝ, 0 ≤ s → s < R → U s = w s.toNNReal) :
    ¬ ∃ v, IsForwardSol U (y : ℂ) u v := by
  rintro ⟨v, hv⟩
  obtain ⟨hc, heq, hint, hnull⟩ := GB7a.centredPkg hp.continuousOn_w
    (hp.continuousOn_vR j) (fun _ ht => hp.integrable_gapR ht j)
    (fun _ ht => hp.vR_eq ht j) (hp.volume_collisionR j) hRT hUw
    u.coe_nonneg (NNReal.coe_lt_coe.2 huR)
  have hnonneg : ∀ s ∈ Icc (0 : ℝ) u, 0 ≤ vR j s.toNNReal - w s.toNNReal := by
    intro s hs
    refine sub_nonneg.2 (hp.w_le_vR ?_ j)
    refine lt_of_lt_of_le ?_ hRT
    rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hs.1]
    exact hs.2.trans_lt (NNReal.coe_lt_coe.2 huR)
  have hseed : y < vR j (0 : ℝ).toNNReal - w (0 : ℝ).toNNReal := by
    simpa only [Real.toNNReal_zero, hp.vR_zero, hp.w_zero, sub_zero] using hyj
  have hcmp := GB7a.re_lt_of_centred hU hU0 hy u.coe_nonneg hv hc hnonneg heq hint hnull hseed
  obtain ⟨c, hc0, hcle⟩ := exists_pos_le_re_of_isForwardSol hU hU0 hy u.coe_nonneg hv
  have hpos := hc0.trans_le (hcle u ⟨u.coe_nonneg, le_rfl⟩)
  simpa only [Real.toNNReal_coe, hcol, sub_self, lt_self_iff_false] using hpos.trans hcmp

/-- A swallowed point below a collided mark, if off the prefix, cannot be
visited later. Only local path equations and the given generating trace enter. -/
theorem trace_ne_of_right_collision
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR β T)
    (hη : IsGeneratingTrace w T η) {j : Fin nR} {y : ℝ}
    (hy : 0 < y) (hyj : y < xR j) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < T) (hcol : vR j u = w u)
    (hoff : ∀ s : ℝ≥0, s ≤ u → η s ≠ (y : ℂ)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η t ≠ (y : ℂ) := by
  intro t ht
  rcases le_or_gt t u with htu | htu
  · exact hoff t htu
  intro hηt
  obtain ⟨R, huR, hRT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hu
  have huR' : u < R := ENNReal.coe_lt_coe.1 huR
  set U : ℝ → ℝ := frozenDrive w R
  have hU : Continuous U := continuous_frozenDrive_of_lt hp.continuousOn_w
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hRT)
  have hUw : ∀ s : ℝ, 0 ≤ s → s < R → U s = w s.toNNReal :=
    fun _ hs0 hs => frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by
    rw [hUw 0 le_rfl (u.coe_nonneg.trans_lt (NNReal.coe_lt_coe.2 huR'))]
    simpa only [Real.toNNReal_zero] using hp.w_zero
  have hL : IsLoewnerTraceLT U R (fun s : ℝ => η s.toNNReal) :=
    hη.isLoewnerTraceLT (by simpa only [ENNReal.ofReal_coe_nnreal] using hRT)
  have hnot := not_exists_isForwardSol_of_right_collision hp hy hyj hRT.le huR' hcol hU hU0 hUw
  have hyη : (y : ℂ) ∉ (fun s : ℝ => η s.toNNReal) '' Icc 0 (u : ℝ) := by
    rintro ⟨s, hs, hse⟩
    exact hoff s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2) hse
  have hcl : (y : ℂ) ∉ closure (H \ fwdHull U u) := fun hcl =>
    hnot (GB7a.exists_isForwardSol_of_mem_closure hU hU0 hL u.coe_nonneg
      (NNReal.coe_lt_coe.2 huR') hy.ne' hyη hcl)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ z ∈ H \ fwdHull U u, r ≤ dist (y : ℂ) z := by
    by_contra hne
    push Not at hne
    exact hcl (Metric.mem_closure_iff.2 fun ε hε => by
      obtain ⟨z, hz, hzd⟩ := hne ε hε
      exact ⟨z, hz, hzd⟩)
  have hKu : fwdHull U u = fwdHull (fun s : ℝ => w s.toNNReal) u :=
    fwdHull_eq_of_eqOn u.coe_nonneg (NNReal.coe_lt_coe.2 huR') fun _ hs => frozenDrive_eq hs
  refine Supp7.G11.false_of_hull_stable hη hp.continuousOn_w hp.w_zero
    (lt_of_le_of_lt zero_le htu) ht (U := ball (y : ℂ) r) isOpen_ball
    (by rw [hηt]; exact mem_ball_self hr)
    (ε := (t : ℝ) - u) (by have : (u : ℝ) < t := htu; linarith)
    fun s₁ s₂ hs₁ _ _ z hz => ?_
  have hzH : z ∈ H := (QuantumZipper.fwdHull_mono.2 _) hz.2
  have hzK : z ∈ fwdHull U u := by
    by_contra hzK
    have hdist := hball z ⟨hzH, hzK⟩
    have hz1 := hz.1
    rw [mem_ball, dist_comm] at hz1
    exact (not_lt_of_ge hdist) hz1
  rw [hKu] at hzK
  exact QuantumZipper.fwdHull_mono.1 (show (u : ℝ) ≤ s₁ by linarith) hzK

end InteractingSLE.Sec5.TwoMark.Cover3
