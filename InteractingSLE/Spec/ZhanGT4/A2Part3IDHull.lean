/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Spec.Dimension.ForceGaps

/-!
# A.2 part 3, (I1): the deterministic pull-back of the two alternatives

Packet PROVE-ZHAN-A2P3-ID. Source: Astra, *Follow-up proofs*, §A.2 L586–L594
(`source/external/AstraIG1/ig1_followup_proofs.txt`; R38, R53). Deterministic Loewner facts behind the two
alternatives of (I1):

* **`mem_closure_iUnion_of_newHorizon_top`** (L591–L593): if the new horizon of the target change
  `ψ(z) = z/(x_k − z)` is infinite, the original hulls before the separation time accumulate at the target `x_k`.
  The new hull at the new time `u = C(s)` has half-plane capacity `2u`, so for `u > R²` it leaves the disc of radius
  `R` (`HPHull.hcap_le_rad_sq`); it is `ψ(K_s)` (`PullData.local_hull`), and `|ψ(z)| > R` puts `z` within `2x_k/R`
  of `x_k`;
* **`isBounded_and_notMem_of_mark`** (L586–L588): before a time `T` at which a left mark `v` (started at `v(0) < 0`)
  is still strictly left of the driver, the hulls are bounded and their closure misses the real half-line
  `(−∞, v(0)]`: the real flow of `v(0)` is a forward solution on `[0, T]` (`isForwardSol_ofReal`), the points left
  of it are alive too (reflected `RS.exists_isForwardSol_of_lt`), and an alive real point has a disc outside the hull
  (`not_mem_fwdHull_of_isForwardSol`);
* `mem_closure_of_reflect`: the reflection `z ↦ −z̄` between the left and the right forms (`LP.fwdHull_neg`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2P3ID

open QuantumZipper (H fwdHull IsForwardSol)
open Zhan.Retarget

/-! ### An infinite new horizon -/

/-- **An infinite new horizon: the hulls before the separation time accumulate at the target** `x_k`. -/
theorem mem_closure_iUnion_of_newHorizon_top {xk : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hd : PullData w vk xk T)
    (hT : newHorizon xk w vk T = ⊤) :
    (xk : ℂ) ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  have hxk := hd.pos
  rw [Metric.mem_closure_iff]
  intro ε hε
  set R : ℝ := max 2 (4 * xk / ε) with hR
  have hR2 : 2 ≤ R := le_max_left _ _
  have hRε : 4 * xk / ε ≤ R := le_max_right _ _
  have hM : ENNReal.ofReal (R ^ 2) < newHorizon xk w vk T := by rw [hT]; exact ENNReal.ofReal_lt_top
  obtain ⟨S, hS⟩ := lt_iSup_iff.1 hM
  obtain ⟨hST, hS2⟩ := lt_iSup_iff.1 hS
  have hclk : R ^ 2 < clk (rate xk w vk) S := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sq_nonneg R)).1 hS2
  obtain ⟨S', hSS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hST
  have hSS'' : S < S' := by exact_mod_cast hSS'
  obtain ⟨W', Wn', -, hWn'c, -, hWn'0, hW'eq, -, hcorr⟩ := hd.local_hull hS'T
  obtain ⟨hfwd, -⟩ := hcorr S hSS''
  set u := clk (rate xk w vk) S with hu
  have hu0 : 0 ≤ u := le_trans (sq_nonneg R) hclk.le
  -- the new hull at `u` leaves the closed disc of radius `R`
  have hnot : ¬ fwdHull Wn' u ⊆ Metric.closedBall ((0 : ℝ) : ℂ) R := by
    intro hsub
    have hle := HPHull.hcap_le_rad_sq ⟨fwdHull Wn' u, InteractingSLE.isHPHull_fwdHull hWn'c hu0⟩ hsub
    rw [hcap_fwdHull hWn'c hWn'0 hu0] at hle
    nlinarith
  obtain ⟨w', hw'K, hw'R⟩ := not_subset.1 hnot
  have hw'H : w' ∈ H := (QuantumZipper.fwdHull_mono).2 _ hw'K
  have hw'R' : R < ‖w'‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hw'R
  have hw'1 : w' ≠ -1 := by
    rintro rfl
    have h := hw'H
    simp [QuantumZipper.H] at h
  set z := Sec7.targetChangeInv xk w' with hz
  have hzH : z ∈ H := (targetChangeInv_mem_H_iff hxk w').2 hw'H
  have hψz : Sec7.targetChange xk z = w' := Sec7.targetChange_targetChangeInv hxk.ne' hw'1
  have hzK : z ∈ fwdHull W' S := by
    by_contra hzK
    have h := (hfwd z ⟨hzH, hzK⟩).1
    rw [hψz] at h
    exact h.2 hw'K
  have hzK' : z ∈ fwdHull (fun s : ℝ => w s.toNNReal) S := by
    rw [fwdHull_eq_of_eqOn S.coe_nonneg (by exact_mod_cast hSS'') fun r hr => (hW'eq r hr).symm]
    exact hzK
  refine ⟨z, mem_iUnion₂.2 ⟨S, hST, hzK'⟩, ?_⟩
  have h1w : (1 : ℂ) + w' ≠ 0 := fun h => hw'1 (by linear_combination h)
  have hdiff : (xk : ℂ) - z = xk / (1 + w') := by
    rw [hz, Sec7.targetChangeInv]
    field_simp
    ring
  rw [dist_eq_norm, hdiff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxk]
  have hn : R - 1 < ‖1 + w'‖ := by
    have h := norm_sub_norm_le w' (-1)
    rw [norm_neg, norm_one, sub_neg_eq_add, add_comm] at h
    linarith
  have hRpos : 0 < R - 1 := by linarith
  have h4 : 4 * xk ≤ ε * R := by
    have := hRε
    rw [div_le_iff₀ hε] at this
    linarith
  calc xk / ‖1 + w'‖ < xk / (R - 1) := by gcongr
    _ ≤ ε := by
      rw [div_le_iff₀ hRpos]
      nlinarith

/-! ### Alive real points stay outside the closure of the hull -/

/-- **A real point with a forward solution on `[0, T]` is outside the closure of `K_T`.** -/
theorem ofReal_notMem_closure_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) : (x : ℂ) ∉ closure (fwdHull W T) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  set r := δ / Real.exp (2 / δ ^ 2 * T) with hr
  have hr0 : 0 < r := by positivity
  intro hcl
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hcl r hr0
  have hzH : 0 < z.im := (QuantumZipper.fwdHull_mono).2 _ hz
  refine not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH ?_ hz
  rw [← dist_eq_norm, dist_comm]
  have he : 0 < Real.exp (2 / δ ^ 2 * T) := Real.exp_pos _
  calc dist (x : ℂ) z * Real.exp (2 / δ ^ 2 * T) < r * Real.exp (2 / δ ^ 2 * T) := by gcongr
    _ = δ := by rw [hr]; field_simp

/-- **Real points left of an alive left point are alive.** -/
theorem exists_isForwardSol_of_lt_left {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T x y : ℝ}
    (hT : 0 ≤ T) (hx : x < 0) (hyx : y < x) {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  have hu' := QuantumZipper.RS.isForwardSol_neg hu
  have h1 : (fun t => -W t) 0 < -x := by simp only [hW0, neg_zero]; linarith
  obtain ⟨v, hv⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hW.neg hT h1 (neg_lt_neg hyx)
    (by rw [Complex.ofReal_neg]; exact hu')
  have hv' := QuantumZipper.RS.isForwardSol_neg hv
  simp only [Pi.neg_apply, neg_neg, Complex.ofReal_neg] at hv'
  exact ⟨_, hv'⟩

/-- **Before a time at which a left mark is still strictly left of the driver**, the hulls are bounded and their
closure misses the real half-line left of the mark's start. The driver `w` need only be continuous on some
`[0, T₂]`, `T₂ > T`. -/
theorem isBounded_and_notMem_of_mark {w v : ℝ≥0 → ℝ} {T T₂ : ℝ≥0} (hTT₂ : T < T₂)
    (hwc : ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 T₂))
    (hvc : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 T)) (hw0 : w 0 = 0) (hv0 : v 0 < 0)
    (hveq : ∀ t : ℝ≥0, t ≤ T → v t = v 0 + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hlt : ∀ t : ℝ≥0, t ≤ T → v t < w t) :
    IsBounded (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (Strip.extPath w) t) ∧
      ∀ u : ℝ, u ≤ v 0 → (u : ℂ) ∉ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (Strip.extPath w) t) := by
  set Wc := projExt (Strip.extPath w) T₂ T₂.coe_nonneg with hWc
  have hWcc : Continuous Wc := continuous_projExt _ hwc
  have hWceq : ∀ r ∈ Icc (0 : ℝ) T₂, Strip.extPath w r = Wc r := fun r hr => (projExt_eq _ hr).symm
  have hWc0 : Wc 0 = 0 := by
    rw [← hWceq 0 ⟨le_rfl, T₂.coe_nonneg⟩]
    simp [Strip.extPath, hw0]
  have hTT₂' : (T : ℝ) < T₂ := by exact_mod_cast hTT₂
  have hsub : (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (Strip.extPath w) t) ⊆ fwdHull Wc T := by
    refine iUnion₂_subset fun t ht => ?_
    have htT : t ≤ T := by exact_mod_cast ht.le
    rw [fwdHull_eq_of_eqOn t.coe_nonneg (lt_of_le_of_lt (by exact_mod_cast htT) hTT₂') hWceq]
    exact (QuantumZipper.fwdHull_mono).1 (by exact_mod_cast htT)
  refine ⟨(InteractingSLE.isBounded_fwdHull hWcc T).subset hsub, fun u hu => ?_⟩
  -- the real flow of the mark is a forward solution on `[0, T]`
  have hIcc : ∀ s ∈ Icc (0 : ℝ) T, s.toNNReal ≤ T := fun s hs => Real.toNNReal_le_iff_le_coe.2 hs.2
  have hY : IsForwardSol Wc (((fun s : ℝ => v s.toNNReal - w s.toNNReal) 0 : ℝ) : ℂ) T
      fun s => (((fun s : ℝ => v s.toNNReal - w s.toNNReal) s : ℝ) : ℂ) := by
    refine isForwardSol_ofReal hWc0 (hvc.sub (hwc.mono (Icc_subset_Icc le_rfl hTT₂'.le)))
      (fun s hs => sub_ne_zero.2 (hlt _ (hIcc s hs)).ne) fun s hs => ?_
    have hs₂ : s ∈ Icc (0 : ℝ) T₂ := ⟨hs.1, hs.2.trans hTT₂'.le⟩
    rw [← hWceq s hs₂, ← hWceq 0 ⟨le_rfl, T₂.coe_nonneg⟩]
    have hv := hveq s.toNNReal (hIcc s hs)
    rw [Real.coe_toNNReal _ hs.1] at hv
    simp only [Strip.extPath, Real.toNNReal_zero, hw0, sub_zero]
    rw [hv]
    ring
  have hY0 : ((fun s : ℝ => v s.toNNReal - w s.toNNReal) 0 : ℝ) = v 0 := by simp [hw0]
  rw [hY0] at hY
  have hnot : (u : ℂ) ∉ closure (fwdHull Wc T) := by
    rcases hu.lt_or_eq with hlt' | heq
    · obtain ⟨v', hv'⟩ := exists_isForwardSol_of_lt_left hWcc hWc0 T.coe_nonneg hv0 hlt' hY
      exact ofReal_notMem_closure_of_isForwardSol hWcc T.coe_nonneg hv'
    · rw [heq]
      exact ofReal_notMem_closure_of_isForwardSol hWcc T.coe_nonneg hY
  exact fun h => hnot (closure_mono hsub h)

/-! ### Reflection -/

/-- **Reflection of an accumulation point**: the hulls of `−w` accumulate at `−x` iff those of `w` accumulate at
`x` (one direction). -/
theorem mem_closure_of_reflect {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {x : ℝ}
    (h : ((-x : ℝ) : ℂ) ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (fun s : ℝ => -w s.toNNReal) t)) :
    (x : ℂ) ∈ closure (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (Strip.extPath w) t) := by
  have hrefl : ∀ t : ℝ, fwdHull (fun s : ℝ => -w s.toNNReal) t = LP.reflectC '' fwdHull (Strip.extPath w) t :=
    fun t => LP.fwdHull_neg (Strip.extPath w) t
  have hmaps : MapsTo LP.reflectC (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (fun s : ℝ => -w s.toNNReal) t)
      (⋃ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < T), fwdHull (Strip.extPath w) t) := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 hz
    rw [hrefl] at hzt
    obtain ⟨y, hy, rfl⟩ := hzt
    exact mem_iUnion₂.2 ⟨t, ht, by rw [LP.reflectC_reflectC]; exact hy⟩
  have := map_mem_closure LP.continuous_reflectC h hmaps
  simpa [LP.reflectC] using this

end InteractingSLE.ZhanGT4.A2P3ID
