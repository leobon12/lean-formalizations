/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordConj
import InteractingSLE.Spec.Supplement.BR4aChainWord
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# BR4a's relative words: boundary values (deterministic)

Packet PROVE-T14-BR4A3 (`BR4aChain.BR4aWordDetStatement`, supplement p. 610, (BR4a.1)–(BR4a.2): "Its boundary
imaginary part is zero on `(−1, ∞)` and `−2π` on `(−∞, −1)` […] On `(−1, 0)` and `(0, ∞)` the original left and
right-before-`z` heights are unchanged").

* `liftBdry v y`, **`tendsto_brChart_lift`**: the boundary value of the lift of `brChart v` at a real point
  `y ≠ 0, −1/v`: `ℓ(−1/mob v y) − ℓ(−1/y)` with `ℓ = Sec7.StripSysField.liftBoundary`;
* **`liftBdry_add`**: `liftBdry v y + 2π[y < −1/v] = 2π[v < 0]` (the constant `c₀` of the boundary step identity);
* **`word_eq`**: from the time-0 identity of the transported harmonic extensions, the word `c` of the transformed
  field is `c(mob v y) = b'(y) + χ · liftBdry v y` off finitely many points;
* `flowLineXR_mem`, `flowLineXL_mem`, **`fbd_flow_right`**, **`fbd_flow_left`**: the flowed force datum of a
  flow-line word at the image of an alive real point is the boundary datum there (`Restart.FCAux79` +
  `Sec4.forceBoundaryData_flowLine`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain Supp8.HullDetGen Sec7.StripSysField MartChar.RealFlow

/-! ### The boundary value of the lift -/

/-- The boundary value of the lift of `brChart v` at a real point `y` (`mob v y = y/(vy + 1)`). -/
def liftBdry (v y : ℝ) : ℝ := liftBoundary (-(y / (v * y + 1))⁻¹) - liftBoundary (-y⁻¹)

/-- **The lift of `brChart v` at a real point** `y ≠ 0`, `vy + 1 ≠ 0`. -/
theorem tendsto_brChart_lift {v y : ℝ} (hy0 : y ≠ 0) (hyp : v * y + 1 ≠ 0) :
    Tendsto (brChart v).2.2 (𝓝[H] (y : ℂ)) (𝓝 (liftBdry v y)) := by
  have hmy0 : y / (v * y + 1) ≠ 0 := div_ne_zero hy0 hyp
  have h1 : Tendsto (fun z : ℂ => infinitySourceChart.2.2 (-z⁻¹)) (𝓝[H] (y : ℂ)) (𝓝 (liftBoundary (-y⁻¹))) :=
    (tendsto_infinitySourceChart_lift (neg_ne_zero.2 (inv_ne_zero hy0))).comp (tendsto_negInv_nhdsWithin_H hy0)
  have hm : Tendsto (mob v) (𝓝[H] (y : ℂ)) (𝓝[H] ((y / (v * y + 1) : ℝ) : ℂ)) := by
    rw [← mob_ofReal]
    exact tendsto_mob_nhdsWithin_H hyp
  have h2 : Tendsto (fun z : ℂ => infinitySourceChart.2.2 (-(mob v z)⁻¹)) (𝓝[H] (y : ℂ))
      (𝓝 (liftBoundary (-(y / (v * y + 1))⁻¹))) :=
    (tendsto_infinitySourceChart_lift (neg_ne_zero.2 (inv_ne_zero hmy0))).comp
      ((tendsto_negInv_nhdsWithin_H hmy0).comp hm)
  exact h2.sub h1

theorem neg_inv_lt_zero_iff (x : ℝ) : -x⁻¹ < 0 ↔ 0 < x := by
  rw [neg_lt_zero, inv_pos]

/-- **The constant of the boundary step identity**: `liftBdry v y + 2π[y < −1/v] = 2π[v < 0]`. -/
theorem liftBdry_add {v y : ℝ} (hv : v ≠ 0) (hy0 : y ≠ 0) (hyp : v * y + 1 ≠ 0) :
    liftBdry v y + 2 * (if y < pole v then Real.pi else 0) = 2 * (if v < 0 then Real.pi else 0) := by
  unfold liftBdry liftBoundary pole
  simp only [neg_inv_lt_zero_iff]
  have hvv : v * (-v⁻¹) = -1 := by field_simp
  rcases lt_or_gt_of_ne hv with hv' | hv'
  · have hpole : y < -v⁻¹ ↔ 0 < v * y + 1 := by
      constructor
      · intro h
        have := mul_lt_mul_of_neg_left h hv'
        linarith
      · intro h
        by_contra h'
        push Not at h'
        have := mul_le_mul_of_nonpos_left h' hv'.le
        linarith
    rcases lt_or_gt_of_ne hy0 with hy' | hy'
    · have hp : 0 < v * y + 1 := by nlinarith
      have h1 : ¬ 0 < y / (v * y + 1) := not_lt.2 (div_nonpos_of_nonpos_of_nonneg hy'.le hp.le)
      have h2 : ¬ 0 < y := not_lt.2 hy'.le
      simp only [h1, h2, hpole.2 hp, hv', ↓reduceIte]
      ring
    · rcases lt_or_gt_of_ne hyp with hp | hp
      · have h1 : ¬ 0 < y / (v * y + 1) := not_lt.2 (div_nonpos_of_nonneg_of_nonpos hy'.le hp.le)
        have h3 : ¬ y < -v⁻¹ := fun h => absurd (hpole.1 h) (not_lt.2 hp.le)
        simp only [h1, hy', h3, hv', ↓reduceIte]
        ring
      · simp only [div_pos hy' hp, hy', hpole.2 hp, hv', ↓reduceIte]
        ring
  · have hpole : y < -v⁻¹ ↔ v * y + 1 < 0 := by
      constructor
      · intro h
        have := mul_lt_mul_of_pos_left h hv'
        linarith
      · intro h
        by_contra h'
        push Not at h'
        have := mul_le_mul_of_nonneg_left h' hv'.le
        linarith
    have h4 : ¬ v < 0 := not_lt.2 hv'.le
    rcases lt_or_gt_of_ne hy0 with hy' | hy'
    · have h2 : ¬ 0 < y := not_lt.2 hy'.le
      rcases lt_or_gt_of_ne hyp with hp | hp
      · simp only [div_pos_of_neg_of_neg hy' hp, h2, hpole.2 hp, h4, ↓reduceIte]
        ring
      · have h1 : ¬ 0 < y / (v * y + 1) := not_lt.2 (div_nonpos_of_nonpos_of_nonneg hy'.le hp.le)
        have h3 : ¬ y < -v⁻¹ := fun h => absurd (hpole.1 h) (not_lt.2 hp.le)
        simp only [h1, h2, h3, h4, ↓reduceIte]
        ring
    · have hp : 0 < v * y + 1 := by nlinarith
      have h3 : ¬ y < -v⁻¹ := fun h => absurd (hpole.1 h) (not_lt.2 hp.le)
      simp only [div_pos hy' hp, hy', h3, h4, ↓reduceIte]
      ring

/-! ### The word of the transformed field -/

/-- **The word of the transformed field at the image of a real point** (from the time-0 identity of the transported
harmonic extensions): `c(mob v y) = b'(y) + χ · liftBdry v y` for `y ≠ 0`, `y ∉ J'`, `vy + 1 ≠ 0` and `mob v y` off the
jump candidates of `c`. -/
theorem word_eq {χ : ℝ} {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') {v : ℝ}
    {c : Restart.BoundaryWord}
    (h0 : ∀ u₀ uc : ℂ → ℝ, IsBoundedHarmonicExtension b' J' u₀ → IsBoundedHarmonicExtension c.fn c.jumps uc →
      ∀ z ∈ H, uc z = u₀ (mobInv v z) + χ * (brChart v).2.2 (mobInv v z))
    {y : ℝ} (hy0 : y ≠ 0) (hyp : v * y + 1 ≠ 0) (hyJ : y ∉ J') (hmy : y / (v * y + 1) ∉ c.jumps) :
    c.fn (y / (v * y + 1)) = b' y + χ * liftBdry v y := by
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  obtain ⟨uc, huc, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
    c.isPiecewiseConstantBoundaryData
  set my : ℝ := y / (v * y + 1) with hmydef
  have := neBot_nhdsWithin_H my
  have hL := huc.2.2 my hmy
  -- `mobInv v` maps `mob v y` back to `y`
  have hinv : mobInv v (my : ℂ) = y := by rw [hmydef, ← mob_ofReal, mobInv_mob_ofReal hyp]
  have hden : -v * my + 1 ≠ 0 := by
    have h : ((-v * my + 1 : ℝ) : ℂ) = 1 / ((v : ℂ) * y + 1) := by
      push_cast
      rw [hmydef]
      push_cast
      have hden : (v : ℂ) * (y : ℂ) + 1 ≠ 0 := by exact_mod_cast hyp
      rw [neg_mul, ← neg_mul_mob_add_one hden]
      ring
    intro h'
    rw [h', Complex.ofReal_zero] at h
    have hden : (v : ℂ) * (y : ℂ) + 1 ≠ 0 := by exact_mod_cast hyp
    exact one_div_ne_zero hden h.symm
  have hm : Tendsto (mobInv v) (𝓝[H] (my : ℂ)) (𝓝[H] (y : ℂ)) := by
    have h := tendsto_mob_nhdsWithin_H (v := -v) (y := my) hden
    rw [show mob (-v) (my : ℂ) = mobInv v (my : ℂ) from rfl, hinv] at h
    exact h
  have hR : Tendsto (fun z => u₀ (mobInv v z) + χ * (brChart v).2.2 (mobInv v z)) (𝓝[H] (my : ℂ))
      (𝓝 (b' y + χ * liftBdry v y)) :=
    ((hu₀.2.2 y hyJ).comp hm).add (((tendsto_brChart_lift hy0 hyp).comp hm).const_mul χ)
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (h0 u₀ uc hu₀ huc z hz).symm

/-! ### Flowed force data of flow-line words -/

/-- The right marks of the flow-line word from `0` are `0` and jump candidates. -/
theorem flowLineXR_mem (b : ℝ → ℝ) (J : Finset ℝ) (j : Fin (flowLineNR b J 0)) : flowLineXR b J 0 j ∈ insert 0 J := by
  induction j using Fin.cases with
  | zero => exact Finset.mem_insert_self _ _
  | succ i =>
    refine Finset.mem_insert_of_mem ?_
    show ((PiecewiseConstantBoundaryData.jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl i - 0 ∈ J
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b J).filter (0 < ·)) rfl i
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

/-- The left marks of the flow-line word from `0` are `0` and jump candidates. -/
theorem flowLineXL_mem (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) : flowLineXL b J 0 i ∈ insert 0 J := by
  induction i using Fin.cases with
  | zero => exact Finset.mem_insert_self _ _
  | succ i =>
    refine Finset.mem_insert_of_mem ?_
    show ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0 ∈ J
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)) rfl (Fin.rev i)
    exact (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1

/-- **The flowed force datum of a flow-line word at the image of an alive point `y > 0`** is the boundary datum
`b(y)` (`y ∉ J`). -/
theorem fbd_flow_right {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy0 : 0 < y) (hy : Alive w y t) (hyJ : y ∉ J) :
    forceBoundaryData κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
        (fun i => -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t)
        (fun j => rightImg w (flowLineXR b J 0 j) t - w t) (gImg w y t - w t) = b y := by
  rw [Restart.FCAux79.forceBoundaryData_flow_right _ _ hw ht hy0 hy fun j h => ?_,
    Sec4.forceBoundaryData_flowLine hκ hb hy0.ne' hyJ]
  rcases Finset.mem_insert.1 (flowLineXR_mem b J j) with h' | h'
  · rw [h] at h'
    exact hy0.ne' h'
  · rw [h] at h'
    exact hyJ h'

/-- **The flowed force datum of a flow-line word at the image of an alive point `−y < 0`** (alive for the reflected
driver) is the boundary datum `b(−y)` (`−y ∉ J`, the image off the flowed left marks). -/
theorem fbd_flow_left {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {y : ℝ} (hy0 : 0 < y) (hy : Alive (fun s => -w s) y t)
    (hyJ : -y ∉ J)
    (hne : ∀ i, -gImg (fun s => -w s) y t - w t ≠ -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t) :
    forceBoundaryData κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
        (fun i => -rightImg (fun s => -w s) (-flowLineXL b J 0 i) t - w t)
        (fun j => rightImg w (flowLineXR b J 0 j) t - w t) (-gImg (fun s => -w s) y t - w t) = b (-y) := by
  rw [Restart.FCAux79.forceBoundaryData_flow_left _ _ hw ht hy0 hy (fun i h => ?_) hne,
    Sec4.forceBoundaryData_flowLine hκ hb (neg_ne_zero.2 hy0.ne') hyJ]
  rcases Finset.mem_insert.1 (flowLineXL_mem b J i) with h' | h'
  · rw [h', neg_zero] at h
    exact hy0.ne h
  · have : flowLineXL b J 0 i = -y := by linarith
    rw [this] at h'
    exact hyJ h'

end InteractingSLE.Theorem14.BR4aIn
