/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Collar
import InteractingSLE.Spec.Supplement.LPProbReflect
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# A.3: reflection and scaling of the first-swallow crosscut

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L648–L720, ruling R38): "By reflection suppose `x < 0`", and
the first-swallow assertion for the point `x` is the one for `−1` after Brownian scaling.

## Main definitions

* `FirstSwallowGood κ W x`: the conclusion of `FirstSwallowCrosscutStatement` for a deterministic driver `W` and a
  point `x` (so `FirstSwallowCrosscutStatement κ` says that it holds almost surely for `W = √κ B`).

## Main results

* `firstSwallowGood_of_scale`: if it holds for the scaled driver `s ↦ W(a²s)/a` and the point `x`, it holds for `W`
  and `a x` (hulls scale, `QuantumZipper.LoewnerAlgebra.mem_fwdHull_scale_iff`);
* `firstSwallowGood_of_neg`: if it holds for `−W` and `−x`, it holds for `W` and `x` (hulls reflect by
  `z ↦ −z̄`, `LP.fwdHull_neg`; the crosscut is reflected and reversed);
* **`firstSwallowCrosscutStatement_of_neg_one`**: `FirstSwallowCrosscutStatement κ` follows from its case `x = −1`
  for every Brownian motion (Brownian scaling `IsBrownianReal.smul` and reflection `IsBrownianReal.neg`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A34

open QuantumZipper

/-- **The conclusion of A.3 for a deterministic driver** `W` and a point `x`: `x` is swallowed at some `σ`, and
`∂(ℍ \ K_σ) ∩ ℍ` is the open part of a simple crosscut with real endpoints on both sides of `0`, positioned relative
to `x` as in `FirstSwallowCrosscutStatement`. -/
def FirstSwallowGood (κ : ℝ) (W : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ σ : ℝ, RealSwallowAt W x σ ∧
    ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re < 0 ∧ 0 < (γ 1).re ∧
      frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1 ∧
      (x < 0 → (8 ≤ κ → (γ 0).re = x) ∧ (κ < 8 → (γ 0).re < x)) ∧
      (0 < x → (8 ≤ κ → (γ 1).re = x) ∧ (κ < 8 → x < (γ 1).re))

theorem firstSwallowCrosscutStatement_iff {κ : ℝ} : FirstSwallowCrosscutStatement.{u} κ ↔
    (4 < κ → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ x : ℝ, x ≠ 0 → ∀ᵐ ω ∂P, FirstSwallowGood κ (drive κ B ω) x) := Iff.rfl

/-! ### Images of the frontier under homeomorphisms preserving `ℍ` -/

theorem frontier_diff_inter_H_image (e : ℂ ≃ₜ ℂ) (he : ∀ z, e z ∈ H ↔ z ∈ H) (K : Set ℂ) :
    frontier (H \ e '' K) ∩ H = e '' (frontier (H \ K) ∩ H) := by
  have hH : e '' H = H := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; exact (he w).2 hw
    · intro hz; exact ⟨e.symm z, (he _).1 (by simpa using hz), by simp⟩
  have hd : H \ e '' K = e '' (H \ K) := by rw [Set.image_sdiff e.injective, hH]
  rw [hd, ← e.image_frontier, Set.image_inter e.injective, hH]

/-! ### Scaling -/

theorem realSwallowAt_of_scale {W : ℝ → ℝ} {a x σ : ℝ} (ha : 0 < a)
    (h : RealSwallowAt (fun s => W (a ^ 2 * s) / a) x σ) : RealSwallowAt W (a * x) (a ^ 2 * σ) := by
  have ha2 : 0 < a ^ 2 := by positivity
  have hcast : ((a * x : ℝ) : ℂ) = (a : ℂ) * (x : ℂ) := by push_cast; ring
  obtain ⟨hσ, halive, hdead⟩ := h
  refine ⟨by positivity, fun s hs => ?_, fun ⟨u, hu⟩ => hdead ?_⟩
  · have hs' : s / a ^ 2 ∈ Ico (0 : ℝ) σ :=
      ⟨div_nonneg hs.1 ha2.le, (div_lt_iff₀ ha2).2 (by linarith [hs.2])⟩
    obtain ⟨v, hv⟩ := halive _ hs'
    have h := LoewnerAlgebra.isForwardSol_unscale ha hv
    rw [mul_div_cancel₀ _ ha2.ne'] at h
    exact ⟨_, hcast ▸ h⟩
  · rw [hcast] at hu
    have h := LoewnerAlgebra.isForwardSol_scale ha hu
    rw [mul_div_cancel_left₀ _ ha2.ne'] at h
    exact ⟨_, h⟩

/-- Multiplication by `a > 0` as a homeomorphism of `ℂ`. -/
def mulHomeo {a : ℝ} (ha : 0 < a) : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (a : ℂ) (by exact_mod_cast ha.ne')

theorem mulHomeo_apply {a : ℝ} (ha : 0 < a) (z : ℂ) : mulHomeo ha z = (a : ℂ) * z := rfl

theorem mul_mem_H_iff {a : ℝ} (ha : 0 < a) (z : ℂ) : (a : ℂ) * z ∈ H ↔ z ∈ H := by
  show 0 < ((a : ℂ) * z).im ↔ 0 < z.im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact ⟨fun h => pos_of_mul_pos_right h ha.le, fun h => mul_pos ha h⟩

theorem fwdHull_eq_image_of_scale {W : ℝ → ℝ} {a σ : ℝ} (ha : 0 < a) (hσ : 0 ≤ σ) :
    fwdHull W (a ^ 2 * σ) = mulHomeo ha '' fwdHull (fun s => W (a ^ 2 * s) / a) σ := by
  ext z
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  constructor
  · intro hz
    refine ⟨z / a, ?_, by rw [mulHomeo_apply, mul_div_cancel₀ _ ha']⟩
    rw [LoewnerAlgebra.mem_fwdHull_scale_iff W ha hσ, mul_div_cancel₀ _ ha']
    exact hz
  · rintro ⟨w, hw, rfl⟩
    exact (LoewnerAlgebra.mem_fwdHull_scale_iff W ha hσ w).1 hw

theorem isRealCrosscut_mul {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) {a : ℝ} (ha : 0 < a) :
    IsRealCrosscut fun s => (a : ℂ) * γ s := by
  obtain ⟨hc, hi, hH, h0, h1⟩ := hγ
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  refine ⟨continuousOn_const.mul hc, fun s hs t ht hst => hi hs ht (mul_left_cancel₀ ha' hst), ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (mul_mem_H_iff ha _).2 (hH ⟨s, hs, rfl⟩)
  · simp [Complex.mul_im, h0]
  · simp [Complex.mul_im, h1]

/-- **Scaling the first-swallow conclusion**: from the driver `s ↦ W(a²s)/a` and the point `x` to the driver `W`
and the point `a x`. -/
theorem firstSwallowGood_of_scale {κ : ℝ} {W : ℝ → ℝ} {a x : ℝ} (ha : 0 < a)
    (h : FirstSwallowGood κ (fun s => W (a ^ 2 * s) / a) x) : FirstSwallowGood κ W (a * x) := by
  obtain ⟨σ, hsw, γ, hγ, hγ0, hγ1, hfr, hneg, hpos⟩ := h
  refine ⟨a ^ 2 * σ, realSwallowAt_of_scale ha hsw, fun s => (a : ℂ) * γ s, isRealCrosscut_mul hγ ha,
    ?_, ?_, ?_, fun hx => ?_, fun hx => ?_⟩
  · simpa [Complex.mul_re, hγ.2.2.2.1] using mul_neg_of_pos_of_neg ha hγ0
  · simpa [Complex.mul_re, hγ.2.2.2.2] using mul_pos ha hγ1
  · rw [fwdHull_eq_image_of_scale ha hsw.1.le,
      frontier_diff_inter_H_image (mulHomeo ha) (fun z => mul_mem_H_iff ha z), hfr, Set.image_image]
    rfl
  · have hx' : x < 0 := by
      by_contra h; nlinarith [not_lt.1 h]
    obtain ⟨h8, h8'⟩ := hneg hx'
    have e0 : ((a : ℂ) * γ 0).re = a * (γ 0).re := by simp [Complex.mul_re, hγ.2.2.2.1]
    refine ⟨fun hκ => ?_, fun hκ => ?_⟩
    · show ((a : ℂ) * γ 0).re = a * x
      rw [e0, h8 hκ]
    · show ((a : ℂ) * γ 0).re < a * x
      rw [e0]; exact mul_lt_mul_of_pos_left (h8' hκ) ha
  · have hx' : 0 < x := by
      by_contra h; nlinarith [not_lt.1 h]
    obtain ⟨h8, h8'⟩ := hpos hx'
    have e1 : ((a : ℂ) * γ 1).re = a * (γ 1).re := by simp [Complex.mul_re, hγ.2.2.2.2]
    refine ⟨fun hκ => ?_, fun hκ => ?_⟩
    · show ((a : ℂ) * γ 1).re = a * x
      rw [e1, h8 hκ]
    · show a * x < ((a : ℂ) * γ 1).re
      rw [e1]; exact mul_lt_mul_of_pos_left (h8' hκ) ha

/-! ### Reflection -/

theorem isRealCrosscut_reflect {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) :
    IsRealCrosscut fun s => LP.reflectC (γ (1 - s)) := by
  obtain ⟨hc, hi, hH, h0, h1⟩ := hγ
  have hmaps : MapsTo (fun s : ℝ => 1 - s) (Icc 0 1) (Icc 0 1) := fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  refine ⟨LP.continuous_reflectC.comp_continuousOn (hc.comp (continuousOn_const.sub continuousOn_id) hmaps),
    fun s hs t ht hst => ?_, ?_, ?_, ?_⟩
  · have := hi (hmaps hs) (hmaps ht) (by simpa using congrArg LP.reflectC hst)
    simp only at this; linarith
  · rintro _ ⟨s, hs, rfl⟩
    exact LP.reflectC_mem_H_iff.2 (hH ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩)
  · simp [LP.im_reflectC, h1]
  · simp [LP.im_reflectC, h0]

theorem re_reflectC (z : ℂ) : (LP.reflectC z).re = -z.re := by simp [LP.reflectC]

/-- **Reflecting the first-swallow conclusion**: from the driver `−W` and the point `−x` to `W` and `x`. -/
theorem firstSwallowGood_of_neg {κ : ℝ} {W : ℝ → ℝ} {x : ℝ}
    (h : FirstSwallowGood κ (fun t => -W t) (-x)) : FirstSwallowGood κ W x := by
  obtain ⟨σ, hsw, γ, hγ, hγ0, hγ1, hfr, hneg, hpos⟩ := h
  refine ⟨σ, realSwallowAt_neg_iff.1 hsw, fun s => LP.reflectC (γ (1 - s)), isRealCrosscut_reflect hγ,
    ?_, ?_, ?_, fun hx => ?_, fun hx => ?_⟩
  · simp only [sub_zero, re_reflectC]; linarith
  · simp only [sub_self, re_reflectC]; linarith
  · have hK : fwdHull (fun t => -W t) σ = LP.reflectHomeo '' fwdHull W σ := LP.fwdHull_neg W σ
    have hfr' := frontier_diff_inter_H_image LP.reflectHomeo (fun z => LP.reflectC_mem_H_iff) (fwdHull W σ)
    rw [← hK, hfr] at hfr'
    have hinv : frontier (H \ fwdHull W σ) ∩ H = LP.reflectHomeo '' (γ '' Ioo 0 1) := by
      rw [hfr', Set.image_image]
      ext z; simp [LP.coe_reflectHomeo]
    rw [hinv, Set.image_image]
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp [LP.coe_reflectHomeo]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp [LP.coe_reflectHomeo]⟩
  · obtain ⟨h8, h8'⟩ := hpos (by linarith)
    refine ⟨fun hκ => ?_, fun hκ => ?_⟩
    · simp only [sub_zero, re_reflectC, h8 hκ, neg_neg]
    · simp only [sub_zero, re_reflectC]; linarith [h8' hκ]
  · obtain ⟨h8, h8'⟩ := hneg (by linarith)
    refine ⟨fun hκ => ?_, fun hκ => ?_⟩
    · simp only [sub_self, re_reflectC, h8 hκ, neg_neg]
    · simp only [sub_self, re_reflectC]; linarith [h8' hκ]

/-! ### Reduction to the point `−1` -/

theorem drive_smul_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) {a : ℝ} (ha : 0 < a) (ω : Ω) :
    drive κ (fun t ω => (√((a ^ 2).toNNReal))⁻¹ * B ((a ^ 2).toNNReal * t) ω) ω =
      fun s => drive κ B ω (a ^ 2 * s) / a := by
  funext s
  have hsq : √(((a ^ 2).toNNReal : ℝ≥0) : ℝ) = a := by
    rw [Real.coe_toNNReal _ (by positivity), Real.sqrt_sq ha.le]
  simp only [drive, hsq, Real.toNNReal_mul (sq_nonneg a)]
  ring

theorem drive_neg_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drive κ (-B) ω = fun t => -drive κ B ω t := by
  funext t; simp [drive]

/-- **Reduction of A.3 to the point `−1`**: if, for every Brownian motion, almost surely the first-swallow conclusion
holds at `−1`, then `FirstSwallowCrosscutStatement κ` holds (every `x < 0` by Brownian scaling, every `x > 0` by
reflection). -/
theorem firstSwallowCrosscutStatement_of_neg_one {κ : ℝ}
    (h : 4 < κ → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, FirstSwallowGood κ (drive κ B ω) (-1)) : FirstSwallowCrosscutStatement.{u} κ := by
  rw [firstSwallowCrosscutStatement_iff]
  intro hκ Ω _ P B hB
  -- negative points by scaling
  have hneg : ∀ {B : ℝ≥0 → Ω → ℝ}, IsBrownianReal B P → ∀ x : ℝ, x < 0 →
      ∀ᵐ ω ∂P, FirstSwallowGood κ (drive κ B ω) x := by
    intro B hB x hx
    set a : ℝ := -x with hadef
    have ha : 0 < a := by linarith
    have hc : (a ^ 2).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
    filter_upwards [h hκ P _ (hB.smul hc)] with ω hω
    rw [drive_smul_eq κ B ha ω] at hω
    have := firstSwallowGood_of_scale ha hω
    rwa [show a * -1 = x by rw [hadef]; ring] at this
  intro x hx
  rcases lt_or_gt_of_ne hx with hx | hx
  · exact hneg hB x hx
  · filter_upwards [hneg hB.neg (-x) (by linarith)] with ω hω
    rw [drive_neg_eq] at hω
    exact firstSwallowGood_of_neg hω

end InteractingSLE.ZhanGT4.A34
