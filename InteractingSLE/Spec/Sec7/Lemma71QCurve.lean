/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71QProb
import InteractingSLE.Spec.Sec7.Lemma71NMain
import InteractingSLE.Spec.Sec7.Lemma71OMeas

/-!
# Lemma 7.1's side limits along the middle curve: assembly from the geometric half

Packet PROVE-LEMMA71Q (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; Lemma 7.1,
`source/spec/p193-240.md` L576–L606). The side limits `Lemma71N.PocketCurveSide` of the active pocket component along
the middle curve split into

* the probabilistic half (CS-prob, `ae_middleSideHeight`): the full three-curve mean has the side heights `∓λ` of the
  middle curve (`MiddleSideHeight`);
* the seed values (CS-G, `tendsto_pocketG_left`, `tendsto_pocketG_right`): the seed function `G` tends to `−λ`
  between the image `xL` of `0⁻` and `0`, and to `λ` between `0` and the image `xR` of `0⁺`;
* the geometric half (CS-a and CS-branch, PROVE-LEMMA71P): at each such chart point the time-`t` chart inverse lands
  at a point `γ(s)` of the stopped middle prefix, off the wall facing that side of `γ`, approaching from that side, and
  the chart lift agrees with `Im log g_q′` (`MiddleLanding`).

This file proves the pathwise assembly (`pocketCurveSide_of_middleLanding`): `MiddleSideHeight` + `MiddleLanding` on
both sides ⟹ `PocketCurveSide` with `Gl = G − χ · lift ∘ Finv` (the form of `Lemma71M.pocketGl`). The side form of
`MiddleSideHeight` (`MiddleSideHeight.tendsto_left`, `tendsto_right`) needs no convergence of `g_q` along the
approach: the sign comes from the side, ultrafilter by ultrafilter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71Q

open QuantumZipper (H chiC)
open Lemma71I Lemma71N

/-! ### The side form of the side heights -/

section SideForm

variable {β α γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} {AL : Set ℂ} {vL u₀ : ℂ → ℝ} {k lam : ℝ}

/-- **The side height from the left side of the middle curve** (no convergence of `g_q` along the filter is
assumed: along each ultrafilter from the left side, `g_q` tends to a negative real). -/
theorem MiddleSideHeight.tendsto_left (hM : MiddleSideHeight β α γ W AL vL u₀ k lam) (hγ : IsSimpleProper γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W ⊤ γ) {s : ℝ≥0} {q : ℚ≥0} (hs0 : 0 < s)
    (hsq : s < (q : ℝ≥0)) (hsβ : γ s ∉ range β) {F : Filter ℂ}
    (hF : F ≤ 𝓝[leftSideOf (range γ) \ AL] (γ s)) :
    Tendsto (fun z => vL z + u₀ z + k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im)
      F (𝓝 (-lam)) := by
  rw [tendsto_iff_ultrafilter]
  intro U hU
  have hUF : (U : Filter ℂ) ≤ 𝓝[leftSideOf (range γ) \ AL] (γ s) := hU.trans hF
  obtain ⟨y, hy, hT⟩ := exists_neg_tendsto_of_leftSideOf hγ hW hW0 htr hs0 hsq U
    (hUF.trans (nhdsWithin_mono _ sdiff_subset))
  exact (hM s q hs0 hsq U (hUF.trans (nhdsWithin_mono _ fun z hz => ⟨hz.1.1.1, hz.2⟩)) y hT).1 hy hsβ

/-- **The side height from the right side of the middle curve.** -/
theorem MiddleSideHeight.tendsto_right (hM : MiddleSideHeight β α γ W AL vL u₀ k lam) (hγ : IsSimpleProper γ)
    (hW : Continuous W) (hW0 : W 0 = 0) (htr : IsGeneratingTrace W ⊤ γ) {s : ℝ≥0} {q : ℚ≥0} (hs0 : 0 < s)
    (hsq : s < (q : ℝ≥0)) (hsα : γ s ∉ range α) {F : Filter ℂ}
    (hF : F ≤ 𝓝[rightSideOf (range γ) \ AL] (γ s)) :
    Tendsto (fun z => vL z + u₀ z + k * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im)
      F (𝓝 lam) := by
  rw [tendsto_iff_ultrafilter]
  intro U hU
  have hUF : (U : Filter ℂ) ≤ 𝓝[rightSideOf (range γ) \ AL] (γ s) := hU.trans hF
  obtain ⟨y, hy, hT⟩ := Lemma613.exists_pos_tendsto_of_rightSideOf hγ hW hW0 htr hs0 hsq U
    (hUF.trans (nhdsWithin_mono _ sdiff_subset))
  exact (hM s q hs0 hsq U (hUF.trans (nhdsWithin_mono _ fun z hz => ⟨hz.1.1.1, hz.2⟩)) y hT).2 hy hsα

end SideForm

/-! ### The seed values between the two marks (CS-G) -/

section Seed

open Lemma71M

/-- **The seed function between the left mark and `0`**: `meanHarmonic → −λ` at `x ∈ (xL, 0)` when `0 ≤ xR`. -/
theorem tendsto_meanHarmonic_left (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {xL xR x : ℝ} (hxL : xL < x) (hx0 : x < 0)
    (hxR : 0 ≤ xR) :
    Tendsto (Ito.meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR)) (𝓝[H] (x : ℂ)) (𝓝 (-sleLambda κ)) := by
  have h := tendsto_meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR) hx0.ne (fun _ => hxL.ne')
    (fun _ => (hx0.trans_le hxR).ne)
  have hval : Ito.meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR) x = -sleLambda κ := by
    simp only [Ito.meanHarmonic, Fin.sum_univ_one, sleLambda, ← Complex.ofReal_sub]
    rw [Complex.arg_ofReal_of_neg hx0, Complex.arg_ofReal_of_nonneg (by linarith : (0 : ℝ) ≤ x - xL),
      Complex.arg_ofReal_of_neg (by linarith : x - xR < 0)]
    rw [div_eq_mul_one_div Real.pi]
    ring
  rwa [hval] at h

/-- **The seed function between `0` and the right mark**: `meanHarmonic → λ` at `x ∈ (0, xR)` when `xL ≤ 0`. -/
theorem tendsto_meanHarmonic_right (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {xL xR x : ℝ} (hxL : xL ≤ 0) (hx0 : 0 < x)
    (hxR : x < xR) :
    Tendsto (Ito.meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR)) (𝓝[H] (x : ℂ)) (𝓝 (sleLambda κ)) := by
  have h := tendsto_meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR) hx0.ne' (fun _ => (hxL.trans_lt hx0).ne')
    (fun _ => hxR.ne)
  have hval : Ito.meanHarmonic κ ρL ρR (fun _ => xL) (fun _ => xR) x = sleLambda κ := by
    simp only [Ito.meanHarmonic, Fin.sum_univ_one, sleLambda, ← Complex.ofReal_sub]
    rw [Complex.arg_ofReal_of_nonneg hx0.le, Complex.arg_ofReal_of_nonneg (by linarith : (0 : ℝ) ≤ x - xL),
      Complex.arg_ofReal_of_neg (by linarith : x - xR < 0)]
    rw [div_eq_mul_one_div Real.pi]
    ring
  rwa [hval] at h

/-- The seeds of the mapped segment straddle the driver: `L_t − W_t ≤ 0 ≤ R_t − W_t`. -/
theorem seed_sub_driver {γ' : ℝ → ℂ} (hΓ : Lemma71C.IsSegCurve γ') {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Lemma71C.capLife γ') {vL vR : Fin 1 → ℝ≥0 → ℝ}
    (hvL : vL 0 t = -MartChar.RealFlow.rightImg (fun s => -Ito.rpath (fun s => Lemma71C.segDriver γ' s) s) 0 t)
    (hvR : vR 0 t = MartChar.RealFlow.rightImg (Ito.rpath fun s => Lemma71C.segDriver γ' s) 0 t) :
    vL 0 t - Lemma71C.segDriver γ' t ≤ 0 ∧ 0 ≤ vR 0 t - Lemma71C.segDriver γ' t := by
  set w : ℝ≥0 → ℝ := fun s => Lemma71C.segDriver γ' s with hwdef
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < Lemma71C.capLife γ'} := hΓ.segDriver_spec.2.1
  have hw0 : w 0 = 0 := hΓ.segDriver_spec.1
  obtain ⟨W, t₂, hW, -, htt₂, hEq⟩ := exists_clamp_eqOn hw hw0 ht
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hEqt : EqOn W (Ito.rpath w) (Icc 0 (t : ℝ)) := fun r hr => hEq ⟨hr.1, hr.2.trans htt₂.le⟩
  have hWt : w t = W t := by
    have := hEqt ⟨ht0, le_rfl⟩
    simp only [Ito.rpath, Real.toNNReal_coe] at this
    exact this.symm
  have hWt' : Lemma71C.segDriver γ' t = W t := hWt
  have hR' : MartChar.RealFlow.rightImg (Ito.rpath w) 0 t = MartChar.RealFlow.rightImg W 0 t :=
    Lemma71B.rightImg_congr hW ht0 (fun r hr => (hEqt hr).symm) 0
  have hL' : MartChar.RealFlow.rightImg (fun s => -Ito.rpath w s) 0 t =
      MartChar.RealFlow.rightImg (fun s => -W s) 0 t :=
    Lemma71B.rightImg_congr hW.neg ht0 (fun r hr => by show -Ito.rpath w r = -W r; rw [hEqt hr]) 0
  constructor
  · rw [hvL, hL', hWt']
    have := MartChar.RealFlow.le_rightImg (w := fun s => -W s) hW.neg 0 ht0
    linarith
  · rw [hvR, hR', hWt']
    linarith [MartChar.RealFlow.le_rightImg (w := W) hW 0 ht0]

end Seed

/-! ### The geometric half and the pathwise assembly -/

section Assembly

/-- **The geometric half of Lemma 7.1's side limits along the middle curve at one chart point `x`** (CS-a and
CS-branch, PROVE-LEMMA71P): the chart inverse `Finv` lands at `γ s`, `0 < s < τ`, a point off the wall `η'` facing the
side `S` of `γ`, approaching from `S` off the explored set `A`, and for some `q > s` the chart lift minus
`Im log g_q′` tends to `0` (`g_q` the centred Loewner map of `γ([0, q])` with driver `W`). For Lemma 7.1: `S` the left
(right) side of `γ` and `η' = β` (`α`) at the chart points of `(L_t − W_t, 0)` (`(0, R_t − W_t)`). -/
def MiddleLanding (γ η' : ℝ≥0 → ℂ) (W : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (A S : Set ℂ) (Finv : ℂ → ℂ) (lift : ℂ → ℝ)
    (x : ℝ) : Prop :=
  ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < τ ∧ γ s ∉ range η' ∧ Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 (γ s)) ∧
    (∀ᶠ y in 𝓝[H] (x : ℂ), Finv y ∈ S \ A) ∧
    ∃ q : ℝ≥0, s < q ∧ Tendsto (fun y => lift (Finv y) -
      (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (Finv y)).im) (𝓝[H] (x : ℂ)) (𝓝 0)

variable {β α γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- **The derivative argument of the middle prefix does not depend on the stopping time** along an approach to `γ s`
from the sides of `γ` (Aux. lemma 57, `Lemma613.tendsto_lift_sub_of_agree`, with the prefix `γ([0, q])` against
`γ([0, r])`, `s < r ≤ q`: they agree near `γ s`). -/
theorem tendsto_logDerivFwd_sub_of_sides (hγ : IsSimpleProper γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ γ) {s r q : ℝ≥0} (hs0 : 0 < s) (hsr : s < r) (hrq : r ≤ q) {F : Filter ℂ}
    (hF : F ≤ 𝓝[leftSideOf (range γ) ∪ rightSideOf (range γ)] (γ s)) :
    Tendsto (fun z => (QuantumZipper.logDerivFwd (fun t : ℝ => W t.toNNReal) q z).im -
      (QuantumZipper.logDerivFwd (fun t : ℝ => W t.toNNReal) r z).im) F (𝓝 0) := by
  rcases eq_or_lt_of_le hrq with rfl | hlt
  · simp only [sub_self]; exact tendsto_const_nhds
  have hr0 : 0 < r := hs0.trans hsr
  have hg : IsGeneratingTrace W ⊤ (fun t => γ t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  obtain ⟨κ, hKΓ, hgK, hLK⟩ := ReverseArc.exists_physChart hg hW.continuousOn hW0 (WithTop.coe_lt_top q)
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_tail hγ hsr
  have hloc : γ '' Icc 0 q ∩ ball (γ s) ρ ⊆ γ '' Icc 0 r := by
    rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
    refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
    by_contra hrt
    exact hball t (le_of_lt (not_le.1 hrt)) htb
  have hsides : leftSideOf (range γ) ∪ rightSideOf (range γ) ⊆ H \ fillH (γ '' Icc 0 q) := by
    have h := sides_subset_H_diff_fwdHull hγ htr q
    rwa [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr ENNReal.coe_lt_top] at h
  rw [tendsto_iff_ultrafilter]
  intro U hU
  have hUs : (U : Filter ℂ) ≤ 𝓝[leftSideOf (range γ) ∪ rightSideOf (range γ)] (γ s) := hU.trans hF
  obtain ⟨y, hT⟩ : ∃ y : ℝ, Tendsto (fun z => QuantumZipper.fwdMap (fun t : ℝ => W t.toNNReal) r z) U
      (𝓝 (y : ℂ)) := by
    rcases Ultrafilter.union_mem_iff.1 (hUs self_mem_nhdsWithin) with hL | hR
    · obtain ⟨y, -, hT⟩ := exists_neg_tendsto_of_leftSideOf hγ hW hW0 htr hs0 hsr U
        (le_inf (hUs.trans nhdsWithin_le_nhds) (le_principal_iff.2 hL))
      exact ⟨y, hT⟩
    · obtain ⟨y, -, hT⟩ := Lemma613.exists_pos_tendsto_of_rightSideOf hγ hW hW0 htr hs0 hsr U
        (le_inf (hUs.trans nhdsWithin_le_nhds) (le_principal_iff.2 hR))
      exact ⟨y, hT⟩
  have h := Lemma613.tendsto_lift_sub_of_agree (isCompact_Icc.image hγ.1) hKΓ hgK hLK hρ U
    (hUs.trans (nhdsWithin_mono _ hsides)) hg hW.continuousOn hW0 hγ.2.1.injOn (WithTop.coe_lt_top r) hr0
    (image_mono (Icc_subset_Icc_right hrq)) hloc (by simpa only [Complex.ofReal_zero, sub_zero] using hT)
  simpa only [Complex.ofReal_zero, sub_zero] using h

/-- A point `γ s`, `0 < s < τ`, of the stopped middle prefix lies in the stopped union `A`, and the complete union
agrees with `A` near it (the tail of `γ` after some `q' ∈ (s, τ)` is at positive distance). -/
theorem landing_mem (hγ : IsSimpleProper γ) {τ : ℝ≥0∞} {A AL : Set ℂ}
    (hA : A = (range β ∪ range α ∪ γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ}) ∩ H)
    (hAL : AL = (range β ∪ range α ∪ range γ) ∩ H) {s : ℝ≥0} (hs0 : 0 < s) (hsτ : (s : ℝ≥0∞) < τ) :
    γ s ∈ A ∧ ∃ r > 0, AL ∩ ball (γ s) r ⊆ A := by
  obtain ⟨q', hsq', hq'τ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsτ
  have hsq : s < q' := by exact_mod_cast hsq'
  refine ⟨hA ▸ ⟨Or.inr ⟨s, hsτ.le, rfl⟩, hγ.2.2.2.1 s hs0⟩, ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := exists_ball_tail hγ hsq
  refine ⟨ρ, hρ, ?_⟩
  rintro z ⟨hzAL, hzb⟩
  rw [hAL] at hzAL
  rw [hA]
  obtain ⟨(hzβ | hzα) | ⟨t, rfl⟩, hzH⟩ := hzAL
  · exact ⟨Or.inl (Or.inl hzβ), hzH⟩
  · exact ⟨Or.inl (Or.inr hzα), hzH⟩
  · refine ⟨Or.inr ⟨t, ?_, rfl⟩, hzH⟩
    rcases lt_or_ge t q' with h | h
    · exact (show (t : ℝ≥0∞) ≤ q' by exact_mod_cast h.le).trans hq'τ.le
    · exact absurd hzb (hball t h)

/-- **The side from the sign** (for providers of `MiddleLanding` that control the sign of `g_q` rather than the side):
if a filter approaching `γ s` within `ℍ ∖ γ` carries `g_q` (`q > s`) to a negative real, it is eventually on the left
side of `γ`. -/
theorem leftSideOf_mem_of_tendsto_neg (hγ : IsSimpleProper γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ γ) {s q : ℝ≥0} (hs0 : 0 < s) (hsq : s < q) {F : Filter ℂ}
    (hF : F ≤ 𝓝[H \ range γ] (γ s)) {y : ℝ} (hy0 : y < 0)
    (hy : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q z) F (𝓝 (y : ℂ))) :
    leftSideOf (range γ) ∈ F := by
  rw [Filter.mem_iff_ultrafilter]
  intro U hU
  have hUF : (U : Filter ℂ) ≤ 𝓝[H \ range γ] (γ s) := hU.trans hF
  have hmem : leftSideOf (range γ) ∪ rightSideOf (range γ) ∈ U := by
    refine mem_of_superset (hUF self_mem_nhdsWithin) fun z hz => ?_
    have h := hγ.isProperArc.mem_leftSideOf_or_mem_rightSideOf hz.1 (by rw [arcRange_realPath]; exact hz.2)
    rw [arcRange_realPath] at h
    exact h
  refine (Ultrafilter.union_mem_iff.1 hmem).resolve_right fun hR => ?_
  obtain ⟨y', hy', hT⟩ := Lemma613.exists_pos_tendsto_of_rightSideOf hγ hW hW0 htr hs0 hsq U
    (le_inf (hUF.trans nhdsWithin_le_nhds) (le_principal_iff.2 hR))
  have he : (y : ℂ) = y' := tendsto_nhds_unique (hy.mono_left hU) hT
  have : y = y' := by exact_mod_cast he
  linarith

/-- **The side from the sign**, right side: a positive real limit of `g_q` puts the filter on the right side of `γ`. -/
theorem rightSideOf_mem_of_tendsto_pos (hγ : IsSimpleProper γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ γ) {s q : ℝ≥0} (hs0 : 0 < s) (hsq : s < q) {F : Filter ℂ}
    (hF : F ≤ 𝓝[H \ range γ] (γ s)) {y : ℝ} (hy0 : 0 < y)
    (hy : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q z) F (𝓝 (y : ℂ))) :
    rightSideOf (range γ) ∈ F := by
  rw [Filter.mem_iff_ultrafilter]
  intro U hU
  have hUF : (U : Filter ℂ) ≤ 𝓝[H \ range γ] (γ s) := hU.trans hF
  have hmem : leftSideOf (range γ) ∪ rightSideOf (range γ) ∈ U := by
    refine mem_of_superset (hUF self_mem_nhdsWithin) fun z hz => ?_
    have h := hγ.isProperArc.mem_leftSideOf_or_mem_rightSideOf hz.1 (by rw [arcRange_realPath]; exact hz.2)
    rw [arcRange_realPath] at h
    exact h
  refine (Ultrafilter.union_mem_iff.1 hmem).resolve_left fun hL => ?_
  obtain ⟨y', hy', hT⟩ := exists_neg_tendsto_of_leftSideOf hγ hW hW0 htr hs0 hsq U
    (le_inf (hUF.trans nhdsWithin_le_nhds) (le_principal_iff.2 hL))
  have he : (y : ℂ) = y' := tendsto_nhds_unique (hy.mono_left hU) hT
  have : y = y' := by exact_mod_cast he
  linarith

/-- **The side limits along the middle curve, pathwise** (`Lemma71N.PocketCurveSide`, Remark 6.7): from the side
heights of the complete mean along `γ` (`MiddleSideHeight`, CS-prob), the geometric half at every chart point of
`(xL, 0)` (left side of `γ`, off `β`) and of `(0, xR)` (right side, off `α`) (`MiddleLanding`), and the seed values
`Gs → ∓λ` there (CS-G), the side limits hold with `Gl = Gs − χ · lift ∘ Finv`:
`vL ∘ Finv + u₀ ∘ Finv − Gl = (vL + u₀ + χ Im log g_q′) ∘ Finv + χ (lift ∘ Finv − Im log g_q′ ∘ Finv) − Gs
→ ∓λ + 0 ∓ (−λ) = 0`. -/
theorem pocketCurveSide_of_middleLanding (hγ : IsSimpleProper γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : IsGeneratingTrace W ⊤ γ) {τ : ℝ≥0∞} {A AL : Set ℂ}
    (hA : A = (range β ∪ range α ∪ γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ}) ∩ H)
    (hAL : AL = (range β ∪ range α ∪ range γ) ∩ H) {vL u₀ : ℂ → ℝ} {κ : ℝ}
    (hM : MiddleSideHeight β α γ W AL vL u₀ (chiC κ) (sleLambda κ)) {xL xR : ℝ} {Gs : ℂ → ℝ}
    (hGL : ∀ x : ℝ, xL < x → x < 0 → Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 (-sleLambda κ)))
    (hGR : ∀ x : ℝ, 0 < x → x < xR → Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 (sleLambda κ))) {Finv : ℂ → ℂ}
    {lift : ℂ → ℝ}
    (hlandL : ∀ x : ℝ, xL < x → x < 0 → MiddleLanding γ β W τ A (leftSideOf (range γ)) Finv lift x)
    (hlandR : ∀ x : ℝ, 0 < x → x < xR → MiddleLanding γ α W τ A (rightSideOf (range γ)) Finv lift x) :
    PocketCurveSide A AL vL u₀ Finv (fun y => Gs y - chiC κ * lift (Finv y)) xL xR := by
  intro x hx
  have key : ∀ (η' : ℝ≥0 → ℂ) (S : Set ℂ) (h₀ : ℝ), S ⊆ leftSideOf (range γ) ∪ rightSideOf (range γ) →
      MiddleLanding γ η' W τ A S Finv lift x → Tendsto Gs (𝓝[H] (x : ℂ)) (𝓝 h₀) →
      (∀ (s : ℝ≥0) (q : ℚ≥0), 0 < s → s < (q : ℝ≥0) → γ s ∉ range η' → Tendsto (fun z => vL z + u₀ z +
        chiC κ * (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) (q : ℝ≥0) z).im)
        (𝓝[S \ AL] (γ s)) (𝓝 h₀)) →
      ∃ p : ℂ, Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝 p) ∧ p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
        Tendsto (fun y => vL (Finv y) + u₀ (Finv y) - (Gs y - chiC κ * lift (Finv y))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro η' S h₀ hSLR hland hG hside
    obtain ⟨s, hs0, hsτ, hsη', hlim, hev, q, hsq, hbr⟩ := hland
    obtain ⟨hpA, r, hr, hALA⟩ := landing_mem hγ hA hAL hs0 hsτ
    refine ⟨γ s, hlim, Or.inl hpA, ⟨r, hr, hALA⟩, ?_⟩
    have hF : Tendsto Finv (𝓝[H] (x : ℂ)) (𝓝[S \ AL] (γ s)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
      filter_upwards [hev, hlim (ball_mem_nhds _ hr)] with y hy hyb
      exact ⟨hy.1, fun hyAL => hy.2 (hALA ⟨hyAL, hyb⟩)⟩
    obtain ⟨q', hsq', hq'q⟩ := Lemma71L.exists_nnrat_btwn s.2 (show (s : ℝ) < q from hsq)
    have hsq'' : s < (q' : ℝ≥0) := by exact_mod_cast hsq'
    have hq'q' : (q' : ℝ≥0) ≤ q := by exact_mod_cast hq'q.le
    have hti := (tendsto_logDerivFwd_sub_of_sides hγ hW hW0 htr hs0 hsq'' hq'q' (F := 𝓝[S \ AL] (γ s))
      (nhdsWithin_mono _ (sdiff_subset.trans hSLR))).comp hF
    have h1 := (hside s q' hs0 hsq'' hsη').comp hF
    have hsum := ((h1.add ((hbr.add hti).const_mul (chiC κ))).sub hG)
    have e : h₀ + chiC κ * (0 + 0) - h₀ = 0 := by ring
    rw [e] at hsum
    refine hsum.congr fun y => ?_
    simp only [Function.comp_apply]
    ring
  rcases hx with ⟨hxL, hx0⟩ | ⟨hx0, hxR⟩
  · exact key β (leftSideOf (range γ)) (-sleLambda κ) subset_union_left (hlandL x hxL hx0) (hGL x hxL hx0)
      fun s q hs0 hsq hsβ => hM.tendsto_left hγ hW hW0 htr hs0 hsq hsβ le_rfl
  · exact key α (rightSideOf (range γ)) (sleLambda κ) subset_union_right (hlandR x hx0 hxR) (hGR x hx0 hxR)
      fun s q hs0 hsq hsα => hM.tendsto_right hγ hW hW0 htr hs0 hsq hsα le_rfl

end Assembly

/-! ### The named geometric half and the middle-curve side limits -/

section Named

open QuantumZipper (Hbar)
open LQGMetric (DistOn TestOn)
open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G Lemma71C Lemma71K Lemma71L Sec6 LocalSets

universe u

/-- **Named input (CS-geom): the geometric half of the side limits along the middle curve** (CS-a and CS-branch of
Lemma 7.1's side limits, PROVE-LEMMA71P; Remark 6.7 and supplement §2.3 (2) for the active component). On every pocket
construction over a three-curve space with capacity data, for every `σ(β, α)`-measurable branch shift that is almost
surely the inherited branch, at every capacity time `t`: almost surely on `{t < capLife}` there is a generating driver
`W` of the middle curve such that at every chart point of `(L_t − W_t, 0)` the time-`t` chart inverse of the shifted
chart lands on the left side of `γ` at a point of the stopped prefix off `β`, and at every chart point of
`(0, R_t − W_t)` on the right side at a point off `α`, with the chart lift agreeing with `Im log g_q′`
(`MiddleLanding`). -/
def MiddleLandingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ a b : ℝ, θ₁ < 0 → 0 < θ₂ →
    sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a → sleLambda κ - θ₁ * chiC κ ≤ b →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ) (β α γ : Ω → ℝ≥0 → ℂ) (ζβ ζα ζγ : Ω → ℝ≥0∞),
      Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ →
    ∀ (C : Ω → Set ℂ) (c : Ω → Chart) (γ' : Ω → ℝ → ℂ), IsPocketConstruction P β α γ C c γ' →
    ∀ (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ),
      Measurable G → MeasurableSet M → Measurable Y → (∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω) →
      (∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z) → (∀ ω, Y (outerHist β α ω) = closePt α C ω) →
    ∀ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n →
      (∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) →
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (t : ℝ≥0∞) < capLife (γ' ω) → ∃ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) ∧
      (∀ x : ℝ, geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL 0 t ω - segDriver (γ' ω) t < x → x < 0 →
        MiddleLanding (γ ω) (β ω) W (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (leftSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketLift (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) x) ∧
      (∀ x : ℝ, 0 < x → x < geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR 0 t ω - segDriver (γ' ω) t →
        MiddleLanding (γ ω) (α ω) W (capTime G M Y β α γ t ω)
          (explored (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t)) ω)
          (rightSideOf (range (γ ω))) (pocketInv (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t)
          (pocketLift (shiftLift (c ω) (n ω)) (fun s => segDriver (γ' ω) s) t) x)

/-- **(CS) `Lemma71N.PocketCurveSideStatement` from the geometric half** (`MiddleLandingStatement`) and the §4.2
reference (the input of the three-curve space): the probabilistic half is `ae_middleSideHeight`, the seed values are
`tendsto_meanHarmonic_left`/`right`, the assembly `pocketCurveSide_of_middleLanding`. Conditional helper (R43/R48: no
Theorem 1.2/1.3). -/
theorem pocketCurveSideStatement_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hL : MiddleLandingStatement.{u}) : PocketCurveSideStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb Ω _ P _ h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq hYeq
    n hn hN t gL hgL
  have hland := hL κ hκ hκ4 θ₁ θ₂ a b hθ₁ hθ₂ ha hb P h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc G M Y hG hM hY hMiff hGeq
    hYeq n hn hN t
  have hMS := ae_middleSideHeight href hκ hκ4 hθ₁ hθ₂ ha hb hS hgL
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hae⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsegc, -⟩ := hpc'
  filter_upwards [hland, hMS, hae] with ω hlω hMω hω htl vL hvL hvLr
  obtain ⟨W, hWtr, hlL, hlR⟩ := hlω htl
  obtain ⟨-, -, -, -, -, -, -, -, -, hsγ, -⟩ := hω
  have hMω' := hMω W hWtr vL hvL hvLr
  have hWc : Continuous W := continuousOn_univ.1 ((SideHeight.continuousOn_of_isGeneratingTrace hWtr).mono
    fun s _ => show (s : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hW0 : W 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace hWtr (by simp)
  set w : ℝ≥0 → ℝ := fun s => segDriver (γ' ω) s with hwdef
  set vLf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL i s ω with hvLfdef
  set vRf : Fin 1 → ℝ≥0 → ℝ := fun i s => geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR i s ω with hvRfdef
  have hvL' : vLf 0 t = -RealFlow.rightImg (fun s => -Ito.rpath (fun s => segDriver (γ' ω) s) s) 0 t := by
    simp only [hvLfdef, geomL, LP.twoSeedXL, neg_zero]
    rfl
  have hvR' : vRf 0 t = RealFlow.rightImg (Ito.rpath fun s => segDriver (γ' ω) s) 0 t := by
    simp only [hvRfdef, geomR, LP.twoSeedXR]
    rfl
  obtain ⟨hsL, hsR⟩ := seed_sub_driver (hsegc ω) htl hvL' hvR'
  have e1 : (fun i : Fin 1 => vLf i t - w t) = fun _ => vLf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have e2 : (fun i : Fin 1 => vRf i t - w t) = fun _ => vRf 0 t - segDriver (γ' ω) t := by
    funext i; rw [Subsingleton.elim i 0]
  have hGL : ∀ x : ℝ, vLf 0 t - segDriver (γ' ω) t < x → x < 0 →
      Tendsto (pocketG κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 (-sleLambda κ)) := by
    intro x hxL hx0
    have h1 := tendsto_meanHarmonic_left κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
      hxL hx0 hsR
    have h2 : pocketG κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) w vLf vRf t 0 =
        Ito.meanHarmonic κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
          (fun _ => vLf 0 t - segDriver (γ' ω) t) (fun _ => vRf 0 t - segDriver (γ' ω) t) := by
      funext y
      unfold Lemma71M.pocketG
      rw [e1, e2, sub_zero]
    rw [h2]
    exact h1
  have hGR : ∀ x : ℝ, 0 < x → x < vRf 0 t - segDriver (γ' ω) t →
      Tendsto (pocketG κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) w vLf vRf t 0)
        (𝓝[H] (x : ℂ)) (𝓝 (sleLambda κ)) := by
    intro x hx0 hxR
    have h1 := tendsto_meanHarmonic_right κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
      hsL hx0 hxR
    have h2 : pocketG κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) w vLf vRf t 0 =
        Ito.meanHarmonic κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁)
          (fun _ => vLf 0 t - segDriver (γ' ω) t) (fun _ => vRf 0 t - segDriver (γ' ω) t) := by
      funext y
      unfold Lemma71M.pocketG
      rw [e1, e2, sub_zero]
    rw [h2]
    exact h1
  exact pocketCurveSide_of_middleLanding hsγ hWc hW0 hWtr
    (Three.explored_threeStops β α γ (capTime G M Y β α γ t) ω) (Three.explored_threeTop β α γ ω) hMω' hGL hGR
    hlL hlR

/-- **Lemma 7.1's `IsPocketChartData` on every pocket construction over a three-curve space, from the geometric half
of the middle-curve side limits** (`MiddleLandingStatement`) and the §4.2 reference: the inherited branch (N) is
`Lemma71O.pocketBranchStatement` (proved), the side limits along the middle curve (CS) are
`pocketCurveSideStatement_of_middleLanding`, the outer arcs are `Lemma71N.ae_outerSideLimit`. Conditional helper. -/
theorem exists_isPocketChartData_of_middleLanding (href : Lemma71H.Cond44ReferenceStatement.{u})
    (hL : MiddleLandingStatement.{u}) {κ θ₁ θ₂ a b : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂)
    (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) {C : Ω → Set ℂ} {c : Ω → Chart}
    {γ' : Ω → ℝ → ℂ} (hpc : IsPocketConstruction P β α γ C c γ') :
    ∃ n : Ω → ℤ, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n ∧
      Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
        (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
          (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
        γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) 0
        (chiC κ) :=
  exists_isPocketChartData_of_named href Lemma71O.pocketBranchStatement
    (pocketCurveSideStatement_of_middleLanding href hL) hκ hκ4 hθ₁ hθ₂ ha hb hS hpc

end Named

end InteractingSLE.Sec7.Lemma71Q
