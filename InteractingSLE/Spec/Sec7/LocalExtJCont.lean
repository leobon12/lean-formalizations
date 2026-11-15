/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJWord
import InteractingSLE.Spec.Sec2.Assembly3Cont
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# A stopped seed coupling continued after its local stop

Packet PROVE-LOCEXT-J, input (U) of Aux. lemma 54. Under the measure `Q'` of a stopped seed coupling (clause (a) of
`IsStoppedSeedCoupling`), the driver and the seed marks are a local evolution of the seed-only word up to the local stop
`S`. This file continues them after `S` by the maximal solution driven by the increments of (a continuous version of)
the Brownian motion after `S` (`Sec2.Assembly3.isIntegratedSLEEvolution_contClosed`, as in Theorem 2.2's entrance
uniqueness), giving a full evolution of the seed-only word that agrees with the original processes before `S`
(**`IsStoppedSeedCoupling.exists_seedCont`**).

Pathwise inputs: at `S` the word seen from the driver is good (`goodWord_at`): the seed marks of a side coincide, the
left ones are strictly left of the right ones (`Sec2.vL_lt_vR_of_pos` at `S/2` and monotonicity of the marks in time), and
the seed sums are `> −2`. The stopped processes `X_{t ∧ S}` are adapted (`measurable_stopVal_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Sec7

/-! ### Pathwise facts at the stop -/

section PathFacts

variable {a : ℝ} {mL mR : ℕ} {ρL : Fin mL → ℝ} {ρR : Fin mR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin mL → ℝ≥0 → ℝ}
  {vR : Fin mR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

theorem isOrderedForceWord_zero : IsOrderedForceWord (fun _ : Fin mL => (0 : ℝ)) (fun _ : Fin mR => (0 : ℝ)) :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- A lower bound on `[t₀, S)` passes to `S` for a function continuous on `[0, S]`. -/
theorem le_at_of_continuousOn_Iic {f : ℝ≥0 → ℝ} {S t₀ : ℝ≥0} (ht₀ : t₀ < S) (hf : ContinuousOn f (Iic S)) {c : ℝ}
    (h : ∀ t, t₀ ≤ t → t < S → c ≤ f t) : c ≤ f S := by
  have hne : (𝓝[<] S).NeBot := nhdsLT_neBot_of_exists_lt ⟨t₀, ht₀⟩
  have ht : Tendsto f (𝓝[<] S) (𝓝 (f S)) :=
    (hf S (mem_Iic.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT ht₀] with t ht'
  exact h t ht'.1.le ht'.2

theorem ge_at_of_continuousOn_Iic {f : ℝ≥0 → ℝ} {S t₀ : ℝ≥0} (ht₀ : t₀ < S) (hf : ContinuousOn f (Iic S)) {c : ℝ}
    (h : ∀ t, t₀ ≤ t → t < S → f t ≤ c) : f S ≤ c := by
  have := le_at_of_continuousOn_Iic (f := fun t => -f t) ht₀ hf.neg (c := -c) fun t h1 h2 => neg_le_neg (h t h1 h2)
  linarith

/-- **At the stop the seed-only word seen from the driver is good.** -/
theorem goodWord_at {S : ℝ≥0}
    (hp : IsSLEPathUpTo a (fun _ : Fin mL => 0) (fun _ : Fin mR => 0) ρL ρR w vL vR b S) (hS0 : 0 < S)
    (hcw : ContinuousOn w (Iic S)) (hcL : ∀ i, ContinuousOn (vL i) (Iic S)) (hcR : ∀ j, ContinuousOn (vR j) (Iic S))
    (hsL : -2 < ∑ i, ρL i) (hsR : -2 < ∑ j, ρR j) :
    GoodWord ρL ρR (fun i => vL i S - w S, fun j => vR j S - w S) := by
  classical
  have hlt : ∀ {t : ℝ≥0}, t < S → (t : ℝ≥0∞) < (S : ℝ≥0∞) := fun ht => by exact_mod_cast ht
  -- the seed marks of a side coincide at `S`
  have hcoL : ∀ i k, vL i S = vL k S := fun i k =>
    eq_of_eqOn_Iio hS0 (hcL i) (hcL k) fun s hs => hp.vL_eq_of_xL_eq rfl (hlt hs)
  have hcoR : ∀ j k, vR j S = vR k S := fun j k =>
    eq_of_eqOn_Iio hS0 (hcR j) (hcR k) fun s hs => hp.vR_eq_of_xR_eq rfl (hlt hs)
  -- the sides at `S`
  have hLw : ∀ i, vL i S ≤ w S := fun i => by
    have := ge_at_of_continuousOn_Iic (f := fun t => vL i t - w t) (c := 0) hS0 ((hcL i).sub hcw)
      fun t _ ht => sub_nonpos.2 (hp.vL_le_w (hlt ht) i)
    simpa using this
  have hwR : ∀ j, w S ≤ vR j S := fun j => by
    have := le_at_of_continuousOn_Iic (f := fun t => vR j t - w t) (c := 0) hS0 ((hcR j).sub hcw)
      fun t _ ht => sub_nonneg.2 (hp.w_le_vR (hlt ht) j)
    simpa using this
  -- monotonicity of the marks in time
  have hS2 : S / 2 < S := NNReal.half_lt_self hS0.ne'
  have hS20 : 0 < S / 2 := by positivity
  have hmonoR : ∀ j t, S / 2 ≤ t → t < S → vR j (S / 2) ≤ vR j t := fun j t h1 h2 => by
    have e := hp.vR_sub h1 (hlt h2) j
    have hnn : 0 ≤ ∫ r in ((S / 2 : ℝ≥0) : ℝ)..t, 2 / (vR j r.toNNReal - w r.toNNReal) := by
      refine intervalIntegral.integral_nonneg (by exact_mod_cast h1) fun u hu => ?_
      have hu0 : 0 ≤ u := le_trans (NNReal.coe_nonneg _) hu.1
      have hut : u.toNNReal < S := by
        rw [Real.toNNReal_lt_iff_lt_coe hu0]
        exact lt_of_le_of_lt hu.2 (by exact_mod_cast h2)
      exact div_nonneg zero_le_two (sub_nonneg.2 (hp.w_le_vR (hlt hut) j))
    linarith
  have hmonoL : ∀ i t, S / 2 ≤ t → t < S → vL i t ≤ vL i (S / 2) := fun i t h1 h2 => by
    have e := hp.vL_sub h1 (hlt h2) i
    have hnp : 0 ≤ ∫ r in ((S / 2 : ℝ≥0) : ℝ)..t, -(2 / (vL i r.toNNReal - w r.toNNReal)) := by
      refine intervalIntegral.integral_nonneg (by exact_mod_cast h1) fun u hu => ?_
      have hu0 : 0 ≤ u := le_trans (NNReal.coe_nonneg _) hu.1
      have hut : u.toNNReal < S := by
        rw [Real.toNNReal_lt_iff_lt_coe hu0]
        exact lt_of_le_of_lt hu.2 (by exact_mod_cast h2)
      exact neg_nonneg.2 (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hp.vL_le_w (hlt hut) i)))
    rw [intervalIntegral.integral_neg] at hnp
    linarith
  have hsep : ∀ i j, vL i S < vR j S := fun i j => by
    have h1 := le_at_of_continuousOn_Iic hS2 (hcR j) fun t h1 h2 => hmonoR j t h1 h2
    have h2 := ge_at_of_continuousOn_Iic hS2 (hcL i) fun t h1 h2 => hmonoL i t h1 h2
    have h3 := hp.vL_lt_vR_of_pos isOrderedForceWord_zero hS20 (hlt hS2) i j
    linarith
  -- the threshold
  set uL : ℝ := if h : 0 < mL then vL ⟨0, h⟩ S - w S else 0 with huL
  set uR : ℝ := if h : 0 < mR then vR ⟨0, h⟩ S - w S else 0 with huR
  have heL : (fun i => vL i S - w S) = fun _ => uL := funext fun i => by
    have h : 0 < mL := Fin.pos i
    simp only [huL, h, ↓reduceDIte, hcoL i ⟨0, h⟩]
  have heR : (fun j => vR j S - w S) = fun _ => uR := funext fun j => by
    have h : 0 < mR := Fin.pos j
    simp only [huR, h, ↓reduceDIte, hcoR j ⟨0, h⟩]
  refine ⟨fun i j => by simp only; linarith [hsep i j], ⟨fun i k _ => by simp only [hcoL i k, le_refl],
    fun i => by simp only; linarith [hLw i], fun j k _ => by simp only [hcoR j k, le_refl],
    fun j => by simp only; linarith [hwR j]⟩, ?_⟩
  rw [heL, heR, thresholdCondition_split rfl rfl]
  exact not_thr_twoSeed hsL hsR _ _ _

end PathFacts

/-! ### The stopped processes are adapted -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓓 : Filtration ℝ≥0 mΩ} {S : Ω → WithTop ℝ≥0}

/-- **The stopped process `X_{t ∧ S}` (`stopVal`) is adapted.** -/
theorem measurable_stopVal_le (hS : IsStoppingTime 𝓓 S) {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) X) (t : ℝ≥0) : Measurable[𝓓 t] (stopVal X S t) := by
  intro A hA
  have h1 : MeasurableSet[hS.measurableSpace] (stopVal X S t ⁻¹' A) := measurable_stopVal hS hX t hA
  have e : stopVal X S t ⁻¹' A = (stopVal X S t ⁻¹' A ∩ {ω | S ω ≤ t}) ∪
      {ω | ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) ∧ X t ω ∈ A} := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_preimage, mem_ofPred_eq]
    by_cases h : (t : WithTop ℝ≥0) < S ω
    · have h' : ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) := h
      simp only [stopVal, h, ↓reduceIte, not_le.2 h, and_false, h', true_and, false_or]
    · have h' : ¬ ((t : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) := h
      simp only [not_lt.1 h, and_true, h', false_and, or_false]
  rw [e]
  exact (((hS.measurableSet _).1 h1).2 t).union (hX t A hA)

end Stopped

/-! ### The continuation -/

section Cont

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The seed-only word of a force word: one mark at `0` for every seed mark, with its weight. -/
abbrev seedWL (xL ρL : Fin nL → ℝ) : Fin (seedCount xL) → ℝ := fun j => ρL (seedEmb xL j)

abbrev seedWR (xR ρR : Fin nR → ℝ) : Fin (seedCount xR) → ℝ := fun j => ρR (seedEmb xR j)

/-- **The seed-only local path of the seed-weight word.** -/
theorem isSLEPathUpTo_seedOnly {a : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (hp : IsSLEPathUpTo a xL xR (seedWtL xL ρL) (seedWtR xR ρR) w vL vR b τ) :
    IsSLEPathUpTo a (fun _ : Fin (seedCount xL) => 0) (fun _ : Fin (seedCount xR) => 0) (seedWL xL ρL)
      (seedWR xR ρR) w (fun j => vL (seedEmb xL j)) (fun j => vR (seedEmb xR j)) b τ := by
  have h := hp.compEmb (seedEmb xL) (seedEmb xR) (fun i hi => seedWtL_eq_zero_of_notMem hi)
    (fun i hi => seedWtR_eq_zero_of_notMem hi)
  have e1 : (fun j => xL (seedEmb xL j)) = fun _ => 0 := funext fun j => seedEmb_eq_zero xL j
  have e2 : (fun j => xR (seedEmb xR j)) = fun _ => 0 := funext fun j => seedEmb_eq_zero xR j
  have e3 : (fun j => seedWtL xL ρL (seedEmb xL j)) = seedWL xL ρL := funext fun j => seedWtL_seedEmb xL ρL j
  have e4 : (fun j => seedWtR xR ρR (seedEmb xR j)) = seedWR xR ρR := funext fun j => seedWtR_seedEmb xR ρR j
  rw [e1, e2, e3, e4] at h
  exact h

open Classical in
/-- **A stopped seed coupling continued after its local stop.** Under the measure `Q'` of clause (a) (which gives the
stopped history the same law as `Q`), in the usual augmentation of its filtration, there is an integrated evolution of the
seed-only word that agrees with the driver and the seed marks before `S`; almost surely `S` is a regular stop, the local
stop of a driver continuous beyond it. -/
theorem IsStoppedSeedCoupling.exists_seedCont (hκ : 0 < κ) (hr : 0 < r)
    (hL : -2 < seedSumL xL ρL) (hR : -2 < seedSumR xR ρR)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) :
    ∃ (Q' : Measure Ω) (_ : IsProbabilityMeasure Q') (𝓖 : Filtration ℝ≥0 mΩ) (Gw : ℝ≥0 → Ω → ℝ)
      (GVL : Fin (seedCount xL) → ℝ≥0 → Ω → ℝ) (GVR : Fin (seedCount xR) → ℝ≥0 → Ω → ℝ) (BG : ℝ≥0 → Ω → ℝ)
      (ζG : Ω → ℝ≥0∞),
      AEMeasurable (stoppedHistory (drivingState W VL VR) S) Q ∧
      AEMeasurable (stoppedHistory (drivingState W VL VR) S) Q' ∧
      Q.map (stoppedHistory (drivingState W VL VR) S) = Q'.map (stoppedHistory (drivingState W VL VR) S) ∧
      IsIntegratedSLEEvolution κ (fun _ : Fin (seedCount xL) => 0) (fun _ : Fin (seedCount xR) => 0)
        (seedWL xL ρL) (seedWR xR ρR) Q' 𝓖 Gw GVL GVR BG ζG ∧
      ∀ᵐ ω ∂Q', IsRegularStop W VL VR S ω ∧
        (∃ ζ₀ : ℝ≥0∞, (S ω : ℝ≥0∞) < ζ₀ ∧ S ω = localStopPath r ζ₀ (fun t => W t ω) ∧
          ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀}) ∧ W 0 ω = 0 ∧
        (∀ i k, xL i = 0 → xL k = 0 → ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ S ω → VL i t ω = VL k t ω) ∧
        (∀ j k, xR j = 0 → xR k = 0 → ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ S ω → VR j t ω = VR k t ω) ∧
        ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < S ω → Gw t ω = W t ω ∧ (∀ j, GVL j t ω = VL (seedEmb xL j) t ω) ∧
          ∀ j, GVR j t ω = VR (seedEmb xR j) t ω := by
  classical
  have hreg := hc.ae_isRegularStop hr
  obtain ⟨𝓓, hS, ⟨Q', 𝓕, B, hQ', hQQ', hQ'Q, h𝓓, hE, hagree⟩, hb, hWa, hVLa, hVRa, -⟩ := hc
  -- the law of the stopped history (as in `IsStoppedSeedCoupling.map_stoppedHistory_eq`)
  have hΨ := measurable_histVersion hS hWa hVLa hVRa
  have hΨm : Measurable (histVersion W VL VR S) := hΨ.mono hS.measurableSpace_le le_rfl
  have hregQ' : ∀ᵐ ω ∂Q', IsRegularStop W VL VR S ω := hQ'Q.ae_le hreg
  have hΨQ : histVersion W VL VR S =ᵐ[Q] stoppedHistory (drivingState W VL VR) S := by
    filter_upwards [hreg] with ω ⟨h1, h2, h3⟩ using histVersion_eq h1 h2 h3
  have hΨQ' : histVersion W VL VR S =ᵐ[Q'] stoppedHistory (drivingState W VL VR) S := by
    filter_upwards [hregQ'] with ω ⟨h1, h2, h3⟩ using histVersion_eq h1 h2 h3
  have hlaw : Q.map (stoppedHistory (drivingState W VL VR) S) = Q'.map (stoppedHistory (drivingState W VL VR) S) := by
    rw [← Measure.map_congr hΨQ, ← Measure.map_congr hΨQ']
    ext U hU
    rw [Measure.map_apply hΨm hU, Measure.map_apply hΨm hU]
    exact hagree _ (hΨ hU)
  -- the filtration and a continuous Brownian motion
  set 𝓖 := usualAugmentation 𝓕 Q' with h𝓖
  have h𝓓𝓖 : 𝓓 ≤ 𝓖 := h𝓓.trans (Ito.le_usualAugmentation 𝓕 Q')
  obtain ⟨B', -, hB'c, hB'br, hB'ae⟩ := Sec2.Restart.exists_continuous_version hE.brownian
  -- the good event
  have hbQ' := hQ'Q.ae_le hb
  have hgood : ∀ᵐ ω ∂Q', IsRegularStop W VL VR S ω ∧
      (∃ ζ₀ : ℝ≥0∞, (S ω : ℝ≥0∞) < ζ₀ ∧ S ω = localStopPath r ζ₀ (fun t => W t ω) ∧
        ContinuousOn (fun t => drivingState W VL VR t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀}) ∧
      IsSLEPathUpTo κ xL xR (seedWtL xL ρL) (seedWtR xR ρR) (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (S ω) ∧ ∀ t, B' t ω = B t ω := by
    filter_upwards [hregQ', hbQ', hE.ae_path, hB'ae] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ ω, ω ∉ N → _ := fun ω hω => not_not.1 fun h => hω (hNsub h)
  have hN𝓖 : ∀ t, MeasurableSet[𝓖 t] N := fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hNae : ∀ᵐ ω ∂Q', ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the stop as a real time
  set Sn : Ω → ℝ≥0 := fun ω => if ω ∈ N then 1 else (S ω).untopD 0 with hSn
  have hSnS : ∀ ω, ω ∉ N → S ω = (Sn ω : WithTop ℝ≥0) := fun ω hω => by
    obtain ⟨⟨-, hfin, -⟩, -⟩ := hgoodN ω hω
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hfin
    simp only [hSn, hω, ↓reduceIte, ← hs, WithTop.untopD_coe]
  have hT : IsStoppingTime 𝓖 fun ω => (Sn ω : WithTop ℝ≥0) := fun t => by
    have e : {ω | (Sn ω : WithTop ℝ≥0) ≤ t} = (N ∩ {_ω | (1 : ℝ≥0) ≤ t}) ∪ (Nᶜ ∩ {ω | S ω ≤ t}) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp only [hSn, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and, mem_compl_iff,
          not_true_eq_false, false_and, or_false, WithTop.coe_le_coe]
      · simp only [mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and, mem_compl_iff, not_false_eq_true,
          true_and, false_or, hSnS ω hω]
    rw [e]
    exact ((hN𝓖 t).inter (MeasurableSet.const _)).union ((hN𝓖 t).compl.inter (h𝓓𝓖 t _ (hS t)))
  have hT0 : ∀ ω, 0 < Sn ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp [hSn, hω]
    · have h0 := (hgoodN ω hω).1.1
      rw [hSnS ω hω] at h0
      exact_mod_cast h0
  -- the stopped processes
  set mod : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ := fun X t ω => if ω ∈ N then 0 else stopVal X S t ω with hmod
  have hmodm : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) X → ∀ t,
      Measurable[𝓖 t] (mod X t) := fun X hX t => by
    let _ : MeasurableSpace Ω := 𝓖 t
    exact Measurable.ite (hN𝓖 t) measurable_const ((measurable_stopVal_le hS hX t).mono (h𝓓𝓖 t) le_rfl)
  have hcontX : ∀ ω, ω ∉ N → ∀ X : ℝ≥0 → Ω → ℝ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} →
      ∀ t, mod X t ω = X (min t (Sn ω)) ω := fun ω hω X hX t => by
    obtain ⟨⟨h0, hfin, -⟩, -⟩ := hgoodN ω hω
    simp only [hmod, hω, ↓reduceIte]
    rw [stopVal_eq h0 hfin hX t, stopAt_of_eq_coe (hSnS ω hω) t]
  have hcmod : ∀ X : ℝ≥0 → Ω → ℝ, (∀ ω, ω ∉ N → ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω}) →
      ∀ ω, Continuous (mod X · ω) := fun X hX ω => by
    by_cases hω : ω ∈ N
    · simp only [hmod, hω, ↓reduceIte]; exact continuous_const
    · have e : (mod X · ω) = fun t => X (min t (Sn ω)) ω := funext (hcontX ω hω X (hX ω hω))
      rw [e]
      have hsub : ∀ t, min t (Sn ω) ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := fun t => by
        simp only [mem_ofPred_eq, hSnS ω hω]
        exact WithTop.coe_le_coe.2 (min_le_right _ _)
      exact (hX ω hω).comp_continuous (continuous_id.min continuous_const) hsub
  have hmod_lt : ∀ ω, ω ∉ N → ∀ X : ℝ≥0 → Ω → ℝ, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < S ω → mod X t ω = X t ω :=
    fun ω hω X t ht => by simp only [hmod, hω, ↓reduceIte, stopVal, ht]
  -- continuity of the original coordinates through the stop
  have hcW : ∀ ω, ω ∉ N → ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := fun ω hω =>
    continuous_fst.comp_continuousOn (hgoodN ω hω).1.2.2
  have hcVL : ∀ i, ∀ ω, ω ∉ N → ContinuousOn (fun t => VL i t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} :=
    fun i ω hω => (continuous_apply i).comp_continuousOn
      (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn (hgoodN ω hω).1.2.2))
  have hcVR : ∀ j, ∀ ω, ω ∉ N → ContinuousOn (fun t => VR j t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} :=
    fun j ω hω => (continuous_apply j).comp_continuousOn
      (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn (hgoodN ω hω).1.2.2))
  set W' := mod W with hW'
  set VL' : Fin (seedCount xL) → ℝ≥0 → Ω → ℝ := fun j => mod (VL (seedEmb xL j)) with hVL'
  set VR' : Fin (seedCount xR) → ℝ≥0 → Ω → ℝ := fun j => mod (VR (seedEmb xR j)) with hVR'
  -- the seed-only local path and the word at the stop
  have hIic : ∀ ω, ω ∉ N → {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} = Iic (Sn ω) := fun ω hω => by
    ext t; simp only [mem_ofPred_eq, mem_Iic, hSnS ω hω, WithTop.coe_le_coe]
  have hpath0 : ∀ ω, ω ∉ N → IsSLEPathUpTo κ (fun _ : Fin (seedCount xL) => 0) (fun _ : Fin (seedCount xR) => 0)
      (seedWL xL ρL) (seedWR xR ρR) (fun t => W t ω) (fun j t => VL (seedEmb xL j) t ω)
      (fun j t => VR (seedEmb xR j) t ω) (fun t => B t ω) (Sn ω) := fun ω hω => by
    have h := isSLEPathUpTo_seedOnly (hgoodN ω hω).2.2.1
    rw [hSnS ω hω] at h
    exact h
  have hpath : ∀ᵐ ω ∂Q', IsSLEPathUpTo κ (fun _ : Fin (seedCount xL) => 0) (fun _ : Fin (seedCount xR) => 0)
      (seedWL xL ρL) (seedWR xR ρR) (W' · ω) (fun j t => VL' j t ω) (fun j t => VR' j t ω) (B' · ω) (Sn ω) := by
    filter_upwards [hNae] with ω hω
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (Sn ω : ℝ≥0∞) → (t : WithTop ℝ≥0) < S ω := fun t ht => by
      rw [hSnS ω hω]; exact_mod_cast ht
    have h0 : (0 : WithTop ℝ≥0) < S ω := (hgoodN ω hω).1.1
    refine isSLEPathUpTo_congr (hpath0 ω hω) (hmod_lt ω hω W 0 h0) (fun j => hmod_lt ω hω _ 0 h0)
      (fun j => hmod_lt ω hω _ 0 h0) (fun t ht => hmod_lt ω hω W t (hlt t ht))
      (fun t ht j => hmod_lt ω hω _ t (hlt t ht)) (fun t ht j => hmod_lt ω hω _ t (hlt t ht))
      (fun t _ => (hgoodN ω hω).2.2.2 t)
  have hgw : ∀ᵐ ω ∂Q', GoodWord (seedWL xL ρL) (seedWR xR ρR) (contWord W' VL' VR' Sn ω) := by
    filter_upwards [hNae] with ω hω
    have hval : ∀ X : ℝ≥0 → Ω → ℝ, ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} →
        mod X (Sn ω) ω = X (Sn ω) ω := fun X hX => by rw [hcontX ω hω X hX, min_self]
    have e : contWord W' VL' VR' Sn ω = (fun j => VL (seedEmb xL j) (Sn ω) ω - W (Sn ω) ω,
        fun j => VR (seedEmb xR j) (Sn ω) ω - W (Sn ω) ω) := by
      simp only [contWord, hW', hVL', hVR', hval W (hcW ω hω), hval _ (hcVL _ ω hω), hval _ (hcVR _ ω hω)]
    rw [e]
    have hsL : -2 < ∑ j, seedWL xL ρL j := by rw [sum_seedEmb_L]; exact hL
    have hsR : -2 < ∑ j, seedWR xR ρR j := by rw [sum_seedEmb_R]; exact hR
    exact goodWord_at (hpath0 ω hω) (hT0 ω) (hIic ω hω ▸ hcW ω hω) (fun j => hIic ω hω ▸ hcVL _ ω hω)
      (fun j => hIic ω hω ▸ hcVR _ ω hω) hsL hsR
  -- the continuation
  have hG := isIntegratedSLEEvolution_contClosed (P := Q') (𝓕 := 𝓖) hκ hB'br hB'c (hmodm W hWa)
    (fun j => hmodm _ (hVLa _)) (fun j => hmodm _ (hVRa _)) (hcmod W hcW) (fun j => hcmod _ (hcVL _))
    (fun j => hcmod _ (hcVR _)) hpath hT hT0 hgw
  refine ⟨Q', hQ', 𝓖, _, _, _, B', _, ⟨_, hΨm, hΨQ.symm⟩, ⟨_, hΨm, hΨQ'.symm⟩, hlaw, hG, ?_⟩
  filter_upwards [hNae] with ω hω
  obtain ⟨hreg', ⟨ζ₀, hSζ, hSl, hcont⟩, hp, -⟩ := hgoodN ω hω
  have hSlt : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < S ω → t < Sn ω := fun t ht => by
    rw [hSnS ω hω] at ht; exact_mod_cast ht
  refine ⟨hreg', ⟨ζ₀, hSζ, hSl, continuous_fst.comp_continuousOn hcont⟩, hp.w_zero, ?_, ?_, fun t ht => ?_⟩
  · intro i k hi hk t ht
    have hc1 := hcVL i ω hω
    have hc2 := hcVL k ω hω
    rw [hIic ω hω] at hc1 hc2
    have ht' : t ≤ Sn ω := by rw [hSnS ω hω] at ht; exact_mod_cast ht
    have hall : ∀ s < Sn ω, VL i s ω = VL k s ω := fun s hs =>
      hp.vL_eq_of_xL_eq (hi.trans hk.symm) (by rw [hSnS ω hω]; exact WithTop.coe_lt_coe.2 hs)
    rcases lt_or_eq_of_le ht' with hlt | heq
    · exact hall t hlt
    · rw [heq]; exact eq_of_eqOn_Iio (hT0 ω) hc1 hc2 hall
  · intro i k hi hk t ht
    have hc1 := hcVR i ω hω
    have hc2 := hcVR k ω hω
    rw [hIic ω hω] at hc1 hc2
    have ht' : t ≤ Sn ω := by rw [hSnS ω hω] at ht; exact_mod_cast ht
    have hall : ∀ s < Sn ω, VR i s ω = VR k s ω := fun s hs =>
      hp.vR_eq_of_xR_eq (hi.trans hk.symm) (by rw [hSnS ω hω]; exact WithTop.coe_lt_coe.2 hs)
    rcases lt_or_eq_of_le ht' with hlt | heq
    · exact hall t hlt
    · rw [heq]; exact eq_of_eqOn_Iio (hT0 ω) hc1 hc2 hall
  · refine ⟨?_, fun j => ?_, fun j => ?_⟩
    · show concatAt (Sn ω) (W' · ω) _ _ t = W t ω
      rw [concatAt_of_lt (hSlt t ht)]; exact hmod_lt ω hω W t ht
    · show concatAt (Sn ω) (VL' j · ω) _ _ t = VL (seedEmb xL j) t ω
      rw [concatAt_of_lt (hSlt t ht)]; exact hmod_lt ω hω _ t ht
    · show concatAt (Sn ω) (VR' j · ω) _ _ t = VR (seedEmb xR j) t ω
      rw [concatAt_of_lt (hSlt t ht)]; exact hmod_lt ω hω _ t ht

end Cont

end LocalExt

end InteractingSLE
