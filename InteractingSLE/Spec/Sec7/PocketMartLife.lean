/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketLifeAe
import InteractingSLE.Spec.Sec7.PhaseSelFullWord
import InteractingSLE.Spec.Sec7.PocketTraversalCoords

/-!
# Aux. lemma 125 before the lifetime, part 1: causality, word entrances and transfers

Packet PROVE-STRIPSYS14 (specification §7.4, proof of Aux. lemma 125, `source/spec/p385-432.md` L213–L232,
pp. 396–397: "Stop before a fixed coordinate bound or at `ζ`, whichever occurs first […] These are genuine stopping
times in the relative history and supply pre-lifetime localizations for the martingale and SDE arguments").

The relative driver of a pocket traversal is only defined before its terminal capacity time. Theorem 2.4's converse
(`PhaseSelFull.martingale_martProc_lifeLoc`, `PhaseSelFull.exists_isWordEntrance_before`) needs globally defined
coordinates; they are applied to the coordinates restarted at a stopping time `σ` before the lifetime (the driver
frozen after `σ`, the force points its geometric images). This file collects the generic tools:

* `geomRW_congr`, `geomLW_congr`: the geometric force images at time `t` only depend on the driver on `[0, t]`;
* `isWordEntrance_congr_le`: Definition 2.1's equations before `T` only see the paths on `[0, T]`;
  `isWordEntrance_zero`: they hold trivially at `T = 0`; `isWordEntrance_of_forall`: equations before an exhausting
  family of times give the equations before their supremum;
* `martingale_of_martingale_sub`: a martingale under the conditional law given an event `A ∈ 𝓕₀`, constant off `A`,
  is a martingale; `ae_of_ae_condSub`, `ae_of_ae_prod_fst`: almost sure transfers from the conditional law and from a
  product space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketMartLife

open MartChar PocketTraversal

/-! ### Causality of the geometric force images -/

section Causality

variable {Ω : Type*} {nL nR : ℕ}

/-- **The right force image at time `t` only depends on the driver on `[0, t]`.** -/
theorem geomRW_congr {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW' : Continuous (W' · ω)) {t : ℝ≥0}
    (h : ∀ s ≤ t, W s ω = W' s ω) (xR : Ω → Fin nR → ℝ) (j : Fin nR) :
    geomRW W xR j t ω = geomRW W' xR j t ω := by
  unfold geomRW
  refine Lemma71B.rightImg_congr (hW'.comp continuous_real_toNNReal) t.coe_nonneg (fun r hr => ?_) _
  exact h _ (Real.toNNReal_le_iff_le_coe.2 hr.2)

/-- **The left force image at time `t` only depends on the driver on `[0, t]`.** -/
theorem geomLW_congr {W W' : ℝ≥0 → Ω → ℝ} {ω : Ω} (hW' : Continuous (W' · ω)) {t : ℝ≥0}
    (h : ∀ s ≤ t, W s ω = W' s ω) (xL : Ω → Fin nL → ℝ) (i : Fin nL) :
    geomLW W xL i t ω = geomLW W' xL i t ω := by
  unfold geomLW
  congr 1
  refine Lemma71B.rightImg_congr (hW'.neg.comp continuous_real_toNNReal) t.coe_nonneg (fun r hr => ?_) _
  show -W r.toNNReal ω = -W' r.toNNReal ω
  rw [h _ (Real.toNNReal_le_iff_le_coe.2 hr.2)]

/-- Before a time `L` up to which the driver is continuous, the right force images are those of the driver frozen
after `t`. -/
theorem geomRW_eq_contW {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {L : WithTop ℝ≥0}
    (hW : ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < L}) {s t : ℝ≥0} (hs : (s : WithTop ℝ≥0) < L)
    (hts : t ≤ s) (xR : Ω → Fin nR → ℝ) (j : Fin nR) :
    geomRW W xR j t ω = geomRW (fun t ω => PhaseSelAdapt.contW (W · ω) s t) xR j t ω := by
  have hc : ContinuousOn (W · ω) (Iic s) := hW.mono fun r hr => lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) hs
  exact geomRW_congr (W' := fun t ω => PhaseSelAdapt.contW (W · ω) s t) (PhaseSelAdapt.continuous_contW hc)
    (fun r hr => (PhaseSelAdapt.contW_of_le (w := fun x => W x ω) (hr.trans hts)).symm) xR j

theorem geomLW_eq_contW {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {L : WithTop ℝ≥0}
    (hW : ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < L}) {s t : ℝ≥0} (hs : (s : WithTop ℝ≥0) < L)
    (hts : t ≤ s) (xL : Ω → Fin nL → ℝ) (i : Fin nL) :
    geomLW W xL i t ω = geomLW (fun t ω => PhaseSelAdapt.contW (W · ω) s t) xL i t ω := by
  have hc : ContinuousOn (W · ω) (Iic s) := hW.mono fun r hr => lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) hs
  exact geomLW_congr (W' := fun t ω => PhaseSelAdapt.contW (W · ω) s t) (PhaseSelAdapt.continuous_contW hc)
    (fun r hr => (PhaseSelAdapt.contW_of_le (w := fun x => W x ω) (hr.trans hts)).symm) xL i

/-- **Ordering before the lifetime**: the left images lie below the driver. -/
theorem geomLW_le_of_lt {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {L : WithTop ℝ≥0}
    (hW : ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < L}) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < L)
    (xL : Ω → Fin nL → ℝ) (i : Fin nL) : geomLW W xL i t ω ≤ W t ω := by
  have hc : ContinuousOn (W · ω) (Iic t) := hW.mono fun r hr => lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) ht
  rw [geomLW_eq_contW hW ht le_rfl xL i]
  have e : PhaseSelAdapt.contW (W · ω) t t = W t ω := PhaseSelAdapt.contW_of_le le_rfl
  exact (geomLW_le (W := fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) t s)
    (fun _ => PhaseSelAdapt.continuous_contW hc) xL ω t i).trans_eq e

/-- **Ordering before the lifetime**: the right images lie above the driver. -/
theorem le_geomRW_of_lt {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {L : WithTop ℝ≥0}
    (hW : ContinuousOn (W · ω) {t | (t : WithTop ℝ≥0) < L}) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < L)
    (xR : Ω → Fin nR → ℝ) (j : Fin nR) : W t ω ≤ geomRW W xR j t ω := by
  have hc : ContinuousOn (W · ω) (Iic t) := hW.mono fun r hr => lt_of_le_of_lt (WithTop.coe_le_coe.2 hr) ht
  rw [geomRW_eq_contW hW ht le_rfl xR j]
  have e : PhaseSelAdapt.contW (W · ω) t t = W t ω := PhaseSelAdapt.contW_of_le le_rfl
  exact e.symm.trans_le (le_geomRW (W := fun s (_ : Ω) => PhaseSelAdapt.contW (W · ω) t s)
    (fun _ => PhaseSelAdapt.continuous_contW hc) xR ω t j)

end Causality

/-! ### Definition 2.1's equations before a time -/

section Entrance

open Aux117

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w w' b b' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0∞}

theorem toNNReal_le_of_mem_uIcc {t : ℝ≥0} {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) : s.toNNReal ≤ t := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  exact Real.toNNReal_le_iff_le_coe.2 hs.2

theorem toNNReal_le_of_mem_uIoc {t : ℝ≥0} {s : ℝ} (hs : s ∈ uIoc (0 : ℝ) t) : s.toNNReal ≤ t := by
  rw [uIoc_of_le t.coe_nonneg] at hs
  exact Real.toNNReal_le_iff_le_coe.2 hs.2

/-- **Definition 2.1's equations before `T` only see the paths on `[0, T]`.** -/
theorem isWordEntrance_congr_le (h : IsWordEntrance a xL xR ρL ρR w vL vR b T)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → w' t = w t)
    (hvL : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ i, vL' i t = vL i t)
    (hvR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → ∀ j, vR' j t = vR j t)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → b' t = b t) : IsWordEntrance a xL xR ρL ρR w' vL' vR' b' T := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ T := by simp
  have hle : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → ∀ {s : ℝ}, s ∈ uIcc (0 : ℝ) t → ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T :=
    fun ht _ hs => (ENNReal.coe_le_coe.2 (toNNReal_le_of_mem_uIcc hs)).trans ht.le
  have hle' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → ∀ {s : ℝ}, s ∈ uIoc (0 : ℝ) t →
      ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T :=
    fun ht _ hs => (ENNReal.coe_le_coe.2 (toNNReal_le_of_mem_uIoc hs)).trans ht.le
  have hgapL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → ∀ i, IntervalIntegrable
      (fun s : ℝ => (w' s.toNNReal - vL' i s.toNNReal)⁻¹) volume 0 t := fun ht i =>
    (h.integrable_gapL _ ht i).congr fun s hs => by
      simp only [hw _ (hle' ht hs), hvL _ (hle' ht hs)]
  have hgapR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → ∀ j, IntervalIntegrable
      (fun s : ℝ => (w' s.toNNReal - vR' j s.toNNReal)⁻¹) volume 0 t := fun ht j =>
    (h.integrable_gapR _ ht j).congr fun s hs => by
      simp only [hw _ (hle' ht hs), hvR _ (hle' ht hs)]
  refine ⟨(hw 0 h0).trans h.w_zero, fun i => (hvL 0 h0 i).trans (h.vL_zero i),
    fun j => (hvR 0 h0 j).trans (h.vR_zero j), h.continuousOn_w.congr fun t ht => hw t (le_of_lt ht),
    fun i => (h.continuousOn_vL i).congr fun t ht => hvL t (le_of_lt ht) i,
    fun j => (h.continuousOn_vR j).congr fun t ht => hvR t (le_of_lt ht) j, fun t ht i k hik => ?_,
    fun t ht i => ?_, fun t ht j => ?_, fun t ht i k hik => ?_, fun t ht i => hgapL ht i,
    fun t ht j => hgapR ht j, fun t ht => ?_, fun t ht i => ?_, fun t ht j => ?_, fun i => ?_, fun j => ?_⟩
  · show vL' k t ≤ vL' i t
    rw [hvL t ht.le, hvL t ht.le]; exact h.antitone_vL t ht hik
  · rw [hvL t ht.le, hw t ht.le]; exact h.vL_le_w t ht i
  · rw [hvR t ht.le, hw t ht.le]; exact h.w_le_vR t ht j
  · show vR' i t ≤ vR' k t
    rw [hvR t ht.le, hvR t ht.le]; exact h.monotone_vR t ht hik
  · have e1 : (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal)) =
        ∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) :=
      Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
        simp only [hw _ (hle ht hs), hvL _ (hle ht hs)]
    have e2 : (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w' s.toNNReal - vR' j s.toNNReal)) =
        ∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal) :=
      Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun s hs => by
        simp only [hw _ (hle ht hs), hvR _ (hle ht hs)]
    rw [hw t ht.le, hb t ht, h.w_eq t ht, e1, e2]
  · rw [hvL t ht.le, h.vL_eq t ht i]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hw _ (hle ht hs), hvL _ (hle ht hs)]
  · rw [hvR t ht.le, h.vR_eq t ht j]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hw _ (hle ht hs), hvR _ (hle ht hs)]
  · refine measure_mono_null (fun s hs => ?_) (h.volume_collisionL i)
    refine ⟨hs.1, hs.2.1, ?_⟩
    rw [← hw _ hs.2.1.le, ← hvL _ hs.2.1.le]
    exact hs.2.2
  · refine measure_mono_null (fun s hs => ?_) (h.volume_collisionR j)
    refine ⟨hs.1, hs.2.1, ?_⟩
    rw [← hw _ hs.2.1.le, ← hvR _ hs.2.1.le]
    exact hs.2.2

/-- **Definition 2.1's equations before the time `0`** reduce to the initial values. -/
theorem isWordEntrance_zero (hw : w 0 = 0) (hvL : ∀ i, vL i 0 = xL i) (hvR : ∀ j, vR j 0 = xR j) :
    IsWordEntrance a xL xR ρL ρR w vL vR b 0 := by
  have hn : ∀ t : ℝ≥0, ¬ (t : ℝ≥0∞) < 0 := fun t => not_lt_zero
  have he : {t : ℝ≥0 | (t : ℝ≥0∞) < 0} = ∅ := by
    ext t; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact hn t
  refine ⟨hw, hvL, hvR, by rw [he]; exact continuousOn_empty _, fun i => by rw [he]; exact continuousOn_empty _,
    fun j => by rw [he]; exact continuousOn_empty _, fun t ht => absurd ht (hn t), fun t ht => absurd ht (hn t),
    fun t ht => absurd ht (hn t), fun t ht => absurd ht (hn t), fun t ht => absurd ht (hn t),
    fun t ht => absurd ht (hn t), fun t ht => absurd ht (hn t), fun t ht => absurd ht (hn t),
    fun t ht => absurd ht (hn t), fun i => ?_, fun j => ?_⟩
  · refine measure_mono_null (fun s hs => absurd hs.2.1 (hn _)) measure_empty
  · refine measure_mono_null (fun s hs => absurd hs.2.1 (hn _)) measure_empty

/-- **Gluing**: Definition 2.1's equations before each of a family of times `T m` that exhausts `[0, T')`
give the equations before `T'`. -/
theorem isWordEntrance_of_forall {Tm : ℕ → ℝ≥0∞} {T' : ℝ≥0∞}
    (h : ∀ m, IsWordEntrance a xL xR ρL ρR w vL vR b (Tm m))
    (hex : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T' → ∃ m, (t : ℝ≥0∞) < Tm m) :
    IsWordEntrance a xL xR ρL ρR w vL vR b T' := by
  have hopen : ∀ m, IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tm m} := fun m =>
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hcont : ∀ {f : ℝ≥0 → ℝ}, (∀ m, ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < Tm m}) →
      ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < T'} := fun hf t ht => by
    obtain ⟨m, hm⟩ := hex t ht
    exact ((hf m).continuousAt ((hopen m).mem_nhds hm)).continuousWithinAt
  have hcoll : ∀ {f g : ℝ≥0 → ℝ},
      (∀ m, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < Tm m ∧ f s.toNNReal = g s.toNNReal} = 0) →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T' ∧ f s.toNNReal = g s.toNNReal} = 0 := fun hf => by
    refine measure_mono_null (fun s hs => ?_) (measure_iUnion_null hf)
    obtain ⟨m, hm⟩ := hex _ hs.2.1
    exact mem_iUnion.2 ⟨m, hs.1, hm, hs.2.2⟩
  refine ⟨(h 0).w_zero, (h 0).vL_zero, (h 0).vR_zero, hcont fun m => (h m).continuousOn_w,
    fun i => hcont fun m => (h m).continuousOn_vL i, fun j => hcont fun m => (h m).continuousOn_vR j,
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun i => hcoll fun m => (h m).volume_collisionL i,
    fun j => hcoll fun m => (h m).volume_collisionR j⟩ <;>
  obtain ⟨m, hm⟩ := hex t ht
  · exact (h m).antitone_vL t hm
  · exact (h m).vL_le_w t hm
  · exact (h m).w_le_vR t hm
  · exact (h m).monotone_vR t hm
  · exact (h m).integrable_gapL t hm
  · exact (h m).integrable_gapR t hm
  · exact (h m).w_eq t hm
  · exact (h m).vL_eq t hm
  · exact (h m).vR_eq t hm

/-- **The pre-lifetime path conditions from Definition 2.1's equations** and the failure of the threshold condition
before the lifetime. -/
theorem isForcePathPre_of_isWordEntrance (h : IsWordEntrance a xL xR ρL ρR w vL vR b T)
    (hthr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t)
      (fun j => vR j t)) : Aux125.IsForcePathPre xL xR ρL ρR w vL vR T :=
  ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    fun ht => h.antitone_vL _ ht, fun ht => h.vL_le_w _ ht, fun ht => h.w_le_vR _ ht,
    fun ht => h.monotone_vR _ ht, fun ht => h.integrable_gapL _ ht, fun ht => h.integrable_gapR _ ht,
    fun ht => h.vL_eq _ ht, fun ht => h.vR_eq _ ht, h.volume_collisionL, h.volume_collisionR,
    fun ht => hthr _ ht⟩

end Entrance

/-! ### Transfers from a conditional law and from a product space -/

section Transfer

open PhaseSel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {A : Set Ω}

/-- **A martingale under the conditional law given an event `A ∈ 𝓕₀`, almost surely constant off `A`, is a
martingale** (the converse of `PhaseSel.martingale_sub`). -/
theorem martingale_of_martingale_sub [IsFiniteMeasure P] (hA0 : MeasurableSet[𝓕 0] A) (h0 : P A ≠ 0)
    {X : ℝ≥0 → Ω → ℝ} (hXa : StronglyAdapted 𝓕 X) (hXi : ∀ t, Integrable (X t) P)
    (hoff : ∀ᵐ ω ∂P, ω ∉ A → ∀ t, X t ω = X 0 ω)
    (hX : Martingale (fun t (ω : A) => X t ω) (subFilt 𝓕 A) (condSub P A)) : Martingale X 𝓕 P := by
  have hA : MeasurableSet A := 𝓕.le 0 _ hA0
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA h0
  refine ⟨hXa, fun i j hij => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le i) (hXi j) (fun s _ _ => (hXi i).integrableOn)
    (fun s hs _ => ?_) (hXa i).aestronglyMeasurable).symm
  have hsm : MeasurableSet s := 𝓕.le i _ hs
  -- the part off `A`
  have hdiff : ∫ ω in s \ A, X i ω ∂P = ∫ ω in s \ A, X j ω ∂P := by
    refine setIntegral_congr_ae (hsm.diff hA) ?_
    filter_upwards [hoff] with ω hω hωs
    rw [hω hωs.2 i, hω hωs.2 j]
  -- the part on `A`
  have hsub : MeasurableSet[subFilt 𝓕 A i] (Subtype.val ⁻¹' s : Set A) := ⟨s, hs, rfl⟩
  have hmart := hX.setIntegral_eq hij hsub
  have hc : ((P A)⁻¹).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨ENNReal.inv_ne_zero.2 (measure_ne_top P A),
    ENNReal.inv_ne_top.2 h0⟩
  simp only [condSub, Measure.restrict_smul, integral_smul_measure, smul_eq_mul] at hmart
  have hmart' := mul_left_cancel₀ hc hmart
  rw [setIntegral_comap_subtype hA hsm, setIntegral_comap_subtype hA hsm] at hmart'
  rw [← integral_inter_add_sdiff hA (hXi i).integrableOn, ← integral_inter_add_sdiff hA (hXi j).integrableOn,
    hmart', hdiff]

/-- **An almost sure property under the conditional law given `A` holds almost surely on `A`.** -/
theorem ae_of_ae_condSub [IsFiniteMeasure P] (hA : MeasurableSet A) {p : Ω → Prop}
    (h : ∀ᵐ (ω : A) ∂(condSub P A), p ω) : ∀ᵐ ω ∂P, ω ∈ A → p ω := by
  rw [ae_iff] at h ⊢
  rw [condSub_apply hA] at h
  have hP : P (Subtype.val '' {ω : A | ¬ p ω}) = 0 := by
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 (ENNReal.inv_ne_zero.2 (measure_ne_top P A))
    · exact h1
  refine measure_mono_null (fun ω hω => ?_) hP
  simp only [mem_ofPred_eq, Classical.not_imp] at hω
  exact ⟨⟨ω, hω.1⟩, hω.2, rfl⟩

/-- **An almost sure property of the first coordinate on a product with a probability space holds almost
surely.** -/
theorem ae_of_ae_prod_fst {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {Q : Measure Ω} {P₀ : Measure Ω₀} [SFinite Q]
    [IsProbabilityMeasure P₀] {p : Ω → Prop} (h : ∀ᵐ x ∂(Q.prod P₀), p x.1) : ∀ᵐ ω ∂Q, p ω :=
  (Measure.ae_ae_of_ae_prod h).mono fun _ hx => hx.exists.choose_spec

end Transfer

end InteractingSLE.Sec7.PocketMartLife
