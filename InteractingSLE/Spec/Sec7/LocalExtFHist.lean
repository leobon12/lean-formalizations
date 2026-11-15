/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtFStmt

/-!
# The stopped history is measurable for the stopped σ-algebra (PROVE-LOCEXT-A3's gap)

Packet PROVE-LOCEXT-F. PROVE-LOCEXT-A3's `map_srcMeasure_eq_map_girsanovMeasure` transfers the law of every
`𝓖_S`-measurable map from `Q = Z·P` to the Girsanov measure `Q'`; its handoff left open that the stopped history
`𝒳_S = (S, (X_{q∧S})_{q ∈ ℚ≥0})` is such a map. It is, up to a null set:

* `measurableSet_stopping_of_subset_lt`: an event of `𝓓_c` inside `{c < S}` lies in the stopped σ-algebra `𝓓_S`;
* `stopVal X S q`: `X_q` on `{q < S}`, and on `{S ≤ q}` the limit of `X` along the dyadic times strictly below `S`
  (`lowVal`); **`measurable_stopVal`**: it is `𝓓_S`-measurable for every process `X` adapted to `𝓓` before `S` (no
  continuity, no null sets); `stopVal_eq`: it is `X_{q∧S}` on every path continuous on `[0, S]` with `0 < S < ∞`;
* `histVersion`: the resulting version of the stopped history of the driving state; **`measurable_histVersion`** and
  `histVersion_eq`;
* **`IsStoppedSeedCoupling.map_stoppedHistory_eq`**: for a stopped seed coupling, the stopped history is almost
  everywhere measurable and has the same law under `Q` and under the measure `Q'` of its driving law (the evolution
  measure through `S`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec2

section Version

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓓 : Filtration ℝ≥0 mΩ} {S : Ω → WithTop ℝ≥0}

/-- **An event of `𝓓_c` inside `{c < S}` is an event of the stopped σ-algebra `𝓓_S`.** -/
theorem measurableSet_stopping_of_subset_lt (hS : IsStoppingTime 𝓓 S) {c : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[𝓓 c] A) (hAS : ∀ ω ∈ A, (c : WithTop ℝ≥0) < S ω) :
    MeasurableSet[hS.measurableSpace] A := by
  refine ⟨le_iSup (fun t => 𝓓 t) c A hA, fun i => ?_⟩
  by_cases hci : c < i
  · exact (𝓓.mono hci.le A hA).inter (hS i)
  · have he : A ∩ {ω | S ω ≤ i} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hω
      exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (not_lt.1 hci)) (hAS ω hω)
    rw [he]
    exact @MeasurableSet.empty Ω (𝓓 i)

/-- The value at the `n`-th dyadic time below the stop, `X_{d_n}` with `d_n = lowApprox n S < S`, and `0` when `d_n` is
not strictly before the stop. -/
def lowVal (X : ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  if (lowApprox n ((S ω).untopD 0) : WithTop ℝ≥0) < S ω then X (lowApprox n ((S ω).untopD 0)) ω else 0

/-- **The stopped value `X_{q ∧ S}`, measurably**: `X_q` on `{q < S}`, and the limit of the dyadic values below `S` on
`{S ≤ q}`. -/
def stopVal (X : ℝ≥0 → Ω → ℝ) (S : Ω → WithTop ℝ≥0) (q : ℝ≥0) (ω : Ω) : ℝ :=
  if (q : WithTop ℝ≥0) < S ω then X q ω else limUnder atTop fun n => lowVal X S n ω

theorem measurable_lowVal (hS : IsStoppingTime 𝓓 S) {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) X) (n : ℕ) :
    Measurable[hS.measurableSpace] (lowVal X S n) := by
  set G : ℕ → Ω → ℝ := fun k ω => if (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0) < S ω then
    X ((k : ℝ≥0) / 2 ^ n) ω else 0 with hGdef
  have hG : ∀ k (A : Set ℝ), MeasurableSet A → MeasurableSet[hS.measurableSpace] (G k ⁻¹' A) := by
    intro k A hA
    set c : ℝ≥0 := (k : ℝ≥0) / 2 ^ n with hc
    have e : G k ⁻¹' A = {ω | ((c : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) ∧ X c ω ∈ A} ∪
        ({ω | S ω ≤ c} ∩ {_ω | (0 : ℝ) ∈ A}) := by
      ext ω
      by_cases h : (c : WithTop ℝ≥0) < S ω
      · have h' : ¬ S ω ≤ c := not_le.2 h
        simp only [hGdef, mem_preimage, ← hc, h, ite_true, mem_union, mem_ofPred_eq, mem_inter_iff, h', false_and,
          or_false]
        exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
      · have h' : S ω ≤ c := not_lt.1 h
        simp only [hGdef, mem_preimage, ← hc, h, ite_false, mem_union, mem_ofPred_eq, mem_inter_iff, h', true_and]
        exact ⟨fun hx => Or.inr hx, fun hx => hx.elim (fun hx' => absurd hx'.1 h) id⟩
    rw [e]
    refine MeasurableSet.union (measurableSet_stopping_of_subset_lt hS (hX c A hA) fun ω hω => hω.1) ?_
    exact (hS.measurableSet_le' c).inter (MeasurableSet.const _)
  have hidx : Measurable[hS.measurableSpace] fun ω => lowIdx n ((S ω).untopD 0) :=
    (measurable_lowIdx n).comp ((WithTop.measurable_untopD (0 : ℝ≥0)).comp hS.measurable)
  intro A hA
  have e : lowVal X S n ⁻¹' A = ⋃ k : ℕ, {ω | lowIdx n ((S ω).untopD 0) = k} ∩ G k ⁻¹' A := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨_, rfl, hω⟩
    · rintro ⟨k, hk, hω⟩
      simp only [lowVal, lowApprox, hk]
      exact hω
  rw [e]
  exact MeasurableSet.iUnion fun k => (hidx (measurableSet_singleton k)).inter (hG k A hA)

/-- The pointwise limit (`limUnder`) of measurable real functions is measurable. -/
theorem measurable_limUnder_nat {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable fun x => limUnder atTop fun n => f n x :=
  (StronglyMeasurable.limUnder fun n => (hf n).stronglyMeasurable).measurable

/-- **`stopVal` is measurable for the stopped σ-algebra** (no continuity and no null sets needed). -/
theorem measurable_stopVal (hS : IsStoppingTime 𝓓 S) {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) X) (q : ℝ≥0) :
    Measurable[hS.measurableSpace] (stopVal X S q) := by
  have hL : Measurable[hS.measurableSpace] fun ω => limUnder atTop fun n => lowVal X S n ω :=
    @measurable_limUnder_nat Ω hS.measurableSpace _ fun n => measurable_lowVal hS hX n
  intro A hA
  have e : stopVal X S q ⁻¹' A = {ω | ((q : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) ∧ X q ω ∈ A} ∪
      ({ω | S ω ≤ q} ∩ (fun ω => limUnder atTop fun n => lowVal X S n ω) ⁻¹' A) := by
    ext ω
    by_cases h : (q : WithTop ℝ≥0) < S ω
    · have h' : ¬ S ω ≤ q := not_le.2 h
      simp only [stopVal, mem_preimage, h, ite_true, mem_union, mem_ofPred_eq, mem_inter_iff, h', false_and, or_false]
      exact ⟨fun hx => ⟨h, hx⟩, fun hx => hx.2⟩
    · have h' : S ω ≤ q := not_lt.1 h
      simp only [stopVal, mem_preimage, h, ite_false, mem_union, mem_ofPred_eq, mem_inter_iff, h', true_and]
      exact ⟨fun hx => Or.inr hx, fun hx => hx.elim (fun hx' => absurd hx'.1 h) id⟩
  rw [e]
  exact (measurableSet_stopping_of_subset_lt hS (hX q A hA) fun ω hω => hω.1).union
    ((hS.measurableSet_le' q).inter (hL hA))

/-- On a path continuous on `[0, S]` with `0 < S < ∞`, `stopVal` is the stopped value `X_{q ∧ S}`. -/
theorem stopVal_eq {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hpos : 0 < S ω) (hfin : S ω ≠ ⊤)
    (hc : ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω}) (q : ℝ≥0) :
    stopVal X S q ω = X (stopAt S q ω) ω := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hfin
  have hs' : S ω = s := hs.symm
  rw [stopAt_of_eq_coe hs' q]
  have hs0 : 0 < s := by
    have : ((0 : ℝ≥0) : WithTop ℝ≥0) < s := by rw [WithTop.coe_zero, ← hs']; exact hpos
    exact WithTop.coe_lt_coe.1 this
  by_cases hq : q < s
  · have hq' : (q : WithTop ℝ≥0) < S ω := by rw [hs']; exact WithTop.coe_lt_coe.2 hq
    rw [stopVal, ite_eq_left hq', min_eq_left hq.le]
  · have hq' : ¬ (q : WithTop ℝ≥0) < S ω := by rw [hs']; exact fun h => hq (WithTop.coe_lt_coe.1 h)
    rw [stopVal, ite_eq_right hq', min_eq_right (not_lt.1 hq)]
    have hlow : ∀ n, lowVal X S n ω = X (lowApprox n s) ω := by
      intro n
      have hlt : (lowApprox n ((S ω).untopD 0) : WithTop ℝ≥0) < S ω := by
        rw [hs', WithTop.untopD_coe]
        exact WithTop.coe_lt_coe.2 (lowApprox_lt hs0 n)
      rw [lowVal, ite_eq_left hlt, hs', WithTop.untopD_coe]
    simp_rw [hlow]
    have hmem : s ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := by rw [mem_ofPred_eq, hs']
    have hmem' : ∀ n, lowApprox n s ∈ {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := fun n => by
      rw [mem_ofPred_eq, hs']
      exact WithTop.coe_le_coe.2 (lowApprox_lt hs0 n).le
    exact ((hc s hmem).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_lowApprox s, Eventually.of_forall hmem'⟩)).limUnder_eq

variable {nL nR : ℕ}

/-- **A version of the stopped history of the driving state** built from `stopVal`. -/
def histVersion (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (S : Ω → WithTop ℝ≥0) (ω : Ω) : DrivingHist nL nR :=
  (S ω, fun q => (stopVal W S q ω, fun i => stopVal (VL i) S q ω, fun j => stopVal (VR j) S q ω))

/-- **The version of the stopped history is measurable for the stopped σ-algebra.** -/
theorem measurable_histVersion (hS : IsStoppingTime 𝓓 S) {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) W)
    (hVL : ∀ i, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓓 (fun ω => (S ω : ℝ≥0∞)) (VR j)) :
    Measurable[hS.measurableSpace] (histVersion W VL VR S) := by
  let _ : MeasurableSpace Ω := hS.measurableSpace
  refine hS.measurable.prodMk (measurable_pi_iff.mpr fun q => ?_)
  exact (measurable_stopVal hS hW q).prodMk ((measurable_pi_iff.mpr fun i => measurable_stopVal hS (hVL i) q).prodMk
    (measurable_pi_iff.mpr fun j => measurable_stopVal hS (hVR j) q))

/-- On a path whose driving state is continuous on `[0, S]`, `0 < S < ∞`, the version is the stopped history. -/
theorem histVersion_eq {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hpos : 0 < S ω) (hfin : S ω ≠ ⊤)
    (hc : ContinuousOn (fun t => drivingState W VL VR t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω}) :
    histVersion W VL VR S ω = stoppedHistory (drivingState W VL VR) S ω := by
  have hW : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} :=
    continuous_fst.comp_continuousOn hc
  have hVL : ∀ i, ContinuousOn (fun t => VL i t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := fun i =>
    (continuous_apply i).comp_continuousOn (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hc))
  have hVR : ∀ j, ContinuousOn (fun t => VR j t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} := fun j =>
    (continuous_apply j).comp_continuousOn (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hc))
  refine Prod.ext rfl (funext fun q => ?_)
  simp only [histVersion, stoppedHistory, drivingState, stopVal_eq hpos hfin hW, stopVal_eq hpos hfin (hVL _),
    stopVal_eq hpos hfin (hVR _)]

end Version

/-! ### The law of the stopped history of a stopped seed coupling -/

section Law

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {S : Ω → WithTop ℝ≥0} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The pathwise regularity at the stop: `0 < S < ∞` and the driving state is continuous on `[0, S]`. -/
def IsRegularStop (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (S : Ω → WithTop ℝ≥0) (ω : Ω) : Prop :=
  0 < S ω ∧ S ω ≠ ⊤ ∧ ContinuousOn (fun t => drivingState W VL VR t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω}

/-- On a path that is the local stop of radius `r > 0` of a driver with `W₀ = 0`, continuous beyond the stop, the stop
is regular. -/
theorem isRegularStop_of_localStop (hr : 0 < r) {ω : Ω} (hW0 : W 0 ω = 0) {ζ₀ : ℝ≥0∞} (hSζ : (S ω : ℝ≥0∞) < ζ₀)
    (hSl : S ω = localStopPath r ζ₀ (fun t => W t ω))
    (hc : ContinuousOn (fun t => drivingState W VL VR t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀}) :
    IsRegularStop W VL VR S ω := by
  have hsub : {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ S ω} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := fun t ht =>
    lt_of_le_of_lt (show ((t : ℝ≥0) : ℝ≥0∞) ≤ (S ω : ℝ≥0∞) from ht) hSζ
  have hWc : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₀} := continuous_fst.comp_continuousOn hc
  have hζ₀ : 0 < ζ₀ := lt_of_le_of_lt zero_le hSζ
  refine ⟨?_, ne_top_of_lt hSζ, hc.mono hsub⟩
  rw [hSl]
  exact localStopPath_pos hWc hW0 hr hζ₀

/-- **A stopped seed coupling has a regular stop almost surely**, under `Q` and under the measure `Q'` of (a). -/
theorem IsStoppedSeedCoupling.ae_isRegularStop (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) : ∀ᵐ ω ∂Q, IsRegularStop W VL VR S ω := by
  obtain ⟨𝓓, hS, ⟨Q', 𝓕, B, -, hQQ', -, -, hE, -⟩, hb, -⟩ := hc
  filter_upwards [hb, hQQ'.ae_le hE.ae_path] with ω ⟨ζ₀, hSζ, hSl, hcont⟩ hp
  exact isRegularStop_of_localStop hr hp.w_zero hSζ hSl hcont

/-- **The stopped history of a stopped seed coupling has the same law under `Q` and under the evolution measure `Q'`**
(PROVE-LOCEXT-A3's gap: the stopped history agrees almost surely with the `𝓓_S`-measurable `histVersion`, and `Q = Q'`
on `𝓓_S`). -/
theorem IsStoppedSeedCoupling.map_stoppedHistory_eq (hr : 0 < r)
    (hc : IsStoppedSeedCoupling κ xL xR ρL ρR r Q W VL VR S h) :
    ∃ (Q' : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure Q' ∧ Q ≪ Q' ∧ Q' ≪ Q ∧
      IsSLEEvolutionUpTo κ xL xR (seedWtL xL ρL) (seedWtR xR ρR) Q' 𝓕 W VL VR B (fun ω => (S ω : ℝ≥0∞)) ∧
      AEMeasurable (stoppedHistory (drivingState W VL VR) S) Q ∧
      Q.map (stoppedHistory (drivingState W VL VR) S) = Q'.map (stoppedHistory (drivingState W VL VR) S) := by
  have hreg := hc.ae_isRegularStop hr
  obtain ⟨𝓓, hS, ⟨Q', 𝓕, B, hQ', hQQ', hQ'Q, -, hE, hagree⟩, -, hW, hVL, hVR, -⟩ := hc
  have hΨ := measurable_histVersion hS hW hVL hVR
  have hΨm : Measurable (histVersion W VL VR S) := hΨ.mono hS.measurableSpace_le le_rfl
  have hΨQ : histVersion W VL VR S =ᵐ[Q] stoppedHistory (drivingState W VL VR) S := by
    filter_upwards [hreg] with ω ⟨h1, h2, h3⟩ using histVersion_eq h1 h2 h3
  have hΨQ' : histVersion W VL VR S =ᵐ[Q'] stoppedHistory (drivingState W VL VR) S := by
    filter_upwards [hQ'Q.ae_le hreg] with ω ⟨h1, h2, h3⟩ using histVersion_eq h1 h2 h3
  refine ⟨Q', 𝓕, B, hQ', hQQ', hQ'Q, hE, ⟨_, hΨm, hΨQ.symm⟩, ?_⟩
  rw [← Measure.map_congr hΨQ, ← Measure.map_congr hΨQ']
  ext U hU
  rw [Measure.map_apply hΨm hU, Measure.map_apply hΨm hU]
  exact hagree _ (hΨ hU)

end Law

end LocalExt

end InteractingSLE
