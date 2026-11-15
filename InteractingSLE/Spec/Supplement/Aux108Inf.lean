/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux108InfEnergy
import InteractingSLE.Spec.Sec7.TrialsHiCompare
import InteractingSLE.Spec.Zhan.WordsTail
import InteractingSLE.Spec.ZhanGT4.NoClusterRec
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# Aux. lemma 108, driver form, through an infinite stopping time

Packet PROVE-T14-TIP2. Specification §7.3, **Aux. lemma 108** (`source/spec/p337-384.md` L443–L503, pp. 357–359):

> … its entire stopped driving law through `τ` is equivalent to the corresponding law with mean `m₁`. **This includes
> an infinite terminal time on the event that the buffer is never left.** … If `E` is a reference event determined by
> that stopped history, its probability under the second law is at least `P₀(E)² e^{−‖f‖²_∇}` (HBT1).

and its use in Lemma GB8 (supplement p. 524): "Aux. 108 gives equivalence on the entire stopped history, including the
event of an infinite stopping time, by one strictly positive finite-energy density. It therefore gives the same zero
probability for the actual interior transient future. … This argument does not condition on a last contact or
multiply finite-time densities along an unbounded sequence."

## Driver form

The two laws are integrated evolutions of one ordered separated word with weights `ρ` (the law that is run) and `ρ'`
(the compared law) with **the same side totals** (GB8: "their far heights agree exactly"). The hull buffer is the
event that every gap stays at least `δ > 0` (`minGap`), and its first exit is the first time a gap falls below `δ`; on
the event that the buffer is never left the stopping time is infinite. The finite-energy bound (HBT3) is
`Aux108Inf.changeEnergy_le_neutralBound` (`Aux108InfEnergy.lean`), uniform in the horizon.

* `measure_sepHorizon_le`: one horizon, with the compared event a property of the **whole compared state** (not only
  its driver) before the horizon — the landed `Sec7.TrialsHi.measure_horizonEvent_le` with this code set;
* **`measure_sepForever_le`** (HBT1 through the infinite stopping time): the probability that the run law never
  leaves the buffer is at most `(e^M)^{1/2}` times the square root of the canonical probability that the compared law
  never leaves it, `M = neutralBound`;
* **`measure_sepForever_eq_zero`**: if the compared law leaves every buffer almost surely, so does the run law
  (zero probability transfers through the infinite stopping time); `measure_sepEventually_eq_zero`: the same for
  "the gaps stay bounded away from zero", a countable union of buffers.

The single horizon-free bound `M` replaces "one strictly positive finite-energy density" on the infinite history: no
finite-time densities are multiplied; the limit is taken in the compared canonical law (continuity from above).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace Aux108Inf

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling Sec7.TrialsHi

variable {nL nR : ℕ}

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- **Aux. lemma 108 in driver form, one horizon, with a state event.** As `Sec7.TrialsHi.measure_horizonEvent_le`
(no driver property), with two changes: the good event `G ∈ 𝓖₀` need not have infinite lifetime (on `G` the state is
continuous before `ζ`, and a finite lifetime forces arbitrarily small gaps), and the code set `S` need only contain the
canonical codes of `ρ'` with lifetime at least `T` whose **whole state** keeps every gap at least `δ` before `T`. -/
theorem measure_sepHorizon_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G)
    (hGthr : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ minGap (stateAt W VL VR t ω) < ε)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (m : ℝ)
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hSsep : ∀ x ∈ CRel κ xL xR ρL' ρR', (T : ℝ≥0∞) ≤ cζ x →
      (∀ r : ℝ≥0, r < T → δ ≤ minGap (Assembly.stateAt x r)) → x ∈ S) :
    P (horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m (fun _ => True)) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ ρL' ρR' S (xL, xR) ^ (1 / 2 : ℝ) := by
  have href : codeLaw κ ρL' ρR' (univ : Set (XCode nL nR)) (xL, xR) = 1 := by
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL') (ρR := ρR')
    rw [← measure_eventOf_eq_codeLaw hκ hsep hE' (Φ := fun _ _ => True) MeasurableSet.univ
      (fun _ _ _ => iff_of_true (mem_univ _) trivial) (fun _ _ _ _ h => h)]
    simp
  set τ := minGapStop G δ T ζ W VL VR with hτdef
  have hcontOn : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω} := hGc
  have hτm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s} :=
    measurableSet_minGapStop_le hE.2.1 hE.2.2.1 hE.2.2.2.1 hG hcontOn
  have hτζ : ∀ ω, τ ω ≤ ζ ω := by
    intro ω
    by_cases hω : ω ∈ G
    · by_cases hζ : ζ ω = ⊤
      · rw [hζ]; exact le_top
      · obtain ⟨t, ht, hlt⟩ := hGthr ω hω hζ δ hδ
        refine le_trans ?_ ht.le
        by_contra hgt
        push Not at hgt
        exact absurd (le_minGap_of_lt_minGapStop hω hgt ht) (not_le.2 hlt)
    · simp [hτdef, minGapStop, hω]
  have hτT : ∀ ω, τ ω ≤ T := minGapStop_le
  have hgapG : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      δ ≤ 1 ∧ (∀ i, δ ≤ |W t ω - VL i t ω|) ∧ ∀ j, δ ≤ |W t ω - VR j t ω| := fun ω hω t ht =>
    le_minGap_iff.1 (le_minGap_of_lt_minGapStop hω ht (ht.trans_le (hτζ ω)))
  have hτG : ∀ ω, ω ∉ G → τ ω = 0 := fun ω hω => by simp [hτdef, minGapStop, hω]
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω| :=
    Eventually.of_forall fun ω t ht => by
      by_cases hω : ω ∈ G
      · obtain ⟨-, hL, hR⟩ := hgapG ω hω t ht
        exact ⟨fun i _ => hL i, fun j _ => hR j⟩
      · rw [hτG ω hω] at ht
        exact absurd ht (not_lt.2 zero_le)
  have hEU := hE.isSLEEvolutionUpTo
  obtain ⟨hQeq, hEQ⟩ := hEU.girsanov_changeWeights hκ ρL' ρR' hτm hτζ hτT hδ hgap
  obtain ⟨hθp, hθb, hθreg⟩ := hEU.weightDrift_props ρL' ρR' hτm hτζ hδ
  set θ := weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (T + 1) with hQdef
  have hQp : IsProbabilityMeasure Q := hQeq.isProb
  have hpath : Measurable fun ω (s : ℝ≥0) => girsanovProcess B θ s ω :=
    measurable_pi_iff.2 fun s => (hEQ.brownian.2.1 s).mono (𝓖.le s) le_rfl
  have hmap : Q.map (fun ω (s : ℝ≥0) => girsanovProcess B θ s ω) = wienerPath :=
    map_path_eq_wienerPath hEQ.brownian.1.toIsPreBrownianReal hpath
  have hstart : Measurable fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
      fun s : ℝ≥0 => girsanovProcess B θ s ω) := measurable_const.prodMk hpath
  set F := (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω)) ⁻¹'
    restartSetS κ ρL' ρR' S with hFdef
  have hFm : MeasurableSet F := hstart (measurableSet_restartSetS hS)
  set A := {ω | quadInt θ (T + 1) ω ≤ m} with hAdef
  have hAm : MeasurableSet A := by
    have hq : Measurable fun ω => quadInt θ (T + 1) ω :=
      ((stronglyMeasurable_integral_comp hθp (g := fun x : ℝ => x ^ 2) (measurable_id.pow_const 2)
        (T + 1)).measurable.mono (𝓖.le _) le_rfl)
    exact measurableSet_le hq measurable_const
  have hdens := measure_inter_le_girsanov (isFilteredPreBrownian_of_isFilteredBrownianReal hE.1)
    hθp.stronglyAdapted hθb hθreg (T + 1) hFm hAm (A := A) (m := m) fun ω h => h
  have hQF : Q F = codeLaw κ ρL' ρR' S (xL, xR) := by
    rw [hFdef, show (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
        fun s : ℝ≥0 => girsanovProcess B θ s ω)) =
        Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ∘ fun ω (s : ℝ≥0) => girsanovProcess B θ s ω from rfl,
      Set.preimage_comp, ← Measure.map_apply hpath
        ((measurableSet_restartSetS hS).preimage measurable_prodMk_left), hmap]
    rfl
  have hcan : ∀ᵐ ω ∂Q, (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω) ∈
      restartSetS κ ρL' ρR' (univ : Set (XCode nL nR)) := by
    have hS : MeasurableSet (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' (univ : Set (XCode nL nR))) :=
      (measurableSet_restartSetS MeasurableSet.univ).preimage measurable_prodMk_left
    have hW1 : ∀ᵐ f ∂wienerPath, f ∈ Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' (univ : Set (XCode nL nR)) := by
      have h1 : wienerPath (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
          restartSetS κ ρL' ρR' (univ : Set (XCode nL nR))) = 1 := href
      exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
    rw [← hmap] at hW1
    exact ae_of_ae_map hpath.aemeasurable hW1
  have hsub : horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m (fun _ => True) ≤ᵐ[P] (F ∩ A : Set Ω) := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan] with ω hpω hcω hxω hω
    obtain ⟨hωG, hgT, hen, -⟩ := hω
    have hτω : τ ω = T := minGapStop_eq_of_le hωG hgT
    have hTζ' : (T : ℝ≥0∞) < ζ ω := by
      by_cases hζ : ζ ω = ⊤
      · rw [hζ]; exact ENNReal.coe_lt_top
      · obtain ⟨t, ht, hlt⟩ := hGthr ω hωG hζ δ hδ
        rcases lt_or_ge t T with h | h
        · exact absurd (hgT t h.le) (not_le.2 hlt)
        · exact lt_of_le_of_lt (by exact_mod_cast h) ht
    have hst := hGc ω hωG
    have hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} := continuous_fst.comp_continuousOn hst
    have hVLc : ∀ i, ContinuousOn (fun s => VL i s ω) {s | (s : ℝ≥0∞) < ζ ω} := fun i =>
      (continuous_apply i).comp_continuousOn
        (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hst))
    have hVRc : ∀ j, ContinuousOn (fun s => VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := fun j =>
      (continuous_apply j).comp_continuousOn
        (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hst))
    have hUc : ∀ j, ContinuousOn (fun s => allMarks VL VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
      intro j
      cases j using Fin.addCases with
      | left i => simpa [allMarks] using hVLc i
      | right i => simpa [allMarks] using hVRc i
    have hgω : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, weightDiff ρL ρL' ρR ρR' j ≠ 0 →
        δ ≤ |W t ω - allMarks VL VR j t ω| := by
      intro t ht j _
      obtain ⟨-, hL, hR⟩ := hgapG ω hωG t ht
      cases j using Fin.addCases with
      | left i => simpa [allMarks] using hL i
      | right i => simpa [allMarks] using hR i
    refine ⟨?_, ?_⟩
    · obtain ⟨x, ⟨⟨hxF, hxS⟩, hxζ⟩, hxeq⟩ := hxω
      have hxs : startOf x = (xL, xR) := (Prod.ext_iff.1 hxeq).1
      have hx1 : x.1 = enc (fun s => girsanovProcess B θ s ω) := (Prod.ext_iff.1 hxeq).2
      have hxC : x ∈ CRel κ xL xR ρL' ρR' := mem_cRelF_iff.1 ⟨hxF, hxs⟩
      have hpx : IsIntegratedSLEPath κ xL xR ρL' ρR' (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
      have hcb : cb x = fun s => girsanovProcess B θ s ω := by
        show dec x.1 = _
        rw [hx1]
        exact Sec2.Assembly2.dec_enc_of_continuous hcω
      rw [hcb] at hpx
      have hup := hpx.isSLEPathUpTo (le_refl (cζ x))
      have hgapT : ∀ s : ℝ≥0, s ≤ T → (∀ i, W s ω ≠ VL i s ω) ∧ ∀ j, W s ω ≠ VR j s ω := fun s hs => by
        obtain ⟨-, hL, hR⟩ := le_minGap_iff.1 (hgT s hs)
        simp only [Coupling.stateAt] at hL hR
        refine ⟨fun i he => ?_, fun j he => ?_⟩
        · have := hL i; rw [he, sub_self, abs_zero] at this; linarith
        · have := hR j; rw [he, sub_self, abs_zero] at this; linarith
      -- the canonical solution of the new weights lives at least until `T`: no threshold while all gaps are positive
      have hTζ : (T : ℝ≥0∞) ≤ cζ x := by
        by_contra hlt
        push Not at hlt
        have hxfin : cζ x ≠ ⊤ := ne_top_of_lt hlt
        set t₀ : ℝ≥0 := (cζ x).toNNReal with ht₀
        have ht₀e : (t₀ : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hxfin
        have ht₀T : t₀ ≤ T := by
          have : (t₀ : ℝ≥0∞) ≤ T := by rw [ht₀e]; exact hlt.le
          exact_mod_cast this
        have hthr : ForceWord.ThresholdCondition ρL' ρR' (W t₀ ω) (fun i => VL i t₀ ω) (fun j => VR j t₀ ω) := by
          rcases eq_or_ne t₀ 0 with h0 | h0
          · have hz : cζ x = 0 := by rw [← ht₀e, h0]; rfl
            have h := hpx.isForcePath.threshold_of_eq_zero hz
            have hw0 : W t₀ ω = 0 := by rw [h0]; exact hpω.1
            have hl0 : (fun i => VL i t₀ ω) = xL := funext fun i => by rw [h0]; exact hpω.vL_zero i
            have hr0 : (fun j => VR j t₀ ω) = xR := funext fun j => by rw [h0]; exact hpω.vR_zero j
            rw [hw0, hl0, hr0]
            exact h
          · have hagree : ∀ r : ℝ≥0, r < t₀ → Agree (fun s => W s ω) (fun i s => VL i s ω) (fun j s => VR j s ω)
                (cw x) (cvL x) (cvR x) r := fun r hr =>
              UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := r)
                (lt_min (by rw [hτω]; exact ENNReal.coe_lt_coe.2 (lt_of_lt_of_le hr ht₀T))
                  (by rw [← ht₀e]; exact ENNReal.coe_lt_coe.2 hr))
            have hcont : ContinuousAt (fun s => (W s ω, fun i => VL i s ω, fun j => VR j s ω)) t₀ :=
              hst.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
                (lt_of_le_of_lt (by exact_mod_cast ht₀T) hTζ'))
            have hlim : Tendsto (fun s => (cw x s, fun i => cvL x i s, fun j => cvR x j s)) (𝓝[<] t₀)
                (𝓝 (W t₀ ω, fun i => VL i t₀ ω, fun j => VR j t₀ ω)) := by
              refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
              filter_upwards [self_mem_nhdsWithin] with r hr
              obtain ⟨h1, h2, h3⟩ := hagree r hr
              simp only [h1, h2, h3]
            exact hpx.isForcePath.threshold_of_tendsto (pos_iff_ne_zero.2 h0) ht₀e hlim
        obtain ⟨hL, hR⟩ := hgapT t₀ ht₀T
        rcases hthr with h | h
        · have hfe : (Finset.univ.filter fun i => VL i t₀ ω = W t₀ ω) = ∅ :=
            Finset.filter_eq_empty_iff.2 fun i _ he => hL i he.symm
          rw [hfe, Finset.sum_empty] at h
          linarith
        · have hfe : (Finset.univ.filter fun j => VR j t₀ ω = W t₀ ω) = ∅ :=
            Finset.filter_eq_empty_iff.2 fun j _ he => hR j he.symm
          rw [hfe, Finset.sum_empty] at h
          linarith
      have hgx : ∀ r : ℝ≥0, r < T → δ ≤ minGap (Assembly.stateAt x r) := fun r hr => by
        obtain ⟨h1, h2, h3⟩ := UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := r)
          (lt_min (by rw [hτω]; exact_mod_cast hr) (lt_of_lt_of_le (by exact_mod_cast hr) hTζ))
        have e : Assembly.stateAt x r = stateAt W VL VR r ω := by
          simp only [Assembly.stateAt, Coupling.stateAt, h1]
          exact Prod.ext rfl (Prod.ext (funext fun i => (h2 i).symm) (funext fun j => (h3 j).symm))
        rw [e]
        exact hgT r hr.le
      exact ⟨x, ⟨⟨hxF, hxS⟩, hSsep x hxC hTζ hgx⟩, hxeq⟩
    · show quadInt θ (T + 1) ω ≤ m
      rw [quadInt_weightDrift_eq hκ hδ hθp hθb hτω (hτζ ω) hWc hUc hgω]
      exact hen
  calc P (horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m (fun _ => True)) ≤ P (F ∩ A) := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * Q F ^ (1 / 2 : ℝ) := hdens
    _ = _ := by rw [hQF]



/-! ### The whole history: the buffer is never left -/

/-- Codes alive at least until `T` whose gaps stay at least `δ` at the rational times before `T`. -/
def sepSetT (δ : ℝ) (T : ℝ≥0) : Set (XCode nL nR) :=
  {x | (T : ℝ≥0∞) ≤ cζ x ∧ ∀ q : ℚ≥0, (q : ℝ≥0) < T → δ ≤ minGap (Assembly.stateAt x q)}

/-- **The buffer is never left**: codes with infinite lifetime whose gaps stay at least `δ` at every rational
time. -/
def sepSet (δ : ℝ) : Set (XCode nL nR) :=
  {x | cζ x = ⊤ ∧ ∀ q : ℚ≥0, δ ≤ minGap (Assembly.stateAt x q)}

theorem measurableSet_sepSetT (δ : ℝ) (T : ℝ≥0) : MeasurableSet (sepSetT (nL := nL) (nR := nR) δ T) :=
  measurableSet_setOfPred.2 ((measurableSet_setOfPred.1 (measurableSet_le measurable_const measurable_cζ)).and
    (Measurable.forall fun _ => measurable_const_imp _ (measurableSet_setOfPred.1
      (measurableSet_le measurable_const (continuous_minGap.measurable.comp (measurable_stateAt _))))))

theorem antitone_sepSetT (δ : ℝ) : Antitone fun n : ℕ => sepSetT (nL := nL) (nR := nR) δ (n : ℝ≥0) := by
  intro m n hmn x hx
  have hmn' : ((m : ℝ≥0) : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hmn
  refine ⟨hmn'.trans hx.1, fun q hq => hx.2 q (lt_of_lt_of_le hq ?_)⟩
  exact_mod_cast hmn

theorem iInter_sepSetT (δ : ℝ) : (⋂ n : ℕ, sepSetT (nL := nL) (nR := nR) δ (n : ℝ≥0)) = sepSet δ := by
  ext x
  simp only [mem_iInter, sepSetT, sepSet, mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨?_, fun q => ?_⟩
    · by_contra hne
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
      have := (h n).1
      push_cast at this
      exact absurd hn (not_lt.2 this)
    · obtain ⟨n, hn⟩ := exists_nat_gt ((q : ℝ≥0) : ℝ)
      exact (h n).2 q (by exact_mod_cast hn)
  · rintro ⟨hζ, hq⟩ n
    exact ⟨by rw [hζ]; exact le_top, fun q _ => hq q⟩

/-- **Aux. lemma 108 through an infinite stopping time, (HBT1).** Let `(W, V)` be an integrated evolution of a
separated ordered word with weights `ρ` in a right-continuous filtration, `G ∈ 𝓖₀` a good event (continuous state
before the lifetime; a finite lifetime forces arbitrarily small gaps, see `exists_good`), and `ρ'` weights with the
**same side totals**. Then the probability that the gaps stay at least
`δ > 0` **forever** (the buffer is never left, the comparison stop is infinite) is at most
`(e^M)^{1/2} · codeLaw ρ' (sepSet δ) (x)^{1/2}` with the horizon-free energy bound `M = neutralBound`. -/
theorem measure_sepForever_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G)
    (hGthr : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ minGap (stateAt W VL VR t ω) < ε)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W VL VR s ω)} ≤
      ENNReal.ofReal (Real.exp (neutralBound κ δ xL xR (fun i => ρL' i - ρL i) (fun j => ρR' j - ρR j))) ^
          (1 / 2 : ℝ) * codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) ^ (1 / 2 : ℝ) := by
  set M := neutralBound κ δ xL xR (fun i => ρL' i - ρL i) (fun j => ρR' j - ρR j) with hM
  have hstep : ∀ n : ℕ, P {ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W VL VR s ω)} ≤
      ENNReal.ofReal (Real.exp M) ^ (1 / 2 : ℝ) *
        codeLaw κ ρL' ρR' (sepSetT δ (n : ℝ≥0)) (xL, xR) ^ (1 / 2 : ℝ) := by
    intro n
    refine (measure_mono_ae ?_).trans (measure_sepHorizon_le (ρL' := ρL') (ρR' := ρR') hκ hF hsep hE hG hGthr hGc
      hδ (n : ℝ≥0) M (measurableSet_sepSetT δ n) fun x _ hT hg => ⟨hT, fun q hq => hg q hq⟩)
    filter_upwards [hE.2.2.2.2] with ω hpω hω
    obtain ⟨hωG, hgap⟩ := hω
    refine ⟨hωG, fun s _ => hgap s, ?_, trivial⟩
    have hζω : ζ ω = ⊤ := by
      by_contra hζ
      obtain ⟨t, -, hlt⟩ := hGthr ω hωG hζ δ hδ
      exact absurd (hgap t) (not_le.2 hlt)
    exact changeEnergy_le_neutralBound hκ hL hR hpω.isForcePath
      (by rw [hζω]; exact ENNReal.coe_lt_top) hδ fun s _ => hgap s
  have hlim := Zhan.tendsto_codeLaw_of_antitone (a := κ) (ρL := ρL') (ρR := ρR')
    (fun n => measurableSet_sepSetT (nL := nL) (nR := nR) δ (n : ℝ≥0)) (antitone_sepSetT δ) (xL, xR)
  rw [iInter_sepSetT] at hlim
  have h1 : Tendsto (fun n : ℕ => codeLaw κ ρL' ρR' (sepSetT δ (n : ℝ≥0)) (xL, xR) ^ (1 / 2 : ℝ)) atTop
      (𝓝 (codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) ^ (1 / 2 : ℝ))) :=
    ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto _).comp hlim
  have hne : ENNReal.ofReal (Real.exp M) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) ENNReal.ofReal_ne_top
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul h1 (Or.inr hne)) hstep

/-- **Zero probability transfers through the infinite stopping time** (GB8, p. 524: "It therefore gives the same
zero probability for the actual interior transient future"). If the compared canonical law of `ρ'` (same side
totals) leaves the buffer `{gaps ≥ δ}` almost surely, so does the run law. -/
theorem measure_sepForever_eq_zero (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G)
    (hGthr : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ minGap (stateAt W VL VR t ω) < ε)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {δ : ℝ} (hδ : 0 < δ)
    (href : codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) = 0) :
    P {ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W VL VR s ω)} = 0 := by
  refine le_antisymm ((measure_sepForever_le hκ hF hsep hE hG hGthr hGc hL hR hδ).trans ?_) bot_le
  rw [href, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]

/-- **The gaps cannot stay bounded away from zero** under the run law when they cannot under the compared law
(a countable union of buffers `δ = 1/(n+1)`). -/
theorem measure_sepEventually_eq_zero (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G)
    (hGthr : ∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ minGap (stateAt W VL VR t ω) < ε)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j)
    (href : ∀ δ : ℝ, 0 < δ → codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) = 0) :
    P {ω | ω ∈ G ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ s, δ ≤ minGap (stateAt W VL VR s ω)} = 0 := by
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null fun n : ℕ =>
    measure_sepForever_eq_zero (δ := 1 / ((n : ℝ) + 1)) hκ hF hsep hE hG hGthr hGc hL hR (by positivity)
      (href _ (by positivity)))
  obtain ⟨hωG, δ, hδ, hgap⟩ := hω
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  exact mem_iUnion.2 ⟨n, hωG, fun s => hn.le.trans (hgap s)⟩


/-! ### The canonical law from a start with marks off the seed -/

theorem measurableSet_sepSet (δ : ℝ) : MeasurableSet (sepSet (nL := nL) (nR := nR) δ) := by
  rw [← iInter_sepSetT]
  exact MeasurableSet.iInter fun n => measurableSet_sepSetT δ n

/-- A continuous function on `ℝ≥0` at least `δ` at every nonnegative rational is at least `δ` everywhere. -/
theorem le_of_forall_nnrat {f : ℝ≥0 → ℝ} (hf : Continuous f) {δ : ℝ} (h : ∀ q : ℚ≥0, δ ≤ f q) (s : ℝ≥0) :
    δ ≤ f s := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hf.continuousAt.preimage_mem_nhds (Iio_mem_nhds hlt))
  obtain ⟨p, hp1, hp2⟩ := Zhan.exists_nnrat_near s hε
  have hp : (p : ℝ≥0) ∈ Metric.ball s ε := by
    rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_lt_iff]
    have : (s : ℝ) ≤ ((p : ℝ≥0) : ℝ) := by exact_mod_cast hp1
    constructor <;> linarith
  exact absurd (h p) (not_le.2 (hball hp))

/-- **The good event of an evolution whose marks are off the seed**, in the usual augmentation: almost sure, with
continuous state before the lifetime, and a finite lifetime forces a small gap (Aux. lemma 3: the state has a limit
at a finite positive lifetime, and it satisfies the threshold condition, so some mark is at the driver). -/
theorem exists_good (hκ : 0 < κ) [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (hL0 : ∀ i, xL i < 0) (hR0 : ∀ j, 0 < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ G : Set Ω, MeasurableSet[usualAugmentation 𝓕 P 0] G ∧ P Gᶜ = 0 ∧
      (∀ ω ∈ G, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω ∧ minGap (stateAt W VL VR t ω) < ε) ∧
      (∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω}) := by
  set Good : Ω → Prop := fun ω =>
    IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
        (fun t => B t ω) (ζ ω) ∧
      ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ with hGood
  have hae : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω h1 h2 using ⟨h1, h2⟩
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hae
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  refine ⟨G, (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
    (by rw [measure_toMeasurable]; exact hN) 0).compl, by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN,
    fun ω hω hζ ε hε => ?_, fun ω hω => ?_⟩
  · obtain ⟨hp, hlim⟩ := hGgood ω hω
    have hnothr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
      rintro (h | h)
      · rw [Finset.filter_eq_empty_iff.2 fun i _ => (hL0 i).ne, Finset.sum_empty] at h; linarith
      · rw [Finset.filter_eq_empty_iff.2 fun j _ => (hR0 j).ne', Finset.sum_empty] at h; linarith
    have hζ0 : ζ ω ≠ 0 := fun h0 => hnothr (hp.isForcePath.threshold_of_eq_zero h0)
    set T := (ζ ω).toNNReal with hT
    have hTe : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
    have hT0 : 0 < T := by
      rw [pos_iff_ne_zero]; intro h; rw [h] at hTe; exact hζ0 (by rw [← hTe]; rfl)
    obtain ⟨w₀, vL₀, vR₀, hlim', hthr⟩ := hlim T hT0 hTe
    have hgap0 : minGap ((w₀, vL₀, vR₀) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) < ε := by
      refine lt_of_le_of_lt ?_ hε
      rcases hthr with h | h
      · obtain ⟨i, hi⟩ : ∃ i, vL₀ i = w₀ := by
          by_contra hne
          push Not at hne
          rw [Finset.filter_eq_empty_iff.2 fun i _ => hne i, Finset.sum_empty] at h; linarith
        refine (Finset.inf'_le _ (Finset.mem_univ (some (Sum.inl i)))).trans (le_of_eq ?_)
        show |w₀ - vL₀ i| = 0
        rw [hi, sub_self, abs_zero]
      · obtain ⟨j, hj⟩ : ∃ j, vR₀ j = w₀ := by
          by_contra hne
          push Not at hne
          rw [Finset.filter_eq_empty_iff.2 fun j _ => hne j, Finset.sum_empty] at h; linarith
        refine (Finset.inf'_le _ (Finset.mem_univ (some (Sum.inr j)))).trans (le_of_eq ?_)
        show |w₀ - vR₀ j| = 0
        rw [hj, sub_self, abs_zero]
    have hev : ∀ᶠ t in 𝓝[<] T, minGap (stateAt W VL VR t ω) < ε :=
      (continuous_minGap.continuousAt.tendsto.comp hlim').eventually (gt_mem_nhds hgap0)
    have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    obtain ⟨t, ht, htT⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨t, by rw [← hTe]; exact_mod_cast htT, ht⟩
  · have hp := (hGgood ω hω).1.isForcePath
    exact hp.continuousOn_w.prodMk ((continuousOn_pi.2 hp.continuousOn_vL).prodMk
      (continuousOn_pi.2 hp.continuousOn_vR))

/-- The state event "infinite lifetime and every gap at least `δ` at every rational time". -/
def SepForever (δ : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ ∀ q : ℚ≥0, δ ≤ minGap ((w q, fun i => vL i q, fun j => vR j q) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

theorem sepForever_congr {δ : ℝ} (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ)
    (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hs : SepForever δ w vL vR τ) : SepForever δ w' vL' vR' τ := by
  obtain ⟨hτ, hq⟩ := hs
  refine ⟨hτ, fun q => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h q (by rw [hτ]; exact ENNReal.coe_lt_top)
  have e : ((w' q, fun i => vL' i q, fun j => vR' j q) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) =
      (w q, fun i => vL i q, fun j => vR j q) := by
    rw [h1]; exact Prod.ext rfl (Prod.ext (funext fun i => (h2 i).symm) (funext fun j => (h3 j).symm))
  rw [e]
  exact hq q

theorem mem_sepSet_iff {δ : ℝ} (x : XCode nL nR) :
    x ∈ sepSet δ ↔ SepForever δ (cw x) (cvL x) (cvR x) (cζ x) := Iff.rfl

/-- **Aux. lemma 108 through an infinite stopping time, canonical form** (HBT1): for an ordered word with marks off
the seed and weights `ρ`, `ρ'` with the same side totals,
`codeLaw ρ (sepSet δ) (x) ≤ (e^M)^{1/2} · codeLaw ρ' (sepSet δ) (x)^{1/2}`. -/
theorem codeLaw_sepSet_le (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hL0 : ∀ i, xL i < 0)
    (hR0 : ∀ j, 0 < xR j) (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {δ : ℝ} (hδ : 0 < δ) :
    codeLaw κ ρL ρR (sepSet δ) (xL, xR) ≤
      ENNReal.ofReal (Real.exp (neutralBound κ δ xL xR (fun i => ρL' i - ρL i) (fun j => ρR' j - ρR j))) ^
          (1 / 2 : ℝ) * codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) ^ (1 / 2 : ℝ) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL) (ρR := ρR)
  have hsep : ∀ i j, xL i < xR j := fun i j => (hL0 i).trans (hR0 j)
  obtain ⟨G, hG, hGc0, hGthr, hGc⟩ := exists_good hκ hL0 hR0 hE'
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE'
  rw [← ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE' (S := sepSet δ) (Ψ := SepForever δ)
    (measurableSet_sepSet δ)
    (fun x _ _ => mem_sepSet_iff x) sepForever_congr]
  calc P' {ω | SepForever δ (fun t => W' t ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω) (ζ' ω)}
      ≤ P' ({ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W' VL' VR' s ω)} ∪ Gᶜ) := by
        refine measure_mono fun ω hω => ?_
        by_cases hωG : ω ∈ G
        · refine Or.inl ⟨hωG, le_of_forall_nnrat ?_ hω.2⟩
          have hc := hGc ω hωG
          rw [hω.1] at hc
          exact continuous_minGap.comp (continuousOn_univ.1 (hc.mono fun _ _ => ENNReal.coe_lt_top))
        · exact Or.inr hωG
    _ ≤ P' {ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W' VL' VR' s ω)} + P' Gᶜ := measure_union_le _ _
    _ = P' {ω | ω ∈ G ∧ ∀ s, δ ≤ minGap (stateAt W' VL' VR' s ω)} := by rw [hGc0, add_zero]
    _ ≤ _ := measure_sepForever_le hκ hF hsep hE𝓖 hG hGthr hGc hL hR hδ

/-- **Zero probability transfers through the infinite stopping time, canonical form.** -/
theorem codeLaw_sepSet_eq_zero (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR) (hL0 : ∀ i, xL i < 0)
    (hR0 : ∀ j, 0 < xR j) (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {δ : ℝ} (hδ : 0 < δ)
    (href : codeLaw κ ρL' ρR' (sepSet δ) (xL, xR) = 0) : codeLaw κ ρL ρR (sepSet δ) (xL, xR) = 0 := by
  refine le_antisymm ((codeLaw_sepSet_le hκ hF hL0 hR0 hL hR hδ).trans ?_) bot_le
  rw [href, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero]

/-- **Zero probability transfers for the future after a stopping time** (the form used by Lemma GB8 at a late rational
time, p. 524). Let `T` be a stopping time and `A ∈ 𝓕_T` an event on which `T < ζ` and every mark is off the driver
at `T` (almost surely). If, from every ordered word with marks off the seed, the compared canonical law of `ρ'`
(same side totals) leaves the buffer `{gaps ≥ δ}` almost surely, then almost surely on `A` the restarted run law
leaves it too. -/
theorem measure_restart_sepForever_eq_zero (hκ : 0 < κ) [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A)
    (hAT : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j))
    (hAoff : ∀ᵐ ω ∂P, ω ∈ A → (∀ i, VL i (T ω) ω < W (T ω) ω) ∧ ∀ j, W (T ω) ω < VR j (T ω) ω)
    (hL : ∑ i, ρL' i = ∑ i, ρL i) (hR : ∑ j, ρR' j = ∑ j, ρR j) {δ : ℝ} (hδ : 0 < δ)
    (href : ∀ y : (Fin nL → ℝ) × (Fin nR → ℝ), IsOrderedForceWord y.1 y.2 → (∀ i, y.1 i < 0) →
      (∀ j, 0 < y.2 j) → codeLaw κ ρL' ρR' (sepSet δ) y = 0) :
    P (A ∩ {ω | SepForever δ (fun t => W (T ω + t) ω - W (T ω) ω) (fun i t => VL i (T ω + t) ω - W (T ω) ω)
      (fun j t => VR j (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)}) = 0 := by
  rw [ZhanGT4.measure_restart_stateEvent hκ hE hT hA hAT (measurableSet_sepSet δ) (fun x _ _ => mem_sepSet_iff x)
    sepForever_congr]
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  rw [setLIntegral_congr_fun_ae hAm (g := fun _ => 0) ?_, lintegral_zero]
  filter_upwards [hE.2.2.2.2, hAoff] with ω hp hoff hωA
  have hpF := hp.isForcePath
  have hTζ := (hAT ω hωA).1
  obtain ⟨hoL, hoR⟩ := hoff hωA
  have hord : IsOrderedForceWord (wordAt W VL VR T ω).1 (wordAt W VL VR T ω).2 :=
    ⟨fun i i' hii' => sub_le_sub_right (hpF.antitone_vL hTζ hii') _, fun i => (sub_neg.2 (hoL i)).le,
      fun j j' hjj' => sub_le_sub_right (hpF.monotone_vR hTζ hjj') _, fun j => (sub_pos.2 (hoR j)).le⟩
  exact codeLaw_sepSet_eq_zero hκ hord (fun i => sub_neg.2 (hoL i)) (fun j => sub_pos.2 (hoR j)) hL hR hδ
    (href _ hord (fun i => sub_neg.2 (hoL i)) (fun j => sub_pos.2 (hoR j)))

end Aux108Inf

end Supp8

end InteractingSLE
