/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsHorizon
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# Aux. lemma 108, driver form: the change of weights on one horizon, with a general driver event

Packet PROVE-TRIALS-HI. Specification §7.3, Aux. lemma 108 (`source/spec/p337-384.md` L444–L503, pp. 357–360), its
conclusion (HBT1): "If `E` is a reference event determined by that stopped history, its probability under the second
law is at least `P₀(E)² e^{−‖f‖²_∇}`." Here the comparison is made on the **driving process** of one force word
with two weight vectors `ρ` (the reference, the law that is run) and `ρ'` (the proposed law), by Girsanov's theorem with
the deterministic energy cutoff `m` (no Gaussian free field):

> on a horizon `T`, on the event that every gap of the reference state stays at least `δ` on `[0, T]`, that the energy
> `κ⁻¹ ∫₀ᵀ (Σ (ρ' − ρ)/(W − V))²` of the change of drift is at most `m`, and that the driver has a property `Φ` of its
> restriction to `[0, T)`, `P(event) ≤ (e^m)^{1/2} · codeLaw ρ' S (x)^{1/2}` for every Borel code set `S` containing the
> canonical codes `y` of `ρ'` with `T ≤ ζ(y)` and `Φ(w(y))` (`measure_horizonEvent_le`).

This is PROVE-ZHAN-B4's one-horizon comparison `Zhan.measure_lateEvent_le` with the late-return event replaced by a
general driver event, and without its assumption that the canonical law of `ρ'` has an infinite lifetime: on the event
every gap is positive on `[0, T]`, so the canonical solution of `ρ'` driven by the Girsanov Brownian motion, which
agrees
with the reference driver before its own lifetime, reaches no continuation threshold before `T` (a threshold needs a
mark at the driver). The proof is the same otherwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open Zhan Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

variable {nL nR : ℕ}

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- **The horizon event**: on `G`, gaps `≥ δ` on `[0, T]`, energy of the change `ρ → ρ'` at most `m` on `[0, T]`, and
the driver property `Φ`. -/
def horizonEvent (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (δ : ℝ) (T : ℝ≥0) (m : ℝ)
    (Φ : (ℝ≥0 → ℝ) → Prop) : Set Ω :=
  {ω | ω ∈ G ∧ (∀ s ≤ T, δ ≤ minGap (stateAt W VL VR s ω)) ∧
    changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤ m ∧ Φ (fun t => W t ω)}

/-- **Aux. lemma 108 in driver form, one horizon** (every `κ > 0`). For an evolution of a separated ordered word in
a right-continuous filtration, a good event `G ∈ 𝓖₀` (infinite lifetime, continuous state), other weights `ρ'`,
levels `δ > 0`, `T`, `m`, a driver property `Φ` that only depends on the driver before `T`, and a Borel code set `S`
containing every canonical code of `ρ'` from the same start with lifetime at least `T` whose driver has `Φ`:
`P(horizonEvent) ≤ (e^m)^{1/2} · codeLaw ρ' S (x)^{1/2}`. -/
theorem measure_horizonEvent_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G) (hGζ : ∀ ω ∈ G, ζ ω = ⊤)
    (hGc : ∀ ω ∈ G, Continuous (fun s => stateAt W VL VR s ω)) {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (m : ℝ)
    {Φ : (ℝ≥0 → ℝ) → Prop} (hΦ : ∀ w w' : ℝ≥0 → ℝ, (∀ r : ℝ≥0, r < T → w r = w' r) → Φ w → Φ w')
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRel κ xL xR ρL' ρR', (T : ℝ≥0∞) ≤ cζ x → Φ (cw x) → x ∈ S) :
    P (horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m Φ) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ ρL' ρR' S (xL, xR) ^ (1 / 2 : ℝ) := by
  have href : codeLaw κ ρL' ρR' (univ : Set (XCode nL nR)) (xL, xR) = 1 := by
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL') (ρR := ρR')
    rw [← measure_eventOf_eq_codeLaw hκ hsep hE' (Φ := fun _ _ => True) MeasurableSet.univ
      (fun _ _ _ => iff_of_true (mem_univ _) trivial) (fun _ _ _ _ h => h)]
    simp
  set τ := minGapStop G δ T ζ W VL VR with hτdef
  have hcontOn : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hGc ω hω).continuousOn
  have hτm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s} :=
    measurableSet_minGapStop_le hE.2.1 hE.2.2.1 hE.2.2.2.1 hG hcontOn
  have hτζ : ∀ ω, τ ω ≤ ζ ω := minGapStop_le_zeta hGζ
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
  have hsub : horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m Φ ≤ᵐ[P] (F ∩ A : Set Ω) := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan] with ω hpω hcω hxω hω
    obtain ⟨hωG, hgT, hen, hΦω⟩ := hω
    have hτω : τ ω = T := minGapStop_eq_of_le hωG hgT
    have hst := hGc ω hωG
    have hWc : Continuous fun s => W s ω := continuous_fst.comp hst
    have hVLc : ∀ i, Continuous fun s => VL i s ω := fun i =>
      (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp hst))
    have hVRc : ∀ j, Continuous fun s => VR j s ω := fun j =>
      (continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp hst))
    have hUc : ∀ j, ContinuousOn (fun s => allMarks VL VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
      intro j
      cases j using Fin.addCases with
      | left i => simpa [allMarks] using (hVLc i).continuousOn
      | right i => simpa [allMarks] using (hVRc i).continuousOn
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
              hst.continuousAt
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
      have hagree : ∀ r : ℝ≥0, r < T → W r ω = cw x r := fun r hr =>
        (UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := r)
          (lt_min (by rw [hτω]; exact_mod_cast hr) (lt_of_lt_of_le (by exact_mod_cast hr) hTζ))).1
      exact ⟨x, ⟨⟨hxF, hxS⟩, hSΦ x hxC hTζ (hΦ _ _ hagree hΦω)⟩, hxeq⟩
    · show quadInt θ (T + 1) ω ≤ m
      rw [quadInt_weightDrift_eq hκ hδ hθp hθb hτω (hτζ ω) hWc.continuousOn hUc hgω]
      exact hen
  calc P (horizonEvent κ ρL ρL' ρR ρR' G W VL VR δ T m Φ) ≤ P (F ∩ A) := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * Q F ^ (1 / 2 : ℝ) := hdens
    _ = _ := by rw [hQF]


end TrialsHi

end Sec7

end InteractingSLE
