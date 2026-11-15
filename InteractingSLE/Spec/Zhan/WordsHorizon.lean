/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsDensity
import InteractingSLE.Spec.Zhan.WordsCode
import InteractingSLE.Spec.Zhan.WordsGap
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Spec.Sec2.Assembly2UpTo
import InteractingSLE.Spec.Sec2.Assembly2Life

/-!
# One horizon of the whole-tail comparison

Packet PROVE-ZHAN-B4. Fix a horizon `T`, a gap level `δ`, an energy level `m`, a late time `k` and a radius `R`.
Change the weights `ρ` of an evolution to `ρ'` by Girsanov's theorem up to the first time a gap falls below `δ`
(capped at `T`). On the event that the gaps stay at least `δ` on `[0, T]`, that the energy of the change of drift on
`[0, T]` is at most `m`, and that the trace is within `R` of `0` at a rational time in `[k, T)`, the driver before `T`
is the canonical driver of the reference weights `ρ'` driven by the changed Brownian motion (local pathwise
uniqueness), so its canonical code is a late return. Hence (`WordsDensity`, `Q = Z · P`, `Q`-law of `B̃` = Wiener)

  `P(event) ≤ (e^m)^{1/2} · codeLaw ρ' (lateSet k R) (x)^{1/2}`,

with a bound independent of `T` and `δ` (`measure_lateEvent_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov Coupling

variable {nL nR : ℕ}

/-- The energy `κ⁻¹ ∫₀ᵀ (∑ⱼ (ρ'ⱼ − ρⱼ)/(W − Uⱼ))²` of the change of weights `ρ → ρ'` on `[0, T]`. -/
def changeEnergy (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  1 / κ * ∫ s in (0 : ℝ)..(T : ℝ),
    (∑ j, weightDiff ρL ρL' ρR ρR' j / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The late event at horizon `T`: on `G`, gaps `≥ δ` on `[0, T]`, energy `≤ m` on `[0, T]`, and a rational time in
`[k, T)` at which the trace is within `R` of `0`. -/
def lateEvent (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (δ : ℝ) (T : ℝ≥0) (m : ℝ) (k : ℕ)
    (R : ℝ) : Set Ω :=
  {ω | ω ∈ G ∧ (∀ s ≤ T, δ ≤ minGap (stateAt W VL VR s ω)) ∧
    changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤ m ∧
    ∃ p : ℚ≥0, (k : ℚ≥0) ≤ p ∧ (p : ℝ≥0) < T ∧ ‖LP.traceAt (p : ℝ≥0) (fun t => W t ω)‖ ≤ R}

/-- **The energy of the cut drift on the long horizon** is the change energy on `[0, T]` when the cut time is `T` and
the gaps of the changed marks stay at least `δ` before it. -/
theorem quadInt_weightDrift_eq (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ) {τ : Ω → ℝ≥0∞}
    (hθ : IsStronglyProgressive 𝓖 (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR)) {C : ℝ}
    (hθb : ∀ t ω, |weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR t ω| ≤ C) {ω : Ω} {T : ℝ≥0}
    (hτ : τ ω = T) (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => allMarks VL VR j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hgω : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, weightDiff ρL ρL' ρR ρR' j ≠ 0 →
      δ ≤ |W t ω - allMarks VL VR j t ω|) :
    quadInt (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) (T + 1) ω =
      changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω := by
  set θ := weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR with hθdef
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω ^ 2) volume a b := fun a b =>
    (intervalIntegrable_const (c := C ^ 2)).mono_fun'
      ((measurable_time_of_progressive hθ ω).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖θ u.toNNReal ω ^ 2‖ ≤ C ^ 2
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ ω) 2)
  have hTT : ((T + 1 : ℝ≥0) : ℝ) = (T : ℝ) + 1 := by push_cast; ring
  rw [quadInt, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T ((T + 1 : ℝ≥0) : ℝ))]
  have h2 : ∫ u in (T : ℝ)..((T + 1 : ℝ≥0) : ℝ), θ u.toNNReal ω ^ 2 = 0 := by
    refine intervalIntegral.integral_zero_ae (Eventually.of_forall fun u hu => ?_)
    rw [Set.uIoc_of_le (by rw [hTT]; linarith)] at hu
    have hlt : τ ω < (u.toNNReal : ℝ≥0∞) := by
      rw [hτ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg T).trans hu.1.le)]
      exact hu.1
    show (cutDrift τ ζ (shiftIntegrand κ 1 δ (weightDiff ρL ρL' ρR ρR')) W (allMarks VL VR) u.toNNReal ω) ^ 2
      = 0
    rw [cutDrift_eq_zero hlt]
    ring
  rw [h2, add_zero]
  have h1 := quadInt_shiftDrift_eq hκ 1 hδ (weightDiff ρL ρL' ρR ρR') hτζ hWc hUc hgω (t := T) (by rw [hτ])
  rw [quadInt] at h1
  rw [show θ = shiftDrift κ 1 δ (weightDiff ρL ρL' ρR ρR') τ ζ W (allMarks VL VR) from rfl, h1, changeEnergy,
    one_pow]

/-- **One horizon of the whole-tail comparison.** For an evolution of a separated word in a right-continuous
filtration, a good event `G ∈ 𝓖₀` (infinite lifetime, continuous state), reference weights `ρ'` whose canonical
lifetime is infinite with probability one, and levels `δ > 0`, `T`, `m`, `k`, `R`:
`P(lateEvent) ≤ (e^m)^{1/2} · codeLaw ρ' (lateSet k R) (x)^{1/2}`. -/
theorem measure_lateEvent_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hsep : ∀ i j, xL i < xR j) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G) (hGζ : ∀ ω ∈ G, ζ ω = ⊤)
    (hGc : ∀ ω ∈ G, Continuous (fun s => stateAt W VL VR s ω))
    (href : codeLaw κ ρL' ρR' {x | cζ x = ⊤} (xL, xR) = 1) {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (m : ℝ)
    (k : ℕ) (R : ℝ) :
    P (lateEvent κ ρL ρL' ρR ρR' G W VL VR δ T m k R) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
        codeLaw κ ρL' ρR' (lateSet k R) (xL, xR) ^ (1 / 2 : ℝ) := by
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
    restartSetS κ ρL' ρR' (lateSet k R) with hFdef
  have hFm : MeasurableSet F := hstart (measurableSet_restartSetS (measurableSet_lateSet k R))
  set A := {ω | quadInt θ (T + 1) ω ≤ m} with hAdef
  have hAm : MeasurableSet A := by
    have hq : Measurable fun ω => quadInt θ (T + 1) ω :=
      ((stronglyMeasurable_integral_comp hθp (g := fun x : ℝ => x ^ 2) (measurable_id.pow_const 2)
        (T + 1)).measurable.mono (𝓖.le _) le_rfl)
    exact measurableSet_le hq measurable_const
  have hdens := measure_inter_le_girsanov (isFilteredPreBrownian_of_isFilteredBrownianReal hE.1)
    hθp.stronglyAdapted hθb hθreg (T + 1) hFm hAm (A := A) (m := m) fun ω h => h
  have hQF : Q F = codeLaw κ ρL' ρR' (lateSet k R) (xL, xR) := by
    rw [hFdef, show (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
        fun s : ℝ≥0 => girsanovProcess B θ s ω)) =
        Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ∘ fun ω (s : ℝ≥0) => girsanovProcess B θ s ω from rfl,
      Set.preimage_comp, ← Measure.map_apply hpath
        ((measurableSet_restartSetS (measurableSet_lateSet k R)).preimage measurable_prodMk_left), hmap]
    rfl
  have hcan : ∀ᵐ ω ∂Q, (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω) ∈
      restartSetS κ ρL' ρR' {x | cζ x = ⊤} := by
    have hS : MeasurableSet (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' {x : XCode nL nR | cζ x = ⊤}) :=
      (measurableSet_restartSetS (measurable_cζ (measurableSet_singleton ⊤))).preimage measurable_prodMk_left
    have hW1 : ∀ᵐ f ∂wienerPath, f ∈ Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR' {x : XCode nL nR | cζ x = ⊤} := by
      have h1 : wienerPath (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
          restartSetS κ ρL' ρR' {x : XCode nL nR | cζ x = ⊤}) = 1 := href
      exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
    rw [← hmap] at hW1
    exact ae_of_ae_map hpath.aemeasurable hW1
  have hsub : lateEvent κ ρL ρL' ρR ρR' G W VL VR δ T m k R ≤ᵐ[P] (F ∩ A : Set Ω) := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan] with ω hpω hcω hxω hω
    obtain ⟨hωG, hgT, hen, p, hkp, hpT, hpR⟩ := hω
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
      have hxζ' : cζ x = ⊤ := hxζ
      have hagree : ∀ r : ℝ≥0, r < T → W r ω = cw x r := fun r hr =>
        (UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := r)
          (lt_min (by rw [hτω]; exact_mod_cast hr) (by rw [hxζ']; exact ENNReal.coe_lt_top))).1
      have hlate : x ∈ lateSet k R := by
        refine ⟨hxζ', p, hkp, ?_⟩
        rw [← LP.traceAt_congr fun r hr => hagree r (lt_of_le_of_lt hr hpT)]
        exact hpR
      exact ⟨x, ⟨⟨hxF, hxS⟩, hlate⟩, hxeq⟩
    · show quadInt θ (T + 1) ω ≤ m
      rw [quadInt_weightDrift_eq hκ hδ hθp hθb hτω (hτζ ω) hWc.continuousOn hUc hgω]
      exact hen
  calc P (lateEvent κ ρL ρL' ρR ρR' G W VL VR δ T m k R) ≤ P (F ∩ A) := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * Q F ^ (1 / 2 : ℝ) := hdens
    _ = _ := by rw [hQF]

end InteractingSLE.Zhan
