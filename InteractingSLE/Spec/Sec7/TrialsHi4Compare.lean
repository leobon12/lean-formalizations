/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi4Pos

/-!
# Aux. lemma 108, driver form, with an unchanged colliding side

Packet PROVE-TRIALS-HI4. Specification §7.3, Aux. lemma 108 ("The initial force groups whose weights differ are
required to remain separated before `τ`; groups with identical weights may undergo admissible collisions there") and
Aux. lemma 111 ("In the transient version its unchanged singleton may collide without stopping the comparison"). When
the right weights are unchanged, the comparison `TrialsHi.measure_horizonEvent_le` holds with the gap condition on
the **left marks only** (`measure_horizonEventL_le`): the Girsanov change of weights only needs gaps of the changed
marks, and the canonical solution of the new weights reaches no continuation threshold before the horizon because a
right group at the driver carries the old (admissible) weights. Consequences:

* the one-sided energy bound `changeEnergy_le_oscL` (right weights unchanged);
* `sq_measure_succEventL_le` (the reference success event, left side only, transfers to the proposed weights);
* **`uniformTrialBound_of_referenceL`**: the uniform trial bound of weights with an unchanged right singleton from the
  positivity of the one-sided reference success event (`RefTrialPositivityL`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

open ZhanGT4 Zhan Coupling Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Girsanov TrialsHi

/-! ### The smallest left gap and its hitting time -/

section LGap

variable {nL nR : ℕ}

/-- The smallest gap between the driver and the **left** marks, capped at `1`. -/
def lGap (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := minGap (nR := 0) (p.1, p.2.1, Fin.elim0)

theorem continuous_lGap : Continuous (lGap (nL := nL) (nR := nR)) :=
  continuous_minGap.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const))

theorem le_lGap_iff {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} {δ : ℝ} :
    δ ≤ lGap p ↔ δ ≤ 1 ∧ ∀ i, δ ≤ |p.1 - p.2.1 i| := by
  rw [lGap, le_minGap_iff]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun j => j.elim0⟩⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The first time the smallest left gap falls below `δ`, on `G` (`⊤` off `G`). -/
def lGapHit (G : Set Ω) (δ : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 := fun ω =>
  open Classical in
  if ω ∈ G then hitBelow (fun s => lGap (stateAt W VL VR s ω)) (ζ ω) δ else ⊤

/-- The gap time capped at the horizon `T` on `G`, and `0` off `G`. -/
def lGapStop (G : Set Ω) (δ : ℝ) (T : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Ω → ℝ≥0∞ := fun ω =>
  open Classical in
  if ω ∈ G then ((capTime (lGapHit G δ ζ W VL VR) T ω : ℝ≥0) : ℝ≥0∞) else 0

variable {G : Set Ω} {δ : ℝ} {T : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem lGapStop_le (ω : Ω) : lGapStop G δ T ζ W VL VR ω ≤ T := by
  unfold lGapStop
  split_ifs
  · have h := coe_capTime (lGapHit G δ ζ W VL VR) T ω
    have : (capTime (lGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ T := by
      rw [h]; exact min_le_right _ _
    exact ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 this)
  · exact zero_le

theorem lGapStop_le_zeta (hG : ∀ ω ∈ G, ζ ω = ⊤) (ω : Ω) : lGapStop G δ T ζ W VL VR ω ≤ ζ ω := by
  by_cases hω : ω ∈ G
  · rw [hG ω hω]; exact le_top
  · simp [lGapStop, hω]

/-- On `G`, the capped gap time is `T` when the gaps stay at least `δ` on `[0, T]`. -/
theorem lGapStop_eq_of_le (hω : ω ∈ G)
    (hgap : ∀ s ≤ T, δ ≤ lGap (stateAt W VL VR s ω)) : lGapStop G δ T ζ W VL VR ω = T := by
  have hle : (T : WithTop ℝ≥0) ≤ lGapHit G δ ζ W VL VR ω := by
    simp only [lGapHit, hω, ↓reduceIte]
    refine le_hitBelow fun s _ hs => ?_
    by_contra hlt
    exact absurd (hgap s (not_le.1 hlt).le) (not_le.2 hs)
  have h := coe_capTime (lGapHit G δ ζ W VL VR) T ω
  rw [min_eq_right hle] at h
  simp only [lGapStop, hω, ↓reduceIte, WithTop.coe_eq_coe.1 h]

/-- Before the capped gap time every gap is at least `δ` (on `G`, with continuous state). -/
theorem le_lGap_of_lt_lGapStop (hω : ω ∈ G) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < lGapStop G δ T ζ W VL VR ω) (htζ : (t : ℝ≥0∞) < ζ ω) :
    δ ≤ lGap (stateAt W VL VR t ω) := by
  by_contra hlt
  push Not at hlt
  have h1 : lGapHit G δ ζ W VL VR ω ≤ t := by
    simp only [lGapHit, hω, ↓reduceIte]
    exact hitBelow_le htζ hlt
  have h := coe_capTime (lGapHit G δ ζ W VL VR) T ω
  have h2 : (capTime (lGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ t := by
    rw [h]; exact (min_le_left _ _).trans h1
  have h3 : lGapStop G δ T ζ W VL VR ω ≤ t := by
    simp only [lGapStop, hω, ↓reduceIte]
    exact ENNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 h2)
  exact absurd ht (not_lt.2 h3)

/-- **The capped gap time is a stopping time** of a right-continuous filtration in which the state is adapted,
for a good event `G ∈ 𝓖₀` on which the state is continuous. -/
theorem measurableSet_lGapStop_le {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) (hG : MeasurableSet[𝓖 0] G)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω})
    (s : ℝ≥0) : MeasurableSet[𝓖 s] {ω | lGapStop G δ T ζ W VL VR ω ≤ s} := by
  have hst : IsStoppingTime 𝓖 (lGapHit G δ ζ W VL VR) := by
    classical
    exact isStoppingTime_hitBelow_state hW hVL hVR hG hGc continuous_lGap δ
  have hcap := (isStoppingTime_capTime hst T).measurableSet_le s
  have hGs : MeasurableSet[𝓖 s] G := 𝓖.mono (zero_le (a := s)) _ hG
  have e : {ω | lGapStop G δ T ζ W VL VR ω ≤ s} =
      (G ∩ {ω | (capTime (lGapHit G δ ζ W VL VR) T ω : WithTop ℝ≥0) ≤ s}) ∪ Gᶜ := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [lGapStop, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and,
        mem_compl_iff, not_true_eq_false, or_false, ENNReal.coe_le_coe, WithTop.coe_le_coe]
    · simp [lGapStop, hω]
  rw [e]
  exact (hGs.inter hcap).union hGs.compl

end LGap

/-! ### The comparison with an unchanged right side -/

section Horizon

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- **The horizon event**: on `G`, gaps `≥ δ` on `[0, T]`, energy of the change `ρ → ρ'` at most `m` on `[0, T]`, and
the driver property `Φ`. -/
def horizonEventL (κ : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (δ : ℝ) (T : ℝ≥0) (m : ℝ)
    (Φ : (ℝ≥0 → ℝ) → Prop) : Set Ω :=
  {ω | ω ∈ G ∧ (∀ s ≤ T, δ ≤ lGap (stateAt W VL VR s ω)) ∧
    changeEnergy κ ρL ρL' ρR ρR W VL VR T ω ≤ m ∧ Φ (fun t => W t ω)}

/-- **Aux. lemma 108 in driver form, one horizon** (every `κ > 0`). For an evolution of a separated ordered word in
a right-continuous filtration, a good event `G ∈ 𝓖₀` (infinite lifetime, continuous state), other weights `ρ'`,
levels `δ > 0`, `T`, `m`, a driver property `Φ` that only depends on the driver before `T`, and a Borel code set `S`
containing every canonical code of `ρ'` from the same start with lifetime at least `T` whose driver has `Φ`:
`P(horizonEvent) ≤ (e^m)^{1/2} · codeLaw ρ' S (x)^{1/2}`. -/
theorem measure_horizonEventL_le (hκ : 0 < κ) [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ)
    (hG : MeasurableSet[𝓖 0] G) (hGζ : ∀ ω ∈ G, ζ ω = ⊤)
    (hGc : ∀ ω ∈ G, Continuous (fun s => stateAt W VL VR s ω))
    (hGnt : ∀ ω ∈ G, ∀ t : ℝ≥0, ¬ ForceWord.ThresholdCondition ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω))
    {δ : ℝ} (hδ : 0 < δ) (T : ℝ≥0) (m : ℝ)
    {Φ : (ℝ≥0 → ℝ) → Prop} (hΦ : ∀ w w' : ℝ≥0 → ℝ, (∀ r : ℝ≥0, r < T → w r = w' r) → Φ w → Φ w')
    {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    (hSΦ : ∀ x ∈ CRel κ xL xR ρL' ρR, (T : ℝ≥0∞) ≤ cζ x → Φ (cw x) → x ∈ S) :
    P (horizonEventL κ ρL ρL' ρR G W VL VR δ T m Φ) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ ρL' ρR S (xL, xR) ^ (1 / 2 : ℝ) := by
  have href : codeLaw κ ρL' ρR (univ : Set (XCode nL nR)) (xL, xR) = 1 := by
    obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE'⟩ :=
      exists_isIntegratedSLEEvolution_assembled hκ hF (ρL := ρL') (ρR := ρR)
    rw [← measure_eventOf_eq_codeLaw hκ hsep hE' (Φ := fun _ _ => True) MeasurableSet.univ
      (fun _ _ _ => iff_of_true (mem_univ _) trivial) (fun _ _ _ _ h => h)]
    simp
  set τ := lGapStop G δ T ζ W VL VR with hτdef
  have hcontOn : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hGc ω hω).continuousOn
  have hτm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {ω | τ ω ≤ s} :=
    measurableSet_lGapStop_le hE.2.1 hE.2.2.1 hE.2.2.2.1 hG hcontOn
  have hτζ : ∀ ω, τ ω ≤ ζ ω := lGapStop_le_zeta hGζ
  have hτT : ∀ ω, τ ω ≤ T := lGapStop_le
  have hgapG : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      δ ≤ 1 ∧ ∀ i, δ ≤ |W t ω - VL i t ω| := fun ω hω t ht =>
    le_lGap_iff.1 (le_lGap_of_lt_lGapStop hω ht (ht.trans_le (hτζ ω)))
  have hτG : ∀ ω, ω ∉ G → τ ω = 0 := fun ω hω => by simp [hτdef, lGapStop, hω]
  have hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR i ≠ ρR i → δ ≤ |W t ω - VR i t ω| :=
    Eventually.of_forall fun ω t ht => by
      by_cases hω : ω ∈ G
      · obtain ⟨-, hL⟩ := hgapG ω hω t ht
        exact ⟨fun i _ => hL i, fun j hj => absurd rfl hj⟩
      · rw [hτG ω hω] at ht
        exact absurd ht (not_lt.2 zero_le)
  have hEU := hE.isSLEEvolutionUpTo
  obtain ⟨hQeq, hEQ⟩ := hEU.girsanov_changeWeights hκ ρL' ρR hτm hτζ hτT hδ hgap
  obtain ⟨hθp, hθb, hθreg⟩ := hEU.weightDrift_props ρL' ρR hτm hτζ hδ
  set θ := weightDrift κ δ ρL ρL' ρR ρR τ ζ W VL VR with hθdef
  set Q := girsanovMeasure P 𝓖 B θ (T + 1) with hQdef
  have hQp : IsProbabilityMeasure Q := hQeq.isProb
  have hpath : Measurable fun ω (s : ℝ≥0) => girsanovProcess B θ s ω :=
    measurable_pi_iff.2 fun s => (hEQ.brownian.2.1 s).mono (𝓖.le s) le_rfl
  have hmap : Q.map (fun ω (s : ℝ≥0) => girsanovProcess B θ s ω) = wienerPath :=
    map_path_eq_wienerPath hEQ.brownian.1.toIsPreBrownianReal hpath
  have hstart : Measurable fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
      fun s : ℝ≥0 => girsanovProcess B θ s ω) := measurable_const.prodMk hpath
  set F := (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω)) ⁻¹'
    restartSetS κ ρL' ρR S with hFdef
  have hFm : MeasurableSet F := hstart (measurableSet_restartSetS hS)
  set A := {ω | quadInt θ (T + 1) ω ≤ m} with hAdef
  have hAm : MeasurableSet A := by
    have hq : Measurable fun ω => quadInt θ (T + 1) ω :=
      ((stronglyMeasurable_integral_comp hθp (g := fun x : ℝ => x ^ 2) (measurable_id.pow_const 2)
        (T + 1)).measurable.mono (𝓖.le _) le_rfl)
    exact measurableSet_le hq measurable_const
  have hdens := measure_inter_le_girsanov (isFilteredPreBrownian_of_isFilteredBrownianReal hE.1)
    hθp.stronglyAdapted hθb hθreg (T + 1) hFm hAm (A := A) (m := m) fun ω h => h
  have hQF : Q F = codeLaw κ ρL' ρR S (xL, xR) := by
    rw [hFdef, show (fun ω => (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)),
        fun s : ℝ≥0 => girsanovProcess B θ s ω)) =
        Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ∘ fun ω (s : ℝ≥0) => girsanovProcess B θ s ω from rfl,
      Set.preimage_comp, ← Measure.map_apply hpath
        ((measurableSet_restartSetS hS).preimage measurable_prodMk_left), hmap]
    rfl
  have hcan : ∀ᵐ ω ∂Q, (((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)), fun s : ℝ≥0 => girsanovProcess B θ s ω) ∈
      restartSetS κ ρL' ρR (univ : Set (XCode nL nR)) := by
    have hS : MeasurableSet (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR (univ : Set (XCode nL nR))) :=
      (measurableSet_restartSetS MeasurableSet.univ).preimage measurable_prodMk_left
    have hW1 : ∀ᵐ f ∂wienerPath, f ∈ Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
        restartSetS κ ρL' ρR (univ : Set (XCode nL nR)) := by
      have h1 : wienerPath (Prod.mk ((xL, xR) : (Fin nL → ℝ) × (Fin nR → ℝ)) ⁻¹'
          restartSetS κ ρL' ρR (univ : Set (XCode nL nR))) = 1 := href
      exact (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
    rw [← hmap] at hW1
    exact ae_of_ae_map hpath.aemeasurable hW1
  have hsub : horizonEventL κ ρL ρL' ρR G W VL VR δ T m Φ ≤ᵐ[P] (F ∩ A : Set Ω) := by
    filter_upwards [hQeq.ac'.ae_le hEQ.ae_path, hQeq.ac'.ae_le hEQ.brownian.1.cont,
      hQeq.ac'.ae_le hcan] with ω hpω hcω hxω hω
    obtain ⟨hωG, hgT, hen, hΦω⟩ := hω
    have hτω : τ ω = T := lGapStop_eq_of_le hωG hgT
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
    have hgω : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, weightDiff ρL ρL' ρR ρR j ≠ 0 →
        δ ≤ |W t ω - allMarks VL VR j t ω| := by
      intro t ht j hj
      obtain ⟨-, hL⟩ := hgapG ω hωG t ht
      cases j using Fin.addCases with
      | left i => simpa [allMarks] using hL i
      | right i => exact absurd (by simp [weightDiff]) hj
    refine ⟨?_, ?_⟩
    · obtain ⟨x, ⟨⟨hxF, hxS⟩, hxζ⟩, hxeq⟩ := hxω
      have hxs : startOf x = (xL, xR) := (Prod.ext_iff.1 hxeq).1
      have hx1 : x.1 = enc (fun s => girsanovProcess B θ s ω) := (Prod.ext_iff.1 hxeq).2
      have hxC : x ∈ CRel κ xL xR ρL' ρR := mem_cRelF_iff.1 ⟨hxF, hxs⟩
      have hpx : IsIntegratedSLEPath κ xL xR ρL' ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
      have hcb : cb x = fun s => girsanovProcess B θ s ω := by
        show dec x.1 = _
        rw [hx1]
        exact Sec2.Assembly2.dec_enc_of_continuous hcω
      rw [hcb] at hpx
      have hup := hpx.isSLEPathUpTo (le_refl (cζ x))
      have hgapT : ∀ s : ℝ≥0, s ≤ T → ∀ i, W s ω ≠ VL i s ω := fun s hs => by
        obtain ⟨-, hL⟩ := le_lGap_iff.1 (hgT s hs)
        simp only [Coupling.stateAt] at hL
        intro i he
        have := hL i; rw [he, sub_self, abs_zero] at this; linarith
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
        have hthr : ForceWord.ThresholdCondition ρL' ρR (W t₀ ω) (fun i => VL i t₀ ω) (fun j => VR j t₀ ω) := by
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
        have hL := hgapT t₀ ht₀T
        rcases hthr with h | h
        · have hfe : (Finset.univ.filter fun i => VL i t₀ ω = W t₀ ω) = ∅ :=
            Finset.filter_eq_empty_iff.2 fun i _ he => hL i he.symm
          rw [hfe, Finset.sum_empty] at h
          linarith
        · exact hGnt ω hωG t₀ (Or.inr h)
      have hagree : ∀ r : ℝ≥0, r < T → W r ω = cw x r := fun r hr =>
        (UpTo.agree_of_lt_min hsep hpω hpω.driverEq hup hup.driverEq (t := r)
          (lt_min (by rw [hτω]; exact_mod_cast hr) (lt_of_lt_of_le (by exact_mod_cast hr) hTζ))).1
      exact ⟨x, ⟨⟨hxF, hxS⟩, hSΦ x hxC hTζ (hΦ _ _ hagree hΦω)⟩, hxeq⟩
    · show quadInt θ (T + 1) ω ≤ m
      rw [quadInt_weightDrift_eq hκ hδ hθp hθb hτω (hτζ ω) hWc.continuousOn hUc hgω]
      exact hen
  calc P (horizonEventL κ ρL ρL' ρR G W VL VR δ T m Φ) ≤ P (F ∩ A) := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * Q F ^ (1 / 2 : ℝ) := hdens
    _ = _ := by rw [hQF]


end Horizon

/-! ### The energy with unchanged right weights -/

section Energy

variable {nL nR : ℕ} {Ω : Type*}

/-- **The energy of a change of the left weights only is bounded by the left side oscillation** (every `κ > 0`;
the right marks may collide with the driver). -/
theorem changeEnergy_le_oscL {κ : ℝ} (hκ : 0 < κ) {ρL ρL' : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hnL : ∑ i, (ρL' i - ρL i) = 0) {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ω : Ω} {T : ℝ≥0} (hWc : Continuous fun s => W s ω)
    (hLc : ∀ i, Continuous fun s => VL i s ω)
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ i, 0 < W s ω - VL 0 s ω ∧ W s ω - VL 0 s ω ≤ W s ω - VL i s ω ∧
      W s ω - VL i s ω ≤ W s ω - VL (Fin.last nL) s ω) :
    changeEnergy κ ρL ρL' ρR ρR W VL VR T ω ≤
      1 / κ * ((∑ i, |ρL' i - ρL i|) ^ 2 * sideOsc (fun s => W s ω - VL 0 s ω)
          (fun s => W s ω - VL (Fin.last nL) s ω) T) := by
  set A := (∑ i, |ρL' i - ρL i|) ^ 2 with hA
  set g : ℝ → ℝ := fun s => (∑ i, (ρL' i - ρL i) / (W s.toNNReal ω - VL i s.toNNReal ω)) ^ 2 with hg
  set gL : ℝ → ℝ := fun s => 1 / (W s.toNNReal ω - VL 0 s.toNNReal ω) ^ 2 -
    1 / (W s.toNNReal ω - VL (Fin.last nL) s.toNNReal ω) ^ 2 with hgL
  have hTr : (0 : ℝ) ≤ T := T.coe_nonneg
  have hmem : ∀ s ∈ Icc (0 : ℝ) T, s.toNNReal ≤ T := fun s hs => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
  -- the energy integrand is the left sum
  have hsplit : ∀ s : ℝ, (∑ j, weightDiff ρL ρL' ρR ρR j / (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2 =
      g s := fun s => by
    simp only [hg]
    congr 1
    rw [Fin.sum_univ_add]
    simp only [weightDiff, allMarks, Fin.addCases_left, Fin.addCases_right, sub_self, zero_div,
      Finset.sum_const_zero, add_zero]
  have hcR : Continuous fun s : ℝ => s.toNNReal := continuous_real_toNNReal
  have hW' : Continuous fun s : ℝ => W s.toNNReal ω := hWc.comp hcR
  have hL' : ∀ i, Continuous fun s : ℝ => VL i s.toNNReal ω := fun i => (hLc i).comp hcR
  have hposL : ∀ s ∈ Icc (0 : ℝ) T, ∀ i, 0 < W s.toNNReal ω - VL i s.toNNReal ω := fun s hs i => by
    obtain ⟨h1, h2, -⟩ := hL _ (hmem s hs) i; linarith
  have hgc : ContinuousOn g (Icc (0 : ℝ) T) :=
    ContinuousOn.pow (continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.div (hW'.sub (hL' i)).continuousOn fun s hs => (hposL s hs i).ne') 2
  have hgLc : ContinuousOn gL (Icc (0 : ℝ) T) := by
    refine ContinuousOn.sub ?_ ?_
    · exact continuousOn_const.div ((hW'.sub (hL' 0)).pow 2).continuousOn fun s hs =>
        (pow_pos (hposL s hs 0) 2).ne'
    · exact continuousOn_const.div ((hW'.sub (hL' _)).pow 2).continuousOn fun s hs =>
        (pow_pos (hposL s hs _) 2).ne'
  have hgi : IntervalIntegrable g volume 0 T := (hgc.mono (by rw [uIcc_of_le hTr])).intervalIntegrable
  have hgLi : IntervalIntegrable gL volume 0 T := (hgLc.mono (by rw [uIcc_of_le hTr])).intervalIntegrable
  have hpt : ∀ s ∈ Icc (0 : ℝ) T, g s ≤ A * gL s := fun s hs => by
    have ht := hmem s hs
    exact sq_sum_div_le_of_sum_eq_zero (fun i => ρL' i - ρL i) (fun i => W s.toNNReal ω - VL i s.toNNReal ω)
      (hL _ ht 0).1 (fun i => ⟨(hL _ ht i).2.1, (hL _ ht i).2.2⟩) hnL
  have hmono := intervalIntegral.integral_mono_on hTr hgi (hgLi.const_mul A) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  have hk : 0 ≤ 1 / κ := by positivity
  calc changeEnergy κ ρL ρL' ρR ρR W VL VR T ω = 1 / κ * ∫ s in (0 : ℝ)..(T : ℝ), g s := by
        simp only [changeEnergy, hsplit]
    _ ≤ 1 / κ * (A * ∫ s in (0 : ℝ)..(T : ℝ), gL s) := mul_le_mul_of_nonneg_left hmono hk
    _ = _ := by simp only [sideOsc, hgL, A]

end Energy




section OneWordL

variable {nL nR : ℕ} {κ : ℝ} {zL : Fin (nL + 1) → ℝ} {zR : Fin (nR + 1) → ℝ} {τL πL : Fin (nL + 1) → ℝ}
  {τR : Fin (nR + 1) → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The **one-sided** success event of the reference evolution, read on the nearest left mark (index `0`) and the
outermost left mark (index `last`): infinite lifetime, the nearest left mark never hit, the left side oscillation at
most `C`, and quantitative transience. -/
def succEventL (C : ℝ) (K : ℕ → ℕ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    Set Ω :=
  {ω | ζ ω = ⊤ ∧ (∀ t, VL 0 t ω < W t ω) ∧
    (∀ T, sideOsc (fun s => W s ω - VL 0 s ω) (fun s => W s ω - VL (Fin.last nL) s ω) T ≤ C) ∧
    ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) (fun t => W t ω)‖}

/-- **Aux. lemma 108 (HBT1) in driver form, for one word, with unchanged right weights.** Let the reference
evolution (weights `τ`) of a separated ordered word have an almost surely infinite lifetime, and let the proposed left
weights `π` have the same total (right weights unchanged; the right marks may collide). Then
`P(success)² ≤ e^m · codeLaw (π, τ^R) {quantitative transience}` with `m = κ⁻¹ (Σ|Δ^L|)² C`. -/
theorem sq_measure_succEventL_le (hκ : 0 < κ) [IsProbabilityMeasure P] (hF : IsOrderedForceWord zL zR)
    (hsep : ∀ i j, zL i < zR j) (hE : IsIntegratedSLEEvolution κ zL zR τL τR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hnL : ∑ i, (πL i - τL i) = 0) (C : ℝ) (K : ℕ → ℕ) :
    P (succEventL C K W VL ζ) ^ 2 ≤
      ENNReal.ofReal (Real.exp (1 / κ * ((∑ i, |πL i - τL i|) ^ 2 * C))) *
        codeLaw κ πL τR {x | QTrans K (cw x) (cζ x)} (zL, zR) := by
  set m : ℝ := 1 / κ * ((∑ i, |πL i - τL i|) ^ 2 * C) with hm
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set Good : Ω → Prop := fun ω => ζ ω = ⊤ ∧ Continuous (fun s => stateAt W VL VR s ω) ∧
    IsIntegratedSLEPath κ zL zR τL τR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    filter_upwards [hζ, hE.2.2.2.2] with ω hζω hp
    refine ⟨hζω, ?_, hp⟩
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun t => by
      show (t : ℝ≥0∞) < ζ ω; rw [hζω]; exact ENNReal.coe_lt_top
    have hw : Continuous fun t => W t ω := continuousOn_univ.1 (hf.continuousOn_w.mono fun t _ => hlt t)
    have hl : ∀ i, Continuous fun t => VL i t ω := fun i =>
      continuousOn_univ.1 ((hf.continuousOn_vL i).mono fun t _ => hlt t)
    have hr : ∀ j, Continuous fun t => VR j t ω := fun j =>
      continuousOn_univ.1 ((hf.continuousOn_vR j).mono fun t _ => hlt t)
    exact hw.prodMk ((continuous_pi hl).prodMk (continuous_pi hr))
  set N := {ω | ¬ Good ω} with hNdef
  have hN : P N = 0 := ae_iff.1 hgood
  set G := (toMeasurable P N)ᶜ with hGdef
  have hGm : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    (Ito.measurableSet_usualAugmentation_of_null (measurableSet_toMeasurable P N)
      (by rw [measure_toMeasurable]; exact hN) 0).compl
  have hGgood : ∀ ω ∈ G, Good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P N h)
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact hN
  -- one horizon
  set Φ : ℕ → (ℝ≥0 → ℝ) → Prop := fun T w => ∀ (R : ℕ) (p : ℚ≥0), (K R : ℚ≥0) ≤ p →
    (p : ℝ≥0) < (T : ℝ≥0) → (R : ℝ) < ‖LP.traceAt (p : ℝ≥0) w‖ with hΦdef
  have hΦ : ∀ T : ℕ, ∀ w w' : ℝ≥0 → ℝ, (∀ r : ℝ≥0, r < (T : ℝ≥0) → w r = w' r) → Φ T w → Φ T w' :=
    fun T w w' h hw R p hK hp => by
      rw [← LP.traceAt_congr fun r hr => h r (lt_of_le_of_lt hr hp)]
      exact hw R p hK hp
  have hbound : ∀ (T n : ℕ), P (horizonEventL κ τL πL τR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ πL τR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ) :=
    fun T n => measure_horizonEventL_le hκ hF hsep hE𝓖 hGm (fun ω hω => (hGgood ω hω).1)
      (fun ω hω => (hGgood ω hω).2.1) (fun ω hω t => (hGgood ω hω).2.2.isForcePath.not_threshold
        (by rw [(hGgood ω hω).1]; exact ENNReal.coe_lt_top)) (by positivity) (T : ℝ≥0) m (hΦ T) (measurableSet_qSet K T)
      (fun x _ hT hx => ⟨hT, hx⟩)
  -- the success event lies in the union of the horizon events
  have hsub : ∀ T : ℕ, succEventL C K W VL ζ ∩ G ⊆
      ⋃ n : ℕ, horizonEventL κ τL πL τR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T) := by
    intro T ω ⟨hS, hωG⟩
    obtain ⟨hζω, hst, hp⟩ := hGgood ω hωG
    obtain ⟨-, hnear, hoL, hK⟩ := hS
    have hf := hp.isForcePath
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    have hpos : ∀ s, 0 < lGap (stateAt W VL VR s ω) := fun s => by
      rw [lGap, minGap, Finset.lt_inf'_iff]
      rintro (_ | i | j) -
      · exact one_pos
      · show 0 < |W s ω - VL i s ω|
        have h1 := hf.antitone_vL (hlt s) (Fin.zero_le i)
        have h2 := hnear s
        simp only at h1
        exact abs_pos.2 (by linarith)
      · exact j.elim0
    obtain ⟨n, hn⟩ := exists_one_div_le_on_Iic (continuous_lGap.comp hst) hpos (T : ℝ≥0)
    refine mem_iUnion.2 ⟨n, hωG, hn, ?_, fun R p hKp _ => hK R p hKp⟩
    have hwc : Continuous fun t => W t ω := continuous_fst.comp hst
    have hlc : ∀ i, Continuous fun t => VL i t ω := fun i =>
      (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp hst))
    have hrc : ∀ j, Continuous fun t => VR j t ω := fun j =>
      (continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp hst))
    have hE := changeEnergy_le_oscL hκ hnL (ρL := τL) (ρR := τR) (W := W) (VL := VL) (VR := VR) (ω := ω)
      (T := (T : ℝ≥0)) hwc hlc
      (fun s _ i => ⟨by linarith [hnear s], by
          have := hf.antitone_vL (hlt s) (Fin.zero_le i); simp only at this; linarith, by
          have := hf.antitone_vL (hlt s) (Fin.le_last i); simp only at this; linarith⟩)
    refine hE.trans ?_
    have h1κ : 0 ≤ 1 / κ := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hoL (T : ℝ≥0)) (sq_nonneg _)) h1κ
  -- each horizon
  have hT : ∀ T : ℕ, P (succEventL C K W VL ζ) ≤
      ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) * codeLaw κ πL τR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ) := by
    intro T
    have hmono : Monotone fun n : ℕ =>
        horizonEventL κ τL πL τR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T) := by
      intro n n' hnn' ω ⟨h1, h2, h3, h4⟩
      refine ⟨h1, fun s hs => le_trans ?_ (h2 s hs), h3, h4⟩
      have h1' : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2' : (n : ℝ) + 1 ≤ (n' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnn'
      exact one_div_le_one_div_of_le h1' h2'
    calc P (succEventL C K W VL ζ) = P (succEventL C K W VL ζ ∩ G) := (measure_inter_conull hGc).symm
      _ ≤ P (⋃ n : ℕ, horizonEventL κ τL πL τR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) :=
          measure_mono (hsub T)
      _ = ⨆ n : ℕ, P (horizonEventL κ τL πL τR G W VL VR (1 / ((n : ℝ) + 1)) (T : ℝ≥0) m (Φ T)) :=
          hmono.measure_iUnion
      _ ≤ _ := iSup_le fun n => hbound T n
  -- the limit of the horizons
  have hlim := tendsto_codeLaw_of_antitone (a := κ) (ρL := πL) (ρR := τR) (fun T => measurableSet_qSet K T)
    (antitone_qSet K) (zL, zR)
  rw [iInter_qSet] at hlim
  have hlim' : Tendsto (fun T : ℕ => ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      codeLaw κ πL τR (qSet K T) (zL, zR) ^ (1 / 2 : ℝ)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
        codeLaw κ πL τR {x | QTrans K (cw x) (cζ x)} (zL, zR) ^ (1 / 2 : ℝ))) :=
    ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const.tendsto _).comp hlim)
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
  have hle := ge_of_tendsto' hlim' hT
  have hsq : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc P (succEventL C K W VL ζ) ^ 2 ≤ (ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
        codeLaw κ πL τR {x | QTrans K (cw x) (cζ x)} (zL, zR) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ zero_le hle 2
    _ = _ := by rw [mul_pow, hsq, hsq]

end OneWordL

/-! ### The uniform trial bound with an unchanged right singleton -/

section Singleton

variable {nL : ℕ}

/-- On a singleton right side the reference weights `(ρ, 0)` are the proposed weights of the combined word. -/
theorem refW_singleton (ρR : Fin 1 → ℝ) : refW (n := 0) ![ρR 0, 0] = propW ρR := by
  funext i
  rcases TrialsHi2.fin_two_cases i with rfl | rfl
  · rw [← castSucc_zero', propW_castSucc]
    simp [refW]
  · rw [show (1 : Fin 2) = Fin.last 1 from rfl, propW_last]
    simp [refW]

/-- **The uniform trial bound with an unchanged right singleton** (Aux. lemma 111, "A sole right mark is allowed to
continue … If `s_L ≥ c`, use the reference with weights `s_L, s_R` at `−1, 1` … This argument allows all
instantaneous admissible right collisions … The right mark is at the same physical position `1` in every proposed
configuration, so the boundary-data comparison has no support on the right side"), every `κ > 0`: under the
smaller-count hypothesis at `N = 3`, left weights of total at least `κ/2 − 2` and a right singleton of weight `> −2`
have the uniform trial bound. -/
theorem uniformTrialBound_singletonR {κ : ℝ} (hκ : 0 < κ) (hD3 : LP.DistinctCompleteBelow.{u} κ 3)
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin 1 → ℝ} (hsL : κ / 2 - 2 ≤ ∑ i, ρL i) (hsR : -2 < ρR 0) :
    UniformTrialBound κ ρL ρR := by
  set σL : Fin 2 → ℝ := ![∑ i, ρL i, 0] with hσLdef
  set σR : Fin 2 → ℝ := ![ρR 0, 0] with hσRdef
  have hσL : σL 0 + σL 1 = ∑ i, ρL i := by simp [hσLdef]
  have hRW : refW (n := 0) σR = propW ρR := refW_singleton ρR
  intro M
  by_cases hM : 1 ≤ M
  swap
  · refine ⟨1, one_pos, fun yL yR _ hL0 _ hML _ => ?_⟩
    have := hML 0
    rw [hL0] at this
    exact absurd (by linarith) hM
  obtain ⟨C, K, p₀, hp₀, hpos⟩ := refPos hκ hD3 (sL := ∑ i, ρL i) (sR := ρR 0) hsL hsR hM
  set m : ℝ := 1 / κ * ((∑ i, |propW ρL i - refW (n := nL) σL i|) ^ 2 * C) with hm
  refine ⟨Real.exp (-m) * p₀ ^ 2, by positivity, fun yL yR hy hL0 hR0 hML hMR => ?_⟩
  -- the combined word
  have hFz := isOrderedForceWord_comb hy (by linarith) hML hMR
  have hz0L : combL yL M 0 = -1 := by
    rw [← castSucc_zero', combL_castSucc]; exact hL0
  have hz0R : combR yR M 0 = 1 := by
    rw [← castSucc_zero', combR_castSucc]; exact hR0
  have hsepz : ∀ i j, combL yL M i < combR yR M j := fun i j => by
    have h1 := hFz.1 (Fin.zero_le i)
    have h2 := hFz.2.2.1 (Fin.zero_le j)
    rw [hz0L] at h1
    rw [hz0R] at h2
    linarith
  have hsepy : ∀ i j, yL i < yR j := fun i j => by
    have h1 := hy.1 (Fin.zero_le i)
    have h2 := hy.2.2.1 (Fin.zero_le j)
    rw [hL0] at h1
    rw [hR0] at h2
    linarith
  -- the reference evolution of the combined word and its four-mark deletion
  obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hFz (ρL := refW (n := nL) σL) (ρR := refW (n := 0) σR)
  have hE₄ := hE₁.compEmb (refEmb nL) (refEmb 0) (fun i hi => refW_of_notMem σL hi)
    (fun i hi => refW_of_notMem σR hi)
  have hxL : (fun j => combL yL M (refEmb nL j)) = refXL M := funext fun j => by
    rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h
    · rw [refEmb_zero, hz0L]; rfl
    · rw [refEmb_one, combL_last]; rfl
  have hxR : (fun j => combR yR M (refEmb 0 j)) = refXR M := funext fun j => by
    rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h
    · rw [refEmb_zero, hz0R]; rfl
    · rw [refEmb_one, combR_last]; rfl
  have hwL : (fun j => refW (n := nL) σL (refEmb nL j)) = σL := funext (refW_refEmb σL)
  have hwR : (fun j => refW (n := 0) σR (refEmb 0 j)) = σR := funext (refW_refEmb σR)
  rw [hxL, hxR, hwL, hwR] at hE₄
  obtain ⟨hζ₄, hp₄⟩ := hpos P₁ 𝓕₁ W₁ (fun j => VL₁ (refEmb nL j)) (fun j => VR₁ (refEmb 0 j)) B₁ ζ₁ hE₄
  have hsubS : {ω | RefGoodLR (κ / 2 - 2 ≤ ρR 0) C K (fun t => W₁ t ω) (fun i t => VL₁ (refEmb nL i) t ω)
      (fun j t => VR₁ (refEmb 0 j) t ω) (ζ₁ ω)} ⊆ succEventL C K W₁ VL₁ ζ₁ := by
    intro ω h
    obtain ⟨h1, h2, h3, h4, -⟩ := h
    simp only [refEmb_zero, refEmb_one] at h2 h3
    exact ⟨h1, h2, h3, h4⟩
  have hsq := sq_measure_succEventL_le hκ hFz hsepz hE₁ hζ₄ (πL := propW ρL) (sum_propW_sub_refW hσL) C K
  rw [← hm, hRW] at hsq
  set c := codeLaw κ (propW ρL) (propW ρR) {x | QTrans K (cw x) (cζ x)} (combL yL M, combR yR M) with hc
  have hcge : ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) ≤ c := by
    have h1 : ENNReal.ofReal p₀ ^ 2 ≤ ENNReal.ofReal (Real.exp m) * c :=
      (pow_le_pow_left₀ zero_le (hp₄.trans (measure_mono hsubS)) 2).trans hsq
    have he : ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal (Real.exp m) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
        ENNReal.ofReal_one]
    calc ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) = ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal p₀ ^ 2 := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hp₀.le]
      _ ≤ ENNReal.ofReal (Real.exp (-m)) * (ENNReal.ofReal (Real.exp m) * c) := by gcongr
      _ = c := by rw [← mul_assoc, he, one_mul]
  -- the proposed evolution of the combined word and its deletion to `y`
  obtain ⟨Ω₂, m₂, P₂, hP₂, 𝓕₂, W₂, VL₂, VR₂, B₂, ζ₂, hE₂⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hFz (ρL := propW ρL) (ρR := propW ρR)
  have hEy := hE₂.compEmb (Fin.castSuccOrderEmb (n := nL + 1)) (Fin.castSuccOrderEmb (n := 0 + 1))
    (fun i hi => propW_of_notMem ρL hi) (fun i hi => propW_of_notMem ρR hi)
  have hyL : (fun j => combL yL M (Fin.castSuccOrderEmb (n := nL + 1) j)) = yL :=
    funext fun j => combL_castSucc yL M j
  have hyR : (fun j => combR yR M (Fin.castSuccOrderEmb (n := 0 + 1) j)) = yR :=
    funext fun j => combR_castSucc yR M j
  have hρL : (fun j => propW ρL (Fin.castSuccOrderEmb (n := nL + 1) j)) = ρL :=
    funext fun j => propW_castSucc ρL j
  have hρR : (fun j => propW ρR (Fin.castSuccOrderEmb (n := 0 + 1) j)) = ρR :=
    funext fun j => propW_castSucc ρR j
  rw [hyL, hyR, hρL, hρR] at hEy
  have hA : P₂ {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} = codeLaw κ ρL ρR ntCodeSet (yL, yR) :=
    measure_nonTransient_eq_codeLaw hκ hsepy hEy
  have hQm : MeasurableSet {x : XCode (nL + 1 + 1) (0 + 1 + 1) | QTrans K (cw x) (cζ x)} := by
    rw [← iInter_qSet]; exact MeasurableSet.iInter fun T => measurableSet_qSet K T
  have hB : P₂ {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} = c :=
    measure_eventOf_eq_codeLaw hκ hsepz hE₂ hQm (fun _ _ _ => Iff.rfl) (qTrans_congr K)
  -- the two events are disjoint off a null set
  have hAm : MeasurableSet {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} :=
    (iSup_le fun t => 𝓕₂.le t) _ (measurableSet_nonTransient hE₂.2.1 (Ito.isStoppingTime_lifetime hE₂.2.1))
  have hdisj : P₂ ({ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} ∩
      {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)}) = 0 := by
    refine measure_mono_null (fun ω ⟨hq, hnt⟩ => ?_) (ae_iff.1 hE₂.2.2.2.2)
    intro hp
    have hζ : ζ₂ ω = ⊤ := hq.1
    have hwc : Continuous fun t => W₂ t ω :=
      continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
    have hq' : QTrans K (fun t => W₂ t ω) ⊤ := by rw [← hζ]; exact hq
    have hnt' : NonTransientEvent (fun t => W₂ t ω) ⊤ := by rw [← hζ]; exact hnt
    exact not_nonTransientEvent_of_qTrans hwc hp.1 hq' hnt'
  have hsum : P₂ {ω | NonTransientEvent (fun t => W₂ t ω) (ζ₂ ω)} + P₂ {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} ≤ 1 := by
    have h := measure_union_add_inter {ω | QTrans K (fun t => W₂ t ω) (ζ₂ ω)} hAm (μ := P₂)
    rw [hdisj, add_zero] at h
    rw [add_comm, ← h]
    exact prob_le_one
  rw [hA, hB] at hsum
  have hc1 : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self hsum)
  have hp1 : Real.exp (-m) * p₀ ^ 2 ≤ 1 := by
    have h1 : ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) ≤ 1 := hcge.trans (le_trans le_add_self hsum)
    rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h1
  calc codeLaw κ ρL ρR ntCodeSet (yL, yR) ≤ 1 - c := ENNReal.le_sub_of_add_le_right hc1 hsum
    _ ≤ 1 - ENNReal.ofReal (Real.exp (-m) * p₀ ^ 2) := tsub_le_tsub_left hcge 1
    _ = ENNReal.ofReal (1 - Real.exp (-m) * p₀ ^ 2) := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]


end Singleton

end TrialsHi4

end Sec7

end InteractingSLE
