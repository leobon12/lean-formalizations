/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Spec.Sec7.ContinuityProb2Aux99
import InteractingSLE.Spec.Sec7.ContinuityProbInduction

/-!
# §7.3: continuation through a stopping time with a random complete word

Packet PROVE-RANDRESTART2. Aux. lemma 113 (p. 370: "Stop at the continuation threshold or when two distinct
groups on the same side have been swallowed and merge, whichever comes first. Call this time `τ`. If `τ < ∞` and
continuation is allowed, at most `N − 1` active groups remain. The induction hypothesis in the remaining component,
and its continuously extended inverse hydrodynamic map, then give the required continuation and transience. It
remains to treat `τ = ∞`.") and the one-sided step of the revised induction (p. 379: "otherwise restart the original
driving equations with the smaller active count"; "In every continuation case the smaller-count hypothesis gives a
continuous future trace in the original remaining component. […] its inverse Riemann map extends continuously and
joins that future trace to the prefix") share one step. It is proved here once:

* `isCompleteForceWord_of_hasCompletePrefix`: if every evolution of a word has a stopping time `τ ≤ ζ` (of the usual
  augmentation) with a continuous generating trace through `τ` (closed at `τ` if `τ < ζ`, transient if `τ = ∞`) and,
  when `τ < ζ`, a complete realized word at `τ`, then the word is complete (`randomRestartTraceStatement` at
  `τ ∧ n` on `{τ < ζ, τ ≤ n}`, PROVE-SEC7-C3's join `IsGeneratingTraceIcc.join`, union over `n`);
* `hasCompletePrefix_of_count`: the realized word at `τ < ζ` is complete when it has fewer than `N` distinct
  positions and every distinct-position word with fewer than `N` marks is complete (amalgamation, PROVE-LP);
* `aux113Statement_of_prefix`, `oneSidedStepStatement_of_prefix`: `Sec7.Aux113Statement` and
  `Sec7.OneSidedStepStatement` (the inputs of the κ < 4 induction) from their prefix parts, stated exactly as
  `Aux113PrefixStatement` and `OneSidedPrefixStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

variable {nL nR : ℕ}

/-- **A continuous prefix up to a stopping time with a complete realized word.** Every evolution of the word
`(xL; xR)` with weights `(ρL; ρR)` has a stopping time `τ` of the usual augmentation such that almost surely
`τ ≤ ζ`, the word `V_τ − W_τ` is complete when `τ < ζ`, and the driver has a continuous generating trace on
`[0, τ]` (closed at `τ` when `τ < ζ`; transient when `τ = ∞`). -/
def HasCompletePrefix (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∃ τ : Ω → ℝ≥0∞, IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, τ ω ≤ ζ ω ∧
        (τ ω < ζ ω → LP.IsCompleteForceWord.{u} κ
          (fun i => VL i (τ ω).toNNReal ω - W (τ ω).toNNReal ω)
          (fun j => VR j (τ ω).toNNReal ω - W (τ ω).toNNReal ω) ρL ρR) ∧
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η ∧
          (τ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
          (τ ω < ζ ω → IsGeneratingTraceIcc (fun t => W t ω) (τ ω).toNNReal η)

/-- The same with "complete" replaced by "fewer than `N` distinct positions" (counted side by side, as in
`LP.isCompleteForceWord_of_distinctCompleteBelow`). -/
def HasCountPrefix (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (N : ℕ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∃ τ : Ω → ℝ≥0∞, IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      ∀ᵐ ω ∂P, τ ω ≤ ζ ω ∧
        (τ ω < ζ ω →
          (Finset.univ.image fun i => VL i (τ ω).toNNReal ω - W (τ ω).toNNReal ω).card +
            (Finset.univ.image fun j => VR j (τ ω).toNNReal ω - W (τ ω).toNNReal ω).card < N) ∧
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η ∧
          (τ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
          (τ ω < ζ ω → IsGeneratingTraceIcc (fun t => W t ω) (τ ω).toNNReal η)

/-- The realized word of a solution path before its lifetime is ordered. -/
theorem isOrderedForceWord_at {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IsOrderedForceWord (fun i => vL i t - w t) (fun j => vR j t - w t) := by
  have hf := hp.isForcePath
  refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun j => ?_⟩
  · have := hf.antitone_vL ht hij
    simp only at this ⊢
    linarith
  · have := hf.vL_le_w ht i
    linarith
  · have := hf.monotone_vR ht hij
    simp only at this ⊢
    linarith
  · have := hf.w_le_vR ht j
    linarith

/-- **Count prefix ⇒ complete prefix**, given completeness below `N` (amalgamation of coincident marks). -/
theorem hasCompletePrefix_of_count {κ : ℝ} {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : HasCountPrefix.{u} κ xL xR ρL ρR N) : HasCompletePrefix.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨τ, hτ, hae⟩ := h P 𝓕 W VL VR B ζ hE
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hae, hE.2.2.2.2] with ω ⟨h1, h2, h3⟩ hp
  refine ⟨h1, fun hlt => ?_, h3⟩
  have ht : (((τ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [ENNReal.coe_toNNReal (ne_top_of_lt hlt)]; exact hlt
  intro Ω' mΩ'
  exact LP.isCompleteForceWord_of_distinctCompleteBelow hD (isOrderedForceWord_at hp ht) (h2 hlt)

/-- **Continuation through a stopping time with a random complete word.** A word whose evolutions all have a
complete prefix (`HasCompletePrefix`) is complete, for `κ > 0`. -/
theorem isCompleteForceWord_of_hasCompletePrefix {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : HasCompletePrefix.{u} κ xL xR ρL ρR) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨τ, hτ, hae⟩ := h P 𝓕 W VL VR B ζ hE
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hN𝓖 : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] N := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hζ𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE𝓖.2.1
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hgood : ∀ ω ∉ N, τ ω ≤ ζ ω ∧
      (τ ω < ζ ω → LP.IsCompleteForceWord.{u} κ
        (fun i => VL i (τ ω).toNNReal ω - W (τ ω).toNNReal ω)
        (fun j => VR j (τ ω).toNNReal ω - W (τ ω).toNNReal ω) ρL ρR) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η ∧
        (τ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
        (τ ω < ζ ω → IsGeneratingTraceIcc (fun t => W t ω) (τ ω).toNNReal η) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hR : RandomRestartTraceStatement.{u} κ := RandRestart.randomRestartTraceStatement hκ
  -- the restarts at `min τ n`, on `{ω ∉ N, τ < ζ, τ ≤ n}`
  have hrestart : ∀ n : ℕ, ∀ᵐ ω ∂P, (ω ∉ N ∧ τ ω < ζ ω ∧ τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)) →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace
        (shiftNN (fun t => W t ω) (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal)
        (ζ ω - (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) η ∧
        (ζ ω - (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = ⊤ →
          Tendsto (fun t => ‖η t‖) atTop atTop) := by
    intro n
    set T : Ω → ℝ≥0 := fun ω => (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTdef
    have hpt : ∀ ω, ((T ω : ℝ≥0) : ℝ≥0∞) = min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) := fun ω =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    have hTn := IsStoppingTime.min_const hτ (n : ℝ≥0)
    have hT : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) :=
      fun i => by
        have hs : {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
            {ω | min (τ ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0) ≤ i} := by
          ext ω
          exact iff_of_eq (congrArg (· ≤ (i : WithTop ℝ≥0)) (hpt ω))
        rw [hs]
        exact hTn i
    set A := {ω | ω ∉ N ∧ τ ω < ζ ω ∧ τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)} with hAdef
    have hA₁ : MeasurableSet[IsStoppingTime.measurableSpace hτ] A := by
      have h1 : MeasurableSet[IsStoppingTime.measurableSpace hτ]
          {ω | (ζ ω : WithTop ℝ≥0) ≤ (τ ω : WithTop ℝ≥0)}ᶜ :=
        (IsStoppingTime.measurableSet_stopping_time_le hζ𝓖 hτ).compl
      have hs : {ω | (ζ ω : WithTop ℝ≥0) ≤ (τ ω : WithTop ℝ≥0)}ᶜ = {ω | τ ω < ζ ω} := by
        ext ω
        show ¬ (ζ ω ≤ τ ω) ↔ τ ω < ζ ω
        exact not_le
      rw [hs] at h1
      have hN' : MeasurableSet[IsStoppingTime.measurableSpace hτ] Nᶜ :=
        ⟨(le_iSup (fun i => (usualAugmentation 𝓕 P) i) 0) _ (hN𝓖 0).compl,
          fun i => (hN𝓖 i).compl.inter (hτ i)⟩
      have e : A = Nᶜ ∩ ({ω | τ ω < ζ ω} ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
        ext ω; rfl
      rw [e]
      exact hN'.inter (h1.inter (IsStoppingTime.measurableSet_le' hτ (n : ℝ≥0)))
    have hA₂ : MeasurableSet[usualAugmentation 𝓕 P (n : ℝ≥0)] A := by
      have h2 : MeasurableSet[usualAugmentation 𝓕 P (n : ℝ≥0)]
          (A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := hA₁.2 (n : ℝ≥0)
      have hs : A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A :=
        inter_eq_left.2 fun ω hω => hω.2.2
      rwa [hs] at h2
    have hAmin := (IsStoppingTime.measurableSet_min_const_iff hτ A).2 ⟨hA₁, hA₂⟩
    have hA : MeasurableSet[hT.measurableSpace] A := by
      refine ⟨hAmin.1, fun i => ?_⟩
      have hs : A ∩ {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          A ∩ {ω | min (τ ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0) ≤ i} := by
        ext ω
        exact and_congr_right fun _ => iff_of_eq (congrArg (· ≤ (i : WithTop ℝ≥0)) (hpt ω))
      rw [hs]
      exact hAmin.2 i
    have hTA : ∀ ω ∈ A, T ω = (τ ω).toNNReal := fun ω hω => by
      simp only [hTdef, min_eq_left hω.2.2]
    have hAζ : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω := fun ω hω => by
      rw [hpt ω, min_eq_left hω.2.2]
      exact hω.2.1
    have hcA : ∀ ω ∈ A, LP.IsCompleteForceWord.{u} κ (fun i => VL i (T ω) ω - W (T ω) ω)
        (fun j => VR j (T ω) ω - W (T ω) ω) ρL ρR := fun ω hω => by
      rw [hTA ω hω]
      exact (hgood ω hω.1).2.1 hω.2.1
    exact hR xL xR ρL ρR P (usualAugmentation 𝓕 P) W VL VR B ζ hE𝓖 T hT A hA hAζ hcA
  filter_upwards [ae_all_iff.2 hrestart, hNae, hE.2.2.2.2] with ω hres hωN hp
  obtain ⟨hτζ, -, η₁, hη₁, hη₁t, hη₁c⟩ := hgood ω hωN
  rcases hτζ.lt_or_eq with hlt | heq
  · set m : ℝ≥0 := (τ ω).toNNReal with hmdef
    have hm : τ ω = m := (ENNReal.coe_toNNReal (ne_top_of_lt hlt)).symm
    have hmζ : (m : ℝ≥0∞) < ζ ω := hm ▸ hlt
    obtain ⟨n, hn⟩ := exists_nat_ge (m : ℝ)
    have hmn : (m : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe]; simpa using hn)
    have hTm : (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = m := by
      rw [hm, min_eq_left hmn, ENNReal.toNNReal_coe]
    obtain ⟨η₂, hη₂, hη₂t⟩ := hres n ⟨hωN, hlt, by rw [hm]; exact hmn⟩
    rw [hTm] at hη₂ hη₂t
    have h₁ : IsGeneratingTraceIcc (fun t => W t ω) m η₁ := hη₁c hlt
    have hw : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < m + (ζ ω - m)} := by
      rw [add_tsub_cancel_of_le hmζ.le]
      exact hp.isForcePath.continuousOn_w
    obtain ⟨hJ, hJt⟩ := h₁.join hw hp.isForcePath.w_zero hη₂
    rw [add_tsub_cancel_of_le hmζ.le] at hJ
    refine ⟨joinTrace (fun t => W t ω) m η₁ η₂, hJ, fun hζt => ?_⟩
    have htop : ζ ω - m = ⊤ := by rw [hζt]; exact ENNReal.top_sub_coe
    exact hJt htop (hη₂t htop)
  · exact ⟨η₁, heq ▸ hη₁, fun hζt => hη₁t (heq.trans hζt)⟩

/-- **Count prefix ⇒ complete word**, given completeness below `N`. -/
theorem isCompleteForceWord_of_hasCountPrefix {κ : ℝ} (hκ : 0 < κ) {N : ℕ}
    (hD : LP.DistinctCompleteBelow.{u} κ N) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h : HasCountPrefix.{u} κ xL xR ρL ρR N) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  isCompleteForceWord_of_hasCompletePrefix hκ (hasCompletePrefix_of_count hD h)

end Sec7

end InteractingSLE
