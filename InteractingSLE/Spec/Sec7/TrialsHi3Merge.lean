/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Cont
import InteractingSLE.Spec.Sec7.TrialsHiCode
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113

/-!
# A same-side merge excludes the non-transience event

Packet PROVE-TRIALS-HI3. Specification §7.3, Aux. lemma 113 (p. 370: "Stop at the continuation threshold or when two
distinct groups on the same side have been swallowed and merge […] If `τ < ∞` and continuation is allowed, at most
`N − 1` active groups remain. The induction hypothesis in the remaining component […] then give the required
continuation and transience."). Under the smaller-count hypothesis `LP.DistinctCompleteBelow κ N` and for a word with
at most `N` marks, almost surely: if the evolution is non-transient (infinite lifetime, a trace, no transient trace)
then no two marks of one side ever meet (`ae_noMeet_of_nonTransient`).

Proof: at the merge time `τ` (PROVE-SEC7-C4's `mergeTime`, a stopping time) the realized word has fewer than `N`
distinct positions, hence is complete (amalgamation); PROVE-RANDRESTART2's random restart at `τ ∧ n` gives the
restarted driver a transient trace on an infinite remaining lifetime; but non-transience passes to every restarted
driver (`TrialsHi.nonTransientEvent_shiftNN`). A meet at any time gives a meet at a later rational time (merged marks
stay merged), so `τ < ∞`.

As a consequence, the canonical non-transience probability of such a word is at most the probability of an infinite
lifetime with no same-side meet (`codeLaw_nt_le_noMeet`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

open ZhanGT4 Zhan Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-- **A same-side merge excludes non-transience** (under the smaller-count hypothesis). -/
theorem ae_noMeet_of_nonTransient {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hD : LP.DistinctCompleteBelow.{u} κ N)
    (hN : nL + nR ≤ N) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, NonTransientEvent (fun t => W t ω) (ζ ω) →
      ∀ t, ¬ SameSideMeet (fun i t => VL i t ω) (fun j t => VR j t ω) t := by
  set τ : Ω → ℝ≥0∞ := fun ω => mergeTime (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) with hτdef
  have hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0) := isStoppingTime_mergeTime hE
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hae : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (B · ω) (ζ ω) := hE.2.2.2.2
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hN𝓖 : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] Nn := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hζ𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE𝓖.2.1
  have hNae : ∀ᵐ ω ∂P, ω ∉ Nn := measure_eq_zero_iff_ae_notMem.1 hN0
  have hpath : ∀ ω ∉ Nn, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hR : RandomRestartTraceStatement.{u} κ := RandRestart.randomRestartTraceStatement hκ
  -- the restarts at `min τ n`, on `{ω ∉ N, τ < ζ, τ ≤ n}`
  have hrestart : ∀ n : ℕ, ∀ᵐ ω ∂P, (ω ∉ Nn ∧ τ ω < ζ ω ∧ τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)) →
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
    set A := {ω | ω ∉ Nn ∧ τ ω < ζ ω ∧ τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)} with hAdef
    have hA₁ : MeasurableSet[IsStoppingTime.measurableSpace hτ] A := by
      have h1 : MeasurableSet[IsStoppingTime.measurableSpace hτ]
          {ω | (ζ ω : WithTop ℝ≥0) ≤ (τ ω : WithTop ℝ≥0)}ᶜ :=
        (IsStoppingTime.measurableSet_stopping_time_le hζ𝓖 hτ).compl
      have hs : {ω | (ζ ω : WithTop ℝ≥0) ≤ (τ ω : WithTop ℝ≥0)}ᶜ = {ω | τ ω < ζ ω} := by
        ext ω
        show ¬ (ζ ω ≤ τ ω) ↔ τ ω < ζ ω
        exact not_le
      rw [hs] at h1
      have hN' : MeasurableSet[IsStoppingTime.measurableSpace hτ] Nnᶜ :=
        ⟨(le_iSup (fun i => (usualAugmentation 𝓕 P) i) 0) _ (hN𝓖 0).compl,
          fun i => (hN𝓖 i).compl.inter (hτ i)⟩
      have e : A = Nnᶜ ∩ ({ω | τ ω < ζ ω} ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := by
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
      have hp := hpath ω hω.1
      have hlt : τ ω < ζ ω := hω.2.1
      have ht : (((τ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        rw [ENNReal.coe_toNNReal (ne_top_of_lt hlt)]; exact hlt
      have hcard := card_lt_of_sameSideMeet (w := fun t => W t ω) (sameSideMeet_mergeTime hp hlt)
      rw [hTA ω hω]
      intro Ω' mΩ'
      exact LP.isCompleteForceWord_of_distinctCompleteBelow hD (isOrderedForceWord_at hp ht)
        (hcard.trans_le hN)
    exact hR xL xR ρL ρR P (usualAugmentation 𝓕 P) W VL VR B ζ hE𝓖 T hT A hA hAζ hcA
  filter_upwards [ae_all_iff.2 hrestart, hNae] with ω hres hωN hnt t hmeet
  have hp := hpath ω hωN
  have hζ : ζ ω = ⊤ := hnt.1
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω := fun s => by rw [hζ]; exact ENNReal.coe_lt_top
  -- a meet at a later rational time, so `τ < ∞`
  obtain ⟨k, hk⟩ := exists_nat_ge (t : ℝ)
  have hkt : t ≤ Real.toNNReal ((k : ℚ) : ℝ) := by
    rw [Rat.cast_natCast, Real.toNNReal_natCast]; exact_mod_cast hk
  have hmeet' := sameSideMeet_of_le hp hkt (hlt _) hmeet
  have hτk : τ ω ≤ ((Real.toNNReal ((k : ℚ) : ℝ) : ℝ≥0) : ℝ≥0∞) :=
    (min_le_left _ _).trans (Band.hitTime_le (hlt _) hmeet')
  have hτfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτk
  have hτζ : τ ω < ζ ω := by rw [hζ]; exact lt_top_iff_ne_top.2 hτfin
  set m : ℝ≥0 := (τ ω).toNNReal with hmdef
  have hm : τ ω = m := (ENNReal.coe_toNNReal hτfin).symm
  obtain ⟨n, hn⟩ := exists_nat_ge (m : ℝ)
  have hmn : (m : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe]; simpa using hn)
  have hTm : (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = m := by
    rw [hm, min_eq_left hmn, ENNReal.toNNReal_coe]
  obtain ⟨η₂, hη₂, hη₂t⟩ := hres n ⟨hωN, hτζ, by rw [hm]; exact hmn⟩
  rw [hTm, hζ, ENNReal.top_sub_coe] at hη₂ hη₂t
  have hwc : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun s _ => hlt s)
  have hnt2 := TrialsHi.nonTransientEvent_shiftNN hwc hp.1 (hζ ▸ hnt) m
  have hsc : Continuous (shiftNN (fun t => W t ω) m) :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [nonTransientEvent_iff hsc (shiftNN_zero _ _)] at hnt2
  exact hnt2.2 ⟨η₂, hη₂, hη₂t rfl⟩

end TrialsHi3

end Sec7

end InteractingSLE
