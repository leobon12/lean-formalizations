/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SystemStage

/-!
# Proposition 5.9: the stage law of an adaptive construction from the laws of its fixed candidates

Packet PROVE-STAGED6. Astra's follow-up 5 (`source/external/AstraIG1/ig1_followup5.txt`, correction L8–L14 and §2.3,
L303–L352, ruling R73): an adaptively selected schedule may depend on the retained counterflow; what Proposition 5.9
needs is the simultaneous identification of each realized adaptive prefix with the member of a countable canonical
family (equation (2.2): `X_j = Φ_{I_j}(h)` a.s., `I_j` the countably valued realized schedule index).

In PROVE-PROP59T4's construction `histSys` the identification (2.2) holds **by construction**: stage `j` is the
candidate `cand j (times G r k)` on the event `{hist = k}` (`Prop59System.histSys_piece`, `mixPiece`), so the realized
adaptive piece is the fixed candidate of its realized list of switching times. What remains is to carry the
conditional law over the countable partition `{hist = k}`. This file does that:

* `measure_eq_tsum_inter_fiber`: `P X = ∑' k, P (X ∩ {I = k})` for **every** set `X` and a measurable countable
  partition (outer measure; no measurability of `X`);
* **`isStageLaw_of_mix`**: the comparison-form stage law `IsStageLaw` of a countable mixture, from the stage laws of
  its components, given that on `{I = k}` the mixture is the `k`-th component (pointwise processes, a.s. start and
  reached event) and that past events of the mixture restricted to `{I = k}` are, up to null sets, past events of the
  `k`-th component.

The candidate-level hypotheses and the induction along the realized history are in `CrossCondStagedAdaptTree`.
Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedAdapt

open Prop59Stage

/-! ### Countable partitions -/

section Partition

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {K : Type*} [Countable K]

/-- **Outer measure along a countable measurable partition**: `P X = ∑' k, P (X ∩ {I = k})` for every set `X`. -/
theorem measure_eq_tsum_inter_fiber (P : Measure Ω) (I : Ω → K) (hI : ∀ k, MeasurableSet {ω | I ω = k})
    (X : Set Ω) : P X = ∑' k, P (X ∩ {ω | I ω = k}) := by
  have hU : (⋃ k, {ω | I ω = k}) = univ := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨I ω, rfl⟩
  have hd : Pairwise (Disjoint on fun k => {ω | I ω = k}) := by
    intro k k' hkk'
    refine Set.disjoint_left.2 fun ω h1 h2 => hkk' ?_
    exact h1.symm.trans h2
  calc P X = P.restrict (⋃ k, {ω | I ω = k}) X := by rw [hU, Measure.restrict_univ]
    _ = Measure.sum (fun k => P.restrict {ω | I ω = k}) X := by rw [Measure.restrict_iUnion hd hI]
    _ = ∑' k, P.restrict {ω | I ω = k} X := Measure.sum_apply_of_countable _ _
    _ = ∑' k, P (X ∩ {ω | I ω = k}) := by
        congr 1
        funext k
        exact Measure.restrict_apply' (hI k)

end Partition

/-! ### The stage law of a countable mixture -/

section Mix

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {K : Type*} [Countable K]
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The stage law of a countable mixture.** Let `I` be a countably valued index with measurable fibres. Suppose
that for each `k` the `k`-th component `(yk k, Wk k, …)` obeys `IsStageLaw` for its own past `𝓠k k` and reached event
`Rk k ∈ 𝓠k k`; that on `{I = k}` the mixture's processes are those of the `k`-th component (at every sample) and,
almost surely on `R`, its start is `yk k` and `Rk k` is reached; and that every past event `A ⊆ R` of the mixture,
restricted to `{I = k}`, agrees up to a null set with a past event of the `k`-th component. Then the mixture obeys
`IsStageLaw` for its past `𝓠` and reached event `R`. -/
theorem isStageLaw_of_mix {𝓠 : MeasurableSpace Ω} {R : Set Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (I : Ω → K) (hI : ∀ k, MeasurableSet[mΩ] {ω | I ω = k}) (𝓠k : K → MeasurableSpace Ω) (Rk : K → Set Ω)
    (yk : K → Ω → Start nL nR) (Wk : K → ℝ≥0 → Ω → ℝ) (VLk : K → Fin nL → ℝ≥0 → Ω → ℝ)
    (VRk : K → Fin nR → ℝ≥0 → Ω → ℝ) (Bk : K → ℝ≥0 → Ω → ℝ) (ζk : K → Ω → ℝ≥0∞)
    (hlaw : ∀ k, @IsStageLaw κ Ω mΩ P (𝓠k k) (Rk k) nL nR ρL ρR (yk k) (Wk k) (VLk k) (VRk k) (Bk k) (ζk k))
    (hRk : ∀ k, MeasurableSet[𝓠k k] (Rk k))
    (hpt : ∀ k ω, I ω = k → (fun u => W u ω) = (fun u => Wk k u ω) ∧
      (fun i u => VL i u ω) = (fun i u => VLk k i u ω) ∧ (fun i u => VR i u ω) = (fun i u => VRk k i u ω) ∧
      (fun u => B u ω) = (fun u => Bk k u ω) ∧ ζ ω = ζk k ω)
    (hRy : ∀ k, ∀ᵐ ω ∂P, ω ∈ R → I ω = k → ω ∈ Rk k ∧ y ω = yk k ω)
    (htr : ∀ k A, MeasurableSet[𝓠] A → A ⊆ R →
      ∃ A', MeasurableSet[𝓠k k] A' ∧ A ∩ {ω | I ω = k} =ᵐ[P] A') :
    @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ := by
  refine ⟨?_, ?_⟩
  · have h1 := ae_all_iff.2 fun k => (hRy k).and (hlaw k).1
    filter_upwards [h1] with ω hω hωR
    obtain ⟨hRy', hp⟩ := hω (I ω)
    obtain ⟨hR', hy'⟩ := hRy' hωR rfl
    obtain ⟨hW, hVL, hVR, hB, hζ⟩ := hpt (I ω) ω rfl
    rw [hy', hW, hVL, hVR, hB, hζ]
    exact hp hR'
  · intro S hS p hprem A hA hAR
    have hobs : ∀ k, ∀ ω, ω ∈ R → I ω = k → y ω = yk k ω →
        ((y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) : Start nL nR × Samp nL nR) =
          (yk k ω, samp (Wk k · ω) (fun i t => VLk k i t ω) (fun k' t => VRk k k' t ω) (ζk k ω)) := by
      intro k ω _ hk hy
      obtain ⟨hW, hVL, hVR, -, hζ⟩ := hpt k ω hk
      rw [hy, hW, hVL, hVR, hζ]
    have hk : ∀ k, p * P (A ∩ {ω | I ω = k}) ≤
        P ((A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) ∩
          {ω | I ω = k}) := by
      intro k
      obtain ⟨A', hA', he⟩ := htr k A hA hAR
      have he'' : A ∩ {ω | I ω = k} =ᵐ[P] (A' ∩ Rk k : Set Ω) := by
        filter_upwards [he, hRy k] with ω h1 h2
        refine propext ⟨fun h => ⟨?_, (h2 (hAR h.1) h.2).1⟩, fun h => ?_⟩
        · have : (ω ∈ A') := by rw [← h1]; exact h
          exact this
        · have : ω ∈ A ∩ {ω | I ω = k} := by
            have h' : (ω ∈ A') := h.1
            rw [← h1] at h'
            exact h'
          exact this
      have hle := (hlaw k).2 S hS p hprem (A' ∩ Rk k) (hA'.inter (hRk k)) inter_subset_right
      calc p * P (A ∩ {ω | I ω = k}) = p * P (A' ∩ Rk k) := by rw [measure_congr he'']
        _ ≤ P ((A' ∩ Rk k) ∩ {ω | (yk k ω, samp (Wk k · ω) (fun i t => VLk k i t ω)
              (fun k' t => VRk k k' t ω) (ζk k ω)) ∈ S}) := hle
        _ = P ((A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) ∩
              {ω | I ω = k}) := by
            refine measure_congr ?_
            filter_upwards [he'', hRy k] with ω h1 h2
            by_cases hω : ω ∈ A ∩ {ω | I ω = k}
            · have hω' : ω ∈ A' ∩ Rk k := by
                have h' : (ω ∈ A ∩ {ω | I ω = k}) := hω
                rw [h1] at h'
                exact h'
              have e := hobs k ω (hAR hω.1) hω.2 (h2 (hAR hω.1) hω.2).2
              refine propext ⟨fun h => ⟨⟨hω.1, ?_⟩, hω.2⟩, fun h => ⟨hω', ?_⟩⟩
              · show (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S
                rw [e]; exact h.2
              · show (yk k ω, samp (Wk k · ω) (fun i t => VLk k i t ω) (fun k' t => VRk k k' t ω) (ζk k ω)) ∈ S
                rw [← e]; exact h.1.2
            · have hω' : ω ∉ A' ∩ Rk k := by
                intro h'
                have h'' : (ω ∈ A' ∩ Rk k) := h'
                rw [← h1] at h''
                exact hω h''
              refine propext ⟨fun h => absurd h.1 hω', fun h => absurd ⟨h.1.1, h.2⟩ hω⟩
    calc p * P A = p * ∑' k, P (A ∩ {ω | I ω = k}) := by rw [← @measure_eq_tsum_inter_fiber Ω mΩ K _ P I hI A]
      _ = ∑' k, p * P (A ∩ {ω | I ω = k}) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' k, P ((A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) ∩
            {ω | I ω = k}) := ENNReal.tsum_le_tsum hk
      _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) :=
          (@measure_eq_tsum_inter_fiber Ω mΩ K _ P I hI _).symm

/-- **A stage that is never reached obeys the stage law** (both clauses are vacuous on `R = ∅`); for the candidates
of lists of switching times that the construction never realizes. -/
theorem isStageLaw_of_empty {𝓠 : MeasurableSpace Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    @IsStageLaw κ Ω mΩ P 𝓠 ∅ nL nR ρL ρR y W VL VR B ζ := by
  refine ⟨Eventually.of_forall fun ω hω => absurd hω (notMem_empty ω), fun S _ p _ A _ hA => ?_⟩
  rw [subset_empty_iff.1 hA, empty_inter, measure_empty, mul_zero]

end Mix

end InteractingSLE.Sec5.CrossCond.StagedAdapt
