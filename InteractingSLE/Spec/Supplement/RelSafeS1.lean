/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeGB6Wire
import InteractingSLE.Spec.Supplement.GB6RestartProofData
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Sec7.Lemma725RefSafeTransfer
import InteractingSLE.Spec.Supplement.GW3Word

/-!
# GB6's relative safe law, part 1: plumbing and the threshold clause

Packet PROVE-GB6-RELSAFE2. `Q3Stop.GB6RelSafeRStatement` asks, for every R-form version of GB6's relative
exploration and every word type, the four clauses of `Q3Stop.HasRelSafe` under the joint law of the record and the
relative variable, conditioned on the record event of the type. This file proves the parts that need no probability:

* **`cond_map_eq_of_eqOn`**: two measurable maps that agree on the preimage of `S` (with the same preimage) have the
  same image law conditioned on `S`; hence (`hasRelSafe_of_eqOn`) the relative variable may be modified off the record
  event (used to make the relative field integrable on the whole space);
* **`hasSafeLaw_congr_fld`**, **`hasSafeMembers_congr_fld`**: K2's (S) and (L) only see the field almost surely on the
  live event;
* **`ae_canonStp_le_thr_gb6`**: the threshold clause — GB6's conditional word is admissible for every record of the
  record event (GB6, proof: "Consequently the entire conditional word is admissible"; PROVE-GB6-RESTART's
  `isGB6AdmData_gb6WordOfRec` with the counterflow's admissibility transported by `gb6_admL`, `gb6_admR`), so every
  side partial sum of its flow-line word exceeds `−2` and the relative continuation threshold is `∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.FCDet Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv
  Supp8.Q3Stop Sec7.PocketTraversal

/-! ### Conditioned image laws of maps that agree on the event -/

section Cond

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {P : Measure Ω}

/-- Two measurable maps with the same preimage of `S`, agreeing on it, have the same image law conditioned on `S`. -/
theorem cond_map_eq_of_eqOn {Φ Φ' : Ω → Y} (hΦ : Measurable Φ) (hΦ' : Measurable Φ') {S : Set Y}
    (hS : MeasurableSet S) (hpre : Φ ⁻¹' S = Φ' ⁻¹' S) (heq : ∀ ω ∈ Φ ⁻¹' S, Φ ω = Φ' ω) :
    (P.map Φ)[|S] = (P.map Φ')[|S] := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_map hΦ hS, Measure.restrict_map hΦ' hS, Measure.map_apply hΦ hS,
    Measure.map_apply hΦ' hS, ← hpre]
  congr 1
  exact Measure.map_congr ((ae_restrict_iff' (hΦ hS)).2 (Eventually.of_forall heq))

/-- **`HasRelSafe` only sees the relative variable on the record event.** -/
theorem hasRelSafe_of_eqOn {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) {Φ Φ' : Ω → Q3Stop.CanonSpace} (hΦ : Measurable Φ) (hΦ' : Measurable Φ')
    (hfst : ∀ ω, (Φ ω).1 = (Φ' ω).1) (heq : ∀ ω, (Φ ω).1 ∈ E → Φ ω = Φ' ω)
    (h : HasRelSafe k w β E (P.map Φ')) : HasRelSafe k w β E (P.map Φ) := by
  have hS := measurableSet_typeEvent (k := k) (w := w) hβ hE
  have hpre : Φ ⁻¹' typeEvent k w β E = Φ' ⁻¹' typeEvent k w β E := by
    ext ω
    simp only [typeEvent, Set.mem_preimage, hfst]
  have e := cond_map_eq_of_eqOn (P := P) hΦ hΦ' hS hpre fun ω hω => heq ω hω.1
  unfold HasRelSafe
  rw [e]
  exact h

end Cond

/-! ### (S) and (L) only see the field on the live event -/

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {X X' : Ω → DistOn upperHalfPlaneOpens}

theorem hasSafeLaw_congr_fld (hX : ∀ᵐ ω ∂P, ω ∈ F → X ω = X' ω)
    (h : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X' := by
  intro ψ q D hD hDs
  rw [← h ψ q D hD hDs]
  refine setIntegral_congr_ae (𝓗.le q D hD) ?_
  filter_upwards [hX, hDs] with ω h1 h2 hωD
  rw [h1 (h2 hωD).1]

theorem hasSafeMembers_congr_fld (hX : ∀ᵐ ω ∂P, ω ∈ F → X ω = X' ω)
    (h : HasSafeMembers P 𝓗 F ζ W X) : HasSafeMembers P 𝓗 F ζ W X' := by
  intro s Fb hFb D hD hDs f Ξ
  have hDm : MeasurableSet D := 𝓗.le s D hD
  have e : ∀ φ : TestOn upperHalfPlaneOpens, ∫ ω in D, Complex.exp (Complex.I * (X' ω φ : ℂ)) ∂P =
      ∫ ω in D, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂P := fun φ => by
    refine setIntegral_congr_ae hDm ?_
    filter_upwards [hX, hDs] with ω h1 h2 hωD
    rw [h1 (h2 hωD).1]
  rw [e, e]
  exact h s Fb hFb D hD hDs f Ξ

end Congr

/-! ### The threshold clause -/

section Threshold

/-- **GB6's conditional word has all side partial sums above `−2`** for every record of the record event (its data
form `IsGB6AdmData`, with `bigLambda κ = λ(16/κ)`). -/
theorem partialSums_gb6WordOfRec {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ)
    (hθ₂ : θ ≤ Real.pi / 2) (c : BoundaryWord) {s : ℝ≥0} {r : RecData} (hr : r ∈ gb6TS s) (E : Finset ℝ)
    (hcL : ∀ u, u < 0 → u ∉ E → u ∉ c.jumps → -bigLambda κ < -c.fn u + Real.pi * chiC κ)
    (hcR : ∀ u, 0 < u → u ∉ E → u ∉ c.jumps → -c.fn u - Real.pi * chiC κ < bigLambda κ) :
    (∀ i : Fin (flowLineNL (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i),
        flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0 l) ∧
    ∀ j : Fin (flowLineNR (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ j),
        flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0 l := by
  obtain ⟨-, hadm, -⟩ := gb6_word_of_mem hκ hκ4 hθ₁ hθ₂ c hr E hcL hcR
  have hk : 0 < 16 / κ := by positivity
  have hpc := (gb6WordOfRec κ θ c r).isPiecewiseConstantBoundaryData
  exact ⟨fun i => Theorem14.GW3Word.neg_two_lt_sum_flowLineRhoL_of_forall hk hpc (fun y hy hyJ => hadm.2 y hy hyJ) i,
    fun j => Theorem14.GW3Word.neg_two_lt_sum_flowLineRhoR_of_forall hk hpc (fun y hy hyJ => hadm.1 y hy hyJ) j⟩

/-- **The stop precedes the relative continuation threshold** (GB6): for every law on the canonical relative space and
every word type, the relative threshold of GB6's conditional word is `∞` on the type event of the record event. -/
theorem ae_canonStp_le_thr_gb6 {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ)
    (hθ₂ : θ ≤ Real.pi / 2) (c : BoundaryWord) (s : ℝ≥0) (E : Finset ℝ)
    (hcL : ∀ u, u < 0 → u ∉ E → u ∉ c.jumps → -bigLambda κ < -c.fn u + Real.pi * chiC κ)
    (hcR : ∀ u, 0 < u → u ∉ E → u ∉ c.jumps → -c.fn u - Real.pi * chiC κ < bigLambda κ)
    (μ : Measure Q3Stop.CanonSpace) (w : WordType) :
    ∀ᵐ y ∂(μ[|typeEvent (16 / κ) w (gb6WordOfRec κ θ c) (gb6TS s)]), canonStp y ≤
      thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL (16 / κ) w (gb6WordOfRec κ θ c y.1))
        (fun y => typedXR (16 / κ) w (gb6WordOfRec κ θ c y.1)) y := by
  by_cases hw : ∃ r ∈ gb6TS s, wordType (16 / κ) (gb6WordOfRec κ θ c r) = w
  · obtain ⟨r, hr, rfl⟩ := hw
    obtain ⟨hsL, hsR⟩ := partialSums_gb6WordOfRec hκ hκ4 hθ₁ hθ₂ c hr E hcL hcR
    refine Eventually.of_forall fun y => ?_
    have hsL' : ∀ m : Fin (wordType (16 / κ) (gb6WordOfRec κ θ c r)).1, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m),
        typedRhoL (wordType (16 / κ) (gb6WordOfRec κ θ c r)) i := fun m => by
      have e : ∀ i, typedRhoL (wordType (16 / κ) (gb6WordOfRec κ θ c r)) i =
          flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0 i := fun i =>
        padFL_snd_fst_fin _ _ _ _ i
      simp only [e]
      exact hsL m
    have hsR' : ∀ m : Fin (wordType (16 / κ) (gb6WordOfRec κ θ c r)).2.1, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m),
        typedRhoR (wordType (16 / κ) (gb6WordOfRec κ θ c r)) i := fun m => by
      have e : ∀ i, typedRhoR (wordType (16 / κ) (gb6WordOfRec κ θ c r)) i =
          flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0 i := fun i =>
        padFL_snd_snd_fin _ _ _ _ i
      simp only [e]
      exact hsR m
    unfold thr
    rw [Sec7.Lemma725RefSafe.thresholdTime_eq_top_of_partialSums hsL' hsR'
      (fun t i => geomLW_le continuous_canonDrv _ y t i)
      (fun t => antitone_index_geomLW continuous_canonDrv (antitone_typedXL _ _ _) t)
      (fun t j => le_geomRW continuous_canonDrv _ y t j)
      (fun t => monotone_index_geomRW continuous_canonDrv (monotone_typedXR _ _ _) t)]
    exact le_top
  · have hS : typeEvent (16 / κ) w (gb6WordOfRec κ θ c) (gb6TS s) = ∅ := by
      ext y
      simp only [typeEvent, Set.mem_preimage, mem_inter_iff, Set.mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hw ⟨_, h.1, h.2⟩
    rw [hS, ProbabilityTheory.cond_empty]
    exact ae_zero.symm ▸ Filter.eventually_bot

end Threshold

end InteractingSLE.Supp8.RelSafeS
