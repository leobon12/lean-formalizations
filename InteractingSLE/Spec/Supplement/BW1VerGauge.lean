/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerCoord
import InteractingSLE.Spec.Supplement.GW4FixGauge

/-!
# The separation readout of relative coordinates, the retained time read from the record

Packet PROVE-BW1-INPUTS2. For the coordinates of `exists_coord` (good samples on a measurable set `M` of a record
event `TS`), GB6's separation gauge at the record's own time, switched off (constant `1`) on records outside `TS`
(`tsRead TS`), is an almost-sure causal readout (`SourceC.AESeparationReadout`) of the coordinates
(`exists_aeSeparationReadout_tsRead`). With GW4-FIX's any-record version lemmas this gives announced path-rule
versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC

open Classical in
/-- GB6's separation gauge at the record's own time on records of `TS`, the constant `1` on other records. -/
def tsRead (TS : Set RecData) : GaugeReadout := fun t p => if p.1 ∈ TS then bwRead t p else 1

theorem measurable_tsRead {TS : Set RecData} (hTS : MeasurableSet TS) (t : ℝ≥0) : Measurable (tsRead TS t) := by
  classical
  unfold tsRead
  exact Measurable.ite (measurable_fst hTS) (measurable_bwRead t) measurable_const

theorem isCausal_tsRead (TS : Set RecData) : IsCausal (tsRead TS) := by
  intro t r w w' h
  unfold tsRead
  split_ifs
  · exact isCausal_bwRead t r w w' h
  · rfl

/-- On a good sample with coordinates, the gauge is GB6's separation gauge at the record's own time. -/
theorem bwRead_eq_of_good {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hg : IsGoodSample r A w γ) (t : ℝ≥0) (x : ℝ≥0 → ℝ) :
    bwRead t (r, x) = separationRead (recS r) t (r, x) := by
  refine bwRead_eq_separationRead ((hg.continuous_A.continuousOn).congr fun v _ => hg.recordTrace_eq v) ?_ t x
  rw [hg.recordTrace_eq]
  exact hg.trace.1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The almost-sure separation readout of record-time coordinates.** -/
theorem exists_aeSeparationReadout_tsRead {rec : Ω → RecData} (hrec : Measurable rec) {TS : Set RecData}
    (hTS : MeasurableSet TS) {Wd : ℝ≥0 → Ω → ℝ} {Γ A : Ω → ℝ≥0 → ℂ} {M : Set Ω} (hM : MeasurableSet M)
    (hMTS : ∀ ω ∈ M, rec ω ∈ TS) (hae : ∀ᵐ ω ∂P, rec ω ∈ TS → ω ∈ M)
    (hgood : ∀ ω ∈ M, IsGoodSample (rec ω) (A ω) (Wd · ω) (Γ ω)) {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hDm : ∀ t, Measurable (D t)) (hLm : Measurable L) (hD0 : ∀ ω, D 0 ω = 0) (hoff : ∀ ω ∉ M, L ω = ⊤)
    (hcoord : ∀ ω ∈ M, IsSampleCoord (rec ω) (A ω) (Wd · ω) (Γ ω) (D · ω) (L ω)) :
    ∃ g : ℝ≥0 → Ω → ℝ, AESeparationReadout P rec D L g (tsRead TS) := by
  classical
  have hread : ∀ ω ∈ M, ∀ t, tsRead TS t (rec ω, fun u => D u ω) =
      separationRead (recS (rec ω)) t (rec ω, fun u => D u ω) := by
    intro ω hω t
    simp only [tsRead, hMTS ω hω, ↓reduceIte]
    exact bwRead_eq_of_good (hgood ω hω) t _
  have hsam := fun ω (hω : ω ∈ M) => sample_readout (hgood ω hω) (hcoord ω hω)
  have h0L : ∀ ω ∈ M, ((0 : ℝ≥0) : ℝ≥0∞) < L ω := fun ω hω => by
    rw [ENNReal.coe_zero]; exact (hcoord ω hω).pos
  refine ⟨fun t ω => if ω ∈ M then (if (t : ℝ≥0∞) < L ω then tsRead TS t (rec ω, fun u => D u ω) else 0) else 1,
    ⟨fun t => ?_, fun ω => ?_, fun ω => ?_, fun ω t ht => ?_, fun ω t ht => ?_, measurable_tsRead hTS,
      isCausal_tsRead TS, ?_⟩⟩
  · exact Measurable.ite hM (Measurable.ite (measurableSet_lt measurable_const hLm)
      ((measurable_tsRead hTS t).comp (hrec.prodMk (measurable_pi_iff.2 hDm))) measurable_const) measurable_const
  · by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte]
      obtain ⟨-, -, -, -, -, hc, -, hT⟩ := hsam ω hω
      exact continuous_glue (hc.congr fun t _ => hread ω hω t)
        fun T hT' => (hT T hT').congr fun t => (hread ω hω t).symm
    · simp only [hω, ↓reduceIte]
      exact continuous_const
  · by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte, h0L ω hω, hread ω hω]
      exact (hsam ω hω).2.2.2.2.2.2.1 0 (h0L ω hω)
    · simp only [hω, ↓reduceIte]
      exact one_pos
  · by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte, ht, hread ω hω]
      exact (hsam ω hω).2.2.2.2.2.2.1 t ht
    · simp only [hω, ↓reduceIte]
      exact one_pos
  · by_cases hω : ω ∈ M
    · have ht' : ¬ (t : ℝ≥0∞) < L ω := by rw [ht]; exact lt_irrefl _
      simp only [hω, ↓reduceIte, ht']
    · rw [hoff ω hω] at ht
      exact absurd ht ENNReal.coe_ne_top
  · filter_upwards [hae] with ω hω
    by_cases hωM : ω ∈ M
    · refine ⟨?_, fun t ht => ?_⟩
      · simp only [hωM, ↓reduceIte, h0L ω hωM]
        exact isCausal_tsRead TS 0 (rec ω) _ _ fun u hu => by rw [nonpos_iff_eq_zero.1 hu, hD0 ω]
      · simp only [hωM, ↓reduceIte, ht]
    · have hnot : rec ω ∉ TS := fun h => hωM (hω h)
      simp only [hωM, ↓reduceIte, tsRead, hnot, implies_true, and_self]

end InteractingSLE.Theorem14.BW1Ver
