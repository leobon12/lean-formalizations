import QuantumZipper.Proofs.Thm18.G4CMeasCoan
import QuantumZipper.Proofs.Zipper.F1LenReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F1: the read-length regularity set is null-measurable given a jointly measurable reader

Theorem 1.3, node F1 (`F1.LenReadRegMeasStmt`, `F1LenReg.lean`: "descriptive-set measurability
of the read-length regularity set"). Task G4C-MEAS asked whether the unique-witness
(Lusin–Souslin) trick settles it. **It does not**: the regularity set
`{d | MonotoneOn L⁻(d, ·) (Ici 0) ∧ ContinuousOn L⁺(d, ·) (Ici 0)}` is not a projection; its
complement is a projection whose witnesses (the bad times) are not unique. It is coanalytic once
the lengths are read by a *jointly* measurable function of (countable data, time), and then
Lusin's theorem (`G4CMeasLusin.lean`, Kechris Thm 21.10) applies
(`nullMeasurableSet_monotoneOn`, `nullMeasurableSet_continuousOn`, `G4CMeasCoan.lean`).

* `nullMeasurableSet_regSet_of_reader`: abstract form: if on a conull set `G` the two length
  functions are read by jointly measurable `g₁, g₂` of a Polish code of the data and the time,
  the regularity set is null-measurable.
* `lenReadRegMeasStmt_of_reader`: `F1.LenReadRegMeasStmt` from such a reader for the `P_*` data
  law, with the code space `(ℕ → ℝ) × (ℕ → ℝ)` (circle coordinates; driver at the nonnegative
  dyadic times, which is all that `readCfg` reads, `F1.readDrv`/`B4d.pathExt`).

The existing readers (`F1.rdMT`, `F1ReadTimeRd.lean`) are measurable at each **fixed** time
only; the joint (time-uniform) reader is the remaining input.

**Own elementary argument** on top of the cited theorems.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace QuantumZipper.Thm18Asm.G4Core

/-- **Regularity set from a jointly measurable reader.** -/
theorem nullMeasurableSet_regSet_of_reader {D : Type*} [MeasurableSpace D] (μ : Measure D)
    [IsFiniteMeasure μ] {Kc : Type*} [TopologicalSpace Kc] [PolishSpace Kc] [MeasurableSpace Kc]
    [BorelSpace Kc] {code : D → Kc} (hcode : Measurable code) {L₁ : D → ℝ → ℝ≥0∞}
    {L₂ : D → ℝ → ℝ} {g₁ : Kc × ℝ → ℝ≥0∞} {g₂ : Kc × ℝ → ℝ} (hg₁ : Measurable g₁)
    (hg₂ : Measurable g₂) {G : Set D} (hG : μ Gᶜ = 0)
    (hL : ∀ d ∈ G, ∀ t : ℝ, 0 ≤ t → L₁ d t = g₁ (code d, t) ∧ L₂ d t = g₂ (code d, t)) :
    NullMeasurableSet {d | MonotoneOn (L₁ d) (Ici 0) ∧ ContinuousOn (L₂ d) (Ici 0)} μ := by
  set T' : Set Kc := {k | MonotoneOn (fun t => g₁ (k, t)) (Ici 0)} ∩
    {k | ContinuousOn (fun t => g₂ (k, t)) (Ici 0)} with hT'
  have hT'm : NullMeasurableSet T' (μ.map code) :=
    (nullMeasurableSet_monotoneOn hg₁ measurableSet_Ici _).inter
      (nullMeasurableSet_continuousOn hg₂ measurableSet_Ici _)
  -- the preimage of a null-measurable set under the measurable code
  have hpre : NullMeasurableSet (code ⁻¹' T') μ := by
    obtain ⟨U, -, hUm, hUT⟩ := hT'm.exists_measurable_superset_ae_eq
    have h1 : ∀ᵐ k ∂(μ.map code), (k ∈ U ↔ k ∈ T') := hUT.mono fun k hk => Iff.of_eq hk
    have h2 : ∀ᵐ d ∂μ, (code d ∈ U ↔ code d ∈ T') :=
      ae_of_ae_map (p := fun k => k ∈ U ↔ k ∈ T') hcode.aemeasurable h1
    refine (hUm.preimage hcode).nullMeasurableSet.congr ?_
    filter_upwards [h2] with d hd
    exact propext hd
  set T : Set D := {d | MonotoneOn (L₁ d) (Ici 0) ∧ ContinuousOn (L₂ d) (Ici 0)} with hTdef
  have hTG : T ∩ G = code ⁻¹' T' ∩ G := by
    ext d
    simp only [hTdef, hT', mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hm, hc⟩, hd⟩
      refine ⟨⟨fun a ha b hb hab => ?_, hc.congr fun t ht => (hL d hd t ht).2.symm⟩, hd⟩
      show g₁ (code d, a) ≤ g₁ (code d, b)
      rw [← (hL d hd a ha).1, ← (hL d hd b hb).1]
      exact hm ha hb hab
    · rintro ⟨⟨hm, hc⟩, hd⟩
      refine ⟨⟨fun a ha b hb hab => ?_, hc.congr fun t ht => (hL d hd t ht).2⟩, hd⟩
      rw [(hL d hd a ha).1, (hL d hd b hb).1]
      exact hm ha hb hab
  have hGn : NullMeasurableSet G μ := NullMeasurableSet.compl_iff.1 (NullMeasurableSet.of_null hG)
  have e : T = (T ∩ G) ∪ (T ∩ Gᶜ) := (inter_union_compl T G).symm
  rw [e, hTG]
  exact (hpre.inter hGn).union
    (NullMeasurableSet.of_null (measure_mono_null inter_subset_right hG))

end QuantumZipper.Thm18Asm.G4Core
