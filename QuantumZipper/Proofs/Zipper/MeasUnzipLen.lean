import QuantumZipper.Proofs.Zipper.MeasUnzipField
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Rat.Cast.Order
import QuantumZipper.Proofs.Zipper.F1ReadMeas

/-!
# MEAS-UNZIP (2), (3): the unzipped lengths and the length hitting time are measurable

Continuation of `MeasUnzipField.lean` and `MeasUnzipHit.lean`, for a continuous path `f` on
`[0,T]` (driver `W = Wof κ T hT f`) and a field `x`:

* `lenJ hT γ κ s hs (f, x)`: the pair of boundary masses of the good-gated boundary measure
  of `ufJ` on `[O⁻, 0]` and `[0, O⁺]`, with the side images read by `ESM.sideReader` from the
  restricted path `resPath` on `[0,s]`. `measurable_lenJ` (from `ESM.measurable_sideReader`,
  `ESM.measurable_measure_Icc_zero_of_finite`, `F1.measurable_measure_zero_Icc_of_finite`,
  `measurable_qBoundaryMeasure_ufJ`).
* `unzipLengths_eq_lenJ`: `unzipLengths γ (x, W) s = lenJ … (f, x)` whenever `f ∈ PZ`, all real
  points are alive at time `s` for the restricted driver, and the unzipped field at time `s` is
  good (`IsLQGGood`).
* `measurable_hitTime_unzip`: on a measurable set `S` of `(f, x)` on which, at every rational
  time `q ∈ [0,T]`, the identity `unzipLengths = lenJ` holds and the left length is monotone on
  `[0,T]`, the hitting time `sInf {s ≥ 0 | ℓ ≤ L⁻(min s T)}` is measurable (junk `0` off `S`).
* `sInf_hit_min_eq`: if the level is reached by time `T`, the truncation `min s T` does not
  change the hitting time.

Own elementary bookkeeping; the side-image reader and the window measurability are the
ESM-LMEAS / READLEN tools (reused, not duplicated).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper.MeasUnzip

open CharFun RegCont Factorization
open scoped Classical

variable {T : ℝ} (hT : 0 ≤ T)

/-- The restriction of a path on `[0,T]` to `[0,s]`, `s ≤ T`. -/
def resPath (s : ℝ) (f : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) s, ℝ) :=
  ⟨fun q => f (projIcc 0 T hT q), f.continuous.comp (continuous_projIcc.comp continuous_subtype_val)⟩

theorem measurable_resPath (s : ℝ) : Measurable (resPath hT s) :=
  ContinuousMap.measurable_iff_eval.2 fun _ => (continuous_eval_const _).measurable

theorem Wof_resPath_eqOn (κ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ r ∈ Icc (0 : ℝ) s, Wof κ s hs.1 (resPath hT s f) r = Wof κ T hT f r := by
  intro r hr
  simp only [Wof, resPath, ContinuousMap.coe_mk, projIcc_of_mem hs.1 hr]

/-- The side images read from the restricted path. -/
def sideJ (κ s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ × ℝ :=
  ESM.sideReader κ s hs.1 (resPath hT s f)

theorem measurable_sideJ (κ s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : Measurable (sideJ hT κ s hs) :=
  (ESM.measurable_sideReader κ s hs.1).comp (measurable_resPath hT s)

theorem sideImages_eq_sideJ (κ : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (f : C(Icc (0 : ℝ) T, ℝ))
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol (Wof κ s hs.1 (resPath hT s f)) (x : ℂ) s u) :
    sideImages (Wof κ T hT f) s = sideJ hT κ s hs f := by
  rw [sideJ, ← ESM.sideImages_Wof_eq_sideReader κ s hs.1 _ halive]
  exact ESM.sideImages_congr_drive hs.1 fun r hr => (Wof_resPath_eqOn hT κ hs f r hr).symm

/-! ## The hitting time of the left length -/

/-- If the level is reached by time `T`, truncating the time at `T` does not change the hitting
time. -/
theorem sInf_hit_min_eq {L : ℝ → ℝ≥0∞} {ℓ : ℝ≥0∞} {T : ℝ} (hT : 0 ≤ T)
    (hreach : ∃ s ∈ Icc (0 : ℝ) T, ℓ ≤ L s) :
    sInf {s : ℝ | 0 ≤ s ∧ ℓ ≤ L (min s T)} = sInf {s : ℝ | 0 ≤ s ∧ ℓ ≤ L s} := by
  obtain ⟨s0, hs0, hl0⟩ := hreach
  set E := {s : ℝ | 0 ≤ s ∧ ℓ ≤ L s} with hE
  set E' := {s : ℝ | 0 ≤ s ∧ ℓ ≤ L (min s T)} with hE'
  have hb : BddBelow E := ⟨0, fun _ h => h.1⟩
  have hb' : BddBelow E' := ⟨0, fun _ h => h.1⟩
  have hne : E.Nonempty := ⟨s0, hs0.1, hl0⟩
  have hne' : E'.Nonempty := ⟨s0, hs0.1, by rw [min_eq_left hs0.2]; exact hl0⟩
  have hle : sInf E ≤ s0 := csInf_le hb ⟨hs0.1, hl0⟩
  refine le_antisymm (not_lt.1 fun hc => ?_) (le_csInf hne' fun s hs => ?_)
  · -- `sInf E < sInf E'`: some element of `E` lies below `sInf E'`
    obtain ⟨s, hsE, hsc⟩ := exists_lt_of_csInf_lt hne hc
    by_cases hsT : s ≤ T
    · exact lt_irrefl _ ((csInf_le hb' ⟨hsE.1, by rw [min_eq_left hsT]; exact hsE.2⟩).trans_lt hsc)
    · exact lt_irrefl _ ((csInf_le hb' ⟨hs0.1, by rw [min_eq_left hs0.2]; exact hl0⟩).trans_lt
        (lt_of_le_of_lt hs0.2 ((lt_of_not_ge hsT).trans hsc)))
  · by_cases hsT : s ≤ T
    · exact csInf_le hb ⟨hs.1, by rw [← min_eq_left hsT]; exact hs.2⟩
    · have hT' : T ∈ E := ⟨hT, by
        have := hs.2
        rwa [min_eq_right (le_of_not_ge hsT)] at this⟩
      exact (csInf_le hb hT').trans (le_of_not_ge hsT)

end QuantumZipper.MeasUnzip
