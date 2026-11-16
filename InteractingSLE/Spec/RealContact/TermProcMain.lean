/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermProcObs

/-!
# The processes of the first path against the completed second path: the driver and its filtration

Packet PROVE-RC-TERM, second run (ruling R124). Items 2–3 of `RLC.OrdModel.AStopSourceInputs` for the chart path
`Term.pPath` with the physical stop `Term.pStop` (template: `RLC.AStopProc.exists_fstProc`):

* `aLife_pPath`, `aPath_pPath`: the capacity lifetime and the chart path in capacity time are `Term.kLife` and
  `Term.kTrace` of the sample;
* `pSeed`, `pWord`, `pEnds`: the seed position, the stop word and the stop set of the record at own time `N`, with
  their measurability for the record;
* **`exists_termProc`**: on a `retSigma76 … 0 N` event `M` of good samples there are the capacity-time filtration
  `aFilt` of the physical filtration, a continuous adapted driver from `0`, the lifetime as a stopping time and the
  measurable continuous trace, with the driver generating the chart path at every sample of `M`.

R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc
open Exist.StagedLaw (markPos markPosL)

section Defs

variable {Ω : Type*}

/-- The seed position of the record at own time `N`. -/
def pSeed (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) : ℝ :=
  markPos (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂)

/-- The stop word of the record at own time `N`. -/
def pWord (κ θ₂ : ℝ) (c : BoundaryWord) (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : BoundaryWord :=
  stopWord κ (c, θ₂, pRec N E ω)

/-- The stop set of the record at own time `N`. -/
def pEnds (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) : RLC.OrdModel.Ends :=
  kEnds (pU N E ω) (pT N E ω : ℝ) (x₁ - x₂)

theorem pSeed_eq (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (x₁ x₂ : ℝ) (ω : Ω) :
    pSeed N E x₁ x₂ ω = termSeed x₁ x₂ (pRec N E ω) := rfl

theorem pWord_eq (κ θ₂ : ℝ) (c : BoundaryWord) (N : ℝ≥0) (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    pWord κ θ₂ c N E ω = termWord κ θ₂ c (pRec N E ω) := rfl

variable {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηc₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

/-- The capacity lifetime of the chart path is `Term.kLife` of the sample. -/
theorem aLife_pPath (ω : Ω) : aLife (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω =
    kLife (pU N E ω) (pRho₂ ηc₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω) := rfl

/-- The chart path in capacity time is `Term.kTrace` of the sample. -/
theorem aPath_pPath (ω : Ω) (q : ℝ≥0) : aPath (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω q =
    kTrace (pU N E ω) (pRho₂ ηc₂ x₂ ω) (pT N E ω) (x₁ - x₂) (pRho₁ η₁' x₁ ω) (ζ₁ ω) q := rfl

end Defs

/-! ### Measurability for the record -/

theorem measurable_markPos_rec (x : ℝ) : Measurable fun r : RecData => markPos (rdrv r) (rtime r) x :=
  measurable_markPos continuous_rdrv measurable_rdrv_apply rdrv_zero measurable_rtime rtime_nonneg
    measurable_const

theorem measurable_kEnds_rec (d : ℝ) : Measurable fun r : RecData => kEnds (rdrv r) (rtime r) d := by
  have h0 := measurable_markPos_rec 0
  have hd := measurable_markPos_rec d
  exact (hd.neg).prodMk ((h0.sub hd).prodMk ((hd.neg).prodMk (h0.sub hd)))

section Meas

variable {Ω : Type u} {m : MeasurableSpace Ω} {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem measurable_pSeed (hr : Measurable[m] (pRec N E)) (x₁ x₂ : ℝ) : Measurable[m] (pSeed N E x₁ x₂) :=
  (measurable_markPos_rec (x₁ - x₂)).comp hr

theorem measurable_pWord (hr : Measurable[m] (pRec N E)) (κ θ₂ : ℝ) (c : BoundaryWord) :
    Measurable[m] (pWord κ θ₂ c N E) :=
  (measurable_stopWord κ).comp (measurable_const.prodMk (measurable_const.prodMk hr))

theorem measurable_pEnds (hr : Measurable[m] (pRec N E)) (x₁ x₂ : ℝ) : Measurable[m] (pEnds N E x₁ x₂) :=
  (measurable_kEnds_rec (x₁ - x₂)).comp hr

end Meas

/-! ### The processes -/

section Proc

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

omit [IsProbabilityMeasure P] in
/-- **Items 2–3 of `AStopSourceInputs` for the first path against the completed second path** (see the module
docstring). -/
theorem exists_termProc {N : ℝ≥0} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ηc₂ η₁' : Ω → ℝ≥0 → ℂ} {M : Set Ω}
    (ho : AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂)
      (pStop N E ηc₂ η₁' ζ₁ x₁ x₂))
    (hMg : ∀ ω ∈ M, IsTermGood N E ηc₂ η₁' ζ₁ x₁ x₂ ω) :
    ∃ (hQa : ∀ t, Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N t]
        (M.indicator (aClock (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) t))) (W : ℝ≥0 → Ω → ℝ),
      retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N ≤
        aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) hQa 0 ∧
      (∀ ω, Continuous (W · ω)) ∧ (∀ ω, W 0 ω = 0) ∧
      StronglyAdapted (aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) hQa) W ∧
      (∀ t : ℝ≥0, MeasurableSet[aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N) M
          (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) hQa t]
        {ω | M.indicator (aLife (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂)) ω ≤ t}) ∧
      (∀ t, Measurable fun ω =>
        aTrace M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω t) ∧
      (∀ ω, ContinuousOn (aTrace M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω)
        {t | (t : ℝ≥0∞) ≤
          M.indicator (aLife (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂)) ω}) ∧
      (∀ ω, aTrace M (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω 0 = 0) ∧
      ∀ ω ∈ M, IsGeneratingTrace (W · ω)
        (aLife (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω)
        (aPath (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω) := by
  have hg : ∀ ω ∈ M, IsAGood (pPath N E ηc₂ η₁' ζ₁ x₁ x₂) (pStop N E ηc₂ η₁' ζ₁ x₁ x₂) ω := fun ω hω =>
    (hMg ω hω).isAGood
  obtain ⟨W, hWc, hW0, hWa, -, hV, hgen⟩ := ho.exists_driver hg
  refine ⟨ho.measurable_clock hg, W, ?_, hWc, hW0, hWa, hV, ho.measurable_aTrace hg, continuousOn_aTrace hg,
    aTrace_zero hg, fun ω hω => ?_⟩
  · have h0 : fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ 0 N 0 = retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N := by
      rw [fstPhysFiltration_apply, add_zero]
    exact h0 ▸ le_aFilt_zero (ho.measurable_clock hg)
  · have h := hgen ω hω
    rwa [indicator_of_mem hω, aTrace_of_mem hω] at h

end Proc

end Term

end InteractingSLE.RealContact
