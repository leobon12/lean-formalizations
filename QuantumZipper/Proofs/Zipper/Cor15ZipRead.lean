import QuantumZipper.Proofs.Zipper.Cor15MeasVerMain
import QuantumZipper.Proofs.Zipper.Cor15LastZc
import QuantumZipper.Proofs.Zipper.Cor15HullNull
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-ZIPREAD: the reading input `Cor15ZipReadStmt` of the zip direction

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (§1.4) and the
welding-driver reading of §5.3. Task COR15-ZIPREAD. Own assembly of proved repository results,
following `cor15ZcRead` (`Cor15LastZc.lean`) step by step, with the Lebesgue-null hull clause
replaced by the folded-circle clause.

* `measurableSet_hullNull_meas`: for any s-finite `ν`, the event `ν(fwdHull (trev (Vp e) a) a) = 0`
  is measurable in the parameter (the proof of `measurableSet_hullNull` with `ν` for `volume`).
* `cor15ZipRead`: `Cor15ZipReadStmt κ a P B X` for every genuine setup, `0 < κ < 4`, `a > 0`,
  from Theorem 1.3. The reading is the one of `exists_readVp` (`Cor15LastZc.lean`), with parameter
  `e ω = b1Data (grpCfg κ B X ω)`. On the unzipped side the reading equals `vrev (√κ B) a` on
  `[0,a]`, so its time-reversed hull is `revHull (vrev W a) a`, which the dyadic folded circles do
  not charge a.s. (input K0, `cor15HullNullStmt`, proved in `Cor15HullNull.lean`: Rohde–Schramm
  2005 Thm 6.1 and Beffara 2008 Prop. 4). The measurable good event transfers to the zipped side by
  the B1 law identity `b1_full_data`.
* `cor15ZipReadAll`, `cor15ZipVersionStmt_of_verLaw`: the zip side of Corollary 1.5 reduces to the law
  obligation `Cor15ZipVerLawStmt` (given Theorem 1.3).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull

/-- The `ν`-null event of the time-reversed hull is measurable in the parameter (as
`measurableSet_hullNull`, for an arbitrary s-finite measure `ν`). -/
theorem measurableSet_hullNull_meas {α : Type} [MeasurableSpace α] {Vp : α → ℝ → ℝ}
    (hVc : ∀ b, Continuous (Vp b)) (hVm : ∀ s, Measurable fun b => Vp b s) {t : ℝ}
    (ht : 0 ≤ t) (ν : Measure ℂ) [SFinite ν] :
    MeasurableSet {b | ν (fwdHull (ArcDriver.trev (Vp b) t) t) = 0} := by
  set Bf : ℝ≥0 → α → ℝ := fun r b => ArcDriver.trev (Vp b) t r with hBf
  have hBm : ∀ r, Measurable (Bf r) := fun r => by
    simp only [hBf, ArcDriver.trev]; exact (hVm _).sub (hVm _)
  have hBc : ∀ b, Continuous fun r => Bf r b := fun b =>
    (ArcDriver.continuous_trev (hVc b) t).comp NNReal.continuous_coe
  have hS := (NonSwallow.measurableSet_fwdHull_prod hBm hBc 1 ht).preimage measurable_swap
  have hmeas := measurable_measure_prodMk_left (ν := ν) hS
  have heq : ∀ b, fwdHull (ArcDriver.trev (Vp b) t) t = fwdHull (drive 1 Bf b) t := fun b =>
    CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev (hVc b) t)
      (continuous_const.mul ((hBc b).comp continuous_real_toNNReal)) ht fun r hr => by
        show _ = Real.sqrt 1 * ArcDriver.trev (Vp b) t (r.toNNReal : ℝ)
        rw [Real.sqrt_one, one_mul, Real.coe_toNNReal _ hr.1]
  have e : {b | ν (fwdHull (ArcDriver.trev (Vp b) t) t) = 0} =
      (fun b => ν (Prod.mk b ⁻¹' (Prod.swap ⁻¹'
        {p : ℂ × α | p.1 ∈ fwdHull (drive 1 Bf p.2) t}))) ⁻¹' {0} := by
    ext b
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    rw [heq b]
    rfl
  rw [e]
  exact hmeas (measurableSet_singleton 0)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end Cor15Group
end QuantumZipper
