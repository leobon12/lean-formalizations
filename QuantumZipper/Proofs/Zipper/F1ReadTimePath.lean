import QuantumZipper.Proofs.Zipper.F1ReadTimeRd
import QuantumZipper.Proofs.Zipper.F1ReadMeasAlive

/-!
# READLEN at a fixed time: the dyadic read-off of `√κ B` is a.s. good at all times

Theorem 1.3, node F1 (`F1.LenReadTimeStmt`): the path part of the input, at all times at once.
**`ae_pathGoodAll`**: for `0 < κ ≤ 4` and a Brownian motion `B`, for the law `ν` of `√κ B` on
`ℝ≥0 → ℝ` (product σ-algebra), `ν`-a.s. the read-off `readDrv p` carries the continuity
certificate `DyUC`, starts at `0`, and keeps every real `x ≠ 0` alive at *every* time `T ≥ 0`
(`PathGoodAll`).

The argument is that of `readPathGoodStmt_holds` (time `1`): run `RS.ae_real_alive` on the
canonical space `(ℝ≥0 → ℝ, ν)` for the canonical process `canB κ t p = readDrv p t / √κ`
(`isBrownianReal_canB`), which keeps the `∀ T` of `RS.ae_real_alive` (`RS.RealAlive`), so nothing
has to be redone for each time. Own bookkeeping; the mathematics is Rohde–Schramm, *Basic
properties of SLE*, Lemma 6.2 / Theorem 6.1 (real points are never swallowed for `κ ≤ 4`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

/-- **The path law of `√κ B` is a.s. good at all times** (`PathGoodAll`): the continuity
certificate `DyUC`, the read-off starting at `0`, and every real `x ≠ 0` alive at every time
`T ≥ 0`. -/
theorem ae_pathGoodAll {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), PathGoodAll p := by
  have hφ : AEMeasurable (fun ω => drivePath κ (pathOf B ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  have hB' := isBrownianReal_canB hκ hB
  have hUC : ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), DyUC p := by
    refine (ae_map_iff hφ measurableSet_dyUC).2 ?_
    filter_upwards [hB.cont] with ω hc
    refine dyUC_of_continuous ?_
    rw [← drive_nnreal]; exact (continuous_drive_of κ hc).comp NNReal.continuous_coe
  have h0 : ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), p 0 = 0 := by
    refine (ae_map_iff hφ (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)).2 ?_
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    simp only [drivePath, pathOf, h, mul_zero]
  filter_upwards [hUC, h0, RS.ae_real_alive hB' hκ hκ4] with p hp hp0 halive
  refine ⟨hp, by rw [readDrv_zero, hp0], fun x hx T hT => ?_⟩
  obtain ⟨v, hv⟩ := halive x hx T hT
  refine ⟨v, isForwardSol_congr_drive (fun r hr => ?_) hv⟩
  classical
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  simp only [drive, canB, hp, ↓reduceIte, Real.coe_toNNReal _ hr.1]
  field_simp

end F1
end QuantumZipper
