import QuantumZipper.Proofs.LQG.WedgeBdryInfB3
import QuantumZipper.Proofs.LQG.WedgeBdryInfA

/-!
# WEDGE-BDRY 4 (b), final: clause 3 of `S5.WedgeBoundaryRegularStmt` with item 4 (a) discharged

`WedgeBdry.wedgeBdryFreeInfStmt_holds` (file `WedgeBdryInfA`, the other worker's item 4 (a))
proves the free-field weighted infinite-mass statement, so the results of `WedgeBdryInfB3` hold
unconditionally modulo the two handoff conditions (R23 (b): a.s. `0 < scaleParam` for the
reference field, and the a.e.-measurability of the two full-coordinate maps). Clauses 1–2 of the
statement come from `ae_atomless_pos_of_isQuantumWedge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper

namespace WedgeBdry

/-- **`S5.WedgeBoundaryRegularStmt γ γ`** from the two handoff conditions (R23 (b) and the
a.e.-measurability of the full-coordinate maps). -/
theorem wedgeBoundaryRegularStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hYm : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : Ω → FieldSample), IsQuantumWedge γ γ Y P →
      AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
        fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P)
    (href : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
      IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      AEMeasurable (fun ω => (CoordsFull.coordsFull
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))),
        fun ρ : TestFun H => pairRaw
          (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ρ.1)) P') :
    S5.WedgeBoundaryRegularStmt γ γ :=
  wedgeBoundaryRegularStmt_of_freeInf wedgeBdryFreeInfStmt_holds hγ hγ2 hYm href

end WedgeBdry

end QuantumZipper
