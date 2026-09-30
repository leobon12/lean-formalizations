import QuantumZipper.Proofs.Thm18.ASepPathDefs
import QuantumZipper.Proofs.Zipper.WedgeShiftInt
import QuantumZipper.Proofs.LQG.WedgeCanonical2
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.Thm18.G4PushReg2Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (item 2, step 1): the wedge sample as free field plus a radial profile

* `g4SepConcl0_congr_avgReg`: the `τ' = 0` conclusion depends on the field only through its
  dyadic averages `avgReg` (as `G4Core.g4SepConcl_congr_avgReg`);
* `ae_avgReg_wedgeField_eq`: a.s. the wedge field `wedgeField (lateralPart X) A Q` has the dyadic
  averages of `ofFun (wedgeProfile X A Q) + X` (the raw values agree on every dyadic circle:
  `WedgeCan.wedgeField_eq_evalReg_add_ofFun`, and `X` is exact at the countably many dyadic circles,
  `AllOffsets.ae_evalReg_fc_eq`);
* `ae_concl0_wedgeRep_iff`: hence a.s., for every driver,
  `G4SepConcl0 γ (wedgeRep γ X A ω', W) ↔ G4SepConcl0 γ (rescale (ofFun prof + X ω') Q s, W)`
  with `s = scaleParam γ (wedgeField …)` the canonical scale and `prof` the wedge profile.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- The `τ' = 0` conclusion only reads the dyadic averages of the field. -/
theorem g4SepConcl0_congr_avgReg {γ : ℝ} {y y' : FieldSample} (h : avgReg y = avgReg y')
    (W : ℝ → ℝ) : G4SepConcl0 γ (y, W) ↔ G4SepConcl0 γ (y', W) := by
  have e : ∀ τ, unzippedField γ (y, W) τ = unzippedField γ (y', W) τ := fun τ =>
    Factorization.coordChange_congr h _ _
  simp only [G4SepConcl0, BackSupportI, BackSepI, e]

/-- A free field is a.s. exact at every dyadic folded circle. -/
theorem ae_evalReg_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ (n k : ℕ) (z : ℂ),
      evalReg (X ω) (foldedCircle (dyadicRoundC n z) (radius k)) =
        X ω (foldedCircle (dyadicRoundC n z) (radius k)) := by
  have h : ∀ i : ℕ, ∀ᵐ ω ∂P,
      evalReg (X ω) (foldedCircle (foldH (Factorization.dyadicIndex i).1)
        (radius (Factorization.dyadicIndex i).2)) =
      X ω (foldedCircle (foldH (Factorization.dyadicIndex i).1)
        (radius (Factorization.dyadicIndex i).2)) := fun i =>
    AllOffsets.ae_evalReg_fc_eq hX (foldH_mem_Hbar' _) (radius_pos _)
  filter_upwards [ae_all_iff.2 h] with ω hω n k z
  obtain ⟨i, hi⟩ := Factorization.dyadicIndex_surj n k z
  have := hω i
  rw [WedgeTK.fc_foldH_eq, hi] at this
  exact this

/-- **The wedge field has the dyadic averages of free field plus profile.** -/
theorem ae_avgReg_wedgeField_eq (γ α : ℝ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', avgReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) =
      avgReg (ofFun (WedgeCan.wedgeProfile (X ω) (fun t => A t ω) (Qc γ)) + X ω) := by
  filter_upwards [F1.wedgeCircleIntStmt_holds γ α P' X A hX hA hI, ae_evalReg_dyadic hX]
    with ω hint hex
  funext k z
  unfold avgReg
  congr 1
  funext n
  have hr := radius_pos k
  obtain ⟨h1, h2⟩ := hint (dyadicRoundC n z) (radius k) hr
  rw [WedgeCan.wedgeField_eq_evalReg_add_ofFun h1
    (WedgeCan.integrable_logProfile_foldedCircle _ _ _) h2, hex n k z]
  show _ = ofFun _ _ + X ω _
  unfold ofFun
  ring

/-- **The wedge representative's conclusion in free-plus-profile form.** -/
theorem ae_concl0_wedgeRep_iff (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', ∀ W : ℝ → ℝ, G4SepConcl0 γ (wedgeRep γ X A ω, W) ↔
      G4SepConcl0 γ (rescale (ofFun (WedgeCan.wedgeProfile (X ω) (fun t => A t ω) (Qc γ)) + X ω)
        (Qc γ) (scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))), W) := by
  filter_upwards [ae_avgReg_wedgeField_eq γ _ hX hA hI] with ω hω W
  have e : wedgeRep γ X A ω = rescale (ofFun (WedgeCan.wedgeProfile (X ω) (fun t => A t ω) (Qc γ))
      + X ω) (Qc γ) (scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) := by
    show rescale _ _ _ = _
    unfold rescale
    exact Factorization.coordChange_congr hω _ _
  rw [e]

end ASep
end QuantumZipper
