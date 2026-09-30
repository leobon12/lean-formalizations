import QuantumZipper.Proofs.Thm18.RT6MOGroup
import QuantumZipper.Proofs.Thm18.RT6bRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: clause (2) of the D87 Theorem 1.8 from Borel readings of the pieces flow

`g4GroupMOStmt_of` (RT6MOGroup.lean) with the a.e.-measurability node `PiecesFlowMeasStmt`
replaced by the Borel readings `PiecesReadStmt` (RT6bRead.lean): the inverse argument
(`RT6Inv.InvFlow.group`, Sheffield arXiv:1012.4797 p. 26) is run for the Borel reading maps `g ℓ`
themselves; the reading sets carry the zipped wedge data a.s. by law invariance.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **RT6b: clause (2) of the D87 Theorem 1.8 for all signs**, from the Borel readings. -/
theorem g4GroupMOStmt_of_read (hR : PiecesReadStmt) (hLC : MOLawContStmt)
    (hInv : MOInverseExactStmt) (hN : MONegCocycleExactStmt) : G4GroupMOStmt := by
  intro γ Ω _ P _ B Y hS hIn s t
  set c₀ := fun ω => wedgeAConfig γ B Y ω with hc₀
  set X : Ω → RD := fun ω => encR (πdO (c₀ ω)) with hXdef
  have hc0 : ∀ᵐ ω ∂P, Continuous (πdO (c₀ ω)).2 := by
    filter_upwards [D74.ae_wedgeConfig_snd_good hS] with ω hω
    exact hω.1.comp continuous_subtype_val
  have hX : AEMeasurable X P := by
    refine (measurable_encT.comp_aemeasurable (aemeasurable_offData_wedgeAConfig hS hIn)).congr ?_
    filter_upwards [hc0] with ω hω
    exact (encR_πd_eq_encT hω).symm
  choose Bs g hBm hgm hgeq hB0 using hR γ P B Y hS hIn
  have hMe : ∀ ℓ, AEMeasurable (g ℓ) (P.map X) := fun ℓ => (hgm ℓ).aemeasurable
  have hT : ∀ ℓ, ∀ᵐ ω ∂P, g ℓ (X ω) = encR (πdO (zipLenMO γ ℓ (c₀ ω))) := fun ℓ => by
    filter_upwards [hc0, hB0 ℓ] with ω hω hb
    exact (hgeq ℓ _ hω hb).trans
      (congrArg (fun c => encR (πdO c)) (zipLenMO_eq_zipRead γ ℓ (c₀ ω)).symm)
  obtain ⟨hZ0, hInvℓ⟩ := hInv γ P B Y hS hIn
  have hlaw : ∀ ℓ, (P.map X).map (g ℓ) = P.map X := fun ℓ => by
    obtain ⟨hm', hL, hC⟩ := hLC γ P B Y hS hIn ℓ
    rw [AEMeasurable.map_map_of_aemeasurable (hMe ℓ) hX]
    by_cases h0 : ℓ = 0
    · subst h0
      refine Measure.map_congr ?_
      filter_upwards [hT 0, hZ0] with ω e1 e2
      show g 0 (X ω) = X ω
      rw [e1, e2]
    have hm := hm' h0
    have e1 : P.map (g ℓ ∘ X) =
        (P.map fun ω => offData (zipLenMO γ ℓ (c₀ ω)).toPair).map encT := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_encT.aemeasurable hm]
      refine Measure.map_congr ?_
      filter_upwards [hT ℓ, hC] with ω e hω
      exact e.trans (encR_πd_eq_encT hω)
    have e2 : P.map X = (P.map fun ω => offData (c₀ ω).toPair).map encT := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_encT.aemeasurable
        (aemeasurable_offData_wedgeAConfig hS hIn)]
      refine Measure.map_congr ?_
      filter_upwards [hc0] with ω hω
      exact encR_πd_eq_encT hω
    rw [e1, e2]
    exact congrArg (fun m => m.map encT) hL
  have hmem : ∀ ℓ ℓ', ∀ᵐ ω ∂P, encR (πdO (zipLenMO γ ℓ (c₀ ω))) ∈ Bs ℓ' := fun ℓ ℓ' => by
    have h1 : ∀ᵐ y ∂(P.map X), y ∈ Bs ℓ' := (ae_map_iff hX (hBm ℓ')).2 (hB0 ℓ')
    rw [← hlaw ℓ] at h1
    filter_upwards [ae_of_ae_map (hMe ℓ) h1 |> ae_of_ae_map hX, hT ℓ] with ω h e
    rw [← e]; exact h
  have hT2 : ∀ ℓ ℓ', ∀ᵐ ω ∂P, g ℓ' (g ℓ (X ω)) =
      encR (πdO (zipLenMO γ ℓ' (zipLenMO γ ℓ (c₀ ω)))) := fun ℓ ℓ' => by
    filter_upwards [hT ℓ, (hLC γ P B Y hS hIn ℓ).2.2, hmem ℓ ℓ'] with ω e hω hb
    rw [e]
    exact (hgeq ℓ' _ hω hb).trans (congrArg (fun c => encR (πdO c))
      (zipLenMO_eq_zipRead γ ℓ' (zipLenMO γ ℓ (c₀ ω))).symm)
  have hcomp : ∀ ℓ ℓ', AEMeasurable (fun y => g ℓ' (g ℓ y)) (P.map X) := fun ℓ ℓ' => by
    have h' : AEMeasurable (g ℓ') ((P.map X).map (g ℓ)) := by rw [hlaw ℓ]; exact hMe ℓ'
    exact h'.comp_aemeasurable (hMe ℓ)
  have hF : RT6Inv.InvFlow (P.map X) (g) :=
    { meas := hMe
      law := hlaw
      zero := ae_law_of_ae hX (hMe 0) aemeasurable_id (by
        filter_upwards [hT 0, hZ0] with ω e1 e2
        rw [e1, e2])
      inv₁ := fun ℓ hℓ => ae_law_of_ae hX (hcomp ℓ (-ℓ)) aemeasurable_id (by
        filter_upwards [hT2 ℓ (-ℓ), (hInvℓ ℓ hℓ).1] with ω e1 e2
        rw [e1, e2])
      inv₂ := fun ℓ hℓ => ae_law_of_ae hX (hcomp (-ℓ) ℓ) aemeasurable_id (by
        filter_upwards [hT2 (-ℓ) ℓ, (hInvℓ ℓ hℓ).2] with ω e1 e2
        rw [e1, e2])
      neg := fun a b ha hb => ae_law_of_ae hX (hMe _) (hcomp (-b) (-a)) (by
        filter_upwards [hT (-(a + b)), hT2 (-b) (-a), hN γ P B Y hS hIn a b ha hb]
          with ω e1 e2 e3
        rw [e1, e2, e3]) }
  have hG := ae_of_ae_map hX (hF.group s t)
  filter_upwards [hG, hT (s + t), hT2 t s, (hLC γ P B Y hS hIn (s + t)).2.2]
    with ω e e1 e2 hω
  rw [e1, e2] at e
  exact configEqOff_of_encR hω e

end R18
end QuantumZipper
