import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.R18G3Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 2: adding the same constant to both side fields (`G3JointConstInvStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(pp. 69–71) and proof of Proposition 1.7 (pp. 25–26: adding a constant to the field and
re-embedding by the scale parameter does not change the law of the wedge configuration; the SLE is
scale invariant and independent of the field).

Copy of `Thm18Asm.g1SideConstInvStmt_of_reg` (G1ZB2C.lean, G1ZB2CMain.lean) with a pair of
functionals `Γ₁` (left side) `* Γ₂` (right side): the canonicalized shifted configuration has the
same configuration law (`canonConfig_shift_facts`, from `F1.wedgeAddConstLawStmt_holds`); the
pathwise re-embedding identity (`g1SideShiftPathStmt_of`) holds for both sides a.s.; the
measurable factorization A2 is applied to each side (product of the two measurable factor maps,
intersection of the two good sets). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus Factorization CoordsFull

/-- **Joint B2-C** from the pathwise re-embedding identity and the factorization A2. -/
theorem g3JointConstInvStmt_of (hF : G1RerootFactorStmt) (hP : G1SideShiftPathStmt) :
    G3JointConstInvStmt := by
  intro γ Ω _ P _ B Y hS hIn C R Γ₁ Γ₂ hΓ₁ hΓ₂ _ _
  obtain ⟨-, hlaw, hmc', hgood'⟩ := canonConfig_shift_facts hS C
  obtain ⟨_Gr₁, G₁, E₁, -, hG₁, hE₁m, hdet₁, hE₁⟩ := hF γ P B Y hS hIn true 1 one_pos 0
    (fun _ => 0) measurable_const fun _ => zero_le_one
  obtain ⟨_Gr₂, G₂, E₂, -, hG₂, hE₂m, hdet₂, hE₂⟩ := hF γ P B Y hS hIn false 1 one_pos 0
    (fun _ => 0) measurable_const fun _ => zero_le_one
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω) with hc'
  have hpath : AEMeasurable (fun ω => fun t : ℝ≥0 => (c ω).2 t) P := by
    have hm : Measurable fun a : ℝ≥0 → ℝ => fun t : ℝ≥0 =>
        Real.sqrt (γ ^ 2) * a ((t : ℝ).toNNReal) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
    exact hm.comp_aemeasurable (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1)
  have hmc : AEMeasurable (fun ω => g1zCfgData (c ω)) P := hIn.2.1.prodMk hpath
  have hlaw' : P.map (fun ω => g1zCfgData (c' ω)) = P.map (fun ω => g1zCfgData (c ω)) := hlaw
  have hEm : MeasurableSet (E₁ ∩ E₂) := hE₁m.inter hE₂m
  have hE : ∀ᵐ ω ∂P, g1zCfgData (c ω) ∈ E₁ ∩ E₂ := by
    filter_upwards [hE₁, hE₂] with ω h1 h2
    exact ⟨h1, h2⟩
  have hE' : ∀ᵐ ω ∂P, g1zCfgData (c' ω) ∈ E₁ ∩ E₂ := by
    have h : ∀ᵐ p ∂(P.map fun ω => g1zCfgData (c ω)), p ∈ E₁ ∩ E₂ :=
      (ae_map_iff hmc hEm).2 hE
    rw [← hlaw'] at h
    exact (ae_map_iff hmc' hEm).1 h
  set Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun p => Γ₁ (g1zLocData R (G₁ p)) * Γ₂ (g1zLocData R (G₂ p)) with hΦ
  have hΦm : Measurable Φ :=
    (hΓ₁.comp ((measurable_g1zLocData R).comp hG₁)).mul
      (hΓ₂.comp ((measurable_g1zLocData R).comp hG₂))
  calc ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y true ω) C))) *
        Γ₂ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y false ω) C))) ∂P
      = ∫⁻ ω, Φ (g1zCfgData (c' ω)) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hP γ P B Y hS hIn true C, hP γ P B Y hS hIn false C, hE', hgood'] with
          ω h1 h1' h2 h3
        rw [locFieldFull_eq_g1zLocData, locFieldFull_eq_g1zLocData, h1, h1', hΦ]
        simp only
        rw [← (hdet₁ _ h2.1 h3).2, ← (hdet₂ _ h2.2 h3).2]
    _ = ∫⁻ p, Φ p ∂(P.map fun ω => g1zCfgData (c' ω)) :=
        (lintegral_map' hΦm.aemeasurable hmc').symm
    _ = ∫⁻ p, Φ p ∂(P.map fun ω => g1zCfgData (c ω)) := by rw [hlaw']
    _ = ∫⁻ ω, Φ (g1zCfgData (c ω)) ∂P := lintegral_map' hΦm.aemeasurable hmc
    _ = ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
          Γ₂ (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hE, ae_g1zDrvGood hS hIn] with ω h1 h2
        rw [locFieldFull_eq_g1zLocData, locFieldFull_eq_g1zLocData, hΦ]
        simp only
        rw [← (hdet₁ _ h1.1 h2).2, ← (hdet₂ _ h1.2 h2).2]
        rfl

end R18
end QuantumZipper
