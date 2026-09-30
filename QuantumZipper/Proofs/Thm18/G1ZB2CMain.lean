import QuantumZipper.Proofs.Thm18.G1ZB2CLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2C (2): `G1SideConstInvStmt` from the pathwise re-embedding identity and A2

Theorem 1.8, G1 zoom, node B2-C. Sheffield, arXiv:1012.4797, proof of Proposition 1.7
(pp. 25–26: adding a constant to the field and re-embedding by the scale parameter does not change
the law of the wedge configuration; the SLE is scale invariant and independent of the field).

* `G1SideShiftPathStmt` (**the one new pathwise node**): a.s. the canonical data of the
  constant-shifted side field `addConst (g1SideField …) C` are those of the side field of the
  canonicalized shifted configuration `canonConfig γ (Y + C, W)`.
* `g1SideConstInvStmt_of : G1RerootFactorStmt → G1SideShiftPathStmt → G1SideConstInvStmt`: law
  transfer. The canonicalized shifted configuration has the same `configLawFull` as the original
  one (`canonConfig_shift_facts`, from `F1.wedgeAddConstLawStmt_holds`), so the measurable
  factorization A2 (`G1RerootFactorStmt`, a measurable set `E` of full measure and a measurable
  `G₀` reading the canonical side data off `g1zCfgData`) applies to both configurations.

Own bookkeeping (same law transfer as `g1RerootStmt_of`, G1ZSplitWire.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

open Classical in
/-- `locFieldFull` as a function of the full data. -/
def g1zLocData (R : ℕ) (d : (ℕ → ℝ) × (TestFun H → ℝ)) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  (fun i => if inBallFull R i then d.1 i else 0, fun ρ => if suppIn R ρ then d.2 ρ else 0)

theorem locFieldFull_eq_g1zLocData (R : ℕ) (x : FieldSample) :
    locFieldFull R x = g1zLocData R (WedgeMeas.dataFull H x) := rfl

theorem measurable_g1zLocData (R : ℕ) : Measurable (g1zLocData R) := by
  classical
  unfold g1zLocData
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · by_cases h : inBallFull R i
    · simp only [h, ite_true]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : suppIn R ρ
    · simp only [h, ite_true]
      exact (measurable_pi_apply ρ).comp measurable_snd
    · simp only [h, ite_false]; exact measurable_const

/-- **Pathwise re-embedding identity (the new node of B2-C).** A.s. the canonical data of the
side field with a constant added are those of the side field of the canonicalized shifted
configuration: `canonical (S(Y,W) + C)` and `canonical S(canonConfig (Y + C, W))` have the same
circle coordinates and raw pairings. -/
def G1SideShiftPathStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ C : ℝ, ∀ᵐ ω ∂P,
      WedgeMeas.dataFull H (canonical γ (addConst (g1SideField γ B Y left ω) C)) =
        WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left
          (canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω))))

/-- **B2-C from the pathwise identity and the factorization A2.** -/
theorem g1SideConstInvStmt_of (hF : G1RerootFactorStmt) (hP : G1SideShiftPathStmt) :
    G1SideConstInvStmt := by
  intro γ Ω _ P _ B Y hS hIn left C R Γ hΓ hΓ1
  obtain ⟨-, hlaw, hmc', hgood'⟩ := canonConfig_shift_facts hS C
  obtain ⟨G, G₀, E, -, hG₀, hEm, hdet, hE⟩ := hF γ P B Y hS hIn left 1 one_pos 0 (fun _ => 0)
    measurable_const fun _ => zero_le_one
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => canonConfig γ (addConst (Y ω) C, drive (γ ^ 2) B ω) with hc'
  have hpath : AEMeasurable (fun ω => fun t : ℝ≥0 => (c ω).2 t) P := by
    have hm : Measurable fun a : ℝ≥0 → ℝ => fun t : ℝ≥0 =>
        Real.sqrt (γ ^ 2) * a ((t : ℝ).toNNReal) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
    exact hm.comp_aemeasurable (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1)
  have hmc : AEMeasurable (fun ω => g1zCfgData (c ω)) P := hIn.2.1.prodMk hpath
  have hlaw' : P.map (fun ω => g1zCfgData (c' ω)) = P.map (fun ω => g1zCfgData (c ω)) := hlaw
  have hE' : ∀ᵐ ω ∂P, g1zCfgData (c' ω) ∈ E := by
    have h : ∀ᵐ p ∂(P.map fun ω => g1zCfgData (c ω)), p ∈ E := (ae_map_iff hmc hEm).2 hE
    rw [← hlaw'] at h
    exact (ae_map_iff hmc' hEm).1 h
  set Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun p => Γ (g1zLocData R (G₀ p)) with hΦ
  have hΦm : Measurable Φ := hΓ.comp ((measurable_g1zLocData R).comp hG₀)
  calc ∫⁻ ω, Γ (locFieldFull R (canonical γ (addConst (g1SideField γ B Y left ω) C))) ∂P
      = ∫⁻ ω, Φ (g1zCfgData (c' ω)) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hP γ P B Y hS hIn left C, hE', hgood'] with ω h1 h2 h3
        rw [locFieldFull_eq_g1zLocData, h1, hΦ]
        simp only
        rw [← (hdet _ h2 h3).2]
    _ = ∫⁻ p, Φ p ∂(P.map fun ω => g1zCfgData (c' ω)) :=
        (lintegral_map' hΦm.aemeasurable hmc').symm
    _ = ∫⁻ p, Φ p ∂(P.map fun ω => g1zCfgData (c ω)) := by rw [hlaw']
    _ = ∫⁻ ω, Φ (g1zCfgData (c ω)) ∂P := lintegral_map' hΦm.aemeasurable hmc
    _ = ∫⁻ ω, Γ (locFieldFull R (canonical γ (g1SideField γ B Y left ω))) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hE, ae_g1zDrvGood hS hIn] with ω h1 h2
        rw [locFieldFull_eq_g1zLocData, hΦ]
        simp only
        rw [← (hdet _ h1 h2).2]
        rfl

end Thm18Asm
end QuantumZipper
