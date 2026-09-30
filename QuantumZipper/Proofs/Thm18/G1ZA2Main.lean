import QuantumZipper.Proofs.Thm18.G1ZA2Det
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z3Fixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 3: `G1RerootFactorStmt` (Theorem 1.8, G1 zoom, decision D66)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71 (the rerooted side surface is again a wedge-type surface; the functionals involved are
functions of the wedge data and the driver only). Formalization bookkeeping (descriptive set theory:
a.s. properties are turned into memberships in *measurable* sets; Kechris, *Classical Descriptive
Set Theory*, §§ 21, 29 for the analytic route, not needed here).

`g1RerootFactorStmt_of : G1A2GoodSetStmt → G1RerootFactorStmt`.

Route: the measurable selection `Ψ` (`g1PsiSelStmt`, proved) gives measurable formulas `gFun`, `g0Fun`
on the path-data space (G1ZA2Meas.lean), with the side measure replaced by a measurable version
`ν̃` built on the measurable set `SetS` (regularity `G1Meas.measurableSet_rc2` + countable side
certificate of `G1Z5SideCert.lean`). Choice independence is the deterministic chain of
G1ZA2Det.lean, whose inputs are put into the measurable good set: `G1RegGood` (measurable set of
`G1RegFixedStmt`, PROVED) and the measure package `G1Z2MeasGood` of the selected field
(the single named input `G1A2GoodSetStmt`, the measurable-set form of `G1Z2SideGoodStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- **Node A2-G (measurable good set for the measure package of the selected side field).**
There is a measurable set `E₁` of (path, wedge data) pairs, of full law, on which the selected
pulled-back field of the reconstructed wedge field has the area limit and the side boundary limit
(`G1Z2MeasGood`) whenever the path is continuous with a simple trace. This is
`G1Z2SideGoodStmt` (Sheffield–Wang, arXiv:1605.06171, Thm 1.4 and Thm 4.3; DS11 Prop. 2.1) in
the measurable-set form of `G1Z4SideLimStmt` / `G1RegFixedStmt`: the obstacle to deducing it from the
a.s. form is that the good property is not known to be a measurable (or analytic) set of data;
continuity of paths is not a measurable condition (`G1PathNoGo.lean`). -/
def G1A2GoodSetStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ → ∀ left : Bool,
    ∃ E₁ : Set G1PathData, MeasurableSet E₁ ∧
      (∀ p ∈ E₁, Continuous p.1 → IsSimpleChord (pathTrace (γ ^ 2) p.1) →
        G1Z2MeasGood γ left (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))) ∧
      ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ E₁

namespace G1ZA2

open D3Plus Factorization

/-- **Independence step** (as in `g1RegExStmt_of_fixed`): the product form gives a.s. membership of
the (path, data) pair in a measurable set. -/
theorem ae_pair_mem_of_fixed {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {E : Set G1PathData}
    (hE : MeasurableSet E)
    (hae : ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ c ∂(fieldLawFull H Y P), (a, c) ∈ E) :
    ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ E := by
  obtain ⟨-, -, hB, -, hind⟩ := hS
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hdm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := hIn.2.1
  have hind' : IndepFun (hgm.mk _) (hdm.mk _) P :=
    (hind.comp measurable_id measurable_dataFull_H).congr hgm.ae_eq_mk hdm.ae_eq_mk
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (hgm.mk _ ω, hdm.mk _ ω') ∈ E := by
    filter_upwards [ae_of_ae_map hgm hae, hgm.ae_eq_mk] with ω hω hω'
    filter_upwards [ae_of_ae_map hdm hω, hdm.ae_eq_mk] with ω' h2 h3
    rw [← hω', ← h3]; exact h2
  have h2 := CharFunRhs.ae_indep_ae hgm.measurable_mk hdm.measurable_mk hind' hE h1
  filter_upwards [h2, hgm.ae_eq_mk, hdm.ae_eq_mk] with ω hω e1 e2
  rw [← e1, ← e2] at hω
  exact hω

/-- The passage from configuration data to path-data (`W = γ a` on `[0,∞)`). -/
def Theta (γ : ℝ) (q : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : G1PathData :=
  (fun t => q.2 t / γ, q.1)

theorem measurable_Theta (γ : ℝ) : Measurable (Theta γ) :=
  (measurable_pi_iff.2 fun t => ((measurable_pi_apply t).comp measurable_snd).div_const γ).prodMk
    measurable_fst

theorem Theta_wedge {γ : ℝ} (hγ : 0 < γ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (ω : Ω) :
    Theta γ (g1zCfgData (wedgeConfig γ B Y ω)) = (pathOf B ω, WedgeMeas.dataFull H (Y ω)) := by
  unfold Theta g1zCfgData wedgeConfig
  refine Prod.ext ?_ rfl
  funext t
  show drive (γ ^ 2) B ω (t : ℝ) / γ = pathOf B ω t
  rw [drive_eq_pathDrive]
  simp only [pathDrive, Real.sqrt_sq hγ.le, Real.toNNReal_coe]
  field_simp

theorem translate_congr_avg {x x' : FieldSample} (h : avgReg x = avgReg x') (t : ℂ) :
    translate x t = translate x' t := by
  funext μ
  simp only [translate]
  rw [evalReg_congr h]

end G1ZA2

/-- **A2 from the measurable good-set input.** -/
theorem g1RerootFactorStmt_of (hN : G1A2GoodSetStmt) : G1RerootFactorStmt := by
  intro γ Ω _ P _ B Y hS hIn left ℓ hℓ R Γ hΓ hΓ1
  have hγ : 0 < γ := hS.1
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hS.1 hS.2.1
  obtain ⟨E₁, hE₁m, hE₁p, hE₁ae⟩ := hN γ P B Y hS hIn Ψ hΨ left
  obtain ⟨Er, hErm, hErg, hErae⟩ := g1RegFixedStmt_of_rep
    (g1RegRepStmt_of_rc2_rest G1RC.g1RegRepRC2Stmt_holds g1RegRepRestStmt_holds) γ P B Y hS hIn
  have hpair : AEMeasurable (fun ω => (pathOf B ω, WedgeMeas.dataFull H (Y ω))) P :=
    (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1).prodMk hIn.2.1
  obtain ⟨ν, Eν, hνm, hEνm, hEν0, hνeq⟩ := G1ZA2.exists_nuTilde
    (P.map fun ω => (pathOf B ω, WedgeMeas.dataFull H (Y ω))) hΨ left
  have hEr' := G1ZA2.ae_pair_mem_of_fixed hS hIn hErm hErae
  have hEν' : ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ Eν :=
    (ae_map_iff hpair hEνm).1 ((ae_iff (p := fun x => x ∈ Eν)).2 hEν0)
  have hSS : ∀ᵐ ω ∂P, (pathOf B ω, WedgeMeas.dataFull H (Y ω)) ∈ G1ZA2.SetS γ Ψ left := by
    have hreg := g1z2_ae_isRegularSample (g1RegExStmt_of_rest g1RegRepRestStmt_holds) γ hS hIn hΨ
      left
    filter_upwards [hE₁ae, hreg, hS.2.2.1.cont, hIn.2.2] with ω h1 h2 h3 h4
    have hM := hE₁p _ h1 h3 h4.1
    have hx : G1ZA2.xc γ Ψ left (pathOf B ω, WedgeMeas.dataFull H (Y ω)) =
        g1z2Field γ Ψ B Y left ω :=
      (g1z2_coordChange_congr (Cor15Group.regEq_fromC_coordsFull (Y ω)) _ _).symm
    refine ⟨?_, ?_⟩
    · rw [hx]; exact h2
    · obtain ⟨ν', hν'⟩ := hM.2
      exact G1Z5.sideCert_of_lim hν'
  have hEPm : MeasurableSet (Er ∩ E₁ ∩ Eν ∩ G1ZA2.SetS γ Ψ left) :=
    ((hErm.inter hE₁m).inter hEνm).inter (G1ZA2.measurableSet_SetS hΨ left)
  refine ⟨fun q => G1ZA2.gFun γ Ψ left ℓ R Γ ν (G1ZA2.Theta γ q),
    fun q => G1ZA2.g0Fun γ Ψ left (G1ZA2.Theta γ q),
    G1ZA2.Theta γ ⁻¹' (Er ∩ E₁ ∩ Eν ∩ G1ZA2.SetS γ Ψ left),
    (G1ZA2.measurable_gFun hΨ left ℓ R hΓ hνm).comp (G1ZA2.measurable_Theta γ),
    (G1ZA2.measurable_g0Fun hΨ left).comp (G1ZA2.measurable_Theta γ),
    G1ZA2.measurable_Theta γ hEPm, ?_, ?_⟩
  · intro c hcE hW
    have hmem : G1ZA2.pOf γ c ∈ Er ∩ E₁ ∩ Eν ∩ G1ZA2.SetS γ Ψ left := hcE
    obtain ⟨⟨⟨hEr, hE1⟩, hEν⟩, hSS'⟩ := hmem
    have hreg := hErg _ hEr
    have hη : IsSimpleChord (pathTrace (γ ^ 2) (G1ZA2.pOf γ c).1) := by
      show IsSimpleChord (pathTrace (γ ^ 2) (G1ZA2.aOf γ c.2))
      rw [G1ZA2.pathTrace_aOf hγ hW.2.2.1]; exact hW.2.2.2.1
    have hM := hE₁p _ hE1 (G1ZA2.continuous_aOf hW.1) hη
    obtain ⟨hxr, hAE, hF, h0⟩ := G1ZA2.g1za2_det hγ hΨ left ℓ R Γ hW hreg hM
    set p := G1ZA2.pOf γ c with hp
    have hν : g1SideNu γ left (G1ZA2.xc γ Ψ left p) = ν p := hνeq p ⟨hEν, hSS'⟩
    have htr : translate (G1ZA2.xh γ Ψ left p) ((G1ZA2.ptOf left ℓ (ν p) : ℝ) : ℂ) =
        translate (G1ZA2.xc γ Ψ left p)
          (g1SidePt γ left (G1ZA2.xc γ Ψ left p) ℓ : ℂ) := by
      rw [G1ZA2.g1SidePt_eq_ptOf, hν]
      exact G1ZA2.translate_congr_avg (G1ZA2.avgReg_xh γ Ψ left p) _
    refine ⟨?_, ?_⟩
    · show g1zRerootF γ left ℓ R Γ c = G1ZA2.gFun γ Ψ left ℓ R Γ ν p
      rw [hF]
      unfold G1ZA2.gFun
      rw [htr, canonProxy_eq_canonical ((g1zAreaEx_translate_iff hxr _).2 hAE)]
    · show WedgeMeas.dataFull H (canonical γ (g1CfgSideField γ left c)) = G1ZA2.g0Fun γ Ψ left p
      rw [h0]
      have hAEh : G1ZAreaEx γ (G1ZA2.xh γ Ψ left p) := by
        unfold G1ZAreaEx at hAE ⊢
        have har : areaApprox γ (G1ZA2.xh γ Ψ left p) = areaApprox γ (G1ZA2.xc γ Ψ left p) := by
          funext k; unfold areaApprox; rw [G1ZA2.avgReg_xh]
        rw [har]; exact hAE
      have e1 : WedgeMeas.resc (Qc γ) (coords (G1ZA2.xh γ Ψ left p),
          scaleProxy γ (G1ZA2.xh γ Ψ left p)) = canonical γ (G1ZA2.xh γ Ψ left p) := by
        funext ν'
        rw [g1zMeas_canonical_apply_eq, scaleProxy_eq_scaleParam γ _ hAEh]
        rfl
      unfold G1ZA2.g0Fun
      rw [e1, Factorization.canonical_congr (G1ZA2.avgReg_xh γ Ψ left p) γ]
  · filter_upwards [hEr', hE₁ae, hEν', hSS] with ω h1 h2 h3 h4
    rw [Set.mem_preimage, G1ZA2.Theta_wedge hγ]
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

end Thm18Asm
end QuantumZipper
