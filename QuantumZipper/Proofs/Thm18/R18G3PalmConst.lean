import QuantumZipper.Proofs.Thm18.R18G3PalmMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 3: the joint Palm average with a constant

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71, Figure 1.7: the left root is sampled from quantum length and the right root
is its length partner) and proof of Proposition 1.7 (pp. 25–26: rerooting at a point sampled
from quantum length, then adding a constant).

Copy of `Thm18Asm.g1PalmConstStmt_of` (G1ZB2RMain.lean) with pairs of functionals:

1. the joint rerooting G3 step 1 (`G3JointRerootStmt`, all `R`, `Γ₁`, `Γ₂`) gives equal joint
   laws of the coordinates of the rerooted and the plain pair of canonical side fields
   (`g3_pair_map_eq`, π-λ);
2. the quantile change of variables of B1 on the left side (`g1zB2r_pathwise true`), with the
   quantile identity `ν[lenLeft ℓ, 0] = ℓ` (`g3LenL_g1SidePt`) for the right partner, turns the
   joint Palm-window integral into `∫_{(0,U]} dℓ` of the jointly rerooted functional;
3. Tonelli (joint measurability from B1-MEAS for both sides) and (1) make the `ℓ`-integrand
   constant.

Own bookkeeping on top of the cited nodes, as the original.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus CoordsFull

/-- **G3 step 3 (joint Palm average with a constant)** from the joint rerooting, A, B0, B1-MEAS
and the canonical-data identity N′. -/
theorem g3JointPalmConstStmt_of (hJ : G3JointRerootStmt) (hA : G1RerootStmt)
    (hB0 : G1SideBdryRegStmt) (hBM : G1SideTranslMeasStmt) (hN : G1SideConstDataStmt) :
    G3JointPalmConstStmt := by
  intro γ Ω _ P _ B Y hS hIn U hU C R Γ₁ Γ₂ hΓ₁ hΓ₂ hΓ₁1 hΓ₂1
  have hmL := (hA γ P B Y hS hIn true).1
  have hmR := (hA γ P B Y hS hIn false).1
  set ZL := g1SideField γ B Y true with hZL
  set ZR := g1SideField γ B Y false with hZR
  set Θ₁ : (ℕ → ℝ) → ℝ≥0∞ := fun c => Γ₁ (g1zLocData R (g1zB2rPhi γ C c)) with hΘ₁def
  set Θ₂ : (ℕ → ℝ) → ℝ≥0∞ := fun c => Γ₂ (g1zLocData R (g1zB2rPhi γ C c)) with hΘ₂def
  have hΘ₁ : Measurable Θ₁ :=
    hΓ₁.comp ((measurable_g1zLocData R).comp (measurable_g1zB2rPhi γ C))
  have hΘ₂ : Measurable Θ₂ :=
    hΓ₂.comp ((measurable_g1zLocData R).comp (measurable_g1zB2rPhi γ C))
  have hΘ : Measurable fun q : (ℕ → ℝ) × (ℕ → ℝ) => Θ₁ q.1 * Θ₂ q.2 :=
    (hΘ₁.comp measurable_fst).mul (hΘ₂.comp measurable_snd)
  have hpL := hN γ P B Y hS hIn true C
  have hpR := hN γ P B Y hS hIn false C
  -- the right-hand side
  have hRHS : ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (addConst (ZL ω) C))) *
      Γ₂ (locFieldFull R (canonical γ (addConst (ZR ω) C))) ∂P =
      ∫⁻ ω, Θ₁ (coordsFull (canonical γ (ZL ω))) * Θ₂ (coordsFull (canonical γ (ZR ω))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hpL, hpR] with ω h1 h2
    simp only [locFieldFull_eq_g1zLocData]
    rw [h1.1, h2.1]
  -- the left-hand side
  have hLHS : g3PalmIntC γ P B Y U C R Γ₁ Γ₂ = ∫⁻ ω, ∫⁻ b in g1Win γ true (ZL ω) U,
      Θ₁ (coordsFull (canonical γ (translate (ZL ω) (b : ℂ)))) *
        Θ₂ (coordsFull (canonical γ (translate (ZR ω)
          (g1SidePt γ false (ZR ω) (g3LenL γ (ZL ω) b) : ℂ)))) ∂(g1SideNu γ true (ZL ω)) ∂P := by
    unfold g3PalmIntC
    refine lintegral_congr_ae ?_
    filter_upwards [hpL, hpR] with ω h1 h2
    refine lintegral_congr fun b => ?_
    simp only [locFieldFull_eq_g1zLocData]
    rw [h1.2 b, h2.2 _]
  have hm1 : ∀ left : Bool, ∀ᵐ ω ∂P, ∀ R' : ℕ, Measurable fun b : ℝ =>
      locFieldFull R' (canonical γ (translate (g1SideField γ B Y left ω) (b : ℂ))) := by
    intro left
    rw [ae_all_iff]
    intro R'
    exact (hBM γ P B Y hS hIn left R').1
  have hjc : ∀ left : Bool, AEMeasurable (fun p : Ω × ℝ => coordsFull (canonical γ
      (translate (g1SideField γ B Y left p.1)
        (g1SidePt γ left (g1SideField γ B Y left p.1) p.2 : ℂ)))) (P.prod volume) :=
    fun left => g1zB2r_coordsFull_of_loc fun R' => (hBM γ P B Y hS hIn left R').2
  have hstep1 : ∫⁻ ω, ∫⁻ b in g1Win γ true (ZL ω) U,
      Θ₁ (coordsFull (canonical γ (translate (ZL ω) (b : ℂ)))) *
        Θ₂ (coordsFull (canonical γ (translate (ZR ω)
          (g1SidePt γ false (ZR ω) (g3LenL γ (ZL ω) b) : ℂ)))) ∂(g1SideNu γ true (ZL ω)) ∂P =
      ∫⁻ ω, (∫⁻ ℓ in Ioc (0 : ℝ) U,
        Θ₁ (coordsFull (canonical γ (translate (ZL ω) (g1SidePt γ true (ZL ω) ℓ : ℂ)))) *
        Θ₂ (coordsFull (canonical γ (translate (ZR ω) (g1SidePt γ false (ZR ω) ℓ : ℂ))))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hB0 γ P B Y hS hIn true, hm1 true, hm1 false] with ω hreg hmω hmω'
    have hFm : Measurable fun b : ℝ =>
        Θ₁ (coordsFull (canonical γ (translate (ZL ω) (b : ℂ)))) *
          Θ₂ (coordsFull (canonical γ (translate (ZR ω)
            (g1SidePt γ false (ZR ω) (g3LenL γ (ZL ω) b) : ℂ)))) :=
      (hΘ₁.comp (g1zB2r_measurable_coordsFull_of_loc hmω)).mul
        (hΘ₂.comp ((g1zB2r_measurable_coordsFull_of_loc hmω').comp
          (measurable_g3PartnerPt γ (ZL ω) (ZR ω))))
    rw [← g1zB2r_pathwise true hU hreg hFm]
    refine setLIntegral_congr_fun measurableSet_Ioc fun ℓ hℓ => ?_
    rw [g3LenL_g1SidePt hreg hℓ.1.le]
  have hjoint : AEMeasurable (Function.uncurry fun (ω : Ω) (ℓ : ℝ) =>
      Θ₁ (coordsFull (canonical γ (translate (ZL ω) (g1SidePt γ true (ZL ω) ℓ : ℂ)))) *
        Θ₂ (coordsFull (canonical γ (translate (ZR ω) (g1SidePt γ false (ZR ω) ℓ : ℂ)))))
      (P.prod (volume.restrict (Ioc (0 : ℝ) U))) := by
    have he : P.prod (volume.restrict (Ioc (0 : ℝ) U)) =
        (P.prod volume).restrict (univ ×ˢ Ioc 0 U) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [he]
    exact (hΘ₁.comp_aemeasurable (hjc true).restrict).mul
      (hΘ₂.comp_aemeasurable (hjc false).restrict)
  have hℓ : ∀ᵐ ℓ ∂(volume.restrict (Ioc (0 : ℝ) U)),
      ∫⁻ ω, Θ₁ (coordsFull (canonical γ (translate (ZL ω) (g1SidePt γ true (ZL ω) ℓ : ℂ)))) *
        Θ₂ (coordsFull (canonical γ (translate (ZR ω) (g1SidePt γ false (ZR ω) ℓ : ℂ)))) ∂P =
      ∫⁻ ω, Θ₁ (coordsFull (canonical γ (ZL ω))) * Θ₂ (coordsFull (canonical γ (ZR ω))) ∂P := by
    filter_upwards [ae_restrict_of_ae (g1zB2r_ae_aemeasurable_snd (hjc true)),
      ae_restrict_of_ae (g1zB2r_ae_aemeasurable_snd (hjc false)),
      ae_restrict_mem measurableSet_Ioc] with ℓ hfL hfR hℓ
    have hf : AEMeasurable (fun ω =>
        (coordsFull (canonical γ (translate (ZL ω) (g1SidePt γ true (ZL ω) ℓ : ℂ))),
          coordsFull (canonical γ (translate (ZR ω) (g1SidePt γ false (ZR ω) ℓ : ℂ))))) P :=
      hfL.prodMk hfR
    have hpL' : AEMeasurable (fun ω => coordsFull (canonical γ (ZL ω))) P := hmL.fst
    have hpR' : AEMeasurable (fun ω => coordsFull (canonical γ (ZR ω))) P := hmR.fst
    have hpm : AEMeasurable (fun ω =>
        (coordsFull (canonical γ (ZL ω)), coordsFull (canonical γ (ZR ω)))) P :=
      hpL'.prodMk hpR'
    have hmap := g3_pair_map_eq hf hpm (fun R' Γ₁' Γ₂' hΓ₁' hΓ₂' hΓ₁'1 hΓ₂'1 => by
      have := hJ γ P B Y hS hIn ℓ hℓ.1 R' (fun y => Γ₁' y.1) (fun y => Γ₂' y.1)
        (hΓ₁'.comp measurable_fst) (hΓ₂'.comp measurable_fst) (fun y => hΓ₁'1 y.1)
        (fun y => hΓ₂'1 y.1)
      simp only [locFieldFull_fst] at this
      exact this)
    rw [← lintegral_map' hΘ.aemeasurable hf, hmap, lintegral_map' hΘ.aemeasurable hpm]
  rw [hLHS, hstep1, lintegral_lintegral_swap hjoint, lintegral_congr_ae hℓ,
    g1z_inv_mul_setLIntegral_const hU, hRHS]

end R18
end QuantumZipper
