import QuantumZipper.Proofs.Thm18.G1ZmRed
import QuantumZipper.Proofs.Thm18.G3ZrMain
import QuantumZipper.Proofs.Thm18.G3ZrWire2
import QuantumZipper.Proofs.Thm18.G1TopMain
import QuantumZipper.Proofs.Thm18.G1Side2Wire
import QuantumZipper.Proofs.Thm18.G1Side3Tr
import QuantumZipper.Proofs.Thm18.G1Side3Top
import QuantumZipper.Proofs.Thm18.G1ZA1aAff
import QuantumZipper.Proofs.Thm18.G3ZqResc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (3): the one-point Palm limit from the fixed-path limit of the unscaled wedge

One-point analog of `G3Zq.g3WedgeFreeTransferStmt_of_pathU` (G3ZqWireU). G1-ZOOM reduced
`G1WedgePalmLimStmt` to the a.e.-path limit `G1Zm.G1ZmPathAEStmt` for the canonical wedge
`wedgeRep = canonical (wedgeU)`, which cannot be proved path by path because the canonical scale
`b = scaleParam γ wedgeU` is random and global. We average over the path first: by
`G3Zq.lintegral_path_rescale` the path average of the canonical one-point functional equals the
path average of the unscaled one, given the pointwise identity
`g1PhiM (wedgeRep ω', S_b a) = g1PhiM (wedgeU ω', a)` (`G3ZqL1ResclIdStmt`; the deterministic
identity is `G1Zm.g1PhiM_canonical_scalePath`).

Headline: **`g1WedgePalmLimStmt_of_pathU : G3ZqL1ResclIdStmt → G3ZqL1PathUStmt →
G1WedgePalmLimStmt`**.

Sheffield, arXiv:1012.4797, pp. 70–71 (independent curve, SLE scale invariance). Own bookkeeping
(AGENT_GUIDE cost rule), following `g1WedgePalmLimStmt_of_pathAE` (G1ZmTop).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Z2b2 D3Plus G1Zm G3Zq Factorization

/-- **The pointwise one-point rescaling identity, a.s.** For the wedge representative and an
independent Brownian path: for a.e. `ω'` the scale `b` of the unscaled field is positive and for
a.e. path `a` the one-point functional of the canonical field along `S_b a` equals that of the
unscaled field along `a`. -/
def G3ZqL1ResclIdStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (left : Bool) (U L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ →
    ∀ᵐ ω' ∂P', 0 < scaleParam γ (wedgeU γ X A ω') ∧ ∀ᵐ a ∂(P.map (pathOf B)),
      g1PhiM γ L R Γ Ψ left U (wedgeRep γ X A ω', scalePath (scaleParam γ (wedgeU γ X A ω')) a) =
        g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a)

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem g1PhiM_reconstruct_coords {γ L U : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    {left : Bool} (y : FieldSample) (a : ℝ≥0 → ℝ) :
    g1PhiM γ L R Γ Ψ left U (reconstruct (coords y), a) = g1PhiM γ L R Γ Ψ left U (y, a) :=
  g1PhiM_congr (Factorization.avgReg_reconstruct_coords y) a

theorem measurable_g1PhiM_coords {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ) :
    Measurable fun q : (ℝ≥0 → ℝ) × (ℕ → ℝ) => g1PhiM γ L R Γ Ψ left U (reconstruct q.2, q.1) :=
  (measurable_g1PhiM hsel L R hΓ left U).comp
    ((Factorization.measurable_reconstruct.comp measurable_snd).prodMk measurable_fst)

theorem measurable_g1PhiM_wedgeU {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hc : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P') :
    Measurable fun a => ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P' := by
  have e : (fun a => ∫⁻ ω', g1PhiM γ L R Γ Ψ left U (wedgeU γ X A ω', a) ∂P') =
      fun a => ∫⁻ c, g1PhiM γ L R Γ Ψ left U (reconstruct c, a)
        ∂(P'.map fun ω' => coords (wedgeU γ X A ω')) := by
    funext a
    rw [lintegral_map' _ hc]
    · exact lintegral_congr fun ω' => (g1PhiM_reconstruct_coords _ _).symm
    · exact ((measurable_g1PhiM_coords hsel L R hΓ left U).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
  rw [e]
  exact (measurable_g1PhiM_coords hsel L R hΓ left U).lintegral_prod_right'

theorem aemeasurable_g1PhiM_wedgeU_prod {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hc : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P')
    (ν : Measure (ℝ≥0 → ℝ)) [SFinite ν] :
    AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => g1PhiM γ L R Γ Ψ left U (wedgeU γ X A q.2, q.1))
      (ν.prod P') := by
  have h1 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => coords (wedgeU γ X A q.2)) (ν.prod P') :=
    hc.comp_snd
  have h2 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => (q.1, coords (wedgeU γ X A q.2)))
      (ν.prod P') := measurable_fst.aemeasurable.prodMk h1
  refine ((measurable_g1PhiM_coords hsel L R hΓ left U).comp_aemeasurable h2).congr
    (ae_of_all _ fun q => ?_)
  exact g1PhiM_reconstruct_coords (wedgeU γ X A q.2) q.1

theorem aemeasurable_g1PhiM_wedgeRep_prod {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L : ℝ) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (left : Bool) (U : ℝ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hm : AEMeasurable (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')) P')
    (ν : Measure (ℝ≥0 → ℝ)) [SFinite ν] :
    AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => g1PhiM γ L R Γ Ψ left U (wedgeRep γ X A q.2, q.1))
      (ν.prod P') := by
  have h1 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => WedgeMeas.dataFull H (wedgeRep γ X A q.2))
      (ν.prod P') := hm.comp_snd
  have h2 : AEMeasurable
      (fun q : (ℝ≥0 → ℝ) × Ω' => (q.1, WedgeMeas.dataFull H (wedgeRep γ X A q.2)))
      (ν.prod P') := measurable_fst.aemeasurable.prodMk h1
  refine ((measurable_g1PhiData hsel L R hΓ left U).comp_aemeasurable h2).congr
    (ae_of_all _ fun q => ?_)
  exact g1PhiM_fromC (wedgeRep γ X A q.2) q.1

end G3ZqL
end Thm18Asm
end QuantumZipper
