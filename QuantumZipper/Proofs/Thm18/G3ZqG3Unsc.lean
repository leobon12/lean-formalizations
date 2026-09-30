import QuantumZipper.Proofs.Thm18.G3ZqG3Cap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the unscaled wedge comparison

Generalized copy (D92) of `g3pl4_expect_cap_le` (`G3Pl4Asm.lean`),
`g3pl4_lintegral_phiCap_V_eq` (`G3Pl4Good.lean`), `g3pl4_unscaled_of_inputs` (`G3Pl4Wire.lean`)
and `g3PlPhiUnscaledStmt_holds` (`G3Pl4Node.lean`, with `g3pl4_unscaled_of_sep` inlined), with
the plain zooms replaced by abstract zooms `Z`, `Z'` on the UNSCALED wedge field `g3plUW γ X A`.

Besides `hZm`, `hZa` (measurability, invariance under equal regularized averages), the original
uses one property of the plain zoom: **pathwise locality of the capped functional**
(`g3pl4_phiCap_le_of_agree`, from `zoomLaw_mem_lawCyl_iff` and the growth of the area proxy,
`G3Pl4Loc.lean`): if two good fields agree on the folded circles in the unit ball, the second
has positive area on every half-ball, and the separation conditions hold, then for all large
levels the capped functional of the first is at most that of the second plus `ε`. For abstract
zooms this is the explicit hypothesis `G3PlCapLocZ`; `g3PlCapLocZ_zoomLaw` shows the plain zoom
satisfies it. All zoom-free inputs (the coupling `g3pl4_wedge_fcAgree_norm`, the law of the circle
coordinates `g3pl4_coordsLaw_eq`, area-goodness, the separation and small-window events
`g3pl4_hC_sepBad_small`, `g3pl_exists_U₀`, the expectation lemma `g3pl4_expect_le`) are reused.

Headline `g3PlPhiUnscaledStmtZ_holds : G3PlCapLocZ Z Z' γ → G3PlPhiUnscaledStmtZ Z Z' γ`.

Sheffield, arXiv:1012.4797, §5.1 p. 61 and proof of Thm. 1.8, pp. 71–72. Own bookkeeping copied
from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- A.e.-measurability of the capped functional of an a.s. good field (abstract zooms). -/
theorem aemeasurable_phiCapZ
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ δ L U : ℝ} {s t : Set LawD} (hs : MeasurableSet s)
    (ht : MeasurableSet t) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (hg : ∀ᵐ ω ∂P, IsLQGGood γ (Y ω))
    (hm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P) :
    AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y ω)) P :=
  (((measurable_g3pl4CapMZ hZm hZm' γ δ L U hs ht).comp
    (Cor15Group.measurable_fromC.comp measurable_fst)).comp_aemeasurable hm).congr
    (hg.mono fun ω h => (g3pl4PhiCapZ_eq_data hZa hZa' h).symm)

theorem g3pl4_lintegral_phiCapZ_V_eq
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {V : Ω' → FieldSample}
    (hV : IsFreeGFFModConstH V P') (hVn : ∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0)
    {δ U L : ℝ} {s t : Set LawD} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (V ω + F2.logSingField (γ ^ 2)) ∂P' =
      g3plHonXZ Z Z' γ δ U L s t := by
  have := gffBase.prob
  rw [g3plHonXZ_eq_phiCapZ]
  have hVm : ∀ μ : Measure ℂ, Measurable fun ω => (V ω + F2.logSingField (γ ^ 2)) μ :=
    fun μ => (hV.measurable_coord μ).add measurable_const
  have hCm : ∀ μ : Measure ℂ, Measurable fun ω => g3pField γ (g3wProf γ) ω μ := fun μ => by
    simp only [g3pField, normField, Pi.add_apply]
    exact (measurable_const.add ((gffBase.gff.measurable_coord μ).sub
      (gffBase.gff.measurable_coord _))).add measurable_const
  refine lintegral_phiCapZ_eq_of_coordsLaw hZm hZa hZm' hZa' hs ht
    ((g3pl4_ae_isAreaGood_logSing hγ hγ2 hV).mono fun ω h => h.1)
    ((ae_isAreaGood_g3pField hγ hγ2).mono fun ω h => h.1)
    (measurable_pi_iff.2 fun n => hVm _).aemeasurable
    (measurable_pi_iff.2 fun n => hCm _).aemeasurable
    (g3pl4_coordsLaw_eq hγ hV hVn)

end R18
end QuantumZipper
