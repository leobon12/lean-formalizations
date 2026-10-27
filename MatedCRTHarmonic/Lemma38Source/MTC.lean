import MatedCRTHarmonic.Lemma38Source.OneScale
import MatedCRTHarmonic.MesoModel.FinalAssembly
import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.GMS4.Prop48
import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.GMS4.SmallRootMass
import MatedCRTHarmonic.GMSLemma27.Consumers
import MatedCRTHarmonic.GMS4.CellScalingCellModelCoupling

/-!
# Lemma 3.8 at the mating-of-trees coupling

The only probabilistic input of the resulting one-scale theorem is the
uniform per-test conclusion of `GMS4.proposition210_holds`; the Lemma 2.7 and
Peanosphere inputs are instantiated from the existing bundle producers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Lemma38Source

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The exact the one-scale argument one-scale bound at MTC's model, with one named
Proposition 2.10 hypothesis in G4's conclusion shape. -/
theorem annulus38OneScaleBadBound_of_proposition210_at_mtc
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2)
    {betaG4 A α Cfail : ℝ}
    (hbetaG4 : 0 < betaG4) (hα : 0 < α)
    (hA : 0 ≤ A) (hCfail : 0 ≤ Cfail)
    (h210 : ∀ k (V : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) (3 / 4) 100 betaG4 V f →
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family.P
        (GMS4.Prop210Bad
          (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family
          k V f (2 * A) (CellFamily.mesh k ^ α)) ≤
        ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)) :
    MesoModel.Annulus38OneScaleBadBound
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).coupled.family
      (MoTInput.unitMesoModelOfCoupling D hstd hγ).ρ := by
  let M := MoTInput.unitMesoModelOfCoupling D hstd hγ
  let C := MoTInput.coneRealizationOfCoupling D hstd hγ
  let hpar : CellScaling.AreaParametrization C :=
    MesoModel.final_areaParametrization_of_coupling D hstd hγ
  let S := C.toCellModelGraphCoupling hpar
  have hq : 0 < M.q := M.hq.1
  have hden : 0 < (2 + γ) ^ 2 := by
    have htwo : 0 < 2 + γ := by linarith [hγ.1]
    positivity
  have hden4 : 4 < (2 + γ) ^ 2 := by
    nlinarith [sq_nonneg γ, hγ.1]
  have hq1 : M.q < 1 := by
    have hfrac : 2 / (2 + γ) ^ 2 < 1 :=
      (div_lt_iff₀ hden).mpr (by linarith)
    exact M.hq.2.trans hfrac
  have hα27pos : 0 < GMSLemma27.lemma27Exponent M.q γ :=
    GMSLemma27.lemma27Exponent_pos hγ.1 hq M.hq.2
  let α27 := GMSLemma27.lemma27Exponent M.q γ / 2
  have hα27 : 0 < α27 := by dsimp [α27]; linarith
  have hα27lt : α27 < GMSLemma27.lemma27Exponent M.q γ := by
    dsimp [α27]
    linarith
  obtain ⟨C27, hC27, h27⟩ := GMSLemma27.cellDiamBound_of_cellModel
    (C.toCellModel hpar)
    (MesoModel.final_segmentsContainBalls_of_coupling D hstd hγ hpar)
    (GMCFacts.gmcLowerTail_holds hγ.1 hγ.2)
    (GMCFacts.areaDominates_toCellModel C hpar hγ.1 hγ.2)
    hγ.1 S.toRandomCellFamily S.modelMap S.measurePreserving_modelMap
    S.ae_cell_eq hq M.hq.2
    (show (3 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) hα27lt
  have hpeano : CellFamily.PeanosphereG0 M.coupled.family :=
    MesoModel.final_peanosphereG0_of_coupling D hstd hγ
  have h27' : ∀ k, M.coupled.family.P
      {ω | GMS3.CellDiamBound (M.coupled.family.H k ω) (3 / 4)
        (CellFamily.mesh k ^ M.q)}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27) := by
    intro k
    exact h27 k
  exact annulus38OneScaleBadBound_of_L27_G4 M.coupled.family
    (by change (0 : ℝ) < 1 / 2; norm_num)
    (by change (1 / 2 : ℝ) < 3 / 4; norm_num)
    (by norm_num : (3 / 4 : ℝ) < 1)
    hq hq1 hbetaG4 hα hα27 hA hC27 hCfail hpeano h27' h210

end MatedCRTHarmonic.Lemma38Source

