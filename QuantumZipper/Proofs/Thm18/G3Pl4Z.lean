import QuantumZipper.Proofs.Thm18.G3Pl4Wire
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Thm18.R18G3TXSide2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): inputs (I1), (I2) for the unscaled wedge

* `g3pl4_aemeasurable_phiCap_Z` (I1): the capped Palm functional of the unscaled wedge field is
  a.e.-measurable (its dyadic circle coordinates are, `WedgeMeas.aemeasurable_coords_wedgeField`, and
  the functional factors through them on good samples).
* `g3pl4_ae_isAreaGood_Z` (I2): the unscaled wedge field is a.s. area-good: on every folded circle it
  is `V + (γ − 2/γ)(−log|·|) + G` with `G` continuous (`WDec.ae_pathwise`), and area-goodness is
  stable under continuous shifts (`isAreaGood_add_ofFun`) and determined by the circle coordinates.
* `g3pl4_unscaled_of_sep`: the conclusion of `G3PlPhiUnscaledStmt` for one wedge sample space from
  the two boundary-length inputs (I3), (I4) of `g3pl4_unscaled_of_inputs`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm WedgeUnzip.WDec

theorem g3pl4_ae_isAreaGood_Z {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', IsAreaGood γ (g3plUW γ X A ω) := by
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hA' : IsWedgeProcess (Real.sqrt (γ ^ 2) - 2 / Real.sqrt (γ ^ 2)) (Qc (Real.sqrt (γ ^ 2)))
      A P' := by rwa [hs]
  obtain ⟨B, B', hBm, hB'm, -, hAe⟩ := id hA'
  obtain ⟨Bt, hBtm, hBtc, hBtB⟩ := WedgeRes.exists_good_version hBm
  have hAB := wedge_hAB hAe
  have hBtpre : IsPreBrownianReal Bt P' :=
    hBm.toIsPreBrownianReal.congr fun s => hBtB.mono fun ω h => (h s).symm
  have hVfree := isFree_PhiF_of_indep hX hBtm hBtpre (indep_lat_Bt hXA hAB hBtB)
  have hmain := ae_pathwise (κ := γ ^ 2) hX hA' hAe hBm hBtc hBtB
  filter_upwards [hmain, g3pl4_ae_isAreaGood_logSing hγ hγ2 hVfree] with ω hω hY
  obtain ⟨hGc, -, hfc⟩ := hω
  rw [hs] at hGc
  set G := corrField (γ - 2 / γ) (Qc γ) (fun t => A t ω) (nPath (X ω)) with hG
  have hW := isAreaGood_add_ofFun hY hGc
  set W := PhiF ((latW (X ω), nPath (X ω)), pathOf Bt ω) + F2.logSingField (γ ^ 2) + ofFun G
    with hWdef
  have hcoords : Factorization.coords (g3plUW γ X A ω) = Factorization.coords W := by
    refine WedgeUnzip.coords_eq_of_fc fun d hd r hr => ?_
    have e := hfc d hd r hr
    rw [hs] at e
    exact e
  have havg : avgReg (g3plUW γ X A ω) = avgReg W := by
    rw [← Factorization.avgReg_reconstruct_coords (g3plUW γ X A ω), hcoords,
      Factorization.avgReg_reconstruct_coords]
  refine ⟨(WedgeGood.isLQGGood_congr_coords hcoords).2 hW.1, fun V' hV' hV'H hne => ?_⟩
  rw [Factorization.qAreaMeasure_congr havg γ]
  exact hW.2 V' hV' hV'H hne

end R18
end QuantumZipper
