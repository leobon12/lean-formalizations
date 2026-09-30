import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Thm18.R18MuBasic
import QuantumZipper.Proofs.Thm18.D74Headline
import QuantumZipper.Proofs.Wire4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T10: clause (3) of the paper-form Theorem 1.8 at `t = 0`

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), zipper stationarity (3) at `t = 0` (`Z^LEN_0` is
the identity). At `ℓ = 0` the length-welding driver has time `0` (`lenWeldDriver_zero_spec`), so
the carried area is `μ|_ℍ` pushed forward by `revMap W 0 = id` on `ℍ`, whose scale (1.8) is the
wedge's `scaleParam = 1`; the zipped field `x₀ = h ∘ id + 0` has the circle coordinates of `h`,
hence the same scale. So a.s. the area-carrying `Z^LEN_0` is the old `zipLenC γ 0`, whose law
invariance is `Thm18Asm.configLawFull_zipLenC_zero` (with the proved `Wire4.wedgeZeroRegStmt`).
Own elementary bookkeeping (copy of the unfolding in `Thm18Asm.zipLenC_zero_data`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- At `ℓ = 0`, a.s.-free form: if the wedge field's regularized full-circle averages are its raw
ones and its scale is `1`, and the driver is continuous with `W 0 = 0`, then the area-carrying
`Z^LEN_0` is the old `zipLenC γ 0` on the `(field, driver)` part. -/
theorem toPair_zipLenA_zero {γ : ℝ} {c : AreaConfig} (hμ : c.area = qAreaMeasure γ c.fld)
    (hreg : ∀ i : ℕ, evalReg c.fld (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = c.fld (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2))
    (hsc : scaleParam γ c.fld = 1) :
    (zipLenA γ 0 c).toPair = zipLenC γ 0 c.toPair := by
  rw [zipLenA_of_nonneg le_rfl, zipLenC_of_nonneg le_rfl]
  refine toPair_zipLenUpA ?_
  obtain ⟨hT, hc, h0⟩ := lenWeldDriver_zero_spec γ c.fld
  generalize lenWeldDriver γ c.fld 0 = p at hT hc h0 ⊢
  obtain ⟨T, V⟩ := p
  simp only at hT hc h0
  subst hT
  -- the carried area: `revMap V 0 = id` on `ℍ`
  have hmap : (c.area.restrict H).map (revMap V 0) = c.area.restrict H := by
    have hae : revMap V 0 =ᵐ[c.area.restrict H] id :=
      (ae_restrict_iff' isOpen_H.measurableSet).2
        (Filter.Eventually.of_forall fun z hz => CharFun.revMap_zero_eq hc h0 hz)
    rw [Measure.map_congr hae, Measure.map_id]
  have hL : areaScale (zipWeldUpA γ 0 V c).area = 1 := by
    show areaScale ((c.area.restrict H).map (revMap V 0)) = 1
    rw [hmap, areaScale_restrict_H, hμ, areaScale_qAreaMeasure, hsc]
  -- the zipped field has the circle coordinates of `h`
  have hx₀ : CoordsFull.coordsFull (coordChange c.fld (revMapInv V 0) (Qc γ)) =
      CoordsFull.coordsFull c.fld := by
    funext i
    have hr := UnzipFull.fullIndex_radius_pos i
    show coordChange c.fld (revMapInv V 0) (Qc γ) _ = c.fld _
    rw [CoordReg.coordChange_fc_congr c.fld (Cor15Partial.revMapInv_zero_eqOn hc h0) _ _ hr,
      Cor15Partial.coordChange_id_apply, hreg i]
  have havg := CoordsFull.avgReg_congr_full hx₀
  have hR : scaleParam γ (zipWeldUp γ 0 V c.toPair).1 = 1 :=
    (Factorization.scaleParam_congr havg γ).trans hsc
  rw [hL, hR]

/-- **T10: clause (3) at `t = 0`** on area-carrying configurations (no open input). -/
theorem g4ZeroAStmt_holds : G4ZeroAStmt := by
  intro γ Ω _ P _ B Y hS hIn
  have hZ := Wire4.wedgeZeroRegStmt
  obtain ⟨hR, -⟩ := hZ γ P Y hS.1 hS.2.1 hS.2.2.2.1
  have hold := configLawFull_zipLenC_zero hZ hS hIn
  have hOff : configLawOff (fun ω => zipLenC γ 0 (wedgeConfig γ B Y ω)) P =
      configLawOff (wedgeConfig γ B Y) P := by
    refine D74.configLawOff_eq_of_configLawFull_eq hold (aemeasurable_cfgData_wedgeConfig hS hIn)
      (D74.wedge_configLawFull_ne_dirac hS hIn) ?_ (D74.ae_wedgeConfig_snd_good hS)
    filter_upwards [D74.ae_wedgeConfig_snd_good hS] with ω hω
    rw [zipLenC_of_nonneg le_rfl]
    exact D74.zipLenUpC_snd_good hω.1 hω.2 ⟨_, isLenWeldingDriver_zero_zero γ _⟩
  have hae : ∀ᵐ ω ∂P, (zipLenA γ 0 (wedgeAConfig γ B Y ω)).toPair =
      zipLenC γ 0 (wedgeConfig γ B Y ω) := by
    filter_upwards [hR] with ω hω
    exact toPair_zipLenA_zero rfl hω.1 hω.2
  rw [← hOff]
  unfold configLawOff
  exact Measure.map_congr (hae.mono fun ω hω => by simp only [hω])

end R18
end QuantumZipper
