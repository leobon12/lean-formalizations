import QuantumZipper.Proofs.Thm18.R18UnzipArea
import QuantumZipper.Proofs.Thm18.R18Arc
import QuantumZipper.Proofs.Thm18.D74Headline
import QuantumZipper.Proofs.Zipper.AreaCoordBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T4: clause (3) of the paper-form Theorem 1.8 for `t < 0` (E6 on area-carrying configurations)

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26), zipper stationarity (3) for `Z^LEN_{−ℓ}`: the
rescaling (1.8) uses "the transformed quantum measure" (`zipLenDownA`, the carried area pushed
forward by the unzipping map). By the unzipping area rule (T3, `R18.unzipArea_holds`,
Duplantier–Sheffield 2011 Prop 2.1) that measure is a.s. the quantum area of the unzipped field on
every half-disc, so a.s. `zipLenDownA` agrees with the field-normalized open-arc map
`LocLen.zipLenDownArc` (`R18.toPair_zipLenDownA`), whose law invariance is `LocLen.E6StmtArc`
(`R18.e6StmtArc_of_X1`). The masked law follows by `D74.configLawOff_eq_of_configLawFull_eq`.
Wiring plus own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The length time is nonnegative. -/
theorem lenTimeOpen_nonneg (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) : 0 ≤ lenTimeOpen γ ℓ c :=
  Real.sInf_nonneg fun _ hs => hs.1

/-- The driver of the open-arc unzipping map is continuous and starts at `0`. -/
theorem zipLenDownArc_snd_good {γ ℓ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hc : Continuous c.2) :
    Continuous (LocLen.zipLenDownArc γ ℓ c).2 ∧ (LocLen.zipLenDownArc γ ℓ c).2 0 = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [LocLen.zipLenDownArc]
    exact ((hc.comp (continuous_const.add (continuous_const.mul
      (continuous_id.max continuous_const)))).sub continuous_const).div_const _
  · simp [LocLen.zipLenDownArc]

/-- **Scale agreement at the unzipping time**: if the unzipping area rule holds for `c` at time
`t`, the transported area and the unzipped field's own area give the same scale (1.8). -/
theorem areaScale_zipCapDownA_eq {γ t : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0) (ht : 0 ≤ t)
    (hA : ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ c.toPair t) S = c.area (fwdMapInv c.drv t '' S)) :
    areaScale (zipCapDownA γ t c).area = scaleParam γ (zipCapDown γ t c.toPair).1 := by
  have hS : ∀ a : ℝ, (zipCapDownA γ t c).area (Metric.ball 0 a ∩ H) =
      qAreaMeasure γ (unzippedField γ c.toPair t) (Metric.ball 0 a ∩ H) := fun a => by
    have hm : MeasurableSet (Metric.ball (0 : ℂ) a ∩ H) :=
      measurableSet_ball.inter isOpen_H.measurableSet
    show E6.areaTransport c.area c.drv t (Metric.ball 0 a ∩ H) = _
    rw [E6.areaTransport_apply hc hc0 ht c.area hm inter_subset_right,
      hA _ hm inter_subset_right]
  unfold areaScale scaleParam
  simp only [hS]
  rfl

/-- **T4: E6 on area-carrying configurations, from X1.** -/
theorem e6AStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : E6AStmt := by
  intro γ Ω _ P _ B Y hS hIn ℓ hℓ
  have hE := e6StmtArc_of_X1 hX1 (γ ^ 2) P Y B (isPStarSample_of_setting hS) ℓ hℓ
  rw [Real.sqrt_sq hS.1.le] at hE
  -- the field-normalized open-arc law statement, in the masked form
  have hOff : configLawOff (fun ω => LocLen.zipLenDownArc γ ℓ (wedgeConfig γ B Y ω)) P =
      configLawOff (wedgeConfig γ B Y) P := by
    refine D74.configLawOff_eq_of_configLawFull_eq hE (aemeasurable_cfgData_wedgeConfig hS hIn)
      (D74.wedge_configLawFull_ne_dirac hS hIn) ?_ (D74.ae_wedgeConfig_snd_good hS)
    filter_upwards [D74.ae_wedgeConfig_snd_good hS] with ω hω
    exact zipLenDownArc_snd_good hω.1
  -- a.s. the area-carrying map is the field-normalized one
  have hae : ∀ᵐ ω ∂P, (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair =
      LocLen.zipLenDownArc γ ℓ (wedgeConfig γ B Y ω) := by
    filter_upwards [unzipArea_holds γ P B Y hS, D74.ae_wedgeConfig_snd_good hS] with ω hA hω
    refine toPair_zipLenDownA (areaScale_zipCapDownA_eq hω.1 hω.2
      (lenTimeOpen_nonneg _ _ _) fun S hSm hSH => ?_)
    exact hA _ (lenTimeOpen_nonneg _ _ _) S hSm hSH
  rw [← hOff]
  unfold configLawOff
  exact Measure.map_congr (hae.mono fun ω hω => by simp only [hω])

end R18
end QuantumZipper
