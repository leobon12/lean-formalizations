/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStep44Reduction
import InteractingSLE.Spec.Sec5.QSchedWire
import InteractingSLE.Spec.Wire.Thm12DawnRestart

/-!
# The proved (4.4) leaves and their restart consumers

Packet PROVE-CFCHART2. Integrability and the zero-prefix leaf are proved. The
positive physical member leaf and the previously selected base's separation
remain explicit; reflection is the separate schedule-side input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfStep

open CfGiven Exist Exist.Staged Exist.StagedLaw Restart
open Sec7.StripHeights44 (IsHeightBounded44)

/-- The existing selected-base reduction leaf follows if that same selected
base retains separation and its zero seeds. This is an explicit conditional adapter. -/
theorem converted44ReductionOn_of_separated (hBase : QSched.PositiveChartBase44Statement.{u})
    (hsep : ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u}
      [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
      (hh : IsGFFWithBoundaryData P h b J) (hcf : IsCenteredCounterflowDriver κ P h W ζ)
      (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (θ : ℝ) (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
      (hθh : IsHeightBounded44 κ b J θ) (hπh : IsHeightBounded44 κ b J (π / 2))
      (D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
      (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
      (s : ℝ≥0) (hs : 0 < s) (η : Ω → ℝ≥0 → ℂ)
      (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (η ω)),
      Wire.Dawn.ChartSeparated P (Classical.choose
        (hBase κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s hs η hη))) :
    QSched.Converted44ReductionOn hBase := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s hs η hη
  exact Wire.Dawn.chartReduction_of_separated hκ _
    (hsep κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ hθh hπh D hDm hDreg hD s hs η hη)

/-- The proved (4.4) integrability leaf also closes the original Night integrability leaf. -/
theorem convertedIntegrableOn (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : Wire.Night.ConvertedIntegrableOn.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη φ
  have hπ : π / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  exact converted44IntegrableOn hA href κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hθ)
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hπ) D hDm hDreg hD s hs η hη φ

/-- The proved (4.4) zero-prefix leaf also closes the original Night zero-prefix leaf. -/
theorem zeroChartStatement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : Wire.Night.ZeroChartStatement.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD η hη
  have hπ : π / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  exact zeroChart44Statement hA href κ b J P h W ζ hκ hκ4 hb hh hcf hζ θ hθ
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hθ)
    (QSched.isHeightBounded44_of_uniform hκ hκ4 hleft hright hπ) D hDm hDreg hD η hη

/-- The upper (4.4) chart statement after discharging integrability and zero prefix.
The two remaining selected-base leaves are named with their exact types. -/
theorem cfGivenChart44Up_of_remaining (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hRed : QSched.Converted44ReductionOn (QSched.positiveChartBase44Statement hA href))
    (hLoc : QSched.Converted44LocalOn (QSched.positiveChartBase44Statement hA href)) :
    QSched.CfGivenChart44UpStatement.{u} :=
  QSched.cfGivenChart44Up_of_converted _ (converted44IntegrableOn hA href) hRed hLoc
    (zeroChart44Statement hA href)

/-- The schedule's first-hit theorem with only the remaining chart leaves and
the separate reflection input, besides its existing (4.4) and Lemma 4.7 inputs. -/
theorem qScheduleFirstHitStatement_of_remaining
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hRed : QSched.Converted44ReductionOn (QSched.positiveChartBase44Statement hA href))
    (hLoc : QSched.Converted44LocalOn (QSched.positiveChartBase44Statement hA href))
    (hDn : QSched.CfGivenChart44DownStatement.{u}) : FrameQ.QScheduleFirstHitStatement.{u} :=
  QSched.qScheduleFirstHitStatement_of_leaves h44 h47 hA href
    (converted44IntegrableOn hA href) hRed hLoc (zeroChart44Statement hA href) hDn

end InteractingSLE.Sec5.CfStep
