import QuantumZipper.Proofs.Zipper.E6LocAbsDet
import QuantumZipper.Proofs.Section5.Prop16LocalRule
import QuantumZipper.Proofs.LQG.VagueUniqueOn
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# E6-LOCABS, deterministic part: `locRich R ∘ zipLenDown` is a function of `locRich R'`

Theorem 1.3, node E6 under D25. The deterministic half of B5 locality for the rich data
(`locRich_zipLenDown_eq_of_locRich_eq`): if two configurations have equal `locRich R'` data, the
first one satisfies the good-event bounds (driver bounded by `M` on `[0,T]`, side images `< a₀`,
the left length reaches `ℓ` by time `T`, the rescaling factor `a` is small) and both satisfy the
regularity conditions (continuous drivers vanishing at `0`, existing boundary and area limits of
the unzipped fields, left length `< ℓ` at time `0`), then their unzipped-and-rescaled
configurations have equal `locRich R` data.

Chain (own elementary bookkeeping; the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts
the locality without proof): equal stopping times (`hitTime_eq_of_locRich_eq`); circle agreement
of the unzipped fields near `0` (`circAgree_unzippedField_of_locRich_eq`); equal area measures
near `0` (transfer `Prop16Area.G.isVagueLimitOn_of_circAgree` and uniqueness
`isVagueLimitOn_unique`), hence equal scales (`scaleParam_eq_of_circAgree`, the infimum argument
of `D3Plus.scaleParam_eq_scaleParamOn_of_lt`); equal raw values of the rescaled fields at measures
carried by `closedBall 0 R ∩ ℍ̄` (`Prop16Area.G.evalReg_eq_of_circAgree`); equal drivers on
`[0, t + a²R]`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus

/-- A signed test density supported in `closedBall 0 R` gives a measure carried by `ballH R`. -/
theorem withDensity_ballH_compl {ρ : TestFun H} {R : ℕ} (hρ : suppIn R ρ) (sgn : ℝ) :
    (volume.withDensity fun z => ENNReal.ofReal (sgn * ρ.1 z)) (CircleFubini.ballH R)ᶜ = 0 := by
  have hc : Continuous ρ.1 := ρ.2.1.continuous
  have hmeas : Measurable fun z => ENNReal.ofReal (sgn * ρ.1 z) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hc.measurable)
  rw [withDensity_apply_eq_zero' hmeas.aemeasurable]
  convert measure_empty (μ := (volume : Measure ℂ))
  refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzc⟩ => hzc ?_
  have hz0 : ρ.1 z ≠ 0 := by
    intro h0; apply hz; simp [h0]
  have hts : z ∈ tsupport ρ.1 := subset_tsupport _ hz0
  exact ⟨hρ hts, H_subset_Hbar (ρ.2.2.2 hts)⟩

end QuantumZipper.E6
