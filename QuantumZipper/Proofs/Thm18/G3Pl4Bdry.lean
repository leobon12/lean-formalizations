import QuantumZipper.Proofs.Thm18.G3Pl4Ptw
import QuantumZipper.Proofs.Zipper.LocLenLocality
import QuantumZipper.Proofs.Thm18.G4WedgeCert

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): locality of the boundary measure

Two good fields agreeing on the folded circles inside the unit disc have the same boundary
measure on `[−1/2, 1/2]` (`g3pl4_restrict_eq_of_agree`): the boundary approximations on
`(−3/4, 3/4)` only read semicircle averages inside the unit disc (`avgReg_eq_of_circAgree`), so
the local boundary measures on `(−3/4, 3/4)` coincide (`qBoundaryMeasureOn_congr_of_eventually_avgReg`),
and each is the restriction of the global one (`isVagueLimitOnR_of_isVagueLimitR`). This is the
locality of the boundary measure (Duplantier–Sheffield, Invent. Math. 185 (2011), §6; Sheffield
arXiv:1012.4797, (1.5) and §5.1). Own bookkeeping on the cited lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

theorem g3pl4_restrict_eq_of_agree {γ : ℝ} {y y' : FieldSample} (hy : IsLQGGood γ y)
    (hy' : IsLQGGood γ y') (hag : FcAgree (ball (0 : ℂ) 1) y y') :
    (qBoundaryMeasure γ y).restrict (Icc (-(1 / 2)) (1 / 2)) =
      (qBoundaryMeasure γ y').restrict (Icc (-(1 / 2)) (1 / 2)) := by
  set V : Set ℝ := Ioo (-(3 / 4)) (3 / 4) with hVdef
  have hV : IsOpen V := isOpen_Ioo
  have e1 := LocalRule.qBoundaryMeasureOn_eq hV (LocLen.isVagueLimitOnR_of_isVagueLimitR
    (isVagueLimitR_qBoundaryMeasure_of_isLQGGood hy) hV)
  have e2 := LocalRule.qBoundaryMeasureOn_eq hV (LocLen.isVagueLimitOnR_of_isVagueLimitR
    (isVagueLimitR_qBoundaryMeasure_of_isLQGGood hy') hV)
  have hloc : qBoundaryMeasureOn γ y V = qBoundaryMeasureOn γ y' V := by
    refine LocLen.qBoundaryMeasureOn_congr_of_eventually_avgReg hV ?_
    obtain ⟨K, hK⟩ := AtomlessUncond.exists_radius_lt (c := 1 / 8) (by norm_num)
    filter_upwards [eventually_ge_atTop K] with k hk s hs
    refine avgReg_eq_of_circAgree hag.circAgree (show ((s : ℝ) : ℂ) ∈ Hbar by show (0 : ℝ) ≤ ((s : ℝ) : ℂ).im; simp) ?_
    intro z hz
    have hz1 := hz.1
    rw [mem_closedBall, dist_eq_norm] at hz1
    rw [mem_ball, dist_zero_right]
    have hs' : |s| < 3 / 4 := abs_lt.2 hs
    have hk' := hK k hk
    calc ‖z‖ = ‖(z - (s : ℂ)) + (s : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - (s : ℂ)‖ + ‖(s : ℂ)‖ := norm_add_le _ _
      _ = ‖z - (s : ℂ)‖ + |s| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ < 1 := by linarith
  have hsub : Icc (-(1 / 2) : ℝ) (1 / 2) ⊆ V := Icc_subset_Ioo (by norm_num) (by norm_num)
  rw [← Measure.restrict_restrict_of_subset hsub, ← e1, hloc, e2,
    Measure.restrict_restrict_of_subset hsub]

end R18
end QuantumZipper
