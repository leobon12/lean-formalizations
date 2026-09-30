import QuantumZipper.Proofs.Zipper.UnifAWMain
import QuantumZipper.Proofs.Zipper.B5LRID

/-!
# UNIF-SW (1): AW needs no uniform-in-time global limits

Task UNIF-SW (decision D26). `anchorWindowStmt_of_conv` (UNIF-AW) takes `UnifGlobalStmt` (UG:
global vague limits of the boundary approximations of `h⁰_s` at **all** `s ∈ [0,T]`), but its
proof uses UG only at the rational times `r ∈ (0,T]` and at `T`. At each fixed time the global
limit exists (`B5.ae_nu0_regular`: `ν_{h⁰_r}` gives positive mass to every interval, so it is
not the junk `0`, so a limit exists), and there are countably many such times.

* `ae_global_rat`: a.s., global vague limits at every positive rational time and at `T`.
* **`anchorWindowStmt_of_conv_rat`**: AC ⇒ AW (no UG).
* **`anchorWindowStmt_of_cont_unif`**: AC-cont + AC-unif ⇒ AW (no UG).

This removes the circularity AW ← UG ← UO ← AW of the D26 plan. The argument is own
bookkeeping (a countable intersection of fixed-time events); the proof of
`anchorWindowStmt_of_conv_rat` is the proof of `anchorWindowStmt_of_conv` with UG replaced by
`ae_global_rat`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- At a fixed time `r > 0`, a.s. the boundary approximations of `h⁰_r` have a global limit. -/
theorem ae_global_fixed (hκ : 0 < κ) (hκ4 : κ < 4) {r : ℝ} (hr : 0 < r)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ r B X ω)) ν := by
  filter_upwards [B5.ae_nu0_regular RevCouplingReg.revCouplingBoundaryMeasureRegular hκ hκ4 hr
    hB hX hind] with ω hν
  by_contra h
  have h0 : qBoundaryMeasure (Real.sqrt κ) (h0f κ r B X ω) = 0 := by
    rw [qBoundaryMeasure, dif_neg h]
  have := hν.2.1 0 1 one_pos
  rw [h0] at this
  exact lt_irrefl _ this

/-- **UG at the rational times and at `T`** (fixed-time results, countably many times). -/
theorem ae_global_rat (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, (∀ r : ℚ, (0 : ℝ) < r →
        ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ r B X ω)) ν) ∧
      ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ T B X ω)) ν := by
  have h1 : ∀ᵐ ω ∂P, ∀ r : ℚ, (0 : ℝ) < r →
      ∃ ν, IsVagueLimitR (bdryApprox (Real.sqrt κ) (h0f κ r B X ω)) ν := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : (0 : ℝ) < r
    · filter_upwards [ae_global_fixed hκ hκ4 hr hB hX hind] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h hr
  filter_upwards [h1, ae_global_fixed hκ hκ4 hT hB hX hind] with ω h1 h2 using ⟨h1, h2⟩

/-- **AW from AC alone** (UG not needed). -/
theorem anchorWindowStmt_of_conv_rat (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hAC : AnchorConvStmt κ T P B X) : AnchorWindowStmt κ T P B X := by
  intro q hq hqT u v
  filter_upwards [hAC q hq hqT u v, ae_windows_rat hκ hκ4 hT hB hX hind,
    ae_global_rat hκ hκ4 hT hB hX hind,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hc hw hG hzm hcont hK hu huv hv s hs
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set γ := Real.sqrt κ
  have hzmle : ∀ r ∈ Icc (q : ℝ) T, zeroMinus V (T - q) ≤ zeroMinus V (T - r) := fun r hr =>
    hanti.antitoneOn ⟨by linarith [hr.2], by linarith [hr.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hr.1])
  have hlive : ∀ r ∈ Icc (q : ℝ) T, ∀ x ∈ Icc (u : ℝ) v, IsLive V (T - r) x := fun r hr x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hr.2]) (by linarith [hr.1, hq])
      ((hx.2.trans_lt hv).trans_le (hzmle r hr))).2
  have hνT := isVagueLimitR_qBoundaryMeasure hG.2
  have := hνT.1
  obtain ⟨μ, hμ, hμW⟩ := det_anchor (q := q) (T := T) huv
    (A := fun s => bdryApprox γ (h0f κ s B X ω)) (ν := fun r => qBoundaryMeasure γ (h0f κ r B X ω))
    (νT := qBoundaryMeasure γ (h0f κ T B X ω)) measure_Ioo_lt_top
    (F := fun s => realRevMap V (T - s))
    (fun r hr => exists_orderIso_eq_realRevMap hVc (by linarith [hr.2]) huv (hlive r hr))
    (fun r hr => isVagueLimitR_qBoundaryMeasure (hG.1 r (hq.trans_le hr.1)))
    (fun r hr a b ha hab hb => hw r (hq.trans_le hr.1) hr.2 a b (hu.trans_le ha) hab
      ((hb.trans_lt hv).trans_le (hzmle r hr)))
    (hc hu huv hv) s hs
  rw [CoordChange.qBoundaryMeasureOn_eq isOpen_Ioo hμ, hμW]
  exact hw q hq hqT u v hu huv hv

/-- **AW from AC-cont and AC-unif** (UG not needed). -/
theorem anchorWindowStmt_of_cont_unif (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hA : AnchorApproxContStmt κ T P B X) (hU : AnchorUnifCauchyStmt κ T P B X) :
    AnchorWindowStmt κ T P B X :=
  anchorWindowStmt_of_conv_rat hκ hκ4 hT hB hX hind (anchorConvStmt_of_unif hA hU)

end RegUnif
end QuantumZipper
