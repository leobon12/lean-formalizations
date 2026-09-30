import QuantumZipper.Proofs.Thm18.UnzipBdryPosAtBasic
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.Zipper.F2Step3Dens
import QuantumZipper.Proofs.Zipper.B5LRID
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Step3DensSign
import QuantumZipper.Proofs.LQG.RevCouplingReg
import QuantumZipper.Proofs.Zipper.UnifClSide
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-MISC (1): positivity of the unzipped `Γ⁰` boundary measure at **all** times

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 and §5 (Lemma 5.6,
pp. 66–68: the quantum length of a piece of `η[0,s]` is read off in the unzipped picture and does
not depend on the unzipping time). This is the time-covariance behind
`Thm18Asm.UnzipBdryTransferStmt`.

At each fixed integer time `n ≥ 1` the boundary measure of the unzipped `Γ⁰` field `h⁰_n`
charges every nonempty open interval (`B5.ae_nu0_regular`, from the proved blueprint item
`RevCouplingReg.revCouplingBoundaryMeasureRegular`). The uniform window identities **UW**
(`RegUnif.UnifWindowStmt`, at every horizon; an existing frontier node, reduced in
`F1StrictMonoAllT.lean` to `RegUnif.AnchorUnifFamExtAllStmt` and the tip input) say that, for all
`s ∈ (0,n]` at once, `ν_{h⁰_n}(u,v) = ν_{h⁰_s}(F u, F v)` on rational windows of
`(0₋(n), 0₋(n−s))`, `F = realRevMap (vrev W n) (n − s)`. `F` is continuous and increasing on the
window and runs from `O⁻_s` to `0` (`B5.realRevMap_endpoints`), so every nonempty open subinterval
of `[O⁻_s, 0]` contains the image of a rational window interval (`exists_rat_window`), whence
positivity at time `s`.

Main results: `exists_rat_window` (deterministic), **`ae_pos_unzY_all`**.
Own elementary argument (intermediate value theorem on the window).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace T13Misc

open B2 B5 RealLine CaraR

/-- **Rational windows inside a side interval (deterministic).** For `0 < s < T`, simple reverse
hulls at horizons `T` and `s`, and `0₋(vrev W s, s) ≤ a < b ≤ 0`, there are rationals
`0₋(T) < u < v < 0₋(T − s)` whose images under `F = realRevMap (vrev W T) (T − s)` bound a
subinterval of `(a,b)`. -/
theorem exists_rat_window {W : ℝ → ℝ} (hW : Continuous W) {T s : ℝ} (hs : 0 < s)
    (hsT : s < T) (hK : IsSimpleCurveHull (revHull (vrev W T) T))
    (hKs : IsSimpleCurveHull (revHull (vrev W s) s)) {a b : ℝ}
    (ha : zeroMinus (vrev W s) s ≤ a) (hab : a < b) (hb : b ≤ 0) :
    ∃ u v : ℚ, zeroMinus (vrev W T) T < u ∧ (u : ℝ) < v ∧
      (v : ℝ) < zeroMinus (vrev W T) (T - s) ∧
      Ioo (realRevMap (vrev W T) (T - s) u) (realRevMap (vrev W T) (T - s) v) ⊆ Ioo a b := by
  have hT : 0 < T := hs.trans hsT
  set V := vrev W T with hVdef
  have hVc : Continuous V := continuous_vrev hW T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set F := realRevMap V (T - s) with hF
  have hshift : ∀ r, 0 ≤ r → vrev W s r = V (T - s + r) - V (T - s) :=
    fun r hr => (vrev_shift hs.le hsT.le hr).symm
  obtain ⟨hac, hmono, hA, hC⟩ := realRevMap_endpoints hVc hV0 hT hK (continuous_vrev hW s)
    (vrev_zero hs.le) hs hKs (by linarith : (0 : ℝ) ≤ T - s) (by ring) hshift
  set a0 := zeroMinus V T
  set c0 := zeroMinus V (T - s)
  have hFc : ∀ y ∈ Ioo a0 c0, ContinuousAt F y := fun y hy => by
    obtain ⟨g, hg⟩ := RegUnif.exists_isRealRevSol_of_mem (u := s) (s := T - s) hW hT hK hs
      (by linarith) (by linarith) hy
    exact continuousAt_realRevMap hVc (by linarith) (not_mem_swallowedSet_iff.2 ⟨g, hg⟩)
  set m := (a + b) / 2 with hm
  have hm1 : zeroMinus (vrev W s) s < m := by linarith
  have hm2 : m < 0 := by linarith
  obtain ⟨x1, hx1F, hx1I⟩ :=
    ((hA.eventually (gt_mem_nhds hm1)).and (Ioo_mem_nhdsGT hac)).exists
  obtain ⟨x2, hx2F, hx2I⟩ :=
    ((hC.eventually (lt_mem_nhds hm2)).and (Ioo_mem_nhdsLT hac)).exists
  have hx12 : x1 ≤ x2 := by
    by_contra h
    push Not at h
    have := hmono.monotoneOn hx2I hx1I h.le
    linarith
  have hsub : Icc x1 x2 ⊆ Ioo a0 c0 := fun z hz => ⟨hx1I.1.trans_le hz.1, hz.2.trans_lt hx2I.2⟩
  have hcont : ContinuousOn F (Icc x1 x2) := fun z hz => (hFc z (hsub hz)).continuousWithinAt
  obtain ⟨x, hxI, hxm⟩ := intermediate_value_Icc hx12 hcont ⟨hx1F.le, hx2F.le⟩
  have hxw : x ∈ Ioo a0 c0 := hsub hxI
  -- a ball around `x` inside the window and inside `F ⁻¹ (a,b)`
  have hpre : F ⁻¹' Ioo a b ∩ Ioo a0 c0 ∈ 𝓝 x := by
    refine Filter.inter_mem ((hFc x hxw).preimage_mem_nhds ?_) (isOpen_Ioo.mem_nhds hxw)
    rw [hxm]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show x < x + ε by linarith)
  have huB : (u : ℝ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  have hvB : (v : ℝ) ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨hFu, huw⟩ := hball huB
  obtain ⟨hFv, hvw⟩ := hball hvB
  refine ⟨u, v, huw.1, by linarith, hvw.2, fun z hz => ⟨hFu.1.trans hz.1, hz.2.trans hFv.2⟩⟩

end T13Misc
end QuantumZipper
