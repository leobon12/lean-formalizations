import QuantumZipper.Proofs.Zipper.B5VAssemble
import QuantumZipper.Proofs.Zipper.B2Uncond
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.Proofs.LQG.InfiniteMass

/-!
# B5-V at a fixed time: reduction to the coordinate-change windows of `h⁰_s`

Task B5V-FIX (`handoff/B5.md`, R1 (b)). By B2(b) (`B2.b2_regEq` at `t = T − s`), a.s.
`h⁰ = h⁰_T` and `coordChange h⁰_s (revMap V t) Q` have the same regularized circle averages, hence
the same boundary approximations; and `ν_{h⁰}` is a genuine vague limit (it is positive on
intervals, B3(a), `ae_nu0_regular`). So on each window the global `ν_{h⁰}` is the local boundary
measure of `coordChange h⁰_s (revMap V t) Q`:

* `ae_window_h0_eq_qBoundaryMeasureOn`;
* **`ae_b5v_fixed_of_coordChange`**: B5-V at the fixed time `s ∈ (0,T]` given, a.s. on rational
  live windows, the coordinate-change identity
  `ν^{loc}_{coordChange h⁰_s (revMap V t) Q}(u,v) = ν_{h⁰_s}(F u, F v)` (hypothesis `hcc`). For a
  fixed driver and `𝔥₀ + X'` in place of `h⁰_s` this identity is
  `B5.ae_qBoundaryMeasureOn_hFix_window`; `hcc` is its transfer to the pair
  `(h⁰_s, V|[0,t])`, which is independent (`B2.b2_markov`) — the E1-TR/M4 transfer shape.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem Yf_sub_eq_h0f (s : ℝ) (ω : Ω) : Yf κ T (T - s) B X ω = h0f κ s B X ω := by
  rw [Yf_eq_unzippedField, h0f_eq_unzippedField, sub_sub_cancel]

/-- A.s., on every window, `ν_{h⁰}` is the local boundary measure of
`coordChange h⁰_s (revMap V t) Q`, `t = T − s`. -/
theorem ae_window_h0_eq_qBoundaryMeasureOn (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ u v : ℝ,
      qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω) (Ioo u v) =
        qBoundaryMeasureOn (Real.sqrt κ)
          (coordChange (h0f κ s B X ω) (revMap (Vr κ T B ω) (T - s)) (Qc (Real.sqrt κ)))
          (Ioo u v) (Ioo u v) := by
  filter_upwards [b2_regEq (κ := κ) hB hX hind (sub_nonneg.2 hsT) (sub_le_self T hs),
    ae_nu0_regular hReg hκ hκ4 hT hB hX hind] with ω hreg hν u v
  set γ := Real.sqrt κ
  have hex : ∃ ν, IsVagueLimitR (bdryApprox γ (h0f κ T B X ω)) ν := by
    by_contra h
    have h0 : qBoundaryMeasure γ (h0f κ T B X ω) = 0 := by rw [qBoundaryMeasure, dif_neg h]
    have := hν.2.1 0 1 one_pos
    rw [h0] at this
    exact lt_irrefl _ this
  have hlim := E1.M4.isVagueLimitR_qBoundaryMeasure hex
  have hloc := InfMass.isVagueLimitOnR_restrict hlim (isOpen_Ioo (a := u) (b := v))
  have hb : bdryApprox γ (h0f κ T B X ω) = bdryApprox γ
      (coordChange (h0f κ s B X ω) (revMap (Vr κ T B ω) (T - s)) (Qc γ)) := by
    rw [← Yf_sub_eq_h0f s ω]
    exact Factorization.bdryApprox_congr (funext fun k => funext fun z => hreg k z) γ
  rw [hb] at hloc
  rw [LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hloc, Measure.restrict_apply_self]

/-- **B5-V at a fixed time `s ∈ (0,T]`, from the coordinate-change windows of `h⁰_s`.** -/
theorem ae_b5v_fixed_of_coordChange (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    (hcc : ∀ᵐ ω ∂P, ∀ u v : ℚ, zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - s) →
      qBoundaryMeasureOn (Real.sqrt κ)
          (coordChange (h0f κ s B X ω) (revMap (Vr κ T B ω) (T - s)) (Qc (Real.sqrt κ)))
          (Ioo u v) (Ioo u v) =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ s B X ω)
          (Ioo (realRevMap (Vr κ T B ω) (T - s) u) (realRevMap (Vr κ T B ω) (T - s) v))) :
    ∀ᵐ ω ∂P, (unzipLengths (Real.sqrt κ) (cfg κ B X ω) s).1 = lenRHS κ T B X ω s := by
  refine ae_b5v_fixed_of_windows hReg hRSS hκ hκ4 hB hX hind hs hsT ?_
  filter_upwards [hcc, ae_window_h0_eq_qBoundaryMeasureOn hReg hκ hκ4 hB hX hind hs.le hsT
    (hs.trans_le hsT)] with ω hc hw u v hu huv hv
  rw [hw]
  exact hc u v hu huv hv

end B5
end QuantumZipper
