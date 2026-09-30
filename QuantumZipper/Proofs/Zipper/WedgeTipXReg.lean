import QuantumZipper.Proofs.Zipper.WedgeTipXKoebe
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.WedgeXGoodBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TIP-X split: part (1) from a deterministic regularity lemma, part (2) named

`TipXStmt` (`WedgeXGoodBasic.lean`) has two conjuncts. We split it:

* **Part (1)** (`TipXRegStmt`, regularity of `ofFun ψ_t` with its circle averages). We prove it
  (`tipXReg_of_logImDomReg`) from the purely deterministic real-analysis statement
  `LogImDomRegStmt`: *a function `g` continuous on `ℍ` with `|g v| ≤ A_R + B_R |log Im v|` on
  bounded sets is regular with its own circle averages as witness.* The domination for
  `g = ψ_t = −γ log ‖E_t‖` holds for **every** `t ≥ 0` (`abs_logTipFun_le`):
  - upper bound on `‖E_t‖`: continuity of `E_t` on `ℍ̄` (core C, `globalCaraStmt_holds`);
  - lower bound `‖E_t u‖ ≥ c (Im u)^N`: Koebe (`exists_pow_le_norm_fwdMapInv`).
  So part (1) needs no SLE-specific input beyond core C.
* **Part (2)** (`TipXSmallStmt`): the uniform smallness of the approximate boundary measures of
  `x_t` near the tips; kept as a named statement (the probabilistic core, see the report).

`tipX_of_parts : TipXRegStmt → TipXSmallStmt → TipXStmt` is bookkeeping.

Why `LogImDomRegStmt` is true (planned proof, own argument; the standard tool is dominated
convergence): a folded circle `fc(z, r)`, `r > 0`, meets `ℝ` in at most two points, and
`θ ↦ |log |Im z + r sin θ||` is integrable with integral continuous in `(z, r)`; this gives
continuity of the circle averages by generalized dominated convergence, and the local uniform
smoothing limit by uniform continuity of `g` on compact subsets of `ℍ` plus the uniform smallness
of `∫ |log Im|` over `{Im ≤ η}` under the (smoothed) circle measures.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- **(Deterministic, named) Log-dominated functions are regular.** A function continuous on the
open upper half-plane whose size is at most `A + B |log Im v|` on bounded sets is regular, with
its own circle averages as witness. -/
def LogImDomRegStmt : Prop :=
  ∀ g : ℂ → ℝ, ContinuousOn g {v : ℂ | 0 < v.im} →
    (∀ R : ℝ, 0 < R → ∃ A B : ℝ, ∀ v : ℂ, 0 < v.im → ‖v‖ ≤ R →
      |g v| ≤ A + B * |Real.log v.im|) →
    IsRegularWith (ofFun g) (fun q => ∫ v, g v ∂foldedCircle q.1 q.2)

/-- **TIP-X part (1).** -/
def TipXRegStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsRegularWith (ofFun (logTipFun κ (drive κ B ω) t))
        (fun q => ∫ v, logTipFun κ (drive κ B ω) t v ∂foldedCircle q.1 q.2)

/-! ## The domination of `ψ_t` -/

section Det

variable {W : ℝ → ℝ}

theorem extInv_eq_fwdMapInv {t : ℝ} {v : ℂ} (hv : 0 < v.im) :
    F2.extInv W t v = fwdMapInv W t v := by
  simp [F2.extInv, hv]

theorem continuousOn_logTipFun (κ : ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : ContinuousOn (logTipFun κ W t) {v : ℂ | 0 < v.im} := by
  have hc : ContinuousOn (fwdMapInv W t) {v : ℂ | 0 < v.im} :=
    (RS.differentiableOn_fwdMapInv hW hW0 ht).continuousOn
  have hne : ∀ v ∈ {v : ℂ | 0 < v.im}, ‖fwdMapInv W t v‖ ≠ 0 := fun v hv h => by
    have := RS.fwdMapInv_mem_H hW hW0 ht (w := v) hv
    rw [norm_eq_zero.1 h] at this; simp [H] at this
  have h2 : ContinuousOn (fun v => -(Real.sqrt κ * Real.log ‖fwdMapInv W t v‖))
      {v : ℂ | 0 < v.im} :=
    ((continuousOn_const.mul (hc.norm.log hne))).neg
  refine h2.congr fun v hv => ?_
  simp only [logTipFun, extInv_eq_fwdMapInv (W := W) (t := t) hv]

/-- **The domination** `|ψ_t v| ≤ A + B |log Im v|` on bounded subsets of `ℍ`, for every
`t ≥ 0`, given continuity of `E_t` on `ℍ̄`. -/
theorem abs_logTipFun_le (κ : ℝ) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hC : ContinuousOn (F2.extInv W t) Hbar) {R : ℝ} (hR : 0 < R) :
    ∃ A B : ℝ, ∀ v : ℂ, 0 < v.im → ‖v‖ ≤ R →
      |logTipFun κ W t v| ≤ A + B * |Real.log v.im| := by
  obtain ⟨c, hc, N, hN⟩ := exists_pow_le_norm_fwdMapInv hW hW0 ht hR hR.le
  have hK : IsCompact (closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Complex.continuous_im)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hC.mono inter_subset_right)
  refine ⟨Real.sqrt κ * (|Real.log c| + |Real.log M|), Real.sqrt κ * N, fun v hv hvR => ?_⟩
  have hre : |v.re| ≤ R := (Complex.abs_re_le_norm v).trans hvR
  have him : v.im ≤ R := (le_abs_self _).trans ((Complex.abs_im_le_norm v).trans hvR)
  have hlow := hN v hv him hre
  have hmem : v ∈ closedBall (0 : ℂ) R ∩ Hbar := ⟨by simpa using hvR, le_of_lt hv⟩
  have hup := hM v hmem
  rw [extInv_eq_fwdMapInv hv] at hup
  set e := ‖fwdMapInv W t v‖ with he
  have hcy : 0 < c * v.im ^ N := by positivity
  have he0 : 0 < e := hcy.trans_le hlow
  have hM0 : 0 < M := he0.trans_le hup
  have hlog1 : Real.log (c * v.im ^ N) ≤ Real.log e := Real.log_le_log hcy hlow
  have hlog2 : Real.log e ≤ Real.log M := Real.log_le_log he0 hup
  rw [Real.log_mul hc.ne' (by positivity), Real.log_pow] at hlog1
  have habs : |Real.log e| ≤ |Real.log c| + |Real.log M| + N * |Real.log v.im| := by
    rw [abs_le]
    have h1 := neg_abs_le (Real.log c)
    have h2 := le_abs_self (Real.log M)
    have h3 := neg_abs_le (Real.log v.im)
    have h4 := abs_nonneg (Real.log c)
    have h5 := abs_nonneg (Real.log v.im)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h6 : 0 ≤ (N : ℝ) * Real.log v.im + N * |Real.log v.im| := by
      rw [← mul_add]; exact mul_nonneg hN0 (by linarith)
    have h7 : 0 ≤ (N : ℝ) * |Real.log v.im| := mul_nonneg hN0 h5
    have h8 := abs_nonneg (Real.log M)
    constructor <;> linarith
  have hv' : logTipFun κ W t v = -(Real.sqrt κ * Real.log e) := by
    simp only [logTipFun, extInv_eq_fwdMapInv (W := W) (t := t) hv, he]
  rw [hv', abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
  have hs := Real.sqrt_nonneg κ
  calc Real.sqrt κ * |Real.log e|
      ≤ Real.sqrt κ * (|Real.log c| + |Real.log M| + N * |Real.log v.im|) :=
        mul_le_mul_of_nonneg_left habs hs
    _ = _ := by ring

end Det

/-- **TIP-X part (1) from the deterministic regularity lemma** (with core C proved). -/
theorem tipXReg_of_logImDomReg (hL : LogImDomRegStmt) : TipXRegStmt := by
  intro κ hκ hκ4 Ω _ P _ B hB
  filter_upwards [globalCaraStmt_holds κ hκ hκ4 P B hB, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hC hc h0 t ht
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  exact hL _ (continuousOn_logTipFun κ hWc hW0 ht)
    fun R hR => abs_logTipFun_le κ hWc hW0 ht (hC t ht) hR

end WedgeUnzip
end QuantumZipper
