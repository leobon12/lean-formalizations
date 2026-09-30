import QuantumZipper.Proofs.Zipper.BaseFin2ULNrm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL-G: `BaseULGamma0MomStmt` from a one-point Gaussian bound

Proves `baseULGamma0_of_point : BaseULG0PointStmt → BaseULGamma0MomStmt`: Tonelli over the window
`[−n−1, n+1]` turns the first moment of the level-`k` boundary approximation into the integral of
the one-point bound `E[2^{-kγ²/4} e^{(γ/2) h_k(t)}] ≤ K e^{A|t|}` (`BaseULG0PointStmt`, a single
Gaussian computation for the `ϖ₀`-normalized `Γ⁰` field). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

/-- **(X1-UL-G1)** The one-point bound for the level-`k` density of the `ϖ₀`-normalized `Γ⁰`
field at a boundary point `t`. -/
def BaseULG0PointStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ A : ℝ, 0 ≤ A ∧ ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → RegUnif.IsNrmSample X → ∀ (k : ℕ) (t : ℝ),
    ∫⁻ ω, ENNReal.ofReal (radius k ^ (Real.sqrt κ ^ 2 / 4) * Real.exp (Real.sqrt κ / 2 *
        avgReg (ulShift (ofFun (h0rev κ) + X ω)) k (t : ℂ))) ∂P ≤
      K * ENNReal.ofReal (Real.exp (A * |t|))

theorem ul_window_bound (A : ℝ) (n : ℕ) :
    Real.exp (A * ((n : ℝ) + 1)) * ((n : ℝ) + 1 - -((n : ℝ) + 1)) ≤
      2 * Real.exp A * Real.exp ((A + 1) * n) := by
  have h1 : (n : ℝ) + 1 ≤ Real.exp n := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  have e : Real.exp ((A + 1) * n) = Real.exp (A * n) * Real.exp n := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (A * ((n : ℝ) + 1)) = Real.exp A * Real.exp (A * n) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, e2]
  have hp : 0 < Real.exp A * Real.exp (A * n) := by positivity
  nlinarith

/-- **`BaseULGamma0MomStmt` from the one-point bound.** -/
theorem baseULGamma0_of_point (h : BaseULG0PointStmt) : BaseULGamma0MomStmt := by
  intro κ hκ hκ4
  obtain ⟨A, hA, K, hK, hP⟩ := h κ hκ hκ4
  refine ⟨A + 1, K * ENNReal.ofReal (2 * Real.exp A),
    ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top, ?_⟩
  intro Ω _ P _ X hX hN k n
  set γ := Real.sqrt κ
  have hY : Measurable fun ω => ulShift (ofFun (h0rev κ) + X ω) :=
    measurable_ulShift.comp (measurable_pi_iff.2 fun μ => by
      simp only [Pi.add_apply]; exact measurable_const.add (hX.measurable_coord μ))
  let d : Ω → ℝ → ℝ≥0∞ := fun ω t => ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
    Real.exp (γ / 2 * avgReg (ulShift (ofFun (h0rev κ) + X ω)) k (t : ℂ)))
  have hd : Measurable (Function.uncurry d) := by
    have hj : Measurable fun p : Ω × ℝ =>
        avgReg (ulShift (ofFun (h0rev κ) + X p.1)) k (p.2 : ℂ) :=
      (measurable_avgReg k).comp ((hY.comp measurable_fst).prodMk
        (Complex.measurable_ofReal.comp measurable_snd))
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hj)))
  set I := Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) with hI
  calc ∫⁻ ω, bdryApprox γ (ulShift (ofFun (h0rev κ) + X ω)) k I ∂P
      = ∫⁻ ω, (∫⁻ t in I, d ω t) ∂P := by
        refine lintegral_congr fun ω => ?_
        unfold bdryApprox
        rw [withDensity_apply _ measurableSet_Icc]
    _ = ∫⁻ t in I, (∫⁻ ω, d ω t ∂P) := lintegral_lintegral_swap hd.aemeasurable
    _ ≤ ∫⁻ _ in I, K * ENNReal.ofReal (Real.exp (A * ((n : ℝ) + 1))) := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        refine (hP P X hX hN k t).trans ?_
        gcongr
        exact abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    _ = K * ENNReal.ofReal (Real.exp (A * ((n : ℝ) + 1))) *
          ENNReal.ofReal ((n : ℝ) + 1 - -((n : ℝ) + 1)) := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ ≤ K * ENNReal.ofReal (2 * Real.exp A) * ENNReal.ofReal (Real.exp ((A + 1) * n)) := by
        rw [mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_mul (by positivity)]
        exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (ul_window_bound A n)) bot_le

end BaseFin2
end QuantumZipper
