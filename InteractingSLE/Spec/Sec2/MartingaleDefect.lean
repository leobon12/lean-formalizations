import InteractingSLE.Spec.Sec2.MartingaleLevy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# The singular force-point defects (deterministic part of Theorem 2.4)

Packet PROVE-SEC2-MART. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md`, anchor
`thm-2.4-proof`, L842–L854; graph node `SPEC.thm-2.4#singular-defects`): for a force-point path `V`
(continuous, monotone, `dV = 2/(V − W) dt` away from its Lebesgue-null collision set),

* the reciprocal gap is integrable and, by monotonicity, `∫ₐᵇ |2/(V − W)| ≤ |V_b − V_a|`;
* the defect `I_t = V_t − V_0 − ∫₀ᵗ 2/(V − W) ds` is monotone in the same direction as `V` and
  constant on every interval without collision ("its Stieltjes measure is supported on `Zⱼ`").

These are the inputs (`j`, `ψ`) of the Tanaka argument of PROVE-TANAKA.

## Main results

* `IsForcePath.intervalIntegrable_gap`, `IsForcePath.integral_gap_mem_uIcc`,
  `IsForcePath.integral_abs_gap_le`;
* `IsForcePath.intervalIntegrable_inv_sub`: the frozen form `(w − v)⁻¹` of the integrability clause;
* `IsForcePath.forceDefect_sub_mem_uIcc`, `IsForcePath.forceDefect_eq_of_forall_ne`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal Interval

namespace InteractingSLE

namespace MartChar

variable {w v : ℝ≥0 → ℝ}

/-- The derivative of a monotone or antitone function is integrable with integral between `0` and
the increment. -/
lemma intervalIntegral_deriv_mem_of_monotoneOn_or_antitoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    IntervalIntegrable (deriv f) volume a b ∧ ∫ x in a..b, deriv f x ∈ uIcc 0 (f b - f a) := by
  rcases hf with hf | hf
  · rw [← uIcc_of_le hab] at hf
    exact ⟨hf.intervalIntegrable_deriv, hf.intervalIntegral_deriv_mem_uIcc⟩
  · have hg : MonotoneOn (fun x => -f x) (uIcc a b) := by rw [uIcc_of_le hab]; exact hf.neg
    have hd : deriv (fun x => -f x) = fun x => -deriv f x := by
      funext x; exact deriv.neg
    have h1 := hg.intervalIntegrable_deriv
    have h2 := hg.intervalIntegral_deriv_mem_uIcc
    rw [hd] at h1 h2
    refine ⟨by convert h1.neg using 1; funext x; simp, ?_⟩
    rw [intervalIntegral.integral_neg] at h2
    rw [mem_uIcc] at h2 ⊢
    rcases h2 with h | h <;> [right; left] <;> constructor <;> linarith [h.1, h.2]

/-- The extension of a path on `ℝ≥0` to `ℝ`. -/
def realPath (v : ℝ≥0 → ℝ) : ℝ → ℝ := fun s => v s.toNNReal

lemma IsForcePath.monotoneOn_or_antitoneOn (hv : IsForcePath w v) (a b : ℝ) :
    MonotoneOn (realPath v) (Icc a b) ∨ AntitoneOn (realPath v) (Icc a b) := by
  rcases hv.2.1 with h | h
  · exact Or.inl ((h.comp fun _ _ hxy => Real.toNNReal_le_toNNReal hxy).monotoneOn _)
  · exact Or.inr ((h.comp_monotone fun _ _ hxy => Real.toNNReal_le_toNNReal hxy).antitoneOn _)

/-- Off the collision set, the reciprocal gap is the derivative of the force-point path. -/
lemma IsForcePath.ae_gap_eq_deriv (hv : IsForcePath w v) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ s ∂(volume.restrict (Ι a b)), 2 / (v s.toNNReal - w s.toNNReal) = deriv (realPath v) s := by
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hv.2.2.2] with s hs hsI
  rw [uIoc_of_le hab] at hsI
  have hpos : 0 < s := ha.trans_lt hsI.1
  have hne : v s.toNNReal ≠ w s.toNNReal := fun h => hs ⟨hpos.le, h⟩
  exact ((hv.2.2.1 s hpos hne).deriv).symm

/-- **The reciprocal gap is integrable** on every `[a, b] ⊆ [0, ∞)`. -/
theorem IsForcePath.intervalIntegrable_gap (hv : IsForcePath w v) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume a b := by
  have h := (intervalIntegral_deriv_mem_of_monotoneOn_or_antitoneOn hab
    (hv.monotoneOn_or_antitoneOn a b)).1
  rw [intervalIntegrable_iff] at h ⊢
  exact h.congr (Filter.EventuallyEq.symm (hv.ae_gap_eq_deriv ha hab))

/-- **The integral of the reciprocal gap lies between `0` and the increment of the path.** -/
theorem IsForcePath.integral_gap_mem_uIcc (hv : IsForcePath w v) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ s in a..b, 2 / (v s.toNNReal - w s.toNNReal) ∈ uIcc 0 (v b.toNNReal - v a.toNNReal) := by
  have h := (intervalIntegral_deriv_mem_of_monotoneOn_or_antitoneOn hab
    (hv.monotoneOn_or_antitoneOn a b)).2
  have hae := (ae_restrict_iff' measurableSet_uIoc).1 (hv.ae_gap_eq_deriv ha hab)
  rw [intervalIntegral.integral_congr_ae hae]
  exact h

/-- The reciprocal gap has the sign of the monotonicity of the path at every positive time. -/
lemma IsForcePath.gap_sign (hv : IsForcePath w v) {s : ℝ} (hs : 0 < s) :
    (Monotone v → 0 ≤ 2 / (v s.toNNReal - w s.toNNReal)) ∧
      (Antitone v → 2 / (v s.toNNReal - w s.toNNReal) ≤ 0) := by
  by_cases hne : v s.toNNReal = w s.toNNReal
  · rw [hne, sub_self, div_zero]; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  have hd := hv.2.2.1 s hs hne
  refine ⟨fun hm => hd.nonneg_of_monotone (hm.comp fun _ _ hxy => Real.toNNReal_le_toNNReal hxy),
    fun ha => ?_⟩
  have hd' := hd.neg
  have := hd'.nonneg_of_monotone (g := fun x => -v x.toNNReal)
    (fun x y hxy => neg_le_neg (ha (Real.toNNReal_le_toNNReal hxy)))
  linarith

/-- **`∫ₐᵇ |2/(V − W)| ≤ |V_b − V_a|`** (Specification p. 36, "Monotonicity therefore gives"). -/
theorem IsForcePath.integral_abs_gap_le (hv : IsForcePath w v) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ s in a..b, |2 / (v s.toNNReal - w s.toNNReal)| ≤ |v b.toNNReal - v a.toNNReal| := by
  have hmem := mem_uIcc.1 (hv.integral_gap_mem_uIcc ha hab)
  have hΔ := le_abs_self (v b.toNNReal - v a.toNNReal)
  have hΔ' := neg_abs_le (v b.toNNReal - v a.toNNReal)
  have h0 := abs_nonneg (v b.toNNReal - v a.toNNReal)
  rcases hv.2.1 with hm | hm
  · have hcg : ∀ᵐ s ∂volume, s ∈ Ι a b → |2 / (v s.toNNReal - w s.toNNReal)|
        = 2 / (v s.toNNReal - w s.toNNReal) := Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      exact abs_of_nonneg ((hv.gap_sign (ha.trans_lt hs.1)).1 hm)
    rw [intervalIntegral.integral_congr_ae hcg]
    rcases hmem with h | h <;> linarith [h.1, h.2]
  · have hcg : ∀ᵐ s ∂volume, s ∈ Ι a b → |2 / (v s.toNNReal - w s.toNNReal)|
        = -(2 / (v s.toNNReal - w s.toNNReal)) := Eventually.of_forall fun s hs => by
      rw [uIoc_of_le hab] at hs
      exact abs_of_nonpos ((hv.gap_sign (ha.trans_lt hs.1)).2 hm)
    rw [intervalIntegral.integral_congr_ae hcg, intervalIntegral.integral_neg]
    rcases hmem with h | h <;> linarith [h.1, h.2]

/-- The integrability clause of the frozen `IsIntegratedSLEPath`, `(w − v)⁻¹`. -/
theorem IsForcePath.intervalIntegrable_inv_sub (hv : IsForcePath w v) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t := by
  have h := (hv.intervalIntegrable_gap le_rfl (NNReal.coe_nonneg t)).const_mul (-(1 / 2))
  refine h.congr ?_
  intro s _
  simp only
  rcases eq_or_ne (v s.toNNReal - w s.toNNReal) 0 with h0 | h0
  · have : w s.toNNReal - v s.toNNReal = 0 := by linarith
    rw [h0, this, div_zero, mul_zero, inv_zero]
  · have h1 : w s.toNNReal - v s.toNNReal = -(v s.toNNReal - w s.toNNReal) := by ring
    rw [h1, inv_neg]
    field_simp

/-- The singular defect `I_t = V_t − V_0 − ∫₀ᵗ 2/(V − W)` of a force-point path. -/
def forceDefect (w v : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  v t - v 0 - ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)

/-- **The defect moves in the direction of the path**: its increment lies between `0` and the
increment of `V`. -/
theorem IsForcePath.forceDefect_sub_mem_uIcc (hv : IsForcePath w v) {a b : ℝ≥0} (hab : a ≤ b) :
    forceDefect w v b - forceDefect w v a ∈ uIcc 0 (v b - v a) := by
  have hab' : (a : ℝ) ≤ b := hab
  have h1 := hv.intervalIntegrable_gap le_rfl (NNReal.coe_nonneg a)
  have h2 := hv.intervalIntegrable_gap (NNReal.coe_nonneg a) hab'
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hmem := hv.integral_gap_mem_uIcc (NNReal.coe_nonneg a) hab'
  simp only [Real.toNNReal_coe] at hmem
  have heq : forceDefect w v b - forceDefect w v a
      = (v b - v a) - ∫ s in (a : ℝ)..b, 2 / (v s.toNNReal - w s.toNNReal) := by
    simp only [forceDefect]
    rw [← hsplit]
    ring
  rw [heq]
  rw [mem_uIcc] at hmem ⊢
  rcases hmem with h | h
  · left; constructor <;> linarith [h.1, h.2]
  · right; constructor <;> linarith [h.1, h.2]

/-- **The defect is constant on every interval without collision.** -/
theorem IsForcePath.forceDefect_eq_of_forall_ne (hv : IsForcePath w v) {a b : ℝ≥0} (hab : a ≤ b) (hne : ∀ u ∈ Icc a b, v u ≠ w u) :
    forceDefect w v b = forceDefect w v a := by
  have hab' : (a : ℝ) ≤ b := hab
  have h1 := hv.intervalIntegrable_gap le_rfl (NNReal.coe_nonneg a)
  have h2 := hv.intervalIntegrable_gap (NNReal.coe_nonneg a) hab'
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hcont : ContinuousOn (realPath v) (Icc (a : ℝ) b) :=
    (hv.1.comp continuous_real_toNNReal).continuousOn
  have hftc : ∫ s in (a : ℝ)..b, 2 / (v s.toNNReal - w s.toNNReal)
      = realPath v b - realPath v a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab' hcont (fun s hs => ?_) h2
    have hpos : 0 < s := (NNReal.coe_nonneg a).trans_lt hs.1
    refine hv.2.2.1 s hpos ?_
    refine hne s.toNNReal ⟨?_, ?_⟩
    · exact Real.le_toNNReal_iff_coe_le hpos.le |>.2 hs.1.le
    · exact Real.toNNReal_le_iff_le_coe.2 hs.2.le
  simp only [realPath, Real.toNNReal_coe] at hftc
  simp only [forceDefect]
  rw [← hsplit, hftc]
  ring

end MartChar

end InteractingSLE
