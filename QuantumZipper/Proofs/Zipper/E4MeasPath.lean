import QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# E4-MEAS (part 1): a measurable path map `(ℝ≥0 → ℝ) → C([0,t], ℝ)`

`handoff/E-PLAN-2.md`, node E4-MEAS. The path data `(V^t, W⁰)` of the Palm-zip statements live in
`ℝ≥0 → ℝ` with the product σ-algebra, while the measurability lemmas for the Loewner flow
(`CharFun.measurable_Fm`, `UnzipFullSplit.measurable_evalReg_push_gen`,
`B1Full.measurable_integral_log_deriv_gen`) take the driver as a point of `C([0,t], ℝ)` (via
`CharFun.Wof`). Here we build a map `stopPath t : (ℝ≥0 → ℝ) → C([0,t], ℝ)` which is measurable for
the product σ-algebra and restricts every continuous `f` to `[0,t]`:
`stopPath t f = limUnder (Bernstein approximations of u ↦ f (t u))`, rescaled to `[0,t]`.

* `measurable_stopPath`, `stopPath_apply`, `eqOn_Wof_stopPath`.

The Bernstein approximations depend on finitely many values of `f` and converge uniformly for
continuous `f` (mathlib `bernsteinApproximation_uniform`, S. Bernstein 1912; Beals, *Analysis, an
introduction*, §7D). The construction is own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set unitInterval
open scoped Topology NNReal

namespace QuantumZipper
namespace E4Meas

/-- The `n`-th Bernstein approximation of the path `u ↦ f (t u)` on `[0,1]`. -/
def bernPath (t : ℝ) (n : ℕ) (f : ℝ≥0 → ℝ) : C(I, ℝ) :=
  ∑ k : Fin (n + 1), bernstein n k • ContinuousMap.const I (f (t * (bernstein.z k : ℝ)).toNNReal)

theorem measurable_bernPath (t : ℝ) (n : ℕ) : Measurable (bernPath t n) := by
  refine ContinuousMap.measurable_iff_eval.2 fun x => ?_
  simp only [bernPath, ContinuousMap.coe_sum, Finset.sum_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply _)

/-- The limit of the Bernstein approximations (junk if it does not exist). -/
def limPath (t : ℝ) (f : ℝ≥0 → ℝ) : C(I, ℝ) := limUnder atTop fun n => bernPath t n f

theorem measurable_limPath (t : ℝ) : Measurable (limPath t) :=
  (StronglyMeasurable.limUnder fun n => (measurable_bernPath t n).stronglyMeasurable).measurable

/-- The rescaled path `u ↦ f (t u)` of a continuous `f`. -/
def scalePath (t : ℝ) (f : ℝ≥0 → ℝ) (hf : Continuous f) : C(I, ℝ) :=
  ⟨fun u => f (t * (u : ℝ)).toNNReal,
    hf.comp (continuous_real_toNNReal.comp (continuous_const.mul continuous_subtype_val))⟩

theorem limPath_eq {t : ℝ} {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    limPath t f = scalePath t f hf :=
  (bernsteinApproximation_uniform (scalePath t f hf)).limUnder_eq

/-- `[0,t] → [0,1]`, `s ↦ s/t` (clamped; `0` if `t = 0`). -/
def toUnit (t : ℝ) : C(Icc (0 : ℝ) t, I) :=
  ⟨fun s => projIcc 0 1 zero_le_one ((s : ℝ) / t),
    continuous_projIcc.comp (continuous_subtype_val.div_const t)⟩

theorem mul_toUnit {t : ℝ} (s : Icc (0 : ℝ) t) : t * (toUnit t s : ℝ) = s := by
  rcases s with ⟨s, hs0, hst⟩
  show t * (projIcc 0 1 zero_le_one (s / t) : ℝ) = s
  rcases (hs0.trans hst).eq_or_lt with rfl | ht
  · simp [le_antisymm hst hs0]
  · rw [projIcc_of_mem _ ⟨div_nonneg hs0 ht.le, (div_le_one ht).2 hst⟩]
    field_simp

/-- **The measurable path map.** -/
def stopPath (t : ℝ) (f : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) t, ℝ) := (limPath t f).comp (toUnit t)

theorem measurable_stopPath (t : ℝ) : Measurable (stopPath t) :=
  ContinuousMap.measurable_iff_eval.2 fun s =>
    (continuous_eval_const (toUnit t s)).measurable.comp (measurable_limPath t)

theorem stopPath_apply {t : ℝ} {f : ℝ≥0 → ℝ} (hf : Continuous f) (s : Icc (0 : ℝ) t) :
    stopPath t f s = f (s : ℝ).toNNReal := by
  show limPath t f (toUnit t s) = _
  rw [limPath_eq hf]
  show f (t * (toUnit t s : ℝ)).toNNReal = _
  rw [mul_toUnit]

/-- On `[0,t]`, the driver `Wof 1 t (stopPath t f)` is `s ↦ f s` for continuous `f`. -/
theorem eqOn_Wof_stopPath {t : ℝ} (ht : 0 ≤ t) {f : ℝ≥0 → ℝ} (hf : Continuous f) :
    EqOn (CharFun.Wof 1 t ht (stopPath t f)) (fun s => f s.toNNReal) (Icc 0 t) := by
  intro s hs
  simp only [CharFun.Wof, Real.sqrt_one, one_mul, projIcc_of_mem ht hs]
  exact stopPath_apply hf ⟨s, hs⟩

end E4Meas
end QuantumZipper
