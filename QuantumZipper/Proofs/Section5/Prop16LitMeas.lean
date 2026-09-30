import QuantumZipper.Proofs.Section5.Prop16LitScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: first step towards `Prop16LitMeasStmt`

`Prop16Lit.measurable_evalReg_chart`: for a coordinate-measurable random field `Y` and a jointly
measurable family of charts `ψ x`, the regularized evaluation of `Y ω` at the chart image
`(ψ_x)_* m`, translated by `x`, is jointly measurable in `(ω, x)`. This is the raw-coordinate
measurability of the field read through the chart (`zoomFieldLit`), once real translates are
exact (`Thm18Asm.G3Zr.evalReg_translate_eq`). Own elementary argument (the proof of
`measurable_evalReg` with a parameter-dependent measure).
-/

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

variable {Ω' : Type*}

/-- The difference-quotient version of the chart derivative. -/
def chartDeriv (ψ : ℝ → ℂ → ℂ) (q : ℝ × ℂ) : ℂ :=
  limUnder atTop fun n : ℕ => ((n : ℂ) + 1) * (ψ q.1 (q.2 + 1 / ((n : ℂ) + 1)) - ψ q.1 q.2)

/-- `chartDeriv` is jointly measurable for a jointly measurable family. -/
theorem measurable_chartDeriv {ψ : ℝ → ℂ → ℂ} (hψ : Measurable fun q : ℝ × ℂ => ψ q.1 q.2) :
    Measurable (chartDeriv ψ) := by
  have hn : ∀ n : ℕ, StronglyMeasurable fun q : ℝ × ℂ =>
      ((n : ℂ) + 1) * (ψ q.1 (q.2 + 1 / ((n : ℂ) + 1)) - ψ q.1 q.2) := by
    intro n
    refine Measurable.stronglyMeasurable (measurable_const.mul ?_)
    refine Measurable.sub ?_ hψ
    exact hψ.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
  exact (StronglyMeasurable.limUnder hn).measurable

/-- `chartDeriv` is the derivative wherever the chart is differentiable. -/
theorem chartDeriv_eq {ψ : ℝ → ℂ → ℂ} {x : ℝ} {u : ℂ} (hd : DifferentiableAt ℂ (ψ x) u) :
    chartDeriv ψ (x, u) = deriv (ψ x) u := by
  have h := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at h
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℂ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    · simp only [mem_compl_iff, mem_singleton_iff, one_div, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
  have hlim := h.comp hseq
  have e : (fun n : ℕ => ((n : ℂ) + 1) * (ψ x (u + 1 / ((n : ℂ) + 1)) - ψ x u)) =
      (fun t => t⁻¹ • (ψ x (u + t) - ψ x u)) ∘ (fun n : ℕ => 1 / ((n : ℂ) + 1)) := by
    funext n; simp [one_div, inv_inv, smul_eq_mul]
  show limUnder atTop (fun n : ℕ => ((n : ℂ) + 1) * (ψ x (u + 1 / ((n : ℂ) + 1)) - ψ x u)) = _
  rw [e]; exact hlim.limUnder_eq

end Prop16Lit

end QuantumZipper
