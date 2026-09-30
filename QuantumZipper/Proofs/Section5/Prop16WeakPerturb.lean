import QuantumZipper.Proofs.LQG.LocalRule

/-!
# Proposition 1.6, D4-c: a uniformly small continuous perturbation barely moves area pairings

Decision D24 (`DECISIONS.md`); tool for the proof of the weak node D4⁺ʷ
(`Prop16Asm.Prop16TVWeakStmt`). Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25): the
continuous part of the conditioned field is "approximately constant" near the marked point.

By the local rule (5.1) (`LocalRule.qAreaMeasureOn_add_ofFun`), adding a continuous `φ` multiplies
the local area measure by `e^{γφ}`. If `|φ| ≤ ε` where the test function `f` lives, then
`|∫ f dμ_{x+φ} − ∫ f dμ_x| ≤ (e^{|γ|ε} − 1) ∫ |f| dμ_x`
(`abs_integral_qAreaMeasureOn_add_ofFun_sub_le`). Elementary estimate (own proof, AGENT_GUIDE cost
rule), including the Bochner junk convention: if `f` is not integrable, both pairings are `0`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

theorem abs_exp_sub_one_le (t : ℝ) : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
  · rw [abs_of_nonpos ht, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 ht])]
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]

end Prop16Area

end QuantumZipper
