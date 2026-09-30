import QuantumZipper.Proofs.Thm18.ASepPFacts
import QuantumZipper.Proofs.Thm18.ASepDetB
import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Proofs.LQG.RegularSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-RAWC: pathwise continuity of the raw values `x_p(ν_p)` at `τ' = 0` (input `hrawc`)

For every regular sample `x` with witness `F` and every folded circle carried by a compact
`K ⊆ Hbar` avoiding `0`, `evalReg (ofFun g + x) (fc(c, s)) = F(c, s) + ∫ g dfc(c, s)`
(`evalReg_logProfile_fc_of_reg`, from `G1Z3.evalReg_add_ofFun_of_ae_z3` with a continuous
modification of the log profile near `0`). With the deterministic raw identity
(`unzippedField_raw0`, `nuA0_eq_map_psi`, `detLimA0_eq_raw`) this gives, on the event that `X ω`
is a regular sample (`RegSample.ae_isRegularSample`),

`xA0 p ω (nuA0 p) = F_ω(p₁ d, p₁ r) + detLimA0 p`,

continuous in `p` (`continuousOn_detLimA0`). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- Convergence of the regularized means of a regular sample at a folded circle. -/
theorem tendsto_integral_avgReg_fc_of_reg {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {c : ℂ} (hc : c ∈ Hbar) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun j => ∫ w, avgReg x j w ∂foldedCircle c s) atTop (𝓝 (F (c, s))) := by
  have e : ∀ k : ℕ, ∫ u, avgReg x k u ∂foldedCircle c s =
      ∫ u, F (u, radius k) ∂foldedCircle c s := fun k =>
    integral_congr_ae ((RegClosure.fc_ae_mem_Hbar c s).mono fun u hu => hF.avgReg_eq k hu)
  simp_rw [e]
  exact (hF.2.2.tendsto_at (show (c, s) ∈ Hbar ×ˢ Ioi (0 : ℝ) from ⟨hc, hs⟩)).comp
    RegClosure.tendsto_radius_nhdsGT

/-- **`evalReg` of `ofFun g + x` at a folded circle away from `0`**, `g = a' log|·| + g₁`. -/
theorem evalReg_logProfile_fc_of_reg {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (h0K : (0 : ℂ) ∉ K) {c : ℂ} (hc : c ∈ Hbar) {s : ℝ}
    (hs : 0 < s) (hν : ∀ᵐ w ∂foldedCircle c s, w ∈ K) :
    evalReg (ofFun (fun v => a' * Real.log ‖v‖ + g₁ v) + x) (foldedCircle c s) =
      F (c, s) + ∫ v, (a' * Real.log ‖v‖ + g₁ v) ∂foldedCircle c s := by
  obtain ⟨η, hη, hηK⟩ : ∃ η > 0, ∀ v ∈ K, η < ‖v‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun v hv => by rw [he] at hv; exact absurd hv (notMem_empty v)⟩
    obtain ⟨v₀, hv₀, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
    have hv₀0 : 0 < ‖v₀‖ := norm_pos_iff.2 fun h => h0K (h ▸ hv₀)
    refine ⟨‖v₀‖ / 2, by positivity, fun v hv => ?_⟩
    have := hmin hv
    simp only [mem_setOf_eq] at this
    linarith
  have hsub : K ⊆ (closedBall (0 : ℂ) η)ᶜ := fun v hv h => by
    rw [mem_closedBall, dist_zero_right] at h; linarith [hηK v hv]
  obtain ⟨δ₀, hδ₀, hδK⟩ := hK.exists_cthickening_subset_open isClosed_closedBall.isOpen_compl hsub
  set φ' : ℂ → ℝ := fun v => a' * Real.log (max ‖v‖ η) + g₁ v with hφ'
  have hφ'c : Continuous φ' :=
    (continuous_const.mul ((continuous_norm.max continuous_const).log fun v =>
      (hη.trans_le (le_max_right _ _)).ne')).add hg₁
  have heq : EqOn φ' (fun v => a' * Real.log ‖v‖ + g₁ v) (cthickening δ₀ K) := by
    intro v hv
    have h := hδK hv
    simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at h
    simp only [hφ', max_eq_left h.le]
  have hmain := G1Z3.evalReg_add_ofFun_of_ae_z3 hF hφ'c.continuousOn hK hKH hδ₀ heq hν
    (tendsto_integral_avgReg_fc_of_reg hF hc hs)
  rw [add_comm (ofFun _) x, hmain, hF.evalReg_fc_of_mem hc hs]
  congr 1
  exact integral_congr_ae (hν.mono fun v hv => heq (self_subset_cthickening K hv))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
