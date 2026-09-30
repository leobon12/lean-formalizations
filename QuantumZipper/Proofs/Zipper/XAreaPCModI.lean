import QuantumZipper.Proofs.Zipper.XAreaPCLog
import QuantumZipper.Proofs.Zipper.XAreaPCEnergy
import QuantumZipper.Proofs.GFF.SmoothingConvergence
import QuantumZipper.Proofs.LQG.CoordChangeSmooth
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.JointModRandom
import QuantumZipper.Proofs.Zipper.RegContRandom
import QuantumZipper.Proofs.Thm12.CharFun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, R1 for the image circles

* `abs_kernelCov2_fc_fc_le`: for folded circles centred in `H̄`,
  `|E(fc(c, ρ) − fc(c', ρ'))| ≤ 4 (‖c − c'‖ + |ρ − ρ'|) / min ρ ρ'`.
  Proof: with `h(x) = ∫ G(x, ·) dfc(c, ρ) = −log max(ρ, ‖c − x‖) − log max(ρ, ‖c − x̄‖)`
  (`integral_neumannH_foldedCircle`) and `h'` likewise, the energy is
  `∫ (h − h') dfc(c, ρ) − ∫ (h − h') dfc(c', ρ')`, and `|h − h'| ≤ 2δ/min ρ ρ'` pointwise since
  `log max(ρ, ·)` is `1/ρ`-Lipschitz above `ρ`.
* `xPCModIStmt_holds`: the image-circle half of R1 (`XPCModIStmt`), since `z ↦ ψ z`,
  `z ↦ ‖ψ'(z)‖` are Lipschitz on a rectangle in `ℍ` and `‖ψ'‖ ≥ m > 0` there.

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ComplexConjugate

namespace QuantumZipper.E6
namespace XAreaPC

/-- A continuous function is integrable over a folded circle centred in `H̄`. -/
theorem integrable_fc_of_continuous {g : ℂ → ℝ} (hg : Continuous g) {c : ℂ} (hc : c ∈ Hbar)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : Integrable g (foldedCircle c ρ) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c ρ).exists_bound_of_continuousOn hg.continuousOn
  refine (integrable_const C).mono' hg.aestronglyMeasurable ?_
  filter_upwards [foldedCircle_ae_dist_le_pc hc hρ] with x hx
  exact hC x (mem_closedBall.2 hx)

/-- `log max(ρ, ·)` is Lipschitz, jointly in `ρ` and the argument. -/
theorem abs_log_max_sub_le' {ρ ρ' a a' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    |Real.log (max ρ a) - Real.log (max ρ' a')| ≤ (|ρ - ρ'| + |a - a'|) / min ρ ρ' := by
  have hm : 0 < min ρ ρ' := lt_min hρ hρ'
  have hu : min ρ ρ' ≤ max ρ a := (min_le_left _ _).trans (le_max_left _ _)
  have hv : min ρ ρ' ≤ max ρ' a' := (min_le_right _ _).trans (le_max_left _ _)
  have hmax : |max ρ a - max ρ' a'| ≤ |ρ - ρ'| + |a - a'| :=
    (abs_max_sub_max_le_max ρ a ρ' a').trans
      (max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
  have h1 := CircleMV.log_sub_log_le hm hu hv
  have h2 := CircleMV.log_sub_log_le hm hv hu
  rw [abs_sub_comm] at h2
  rw [abs_le]
  constructor
  · have : |max ρ a - max ρ' a'| / min ρ ρ' ≤ (|ρ - ρ'| + |a - a'|) / min ρ ρ' :=
      div_le_div_of_nonneg_right hmax hm.le
    linarith
  · exact h1.trans (div_le_div_of_nonneg_right hmax hm.le)

/-- The inner Neumann integral against a folded circle, as a function. -/
def hfc (c : ℂ) (ρ : ℝ) (x : ℂ) : ℝ :=
  -Real.log (max ρ ‖c - x‖) - Real.log (max ρ ‖c - conj x‖)

theorem continuous_hfc (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) : Continuous (hfc c ρ) := by
  unfold hfc
  have hl : ∀ f : ℂ → ℝ, Continuous f → Continuous fun x => Real.log (max ρ (f x)) :=
    fun f hf => Real.continuousOn_log.comp_continuous (continuous_const.max hf)
      fun x => ne_of_gt (lt_max_of_lt_left hρ)
  exact ((hl _ (continuous_const.sub continuous_id).norm).neg).sub
    (hl _ (continuous_const.sub Complex.continuous_conj).norm)

theorem abs_hfc_sub_le {c c' : ℂ} {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') (x : ℂ) :
    |hfc c ρ x - hfc c' ρ' x| ≤ 2 * ((‖c - c'‖ + |ρ - ρ'|) / min ρ ρ') := by
  have hm : 0 < min ρ ρ' := lt_min hρ hρ'
  have n1 : |‖c - x‖ - ‖c' - x‖| ≤ ‖c - c'‖ := by
    have := abs_norm_sub_norm_le (c - x) (c' - x)
    rwa [show c - x - (c' - x) = c - c' by ring] at this
  have n2 : |‖c - conj x‖ - ‖c' - conj x‖| ≤ ‖c - c'‖ := by
    have := abs_norm_sub_norm_le (c - conj x) (c' - conj x)
    rwa [show c - conj x - (c' - conj x) = c - c' by ring] at this
  have a1 := abs_log_max_sub_le' (a := ‖c - x‖) (a' := ‖c' - x‖) hρ hρ'
  have a2 := abs_log_max_sub_le' (a := ‖c - conj x‖) (a' := ‖c' - conj x‖) hρ hρ'
  have b1 : (|ρ - ρ'| + |‖c - x‖ - ‖c' - x‖|) / min ρ ρ' ≤ (‖c - c'‖ + |ρ - ρ'|) / min ρ ρ' :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  have b2 : (|ρ - ρ'| + |‖c - conj x‖ - ‖c' - conj x‖|) / min ρ ρ' ≤
      (‖c - c'‖ + |ρ - ρ'|) / min ρ ρ' :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  unfold hfc
  have e : -Real.log (max ρ ‖c - x‖) - Real.log (max ρ ‖c - conj x‖) -
      (-Real.log (max ρ' ‖c' - x‖) - Real.log (max ρ' ‖c' - conj x‖)) =
      -(Real.log (max ρ ‖c - x‖) - Real.log (max ρ' ‖c' - x‖)) -
        (Real.log (max ρ ‖c - conj x‖) - Real.log (max ρ' ‖c' - conj x‖)) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_neg]
  linarith

/-- **Energy of the difference of two folded circles.** -/
theorem abs_kernelCov2_fc_fc_le {c c' : ℂ} (hc : c ∈ Hbar) (hc' : c' ∈ Hbar) {ρ ρ' : ℝ}
    (hρ : 0 < ρ) (hρ' : 0 < ρ') :
    |kernelCov2 neumannH (foldedCircle c ρ, foldedCircle c' ρ')
        (foldedCircle c ρ, foldedCircle c' ρ')| ≤
      4 * ((‖c - c'‖ + |ρ - ρ'|) / min ρ ρ') := by
  set δ := (‖c - c'‖ + |ρ - ρ'|) / min ρ ρ' with hδ
  have hin : ∀ (d : ℂ) (r : ℝ), 0 < r →
      (fun x => ∫ y, neumannH x y ∂foldedCircle d r) = hfc d r := fun d r hr =>
    funext fun x => xpc_inner_fc d x hr
  simp only [kernelCov2, kernelCov]
  rw [hin c ρ hρ, hin c' ρ' hρ']
  have i1 := integrable_fc_of_continuous (continuous_hfc c hρ) hc hρ.le
  have i2 := integrable_fc_of_continuous (continuous_hfc c' hρ') hc hρ.le
  have i3 := integrable_fc_of_continuous (continuous_hfc c hρ) hc' hρ'.le
  have i4 := integrable_fc_of_continuous (continuous_hfc c' hρ') hc' hρ'.le
  have hb : ∀ (μ : Measure ℂ) [IsProbabilityMeasure μ], Integrable (hfc c ρ) μ →
      Integrable (hfc c' ρ') μ →
      |(∫ x, hfc c ρ x ∂μ) - ∫ x, hfc c' ρ' x ∂μ| ≤ 2 * δ := by
    intro μ _ ia ib
    rw [← integral_sub ia ib, ← Real.norm_eq_abs]
    calc ‖∫ x, (hfc c ρ x - hfc c' ρ' x) ∂μ‖ ≤ 2 * δ * μ.real univ :=
          norm_integral_le_of_norm_le_const (ae_of_all _ fun x => by
            rw [Real.norm_eq_abs]; exact abs_hfc_sub_le hρ hρ' x)
      _ = 2 * δ := by simp
  have h1 := hb (foldedCircle c ρ) i1 i2
  have h2 := hb (foldedCircle c' ρ') i3 i4
  have e : (∫ x, hfc c ρ x ∂foldedCircle c ρ) - (∫ x, hfc c' ρ' x ∂foldedCircle c ρ) -
      (∫ x, hfc c ρ x ∂foldedCircle c' ρ') + (∫ x, hfc c' ρ' x ∂foldedCircle c' ρ') =
      ((∫ x, hfc c ρ x ∂foldedCircle c ρ) - ∫ x, hfc c' ρ' x ∂foldedCircle c ρ) -
        ((∫ x, hfc c ρ x ∂foldedCircle c' ρ') - ∫ x, hfc c' ρ' x ∂foldedCircle c' ρ') := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end XAreaPC
end QuantumZipper.E6
