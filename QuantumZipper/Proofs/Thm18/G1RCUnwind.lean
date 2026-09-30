import QuantumZipper.Proofs.Thm18.G1RCRep
import QuantumZipper.Proofs.Zipper.WedgeRC3AllBasic

/-!
# G1-RC, part 7: unwinding the rescaled wedge field (toward `G1RC.G1RawSmoothStmt`)

Deterministic, per sample. Let `x` be a good free sample (`WedgeTK.GoodRad x F` with the raw
dyadic agreement `hray`), `A` a continuous radial path, with the wedge-profile integrability on
every folded circle (as provided a.s. by `WedgeCircleIntStmt`), `w₀ = wedgeField (lateralPart x)
A Q` and `y = rescale w₀ Q S`, `S > 0` (the canonical representative for `S = scaleParam γ w₀`).

* `G1RC.rescale_wedge_fc_eq`: raw value of `y` at a folded circle `fc(c, ρ)` with `‖c‖ ≠ ρ`:
  `F(fold(S c), S ρ) + ∫ wedgeProfile dfc(S c, S ρ) + Q log S`;
* `G1RC.avgReg_rescale_wedge`: hence the regularized circle average of `y` at `w ∈ Hbar`,
  `‖w‖ ≠ 2^{-k}`: `avgReg y k w = F(S w, S 2^{-k}) + ∫ wedgeProfile dfc(S w, S 2^{-k}) + Q log S`;
* `G1RC.evalReg_rescale_wedge`: for a probability measure `ν` carried by `Hbar` and, for all
  large `k`, by the complement of the circle `{‖w‖ = 2^{-k}}`, if the profile part `∫∫ wedgeProfile dfc(S w, S 2^{-k}) dν(w)`
  converges to `Lp` (and the integrands are integrable), then `evalReg y ν = L + Lp + Q log S`
  whenever the free-field part `∫ F(S w, S 2^{-k}) dν(w)` converges to `L`.

These are the deterministic steps of the intended proof of `G1RawSmoothStmt` (with
`ν = ψ_* fc(d, r)`); own elementary arguments (circle-average bookkeeping), on top of
`F1.evalReg_wedgeField_fc_of_gap` (WEDGE-RC3ALL) and `G1.rescale_fc_apply` (G1Rescale).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

theorem norm_foldH' (z : ℂ) : ‖foldH z‖ = ‖z‖ := by
  unfold foldH; split_ifs <;> simp

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}

/-- Hypotheses on the free sample and the radial path used below. -/
structure WedgeGood (x : FieldSample) (F : ℂ × ℝ → ℝ) (A : ℝ → ℝ) : Prop where
  good : GoodRad x F
  ray : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
    x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k)
  cont : Continuous A
  intR : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Integrable (fun u => radAvgReg x ‖u‖) (foldedCircle w ρ)
  intA : ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → Integrable (fun u => A (-Real.log ‖u‖)) (foldedCircle w ρ)

/-- Raw value of the rescaled wedge field at a folded circle not through `0`. -/
theorem rescale_wedge_fc_eq (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S) (c : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hgap : ‖c‖ ≠ ρ) :
    rescale (wedgeField (lateralPart x) A Q) Q S (foldedCircle c ρ) =
      F (foldH ((S : ℂ) * c), S * ρ) +
        ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle ((S : ℂ) * c) (S * ρ) +
        Q * Real.log S := by
  set c' := foldH ((S : ℂ) * c) with hc'
  have hSρ : 0 < S * ρ := mul_pos hS hρ
  have hgap' : ‖c'‖ ≠ S * ρ := by
    rw [hc', norm_foldH', norm_mul, Complex.norm_real, Real.norm_of_nonneg hS.le]
    intro h'; exact hgap (mul_left_cancel₀ hS.ne' h')
  rw [G1.rescale_fc_apply _ Q hS c ρ,
    F1.evalReg_wedgeField_fc_of_gap h.good h.ray h.cont Q hSρ hgap' (h.intR c' _ hSρ)
      (h.intA c' _ hSρ),
    WedgeCan.wedgeField_eq_evalReg_add_ofFun (h.intR c' _ hSρ)
      (WedgeCan.integrable_logProfile_foldedCircle Q c' (S * ρ)) (h.intA c' _ hSρ),
    h.good.1.evalReg_fc c' hSρ, foldH_of_mem' (foldH_mem_Hbar' _), hc', fc_foldH_eq]

/-- **Regularized circle averages of the rescaled wedge field** off the dyadic circles
through `0`. -/
theorem avgReg_rescale_wedge (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S) {k : ℕ}
    {w : ℂ} (hw : w ∈ Hbar) (hgap : ‖w‖ ≠ radius k) :
    avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k w =
      F ((S : ℂ) * w, S * radius k) +
        ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle ((S : ℂ) * w) (S * radius k) +
        Q * Real.log S := by
  set ρ := radius k with hρdef
  have hρ : 0 < ρ := radius_pos k
  have hSρ : 0 < S * ρ := mul_pos hS hρ
  have hc := RegClosure.tendsto_dyadicRoundC w
  set δ := |‖w‖ - ρ| with hδ
  have hδ0 : 0 < δ := abs_pos.2 (sub_ne_zero.2 hgap)
  have hnorm : Tendsto (fun n => ‖dyadicRoundC n w‖) atTop (𝓝 ‖w‖) :=
    (continuous_norm.tendsto w).comp hc
  have hev : ∀ᶠ n in atTop, δ / 2 ≤ |‖dyadicRoundC n w‖ - ρ| := by
    filter_upwards [(Metric.tendsto_nhds.1 hnorm) (δ / 2) (by positivity)] with n hn
    rw [Real.dist_eq] at hn
    have := abs_sub_abs_le_abs_sub (‖w‖ - ρ) (‖dyadicRoundC n w‖ - ρ)
    rw [show ‖w‖ - ρ - (‖dyadicRoundC n w‖ - ρ) = -(‖dyadicRoundC n w‖ - ‖w‖) by ring,
      abs_neg] at this
    linarith
  set g := WedgeMeasCoord.gT F A Q (S * δ) with hg
  have hgc : Continuous g := WedgeMeasCoord.continuous_gT h.good.1.1 h.cont (by positivity)
  -- the profile integral equals the truncated one on circles with a gap `≥ δ/2`
  have hprof : ∀ c : ℂ, δ / 2 ≤ |‖c‖ - ρ| →
      ∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle ((S : ℂ) * c) (S * ρ) =
        ∫ u, g u ∂foldedCircle ((S : ℂ) * c) (S * ρ) := by
    intro c hc'
    refine integral_congr_ae ?_
    filter_upwards [WedgeCan.ae_fc_abs_le_norm (w := (S : ℂ) * c) hSρ] with u hu
    refine (WedgeMeasCoord.gT_eq h.good (by positivity) ?_).symm
    have e : |‖(S : ℂ) * c‖ - S * ρ| = S * |‖c‖ - ρ| := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hS.le, ← mul_sub, abs_mul,
        abs_of_pos hS]
    rw [e] at hu
    nlinarith
  unfold avgReg
  refine Tendsto.limUnder_eq ?_
  have hcongr : (fun n => F (foldH ((S : ℂ) * dyadicRoundC n w), S * ρ) +
      ∫ u, g u ∂foldedCircle ((S : ℂ) * dyadicRoundC n w) (S * ρ) + Q * Real.log S) =ᶠ[atTop]
      fun n => rescale (wedgeField (lateralPart x) A Q) Q S
        (foldedCircle (dyadicRoundC n w) ρ) := by
    filter_upwards [hev] with n hn
    have hgn : ‖dyadicRoundC n w‖ ≠ ρ := fun e => by
      rw [e, sub_self, abs_zero] at hn; linarith
    rw [rescale_wedge_fc_eq h Q hS _ hρ hgn, hprof _ hn]
  refine Tendsto.congr' hcongr ?_
  have hSw : (S : ℂ) * w ∈ Hbar := by
    show 0 ≤ ((S : ℂ) * w).im
    rw [Complex.im_ofReal_mul]; exact mul_nonneg hS.le hw
  have hmul : Tendsto (fun n => (S : ℂ) * dyadicRoundC n w) atTop (𝓝 ((S : ℂ) * w)) :=
    hc.const_mul _
  have h1 : Tendsto (fun n => F (foldH ((S : ℂ) * dyadicRoundC n w), S * ρ)) atTop
      (𝓝 (F ((S : ℂ) * w, S * ρ))) := by
    have hin : Tendsto (fun n => (foldH ((S : ℂ) * dyadicRoundC n w), S * ρ)) atTop
        (𝓝[Hbar ×ˢ Ioi 0] ((S : ℂ) * w, S * ρ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        mk_mem_prod (foldH_mem_Hbar' _) (show S * ρ ∈ Ioi 0 from hSρ)⟩
      have := ((continuous_foldH'.tendsto _).comp hmul).prodMk_nhds
        (tendsto_const_nhds (x := S * ρ))
      rwa [foldH_of_mem' hSw] at this
    exact (h.good.1.1 ((S : ℂ) * w, S * ρ)
      (mk_mem_prod hSw (show S * ρ ∈ Ioi 0 from hSρ))).tendsto.comp hin
  have h2 : Tendsto (fun n => ∫ u, g u ∂foldedCircle ((S : ℂ) * dyadicRoundC n w) (S * ρ))
      atTop (𝓝 (∫ u, WedgeCan.wedgeProfile x A Q u ∂foldedCircle ((S : ℂ) * w) (S * ρ))) := by
    rw [hprof w (by rw [← hδ]; linarith)]
    have hcont := continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun hgc.continuousOn)
    exact (hcont.tendsto _).comp (hmul.prodMk_nhds tendsto_const_nhds)
  exact (h1.add h2).add tendsto_const_nhds

/-- **Regularized value of the rescaled wedge field at a measure**, given the convergence of
the profile part. -/
theorem evalReg_rescale_wedge (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S)
    {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hνH : ∀ᵐ w ∂ν, w ∈ Hbar) (hνk : ∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂ν, ‖w‖ ≠ radius k)
    (hiF : ∀ k : ℕ, Integrable (fun w => F ((S : ℂ) * w, S * radius k)) ν)
    (hiP : ∀ k : ℕ, Integrable (fun w => ∫ u, WedgeCan.wedgeProfile x A Q u
      ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ν)
    {Lp : ℝ} (hLp : Tendsto (fun k : ℕ => ∫ w, (∫ u, WedgeCan.wedgeProfile x A Q u
      ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ∂ν) atTop (𝓝 Lp))
    {L : ℝ} (hL : Tendsto (fun k : ℕ => ∫ w, F ((S : ℂ) * w, S * radius k) ∂ν) atTop (𝓝 L)) :
    evalReg (rescale (wedgeField (lateralPart x) A Q) Q S) ν = L + Lp + Q * Real.log S := by
  have e : ∀ᶠ k : ℕ in atTop,
      ∫ w, F ((S : ℂ) * w, S * radius k) ∂ν + ∫ w, (∫ u, WedgeCan.wedgeProfile x A Q u
        ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ∂ν + Q * Real.log S =
      ∫ w, avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k w ∂ν := by
    filter_upwards [hνk] with k hk
    symm
    have hi : Integrable (fun w => F ((S : ℂ) * w, S * radius k) + ∫ u,
        WedgeCan.wedgeProfile x A Q u ∂foldedCircle ((S : ℂ) * w) (S * radius k)) ν :=
      (hiF k).add (hiP k)
    rw [integral_congr_ae ((hνH.and hk).mono fun w hw =>
        avgReg_rescale_wedge h Q hS hw.1 hw.2),
      integral_add hi (integrable_const _), integral_add (hiF k) (hiP k),
      integral_const, probReal_univ, one_smul]
  unfold evalReg
  exact (((hL.add hLp).add tendsto_const_nhds).congr' e).limUnder_eq

end G1RC
end Thm18Asm
end QuantumZipper
