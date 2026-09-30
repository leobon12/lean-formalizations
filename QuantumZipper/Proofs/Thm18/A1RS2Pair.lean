import QuantumZipper.Proofs.Thm18.A1RS2Cont
import QuantumZipper.Proofs.Thm18.A1RFLoopY

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (4): (R2) for the unscaled wedge field `Z = X + α₀(−log|·|) + G` (deterministic)

For a driver `V` and `Z` as in `A1RF.loopUC_of_Z` (A1RFLoopY.lean), whose `Γ⁰` flow pairings
converge uniformly on the parameter boxes (`A1RF.ae_flowPhiYc_tendstoUniformlyOn`):

* `continuousWithinAt_pair_loop`: the circle-smoothed pairings
  `q = (t, c, r) ↦ ∫ g d((f_t⁻¹)_* fc(c, r))` are continuous on bounded parameter sets, for `g`
  continuous on `ℍ̄` (dominated convergence; `F1`/`RegCont` joint continuity of `f_t⁻¹` on
  `[0, T] × ℍ`);
* `exists_loop_limit_Z`: on each box slice `S_m`, the dyadic pairings of `Z` along the pulled-back
  folded circles converge uniformly to a continuous limit, which is `evalReg Z ν_q`
  (`A1RF.tendstoUniformlyOn_Zpair`);
* **`continuousOn_evalReg_smearFam_Z`**: `(p, ρ) ↦ evalReg Z (smearFam V left p ρ)` is continuous
  on `smearU × (0, ∞)` (with `A1RS.continuousOn_evalReg_smearFam`).

Own bookkeeping (dominated convergence, uniform limits of continuous functions).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

/-- Bounded parameter sets of the pulled-back folded circles. -/
def loopBox (T R r₀ : ℝ) : Set (ℝ × ℂ × ℝ) :=
  {q | q.1 ∈ Icc 0 T ∧ q.2.1 ∈ Hbar ∧ r₀ ≤ q.2.2 ∧ ‖q.2.1‖ + q.2.2 ≤ R}

set_option maxHeartbeats 400000 in
/-- **Continuity of the circle-smoothed pairings along the pulled-back folded circles.** -/
theorem continuousOn_pair_loop {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {g : ℂ → ℝ}
    (hg : ContinuousOn g Hbar) (hgm : Measurable g) (T R r₀ : ℝ) (hr₀ : 0 < r₀) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ =>
      ∫ v, g v ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1))) (loopBox T R r₀) := by
  set S := loopBox T R r₀ with hS
  set F : ℝ × ℂ × ℝ → ℝ → ℝ := fun q θ =>
    g (fwdMapInv V q.1 (foldH (circleMap q.2.1 q.2.2 θ))) with hF
  have hmf : ∀ t : ℝ, 0 ≤ t → Measurable (fwdMapInv V t) := fun t ht =>
    RTBeur.measurable_fwdMapInv_rt hV hV0 ht
  have hcm : ∀ (c : ℂ) (r : ℝ), Measurable fun θ : ℝ => foldH (circleMap c r θ) := fun c r =>
    measurable_foldH.comp (measurable_circleMap _ _)
  have heq : ∀ q ∈ S, ∫ v, g v ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)) =
      ∫ θ, F q θ ∂E6.XAreaPC.angMeas := by
    intro q hq
    have hm : Measurable fun θ => fwdMapInv V q.1 (foldH (circleMap q.2.1 q.2.2 θ)) :=
      (hmf _ hq.1.1).comp (hcm _ _)
    rw [A1RF.fc_map_eq_angMeas_map (hmf _ hq.1.1), integral_map hm.aemeasurable
      hgm.aestronglyMeasurable]
  have haeH : ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∀ᵐ θ ∂E6.XAreaPC.angMeas, foldH (circleMap c r θ) ∈ H := by
    intro c r hr
    have h := TwoPoint.foldedCircle_ae_mem_H c hr
    rw [E6.XAreaPC.foldedCircle_eq_map_angMeas] at h
    exact (ae_map_iff (hcm c r).aemeasurable isOpen_H.measurableSet).1 h
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hV T
  set Bu := RegCont.revBound (2 * M) T R with hBu
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) Bu) :=
    (isCompact_closedBall (0 : ℂ) Bu).inter_left isClosed_Hbar
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono inter_subset_left)
  have hjoint := RegUnif.continuousOn_fwdMapInv_joint hV hV0 T
  intro q₀ hq₀
  have hr0 : 0 < q₀.2.2 := hr₀.trans_le hq₀.2.2.1
  refine ContinuousWithinAt.congr ?_ (fun q hq => heq q hq) (heq q₀ hq₀)
  refine continuousWithinAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hgm.comp ((hmf _ hq.1.1).comp (hcm _ _))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with q hq
    filter_upwards [haeH q.2.1 q.2.2 (hr₀.trans_le hq.2.2.1)] with θ hθ
    have hn : ‖foldH (circleMap q.2.1 q.2.2 θ)‖ ≤ R := by
      rw [TwoPoint.norm_foldH]
      exact (TwoPoint.norm_circleMap_le_add _ (hr₀.trans_le hq.2.2.1).le θ).trans hq.2.2.2
    obtain ⟨h1, h2⟩ := RegCont.fwdMapInv_mem_H_bound hV hV0 hM hq.1.1 hq.1.2 hθ hn
    exact hC _ ⟨le_of_lt (show (0 : ℝ) < _ from h1), by rw [mem_closedBall, dist_zero_right]; exact h2⟩
  · filter_upwards [haeH q₀.2.1 q₀.2.2 hr0] with θ hθ
    have hcu : Continuous fun q : ℝ × ℂ × ℝ => foldH (circleMap q.2.1 q.2.2 θ) := by
      have : (fun q : ℝ × ℂ × ℝ => foldH (circleMap q.2.1 q.2.2 θ)) =
          fun q => foldH (q.2.1 + (q.2.2 : ℂ) * Complex.exp (θ * Complex.I)) := by
        funext q; simp [circleMap]
      rw [this]
      exact CircleFubini.continuous_foldH'.comp (by fun_prop)
    have hev1 : ∀ᶠ q in 𝓝[S] q₀, ((q.1, foldH (circleMap q.2.1 q.2.2 θ)) : ℝ × ℂ) ∈
        Icc 0 T ×ˢ H := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hcu.continuousAt.eventually (isOpen_H.mem_nhds hθ))] with q hq hH
      exact ⟨hq.1, hH⟩
    have hin : ContinuousWithinAt (fun q : ℝ × ℂ × ℝ =>
        ((q.1, foldH (circleMap q.2.1 q.2.2 θ)) : ℝ × ℂ)) S q₀ :=
      (continuous_fst.prodMk hcu).continuousWithinAt
    have hq₀' : q₀.1 ∈ Icc 0 T := hq₀.1
    have hJ : ContinuousWithinAt (fun p : ℝ × ℂ => fwdMapInv V p.1 p.2) (Icc 0 T ×ˢ H)
        (q₀.1, foldH (circleMap q₀.2.1 q₀.2.2 θ)) := hjoint _ ⟨hq₀', hθ⟩
    have ht : Tendsto (fun q : ℝ × ℂ × ℝ => ((q.1, foldH (circleMap q.2.1 q.2.2 θ)) : ℝ × ℂ))
        (𝓝[S] q₀) (𝓝[Icc 0 T ×ˢ H] (q₀.1, foldH (circleMap q₀.2.1 q₀.2.2 θ))) :=
      tendsto_nhdsWithin_iff.2 ⟨hin.tendsto, hev1⟩
    have key : Tendsto ((fun p : ℝ × ℂ => fwdMapInv V p.1 p.2) ∘
        fun q : ℝ × ℂ × ℝ => ((q.1, foldH (circleMap q.2.1 q.2.2 θ)) : ℝ × ℂ)) (𝓝[S] q₀)
        (𝓝 (fwdMapInv V q₀.1 (foldH (circleMap q₀.2.1 q₀.2.2 θ)))) := hJ.tendsto.comp ht
    have hev2 : ∀ᶠ q in 𝓝[S] q₀, ((fun p : ℝ × ℂ => fwdMapInv V p.1 p.2) ∘
        fun q : ℝ × ℂ × ℝ => ((q.1, foldH (circleMap q.2.1 q.2.2 θ)) : ℝ × ℂ)) q ∈ Hbar :=
      Eventually.of_forall fun q => F1.fwdMapInv_mem_Hbar V _ _
    have hgc : ContinuousWithinAt g Hbar (fwdMapInv V q₀.1 (foldH (circleMap q₀.2.1 q₀.2.2 θ))) :=
      hg _ (F1.fwdMapInv_mem_Hbar V _ _)
    have key2 := hgc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨key, hev2⟩)
    exact key2

end A1RS
end R18
end QuantumZipper
