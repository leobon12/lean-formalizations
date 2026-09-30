import QuantumZipper.Proofs.Zipper.SWCoreB7bAddOn
import QuantumZipper.Proofs.Zipper.SWCoreN2IdMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (5): the `𝔥₀` add-on at the level of the regularized averages

Decision D64, item (2). Almost surely, for a finite-parameter Lipschitz family of class maps
staying at distance `≥ c₀` from `0`, eventually in `k`, for all maps of the family and all
`t ∈ [a,b]`,

  `avgReg (coordChange (𝔥₀ + X) Ψ_q Q) k t = avgReg (coordChange X Ψ_q Q) k t + H_k(q,t)`,
  `H_k(q,t) = ∫ 𝔥₀ d(fc(t, 2^{-k}).map Ψ_q)`

(`ae_avgReg_add_h0rev_family`). So the boundary approximations of the transported anchor field
`𝔥₀ + Y` are those of `Y` with the density factor `e^{(γ/2) H_k}`.

Proof: the pushed-limit add-on (`ae_evalReg_add_h0rev_family`) on `[a − r, b + r]`, continuity of
`s ↦ H(s)` (dominated convergence, as `swcN2_cc_continuousOn`), and the deterministic dyadic-centre
limit `swcN2_avgReg_eq`, applied to both fields; the `X`-side identity is `swcN2_id` (i).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- Continuity in the centre of the `𝔥₀`-average over a pushed semicircle. -/
theorem continuousOn_h0rev_push (κ : ℝ) {a b ρ M m : ℝ} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ BdryClass a b ρ M m) (hab : a ≤ b) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖ψ z‖) {r : ℝ} (hr : 0 < r) (hrρ : 3 * r < ρ) :
    ContinuousOn (fun s : ℝ => ∫ w, h0rev κ w ∂((foldedCircle (s : ℂ) r).map ψ))
      (Icc (a - r) (b + r)) := by
  have hpt : ∀ s ∈ Icc (a - r) (b + r), ∀ θ,
      foldH (circleMap (s : ℂ) r θ) ∈ thickening ρ (segC a b) := fun s hs θ =>
    swcN2_ball_sub_thick (swcN2Clamp_mem hab s) (R := 2 * r) (by linarith)
      (swcN2_fold_mem_ball2 hab hr.le hs θ)
  have hball : ∀ s ∈ Icc (a - r) (b + r), closedBall (s : ℂ) r ⊆ thickening ρ (segC a b) := by
    intro s hs z hz
    refine swcN2_ball_sub_thick (swcN2Clamp_mem hab s) (R := 2 * r) (by linarith) ?_
    have h3 : dist (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ) = |s - swcN2Clamp a b s| := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := swcN2Clamp_near hab hr.le hs
    rw [mem_closedBall] at hz ⊢
    linarith [dist_triangle z (s : ℂ) ((swcN2Clamp a b s : ℝ) : ℂ)]
  have hψc : ContinuousOn ψ (thickening ρ (segC a b)) := hψ.1.continuousOn
  set F : ℝ → ℝ → ℝ := fun s θ => h0cut κ (c₀ / 2) (ψ (foldH (circleMap (s : ℂ) r θ))) with hF
  have hrep : ∀ s ∈ Icc (a - r) (b + r),
      ∫ w, h0rev κ w ∂((foldedCircle (s : ℂ) r).map ψ) = ∫ θ, F s θ ∂circM := by
    intro s hs
    rw [swcN2_fc_map_eq hr.le (hψc.mono (hball s hs))]
    have hgc : Continuous fun θ : ℝ => ψ (foldH (circleMap (s : ℂ) r θ)) := by
      refine hψc.comp_continuous ?_ (hpt s hs)
      exact CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)
    rw [integral_map hgc.measurable.aemeasurable]
    · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hF]
      exact (h0cut_eq (le_trans (by linarith) (hsep _ (hpt s hs θ)))).symm
    · -- `h0rev` is measurable
      exact (measurable_const.mul (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  refine ContinuousOn.congr ?_ hrep
  -- dominated convergence
  set C : ℝ := |2 / Real.sqrt κ| * (|Real.log (c₀ / 2)| + |Real.log (max M (c₀ / 2))|) with hC
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun s _ => ((continuous_h0cut κ (by positivity)).measurable.comp
      ((hψ.1.continuousOn.comp_continuous ?_ ?_).measurable)).aestronglyMeasurable)
    (fun s hs => Eventually.of_forall fun θ => ?_) (integrable_const _)
    (Eventually.of_forall fun θ => ?_)
  · exact CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)
  · exact hpt s ‹_›
  · have hw := hpt s hs θ
    have hM := hψ.2.1 _ hw
    set w := ψ (foldH (circleMap (s : ℂ) r θ))
    have h1 : c₀ / 2 ≤ max ‖w‖ (c₀ / 2) := le_max_right _ _
    have h2 : max ‖w‖ (c₀ / 2) ≤ max M (c₀ / 2) := max_le_max hM le_rfl
    have l1 := Real.log_le_log (by positivity) h1
    have l2 := Real.log_le_log (by positivity) h2
    simp only [hF, h0cut, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (c₀ / 2)), abs_nonneg (Real.log (max M (c₀ / 2)))]
    · linarith [le_abs_self (Real.log (max M (c₀ / 2))), abs_nonneg (Real.log (c₀ / 2))]
  · have hg : Continuous fun s : ℝ => foldH (circleMap (s : ℂ) r θ) := by
      refine CircleFubini.continuous_foldH'.comp ?_
      simp only [circleMap]
      exact Complex.continuous_ofReal.add continuous_const
    exact (continuous_h0cut κ (by positivity)).comp_continuousOn
      (hψc.comp hg.continuousOn fun s hs => hpt s hs θ)

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {pr : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

set_option maxHeartbeats 1000000 in
/-- **The `𝔥₀` add-on at the level of `avgReg`, a.s., eventually in `k`, over the family.** -/
theorem ae_avgReg_add_h0rev_family (κ Q : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ q ∈ K, ∀ t ∈ Icc a b,
      avgReg (coordChange (ofFun (h0rev κ) + X ω) (Ψ q) Q) k (t : ℂ) =
        avgReg (coordChange (X ω) (Ψ q) Q) k (t : ℂ) +
          ∫ w, h0rev κ w ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) := by
  obtain ⟨k₀, hid, -⟩ := swcN2_id hab hρ hm hΨ hL0 hL hπ hπK hπid Q hX
  obtain ⟨r₂, hr₂, hadd⟩ := ae_evalReg_add_h0rev_family κ hab hρ hm hΨ hL0 hL hπ hπK hπid hc₀
    hsep hX
  obtain ⟨r₃, hr₃, hpush⟩ := swcN2_push_ae hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  set A : ℝ := |M| + 1 with hA
  have hA0 : 0 < A := by positivity
  set rs : ℝ := min (min r₂ r₃) (min (ρ / 16) (m * ρ ^ 2 / (128 * A))) with hrs
  have hrs0 : 0 < rs := lt_min (lt_min hr₂ hr₃) (lt_min (by positivity) (by positivity))
  have hsmall : ∀ᶠ k in atTop, radius k < rs :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).eventually (gt_mem_nhds hrs0)
  have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, radius k < rs →
      (∀ q ∈ K, ∀ t ∈ Icc (a - radius k) (b + radius k),
        evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) =
          evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
            ∫ w, h0rev κ w ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q))) ∧
      ContinuousOn (fun x : (Fin n → ℝ) × ℝ =>
          evalReg (X ω) ((foldedCircle (x.2 : ℂ) (radius k)).map (Ψ x.1)))
          (K ×ˢ Icc (a - radius k) (b + radius k)) := by
    intro k
    by_cases hk : radius k < rs
    · have h2 : radius k ∈ Ioo 0 r₂ :=
        ⟨radius_pos k, lt_of_lt_of_le hk ((min_le_left _ _).trans (min_le_left _ _))⟩
      have h3 : radius k ∈ Ioo 0 r₃ :=
        ⟨radius_pos k, lt_of_lt_of_le hk ((min_le_left _ _).trans (min_le_right _ _))⟩
      filter_upwards [hadd (radius k) h2, (hpush (radius k) h3).1] with ω e1 e2 _
      exact ⟨e1, e2⟩
    · exact Eventually.of_forall fun ω h => absurd h hk
  filter_upwards [hid, ae_all_iff.2 hall] with ω hid' hall'
  filter_upwards [eventually_ge_atTop k₀, hsmall] with k hk hks q hq t ht
  obtain ⟨hadd', hpc⟩ := hall' k hks
  obtain ⟨r, hr⟩ : ∃ r, r = radius k := ⟨_, rfl⟩
  rw [← hr] at hadd' hpc ⊢
  have hr0 : 0 < r := hr ▸ radius_pos k
  rw [← hr] at hks
  have h16 : r < ρ / 16 := lt_of_lt_of_le hks ((min_le_right _ _).trans (min_le_left _ _))
  have hmr : r < m * ρ ^ 2 / (128 * A) :=
    lt_of_lt_of_le hks ((min_le_right _ _).trans (min_le_right _ _))
  have hrm : 32 * (|M| + 1) / ρ ^ 2 * (2 * r) ≤ m / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hmr
    rw [show 32 * (|M| + 1) / ρ ^ 2 * (2 * r) = 64 * A * r / ρ ^ 2 by rw [hA]; ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have htI : t ∈ Icc (a - r) (b + r) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hEX : ContinuousOn (fun s : ℝ => evalReg (X ω) ((foldedCircle (s : ℂ) r).map (Ψ q)))
      (Icc (a - r) (b + r)) :=
    hpc.comp (continuous_const.prodMk continuous_id).continuousOn fun s hs => ⟨hq, hs⟩
  have hH := continuousOn_h0rev_push κ (hΨ q hq) hab.le hc₀ (hsep q hq) hr0 (by linarith)
  have hEZ : ContinuousOn (fun s : ℝ =>
      evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle (s : ℂ) r).map (Ψ q)))
      (Icc (a - r) (b + r)) :=
    (hEX.add hH).congr fun s hs => hadd' q hq s hs
  have hcc := swcN2_cc_continuousOn (hΨ q hq) hab.le hρ hm hr0 (by linarith) hrm
  have e1 := swcN2_avgReg_eq (ofFun (h0rev κ) + X ω) (Ψ q) Q k ht (hr ▸ hEZ t htI)
    (hr ▸ hcc t htI)
  have e2 := (hid' k hk).1 q hq t ht
  rw [← hr] at e1 e2
  rw [e1, hadd' q hq t htI, e2]
  ring

end SWCore
end QuantumZipper
