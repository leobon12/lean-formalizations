import QuantumZipper.Proofs.Zipper.SWCoreB7bWTH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (1): adding an arbitrary continuous function, pathwise, on pushed semicircles

Almost surely (one event, independent of the added function), for a finite-parameter Lipschitz
family of class maps `q ↦ Ψ q`, for EVERY continuous `g : ℂ → ℝ`:

* `ae_evalReg_add_fun_family`: for small `r`, all `q ∈ K`, all `t ∈ [a − r, b + r]`,
  `evalReg (X + g) (fc(t,r).map Ψ_q) = evalReg X (fc(t,r).map Ψ_q) + ∫ g d(fc(t,r).map Ψ_q)`;
* `ae_avgReg_add_fun_family`: eventually in `k`, for all `q ∈ K`, `t ∈ [a,b]`,
  `avgReg (coordChange (X + g) Ψ_q Q) k t = avgReg (coordChange X Ψ_q Q) k t + ∫ g d(fc(t,2^{-k}).map Ψ_q)`;
* `gavg_push_close`: the `g`-average over a pushed semicircle is close to `g (Ψ_q t)`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
(5.1) / Prop. 2.1 (adding a continuous function to the field); the proof is the proved `𝔥₀`
chain (`ae_evalReg_add_h0rev_family`, `ae_avgReg_add_h0rev_family`, `h0avg_push_close`) with the
cut-off of `𝔥₀` replaced by `g` itself. The a.s. event is that of the `X`-side inputs
(`swcB7_push_tendsto`, `RegSample.ae_isRegularSample`, `swcN2_push_ae`, `swcN2_id`); the addition
of `g` is then deterministic. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm.G1RC

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {pr : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Adding any continuous `g` on the pushed semicircles of a family, a.s. (one event).** -/
theorem ae_evalReg_add_fun_family (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    (hX : IsFreeGFFModConstH X P) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂, ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g →
      ∀ q ∈ K, ∀ t ∈ Icc (a - r) (b + r),
      evalReg (X ω + ofFun g) ((foldedCircle (t : ℂ) r).map (Ψ q)) =
        evalReg (X ω) ((foldedCircle (t : ℂ) r).map (Ψ q)) +
          ∫ w, g w ∂((foldedCircle (t : ℂ) r).map (Ψ q)) := by
  obtain ⟨r₁, hr₁, hT⟩ := swcB7_push_tendsto hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  obtain ⟨r₂, hr₂, hB⟩ := swcN2_push_bounds hab hρ hm hΨ hL0 hL hπ hπK
  refine ⟨min (min r₁ r₂) (ρ / 3), lt_min (lt_min hr₁ hr₂) (by linarith), fun r hr => ?_⟩
  have hr1 : r ∈ Ioo 0 r₁ :=
    ⟨hr.1, lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_left _ _))⟩
  have hr2 : r ∈ Ioo 0 r₂ :=
    ⟨hr.1, lt_of_lt_of_le hr.2 ((min_le_left _ _).trans (min_le_right _ _))⟩
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  obtain ⟨hc, hH, -⟩ := hB r hr2
  filter_upwards [hT r hr1, RegSample.ae_isRegularSample hX] with ω hω hreg g hg q hq t ht
  obtain ⟨F, hF⟩ := hreg
  set p : Fin (n + 1) → ℝ := Fin.snoc q t with hp
  set Φ := swcN2PushΦ Ψ pr a b r p with hΦ
  have hΦc : Continuous Φ := hc.comp (continuous_const.prodMk continuous_id)
  have hν : (foldedCircle (t : ℂ) r).map (Ψ q) = circM.map Φ :=
    (swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hq ht).symm
  set Kψ : Set ℂ := Φ '' Icc 0 (2 * Real.pi) with hKψ
  have hKc : IsCompact Kψ := isCompact_Icc.image hΦc
  have hKH : Kψ ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hH p θ
  have : IsProbabilityMeasure (circM.map Φ) :=
    (Measure.isProbabilityMeasure_map_iff hΦc.measurable.aemeasurable).2 inferInstance
  have hcarry : ∀ᵐ w ∂(circM.map Φ), w ∈ Kψ := by
    refine (ae_map_iff hΦc.measurable.aemeasurable hKc.isClosed.measurableSet).2 ?_
    rw [ae_iff]
    refine measure_mono_null (fun θ hθ => ?_) circM_compl
    intro hθI
    exact hθ ⟨θ, hθI, rfl⟩
  have hlim := hω q hq t ht
  rw [hν] at hlim ⊢
  exact Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hF hg.continuousOn hKc hKH one_pos
    (fun _ _ => rfl) hcarry hlim

/-- Continuity in the centre of the `g`-average over a pushed semicircle. -/
theorem continuousOn_fun_push {g : ℂ → ℝ} (hg : Continuous g) {a b ρ M m : ℝ} {ψ : ℂ → ℂ}
    (hψ : ψ ∈ BdryClass a b ρ M m) (hab : a ≤ b) {r : ℝ} (hr : 0 < r) (hrρ : 3 * r < ρ) :
    ContinuousOn (fun s : ℝ => ∫ w, g w ∂((foldedCircle (s : ℂ) r).map ψ))
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
  set F : ℝ → ℝ → ℝ := fun s θ => g (ψ (foldH (circleMap (s : ℂ) r θ))) with hF
  have hrep : ∀ s ∈ Icc (a - r) (b + r),
      ∫ w, g w ∂((foldedCircle (s : ℂ) r).map ψ) = ∫ θ, F s θ ∂circM := by
    intro s hs
    rw [swcN2_fc_map_eq hr.le (hψc.mono (hball s hs))]
    have hgc : Continuous fun θ : ℝ => ψ (foldH (circleMap (s : ℂ) r θ)) := by
      refine hψc.comp_continuous ?_ (hpt s hs)
      exact CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)
    rw [integral_map hgc.measurable.aemeasurable hg.aestronglyMeasurable]
  refine ContinuousOn.congr ?_ hrep
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) M).exists_bound_of_continuousOn
    hg.continuousOn
  refine continuousOn_of_dominated (bound := fun _ => C)
    (fun s _ => (hg.measurable.comp
      ((hψ.1.continuousOn.comp_continuous ?_ ?_).measurable)).aestronglyMeasurable)
    (fun s hs => Eventually.of_forall fun θ => ?_) (integrable_const _)
    (Eventually.of_forall fun θ => ?_)
  · exact CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)
  · exact hpt s ‹_›
  · exact hC _ (mem_closedBall_zero_iff.2 (hψ.2.1 _ (hpt s hs θ)))
  · have hg' : Continuous fun s : ℝ => foldH (circleMap (s : ℂ) r θ) := by
      refine CircleFubini.continuous_foldH'.comp ?_
      simp only [circleMap]
      exact Complex.continuous_ofReal.add continuous_const
    exact hg.comp_continuousOn (hψc.comp hg'.continuousOn fun s hs => hpt s hs θ)

set_option maxHeartbeats 1000000 in
/-- **Adding any continuous `g` at the level of `avgReg`, a.s. (one event), eventually in `k`,
over the family.** -/
theorem ae_avgReg_add_fun_family (Q : ℝ) (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, Continuous g → ∀ᶠ k in atTop, ∀ q ∈ K, ∀ t ∈ Icc a b,
      avgReg (coordChange (X ω + ofFun g) (Ψ q) Q) k (t : ℂ) =
        avgReg (coordChange (X ω) (Ψ q) Q) k (t : ℂ) +
          ∫ w, g w ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) := by
  obtain ⟨k₀, hid, -⟩ := swcN2_id hab hρ hm hΨ hL0 hL hπ hπK hπid Q hX
  obtain ⟨r₂, hr₂, hadd⟩ := ae_evalReg_add_fun_family hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  obtain ⟨r₃, hr₃, hpush⟩ := swcN2_push_ae hab hρ hm hΨ hL0 hL hπ hπK hπid hX
  set A : ℝ := |M| + 1 with hA
  have hA0 : 0 < A := by positivity
  set rs : ℝ := min (min r₂ r₃) (min (ρ / 16) (m * ρ ^ 2 / (128 * A))) with hrs
  have hrs0 : 0 < rs := lt_min (lt_min hr₂ hr₃) (lt_min (by positivity) (by positivity))
  have hsmall : ∀ᶠ k in atTop, radius k < rs :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).eventually (gt_mem_nhds hrs0)
  have hall : ∀ k : ℕ, ∀ᵐ ω ∂P, radius k < rs →
      (∀ g : ℂ → ℝ, Continuous g → ∀ q ∈ K, ∀ t ∈ Icc (a - radius k) (b + radius k),
        evalReg (X ω + ofFun g) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) =
          evalReg (X ω) ((foldedCircle (t : ℂ) (radius k)).map (Ψ q)) +
            ∫ w, g w ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q))) ∧
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
  filter_upwards [hid, ae_all_iff.2 hall] with ω hid' hall' g hg
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
  have hH := continuousOn_fun_push hg (hΨ q hq) hab.le hr0 (by linarith)
  have hEZ : ContinuousOn (fun s : ℝ =>
      evalReg (X ω + ofFun g) ((foldedCircle (s : ℂ) r).map (Ψ q)))
      (Icc (a - r) (b + r)) :=
    (hEX.add hH).congr fun s hs => hadd' g hg q hq s hs
  have hcc := swcN2_cc_continuousOn (hΨ q hq) hab.le hρ hm hr0 (by linarith) hrm
  have e1 := swcN2_avgReg_eq (X ω + ofFun g) (Ψ q) Q k ht (hr ▸ hEZ t htI)
    (hr ▸ hcc t htI)
  have e2 := (hid' k hk).1 q hq t ht
  rw [← hr] at e1 e2
  rw [e1, hadd' g hg q hq t htI, e2]
  ring

/-- **The `g`-average over a pushed semicircle is close to `g (ψ t)`**, given a modulus of
continuity `(ε, δ)` of `g` on the closed `M`-ball. -/
theorem gavg_push_close {g : ℂ → ℝ} (hg : Continuous g) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {ε δ : ℝ}
    (hgε : ∀ z ∈ closedBall (0 : ℂ) M, ∀ w ∈ closedBall (0 : ℂ) M, dist z w < δ →
      |g z - g w| ≤ ε)
    {t r : ℝ} (ht : t ∈ Icc a b) (hr : 0 < r) (hrρ : r < ρ / 2) (hrδ : 4 * M / ρ * r < δ) :
    |(∫ w, g w ∂((foldedCircle (t : ℂ) r).map ψ)) - g (ψ t)| ≤ ε := by
  have hball2 : closedBall (t : ℂ) r ⊆ thickening (ρ / 2) (segC a b) :=
    swcN2_ball_sub_thick ht hrρ
  have hball : closedBall (t : ℂ) r ⊆ thickening ρ (segC a b) :=
    swcN2_ball_sub_thick ht (by linarith)
  have hψc : ContinuousOn ψ (thickening ρ (segC a b)) := hψ.1.continuousOn
  have hpt : ∀ θ, foldH (circleMap (t : ℂ) r θ) ∈ closedBall (t : ℂ) r :=
    swcN2_fold_circle_mem hr.le
  set c : ℝ := g (ψ t) with hc
  set F : ℝ → ℝ := fun θ => g (ψ (foldH (circleMap (t : ℂ) r θ))) with hF
  have hgc : Continuous fun θ : ℝ => ψ (foldH (circleMap (t : ℂ) r θ)) :=
    (hψc.mono hball).comp_continuous
      (CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)) hpt
  have hrep : ∫ w, g w ∂((foldedCircle (t : ℂ) r).map ψ) = ∫ θ, F θ ∂circM := by
    rw [swcN2_fc_map_eq hr.le (hψc.mono hball)]
    rw [integral_map hgc.measurable.aemeasurable hg.aestronglyMeasurable]
  have hpw : ∀ θ, |F θ - c| ≤ ε := by
    intro θ
    have hmv : ‖ψ (foldH (circleMap (t : ℂ) r θ)) - ψ t‖ ≤
        4 * M / ρ * ‖foldH (circleMap (t : ℂ) r θ) - t‖ :=
      (convex_closedBall (t : ℂ) r).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hψ.1.differentiableAt (isOpen_thickening.mem_nhds (hball hz)))
        (fun z hz => norm_deriv_le_of_class hψ hρ (hball2 hz))
        (mem_closedBall_self hr.le) (hpt θ)
    have hdist : ‖foldH (circleMap (t : ℂ) r θ) - t‖ ≤ r := by
      have := hpt θ; rwa [mem_closedBall, dist_eq_norm] at this
    have hM0 : 0 ≤ 4 * M / ρ := by
      have := norm_deriv_le_of_class hψ hρ (hball2 (mem_closedBall_self hr.le))
      exact (norm_nonneg _).trans this
    refine hgε _ (mem_closedBall_zero_iff.2 (hψ.2.1 _ (hball (hpt θ))))
      _ (mem_closedBall_zero_iff.2 (hψ.2.1 _ (hball (mem_closedBall_self hr.le)))) ?_
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hmv.trans (mul_le_mul_of_nonneg_left hdist hM0)) hrδ
  have hFm : AEStronglyMeasurable F circM := (hg.comp hgc).aestronglyMeasurable
  have hFi : Integrable F circM := by
    refine Integrable.mono' (integrable_const (|c| + ε)) hFm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs]
    have := hpw θ
    have h1 := abs_sub_abs_le_abs_sub (F θ) c
    linarith
  rw [hrep]
  have e : ∫ θ, F θ ∂circM - c = ∫ θ, (F θ - c) ∂circM := by
    rw [integral_sub hFi (integrable_const c)]
    simp
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := circM) (f := fun θ => F θ - c) (C := ε)
    (Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hpw θ)
  rw [Real.norm_eq_abs] at this
  simpa using this

end G1Side
end QuantumZipper
