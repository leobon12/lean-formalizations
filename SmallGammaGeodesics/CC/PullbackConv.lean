import SmallGammaGeodesics.CC.PullbackCov

/-!
# Uniform convergence of zoomed pullbacks (track CC, packet CC1; [3] Lemma 2.4 (2.5))

Source: `planning/audits/CC0-conformal-covariance-plan.md`, §5.2 row CC1 ("uniform convergence of
zoomed pullbacks") and Details (a) D9 step 3 ("D1 gives uniform convergence with supports in
`B̄_R`"), for [3] Lemma 2.4 (2.5).

Let `ϕ` be holomorphic and injective on the open set `W`, `z ∈ W` and `a = ϕ'(z)` (`≠ 0`). Along
any filter on which `z_i → z` and `r_i → 0⁺`, the pullback of a continuous compactly supported `g`
by the zoomed map `ϕ̃_i(w) = r_i⁻¹(ϕ(z_i + r_i w) − ϕ(z_i))` converges **uniformly on `ℂ`** to the
linear pullback `w ↦ |a|² g(a w)` (`linPull`), with supports eventually in one ball:

* `exists_eventually_confPullFun_zoomMap_eq_zero` (supports; uses that the inverse of `ϕ` is
  Lipschitz near `ϕ(z)`);
* `tendstoUniformlyOn_confPullFun_zoomMap` (uniform closeness on balls; uses the strict
  differentiability of `ϕ` at `z` and the continuity of `ϕ'`);
* `tendstoUniformly_confPullFun_zoomMap` (uniform convergence on `ℂ`);
* with T7: `tendsto_logCov_confPullFun_zoomMap` and the GFF form
  `tendsto_integral_sq_confPullFun_zoomMap`.

Taking `z_i = z` gives the zoom at a fixed point as `r → 0⁺`; sequences `(z_n, r_n) → (z, 0⁺)` give
the uniformity in `z` that [3] Prop 2.1 needs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- **The linear pullback** `w ↦ |a|² g(a w)`, the pullback by `w ↦ a w`. -/
def linPull (a : ℂ) (g : ℂ → ℝ) : ℂ → ℝ := fun w => ‖a‖ ^ 2 * g (a * w)

private theorem deriv_const_mul_id (a w : ℂ) : deriv (fun w : ℂ => a * w) w = a := by
  simp

theorem confPullFun_mul_left (a : ℂ) (g : ℂ → ℝ) :
    confPullFun (fun w => a * w) univ g = linPull a g := by
  funext w
  rw [confPullFun_of_mem (mem_univ w), deriv_const_mul_id, linPull]

theorem linPull_eq_zero {a : ℂ} (ha : a ≠ 0) {g : ℂ → ℝ} {Rg : ℝ}
    (hgR : ∀ y, Rg < ‖y‖ → g y = 0) {w : ℂ} (hw : Rg / ‖a‖ < ‖w‖) : linPull a g w = 0 := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  have : Rg < ‖a * w‖ := by
    rw [norm_mul]
    rw [div_lt_iff₀ hpos] at hw
    linarith
  rw [linPull, hgR _ this, mul_zero]

/-! ### Mean-zero pullbacks as test functions -/

/-- The pullback of a mean-zero test function supported in `ϕ '' W`, as a mean-zero test
function (D1.1–D1.2: `∫ τg = ∫ g = 0`). -/
def confPullTest0 {ϕ : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (g : TestC0) (hg : tsupport (g.1 : ℂ → ℝ) ⊆ ϕ '' W) : TestC0 :=
  ⟨confPullTest hW hd hi g.1 hg, by
    rw [coe_confPullTest, integral_confPullFun hW hd hi
      fun y hy => image_eq_zero_of_notMem_tsupport fun h => hy (hg h)]
    exact g.2⟩

theorem confPullTest0_coe {ϕ : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (g : TestC0) (hg : tsupport (g.1 : ℂ → ℝ) ⊆ ϕ '' W) :
    ⇑(confPullTest0 hW hd hi g hg).1 = confPullFun ϕ W g.1 :=
  rfl

private theorem differentiableOn_mul_left (a : ℂ) :
    DifferentiableOn ℂ (fun w : ℂ => a * w) univ :=
  (differentiable_id.const_mul a).differentiableOn

private theorem injOn_mul_left {a : ℂ} (ha : a ≠ 0) : InjOn (fun w : ℂ => a * w) univ :=
  fun _ _ _ _ h => mul_left_cancel₀ ha h

private theorem image_mul_left_univ {a : ℂ} (ha : a ≠ 0) :
    (fun w : ℂ => a * w) '' univ = univ :=
  eq_univ_of_forall fun y => ⟨a⁻¹ * y, mem_univ _, by
    show a * (a⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩

/-- The linear pullback of a mean-zero test function, as a mean-zero test function (`a ≠ 0`). -/
def linPullTest0 {a : ℂ} (ha : a ≠ 0) (g : TestC0) : TestC0 :=
  confPullTest0 isOpen_univ (differentiableOn_mul_left a) (injOn_mul_left ha) g
    (by rw [image_mul_left_univ ha]; exact subset_univ _)

theorem linPullTest0_coe {a : ℂ} (ha : a ≠ 0) (g : TestC0) :
    ⇑(linPullTest0 ha g).1 = linPull a g.1 := by
  rw [linPullTest0, confPullTest0_coe, confPullFun_mul_left]

/-- A function with compact support vanishes outside some ball. -/
private theorem exists_eq_zero_of_lt_norm_of_hasCompactSupport {g : ℂ → ℝ}
    (hgs : HasCompactSupport g) :
    ∃ R : ℝ, ∀ y, R < ‖y‖ → g y = 0 := by
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R, fun y hy => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := mem_closedBall_zero_iff.1 (hR h)
  linarith

section Zoom

variable {ϕ : ℂ → ℂ} {W : Set ℂ} {z : ℂ} {ι : Type*} {l : Filter ι} {zs : ι → ℂ} {rs : ι → ℝ}

private theorem norm_real_mul {r : ℝ} (hr : 0 < r) (w : ℂ) : ‖(r : ℂ) * w‖ = r * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private theorem eventually_mul_lt {rs : ι → ℝ} (h2 : Tendsto rs l (𝓝[>] 0)) (C : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ i in l, rs i * C < ε := by
  have hr0 : Tendsto rs l (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin h2
  have : Tendsto (fun i => rs i * C) l (𝓝 (0 * C)) := hr0.mul_const C
  rw [zero_mul] at this
  exact this (Iio_mem_nhds hε)

/-- **Supports of zoomed pullbacks** stay in one ball: if `g` vanishes off `B̄_{R_g}`, then
eventually `τ_i g` vanishes off `B̄_M` for one `M`. Proof: the inverse `ψ` of `ϕ` is Lipschitz
(constant `K`) on a ball around `ϕ(z)`; if `τ_i g (w) ≠ 0` then `x = z_i + r_i w ∈ W` and
`|ϕ(x) − ϕ(z_i)| = r_i |ϕ̃_i(w)| ≤ r_i R_g`, so `r_i |w| = |ψ(ϕ x) − ψ(ϕ z_i)| ≤ K r_i R_g`. -/
theorem exists_eventually_confPullFun_zoomMap_eq_zero (hW : IsOpen W)
    (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ} {Rg : ℝ}
    (hgR : ∀ y, Rg < ‖y‖ → g y = 0) (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) :
    ∃ M : ℝ, ∀ᶠ i in l, ∀ w, M < ‖w‖ →
      confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g w = 0 := by
  set ψ := invFunOn ϕ W
  have hψ : ∀ x ∈ W, ψ (ϕ x) = x := fun x hx => hi.leftInvOn_invFunOn hx
  have hOpen := isOpen_image_conf hW hd hi
  have hϕz : ϕ z ∈ ϕ '' W := mem_image_of_mem ϕ hz
  have hstrict : HasStrictDerivAt ψ (deriv ψ (ϕ z)) (ϕ z) :=
    ((differentiableOn_leftInv hW hd hi hψ).analyticAt (hOpen.mem_nhds hϕz)).hasStrictDerivAt
  obtain ⟨K, s, hs, hK⟩ := HasStrictFDerivAt.exists_lipschitzOnWith hstrict
  obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhds_iff.1 hs
  set Rg' : ℝ := max Rg 0
  refine ⟨K * Rg', ?_⟩
  have hcont : ContinuousAt ϕ z := hd.continuousOn.continuousAt (hW.mem_nhds hz)
  have ev1 : ∀ᶠ i in l, ϕ (zs i) ∈ Metric.ball (ϕ z) (ρ / 2) :=
    (hcont.tendsto.comp h1) (Metric.ball_mem_nhds _ (half_pos hρ))
  have ev2 : ∀ᶠ i in l, zs i ∈ W := h1 (hW.mem_nhds hz)
  have ev3 : ∀ᶠ i in l, 0 < rs i := h2 self_mem_nhdsWithin
  filter_upwards [ev1, ev2, ev3, eventually_mul_lt h2 Rg' (half_pos hρ)] with i hi1 hi2 hi3 hi4 w hw
  by_contra hne
  have hwW : w ∈ zoomSet (zs i) (rs i) W := by
    by_contra hwW
    exact hne (confPullFun_of_notMem hwW)
  have hgne : g (zoomMap ϕ (zs i) (rs i) w) ≠ 0 := by
    intro h0
    apply hne
    rw [confPullFun_of_mem hwW, h0, mul_zero]
  have hnorm : ‖zoomMap ϕ (zs i) (rs i) w‖ ≤ Rg' := by
    by_contra hlt
    push Not at hlt
    exact hgne (hgR _ ((le_max_left _ _).trans_lt hlt))
  have hx : zs i + (rs i : ℂ) * w ∈ W := hwW
  have hϕx : ϕ (zs i + (rs i : ℂ) * w) = ϕ (zs i) + (rs i : ℂ) * zoomMap ϕ (zs i) (rs i) w :=
    (zoomAff_zoomMap hi3.ne' w).symm
  have hdist : dist (ϕ (zs i + (rs i : ℂ) * w)) (ϕ (zs i)) ≤ rs i * Rg' := by
    rw [hϕx, dist_eq_norm, add_sub_cancel_left, norm_real_mul hi3]
    exact mul_le_mul_of_nonneg_left hnorm hi3.le
  have hmem1 : ϕ (zs i) ∈ s := hρs (Metric.ball_subset_ball (half_le_self hρ.le) hi1)
  have hmem2 : ϕ (zs i + (rs i : ℂ) * w) ∈ s := by
    apply hρs
    rw [Metric.mem_ball] at hi1 ⊢
    calc dist (ϕ (zs i + (rs i : ℂ) * w)) (ϕ z)
        ≤ dist (ϕ (zs i + (rs i : ℂ) * w)) (ϕ (zs i)) + dist (ϕ (zs i)) (ϕ z) :=
          dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := by linarith
      _ = ρ := by ring
  have hlip := hK.dist_le_mul _ hmem2 _ hmem1
  rw [hψ _ hx, hψ _ hi2] at hlip
  have hdx : dist (zs i + (rs i : ℂ) * w) (zs i) = rs i * ‖w‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_real_mul hi3]
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have hle : rs i * ‖w‖ ≤ rs i * (K * Rg') := by
    calc rs i * ‖w‖ = dist (zs i + (rs i : ℂ) * w) (zs i) := hdx.symm
      _ ≤ K * dist (ϕ (zs i + (rs i : ℂ) * w)) (ϕ (zs i)) := hlip
      _ ≤ K * (rs i * Rg') := mul_le_mul_of_nonneg_left hdist hK0
      _ = rs i * (K * Rg') := by ring
  have := le_of_mul_le_mul_left hle hi3
  linarith

/-- **Uniform closeness on balls**: `τ_i g → linPull (ϕ' z) g` uniformly on every `B̄_M(0)`. Proof:
for `|w| ≤ M`, `x = z_i + r_i w → z`, so `|ϕ'(x)|² → |a|²`; and by strict differentiability of
`ϕ` at `z`, `|ϕ̃_i(w) − a w| = r_i⁻¹ |ϕ(x) − ϕ(z_i) − a r_i w| ≤ c |w|`, so
`g(ϕ̃_i w) − g(a w) → 0` by uniform continuity. -/
theorem tendstoUniformlyOn_confPullFun_zoomMap (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hz : z ∈ W) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) (M : ℝ) :
    TendstoUniformlyOn
      (fun i => confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g)
      (linPull (deriv ϕ z) g) l (Metric.closedBall 0 M) := by
  set a := deriv ϕ z
  obtain ⟨Mg, hMg⟩ := hgc.bounded_above_of_compact_support hgs
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hguc := hgs.uniformContinuous_of_continuous hgc
  set M' : ℝ := max M 0
  have hM' : 0 ≤ M' := le_max_right _ _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set η : ℝ := ε / (2 * (‖a‖ ^ 2 + 1))
  have hη : 0 < η := by positivity
  obtain ⟨δg, hδg, hg⟩ := Metric.uniformContinuous_iff.1 hguc η hη
  set η₁ : ℝ := ε / (2 * (Mg + 1))
  have hη₁ : 0 < η₁ := by positivity
  have hcd : ContinuousAt (fun u => ‖deriv ϕ u‖ ^ 2) z :=
    ((hd.deriv hW).continuousOn.continuousAt (hW.mem_nhds hz)).norm.pow 2
  obtain ⟨δ₁, hδ₁, hd₁⟩ := Metric.continuousAt_iff.1 hcd η₁ hη₁
  have hstrict : HasStrictDerivAt ϕ a z := (hd.analyticAt (hW.mem_nhds hz)).hasStrictDerivAt
  set c : ℝ := δg / (2 * (M' + 1))
  have hc : 0 < c := by positivity
  obtain ⟨δ₂, hδ₂, hd₂⟩ :=
    Metric.eventually_nhds_iff.1 ((HasStrictFDerivAt.isLittleO hstrict).bound hc)
  obtain ⟨δ₃, hδ₃, hd₃⟩ := Metric.isOpen_iff.1 hW z hz
  set δ : ℝ := min δ₁ (min δ₂ δ₃)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have ev1 : ∀ᶠ i in l, dist (zs i) z < δ / 2 := h1 (Metric.ball_mem_nhds _ (half_pos hδ))
  have ev3 : ∀ᶠ i in l, 0 < rs i := h2 self_mem_nhdsWithin
  filter_upwards [ev1, ev3, eventually_mul_lt h2 (M' + 1) (half_pos hδ)] with i hi1 hi3 hi4 w hw
  set r := rs i
  set x := zs i + (r : ℂ) * w with hxdef
  have hw' : ‖w‖ ≤ M' := (mem_closedBall_zero_iff.1 hw).trans (le_max_left _ _)
  have hrw : r * ‖w‖ < δ / 2 := by
    have : r * ‖w‖ ≤ r * (M' + 1) := mul_le_mul_of_nonneg_left (by linarith) hi3.le
    linarith
  have hdx : dist x (zs i) = r * ‖w‖ := by
    rw [hxdef, dist_eq_norm, add_sub_cancel_left, norm_real_mul hi3]
  have hxz : dist x z < δ := by
    calc dist x z ≤ dist x (zs i) + dist (zs i) z := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by rw [hdx]; linarith
      _ = δ := by ring
  have hxz1 : dist x z < δ₁ := hxz.trans_le (min_le_left _ _)
  have hxz2 : dist x z < δ₂ := hxz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxz3 : dist x z < δ₃ := hxz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hδδ₂ : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hziz2 : dist (zs i) z < δ₂ := by linarith
  have hxW : x ∈ W := hd₃ hxz3
  have hwW : w ∈ zoomSet (zs i) r W := hxW
  -- the value of the zoomed pullback
  have hval : confPullFun (zoomMap ϕ (zs i) r) (zoomSet (zs i) r W) g w =
      ‖deriv ϕ x‖ ^ 2 * g (zoomMap ϕ (zs i) r w) := by
    rw [confPullFun_of_mem hwW, deriv_zoomMap hi3.ne' (hd.differentiableAt (hW.mem_nhds hxW))]
  -- the zoomed map is close to `w ↦ a w`
  have hstr := hd₂ (y := (x, zs i)) (by
    rw [Prod.dist_eq]
    exact max_lt hxz2 hziz2)
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hstr
  have hclose : dist (zoomMap ϕ (zs i) r w) (a * w) < δg := by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hi3.ne'
    have e : zoomMap ϕ (zs i) r w - a * w = (r : ℂ)⁻¹ * (ϕ x - ϕ (zs i) - (x - zs i) * a) := by
      rw [zoomMap, hxdef]
      field_simp
      ring
    rw [dist_eq_norm, e, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hi3]
    have hxzi : ‖x - zs i‖ = r * ‖w‖ := by rw [← dist_eq_norm, hdx]
    calc r⁻¹ * ‖ϕ x - ϕ (zs i) - (x - zs i) * a‖ ≤ r⁻¹ * (c * ‖x - zs i‖) :=
          mul_le_mul_of_nonneg_left hstr (inv_nonneg.2 hi3.le)
      _ = c * ‖w‖ := by rw [hxzi]; field_simp
      _ ≤ c * M' := mul_le_mul_of_nonneg_left hw' hc.le
      _ < δg := by
          have : c * M' < c * (M' + 1) := mul_lt_mul_of_pos_left (by linarith) hc
          have e2 : c * (M' + 1) = δg / 2 := by
            simp only [c]
            field_simp
          linarith
  have hgclose := hg hclose
  rw [Real.dist_eq] at hgclose
  have hdclose := hd₁ hxz1
  rw [Real.dist_eq] at hdclose
  -- assemble
  rw [hval, Real.dist_eq, linPull]
  have hsplit : ‖a‖ ^ 2 * g (a * w) - ‖deriv ϕ x‖ ^ 2 * g (zoomMap ϕ (zs i) r w) =
      (‖a‖ ^ 2 - ‖deriv ϕ x‖ ^ 2) * g (zoomMap ϕ (zs i) r w) +
        ‖a‖ ^ 2 * (g (a * w) - g (zoomMap ϕ (zs i) r w)) := by ring
  have hA : |(‖a‖ ^ 2 - ‖deriv ϕ x‖ ^ 2) * g (zoomMap ϕ (zs i) r w)| ≤ η₁ * Mg := by
    rw [abs_mul]
    have h1' : |‖a‖ ^ 2 - ‖deriv ϕ x‖ ^ 2| ≤ η₁ := by
      rw [abs_sub_comm]
      exact hdclose.le
    have h2' : |g (zoomMap ϕ (zs i) r w)| ≤ Mg := by
      have := hMg (zoomMap ϕ (zs i) r w)
      rwa [Real.norm_eq_abs] at this
    exact mul_le_mul h1' h2' (abs_nonneg _) hη₁.le
  have hB : |‖a‖ ^ 2 * (g (a * w) - g (zoomMap ϕ (zs i) r w))| ≤ ‖a‖ ^ 2 * η := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [abs_sub_comm]
    exact hgclose.le
  have hA' : η₁ * Mg ≤ ε / 2 := by
    simp only [η₁]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hB' : ‖a‖ ^ 2 * η < ε / 2 := by
    simp only [η]
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ‖a‖]
  rw [hsplit]
  calc |(‖a‖ ^ 2 - ‖deriv ϕ x‖ ^ 2) * g (zoomMap ϕ (zs i) r w) +
        ‖a‖ ^ 2 * (g (a * w) - g (zoomMap ϕ (zs i) r w))|
      ≤ |(‖a‖ ^ 2 - ‖deriv ϕ x‖ ^ 2) * g (zoomMap ϕ (zs i) r w)| +
        |‖a‖ ^ 2 * (g (a * w) - g (zoomMap ϕ (zs i) r w))| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Uniform convergence of zoomed pullbacks** (CC0 §5.2 row CC1, D9 step 3): along any filter
with `z_i → z ∈ W` and `r_i → 0⁺`, `τ_i g → linPull (ϕ' z) g` uniformly on `ℂ`. -/
theorem tendstoUniformly_confPullFun_zoomMap (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) :
    TendstoUniformly
      (fun i => confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g)
      (linPull (deriv ϕ z) g) l := by
  have ha : deriv ϕ z ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn hW hd hi hz
  obtain ⟨Rg, hRg⟩ := exists_eq_zero_of_lt_norm_of_hasCompactSupport hgs
  obtain ⟨MA, hMA⟩ := exists_eventually_confPullFun_zoomMap_eq_zero hW hd hi hz hRg h1 h2
  set M : ℝ := max MA (Rg / ‖deriv ϕ z‖)
  have hB := tendstoUniformlyOn_confPullFun_zoomMap hW hd hz hgc hgs h1 h2 M
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformlyOn_iff] at hB
  intro ε hε
  filter_upwards [hB ε hε, hMA] with i hiB hiA w
  by_cases hw : ‖w‖ ≤ M
  · exact hiB w (mem_closedBall_zero_iff.2 hw)
  · push Not at hw
    rw [hiA w ((le_max_left _ _).trans_lt hw),
      linPull_eq_zero ha hRg ((le_max_right _ _).trans_lt hw), dist_self]
    exact hε

/-- The supports of the zoomed pullbacks and of the limit lie eventually in one ball. -/
theorem exists_eventually_support_confPullFun_zoomMap (hW : IsOpen W)
    (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ}
    (hgs : HasCompactSupport g) (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) :
    ∃ R : ℝ, (∀ᶠ i in l, ∀ w, R < ‖w‖ →
      confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g w = 0) ∧
      ∀ w, R < ‖w‖ → linPull (deriv ϕ z) g w = 0 := by
  have ha : deriv ϕ z ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn hW hd hi hz
  obtain ⟨Rg, hRg⟩ := exists_eq_zero_of_lt_norm_of_hasCompactSupport hgs
  obtain ⟨MA, hMA⟩ := exists_eventually_confPullFun_zoomMap_eq_zero hW hd hi hz hRg h1 h2
  refine ⟨max MA (Rg / ‖deriv ϕ z‖), ?_, fun w hw =>
    linPull_eq_zero ha hRg ((le_max_right _ _).trans_lt hw)⟩
  filter_upwards [hMA] with i hi w hw
  exact hi w ((le_max_left _ _).trans_lt hw)

/-- **(2.5) for zoomed pullbacks**: `logCov (τ_i g − τ₀ g) (τ_i g − τ₀ g) → 0`. -/
theorem tendsto_logCov_confPullFun_zoomMap (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) :
    Tendsto (fun i =>
      logCov (confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g -
          linPull (deriv ϕ z) g)
        (confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g -
          linPull (deriv ϕ z) g)) l (𝓝 0) := by
  obtain ⟨R, hR, hR₀⟩ := exists_eventually_support_confPullFun_zoomMap hW hd hi hz hgs h1 h2
  exact tendsto_logCov_sub_of_tendstoUniformly
    (tendstoUniformly_confPullFun_zoomMap hW hd hi hz hgc hgs h1 h2) hR hR₀

/-- **(2.5) for zoomed pullbacks, GFF form**: if mean-zero test functions `τ i` are eventually the
zoomed pullbacks of `g` and `τ₀` is its linear pullback, then `E⟨h, τ i − τ₀⟩² → 0`. -/
theorem tendsto_integral_sq_confPullFun_zoomMap {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (hW : IsOpen W)
    (hd : DifferentiableOn ℂ ϕ W) (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0))
    {τ : ι → TestC0} {τ₀ : TestC0}
    (hτ : ∀ᶠ i in l, ⇑(τ i).1 = confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g)
    (hτ₀ : ⇑τ₀.1 = linPull (deriv ϕ z) g) :
    Tendsto (fun i => ∫ ω, (h ω (τ i).1 - h ω τ₀.1) ^ 2 ∂P) l (𝓝 0) := by
  obtain ⟨R, hR, hR₀⟩ := exists_eventually_support_confPullFun_zoomMap hW hd hi hz hgs h1 h2
  have hu := tendstoUniformly_confPullFun_zoomMap hW hd hi hz hgc hgs h1 h2
  have hu' : TendstoUniformly (fun i x => (τ i).1 x) (fun x => τ₀.1 x) l := by
    rw [show (fun x => τ₀.1 x) = linPull (deriv ϕ z) g from hτ₀]
    refine (tendstoUniformly_congr ?_).2 hu
    filter_upwards [hτ] with i hi
    exact hi
  refine tendsto_integral_sq_sub_of_tendstoUniformly hh hu' (R := R) ?_ ?_
  · filter_upwards [hR, hτ] with i hi hτi x hx
    rw [show (τ i).1 x = confPullFun (zoomMap ϕ (zs i) (rs i)) (zoomSet (zs i) (rs i) W) g x from
      congrFun hτi x]
    exact hi x hx
  · intro x hx
    rw [show τ₀.1 x = linPull (deriv ϕ z) g x from congrFun hτ₀ x]
    exact hR₀ x hx

/-- The zoomed image eventually contains any compact set: if `tsupport g` is compact, then
eventually `tsupport g ⊆ ϕ̃_i '' W̃_i`, so the zoomed pullbacks of a test function are test
functions (`confPullTest`). -/
theorem eventually_tsupport_subset_zoom (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) (hz : z ∈ W) {g : ℂ → ℝ} (hgs : HasCompactSupport g)
    (h1 : Tendsto zs l (𝓝 z)) (h2 : Tendsto rs l (𝓝[>] 0)) :
    ∀ᶠ i in l, tsupport g ⊆ zoomMap ϕ (zs i) (rs i) '' zoomSet (zs i) (rs i) W := by
  have hOpen := isOpen_image_conf hW hd hi
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hOpen (ϕ z) (mem_image_of_mem ϕ hz)
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set R' : ℝ := max R 0
  have hcont : ContinuousAt ϕ z := hd.continuousOn.continuousAt (hW.mem_nhds hz)
  have ev1 : ∀ᶠ i in l, ϕ (zs i) ∈ Metric.ball (ϕ z) (ρ / 2) :=
    (hcont.tendsto.comp h1) (Metric.ball_mem_nhds _ (half_pos hρ))
  have ev3 : ∀ᶠ i in l, 0 < rs i := h2 self_mem_nhdsWithin
  filter_upwards [ev1, ev3, eventually_mul_lt h2 R' (half_pos hρ)] with i hi1 hi3 hi4 y hy
  rw [image_zoomMap_zoomSet hi3.ne', mem_zoomSet]
  apply hρW
  rw [Metric.mem_ball] at hi1 ⊢
  have hyR : ‖y‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hy)).trans (le_max_left _ _)
  calc dist (ϕ (zs i) + (rs i : ℂ) * y) (ϕ z)
      ≤ dist (ϕ (zs i) + (rs i : ℂ) * y) (ϕ (zs i)) + dist (ϕ (zs i)) (ϕ z) :=
        dist_triangle _ _ _
    _ = rs i * ‖y‖ + dist (ϕ (zs i)) (ϕ z) := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_real_mul hi3]
    _ < ρ / 2 + ρ / 2 := by
        have : rs i * ‖y‖ ≤ rs i * R' := mul_le_mul_of_nonneg_left hyR hi3.le
        linarith
    _ = ρ := by ring

end Zoom

end SmallGammaGeodesics.CC
