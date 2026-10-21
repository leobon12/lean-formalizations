import SmallGammaGeodesics.Upper.Interfaces
import SmallGammaGeodesics.Probes.Bounds
import SmallGammaGeodesics.CC.Pullback
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The inverse probe map (blueprint `lem:probe-inverse`; BP2 detail D7; packet P-U2)

For `|θ| ≤ ε_ψ ℓ_j` the probe map `ϕ = z + iθH_{j,a}` is holomorphic and injective on the strip
`S_j = {|Im z| < ℓ_j}` (P-B1's `probeMap_geometry`), with `|ϕ(z) − z| ≤ C₀|θ| ≤ ℓ_j/4` and
`|ϕ'(z) − 1| ≤ 1/4` on the closed strip (`probeMap_bounds`). Its inverse on the strip is
`ψ = probeInv j a θ = Function.invFunOn ϕ S_j` (`Upper/Interfaces.lean`). Results:

* `probeInv_spec` (BP2's planned statement, verbatim):
  (a) the bounds on `ϕ`; (b) for `|Im w| ≤ ℓ_j/2`, `ψ(w) ∈ S_j`, `ϕ(ψ w) = w` and
  `|ψ(w) − w| ≤ C₀|θ|`; (c) `ψ(ϕ z) = z` on `S_j`; `ψ` is holomorphic on `ϕ(S_j)` and Borel;
  (d) `|t − t'| ≤ (3/2) |ψ t − ψ t'|` for `t, t' ∈ [0,1]`.

Proof of (b) (blueprint): the map `T_w(z) = w − (ϕ(z) − z)` sends the closed disc `B̄(w, ℓ/4)`
(contained in `{|Im z| ≤ 3ℓ/4}`) into itself and is `1/4`-Lipschitz there (mean value theorem on
the convex disc), so it has a fixed point `z_w` (Banach); `ϕ(z_w) = w`, and injectivity of `ϕ` on
`S_j` identifies `invFunOn ϕ S_j w = z_w`. Borel measurability: `ψ` is continuous on the open set
`ϕ(S_j)` and equal to the constant `Classical.choice _` off it (`ContinuousOn.measurable_piecewise`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Function
open scoped NNReal

namespace SmallGammaGeodesics

/-! ## Helper facts on the strip -/

theorem isOpen_probeStrip (j : ℕ) : IsOpen (probeStrip j) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem probeInv_leftInvOn {j : ℕ} {a θ : ℝ} (hi : InjOn (probeMap j a θ) (probeStrip j)) :
    ∀ z ∈ probeStrip j, probeInv j a θ (probeMap j a θ z) = z :=
  fun _ hz => hi.leftInvOn_invFunOn hz

/-- The inverse probe map is Borel as soon as `ϕ` is holomorphic and injective on the strip:
it is continuous on the open set `ϕ(S_j)` and constant off it. -/
theorem measurable_probeInv_of {j : ℕ} {a θ : ℝ}
    (hd : DifferentiableOn ℂ (probeMap j a θ) (probeStrip j))
    (hi : InjOn (probeMap j a θ) (probeStrip j)) : Measurable (probeInv j a θ) := by
  classical
  set S := probeMap j a θ '' probeStrip j with hSdef
  have hSo : IsOpen S := CC.isOpen_image_conf (isOpen_probeStrip j) hd hi
  have hcont : ContinuousOn (probeInv j a θ) S :=
    CC.continuousOn_leftInv (isOpen_probeStrip j) hd hi (probeInv_leftInvOn hi)
  have heq : probeInv j a θ =
      S.piecewise (probeInv j a θ) (fun _ => Classical.choice (inferInstance : Nonempty ℂ)) := by
    funext w
    by_cases hw : w ∈ S
    · rw [piecewise_eq_of_mem _ _ _ hw]
    · rw [piecewise_eq_of_notMem _ _ _ hw]
      unfold probeInv
      refine invFunOn_neg fun ⟨z, hz, hzw⟩ => hw ⟨z, hz, hzw⟩
  rw [heq]
  exact hcont.measurable_piecewise continuousOn_const hSo.measurableSet

/-! ## The inverse probe map -/

/-- **Lemma `lem:probe-inverse`** (BP2 D7): the inverse probe map `ψ = probeInv j a θ`. -/
theorem probeInv_spec : ∃ εψ C₀, 0 < εψ ∧ 0 ≤ C₀ ∧ ∀ (j : ℕ) (a θ : ℝ), |θ| ≤ εψ * ell j →
    (∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ C₀ * |θ| ∧
      ‖deriv (probeMap j a θ) z - 1‖ ≤ 1/4) ∧
    (∀ w : ℂ, |w.im| ≤ ell j / 2 → probeInv j a θ w ∈ probeStrip j ∧
        probeMap j a θ (probeInv j a θ w) = w ∧ ‖probeInv j a θ w - w‖ ≤ C₀ * |θ|) ∧
    (∀ z ∈ probeStrip j, probeInv j a θ (probeMap j a θ z) = z) ∧
    DifferentiableOn ℂ (probeInv j a θ) (probeMap j a θ '' probeStrip j) ∧
    Measurable (probeInv j a θ) ∧
    ∀ t ∈ Icc (0:ℝ) 1, ∀ t' ∈ Icc (0:ℝ) 1,
      |t - t'| ≤ 3/2 * ‖probeInv j a θ t - probeInv j a θ t'‖ := by
  obtain ⟨εg, hεg, hgeo⟩ := probeMap_geometry
  obtain ⟨C, hC0, hCb⟩ := probeMap_bounds
  refine ⟨min εg (1 / (4 * C + 4)), C, lt_min hεg (by positivity), hC0, fun j a θ hθ => ?_⟩
  have hℓ := ell_pos j
  have hθg : |θ| ≤ εg * ell j := hθ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hℓ.le)
  have hθe : |θ| ≤ 1 / (4 * C + 4) * ell j :=
    hθ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hℓ.le)
  obtain ⟨hd, hi, -, -⟩ := hgeo j a θ hθg
  -- `C|θ| ≤ ℓ/4`
  have hCθ : C * |θ| ≤ ell j / 4 := by
    have h1 : C * |θ| ≤ C * (1 / (4 * C + 4) * ell j) := mul_le_mul_of_nonneg_left hθe hC0
    have h3 : C * (1 / (4 * C + 4)) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have h2 : C * (1 / (4 * C + 4) * ell j) ≤ ell j / 4 :=
      calc C * (1 / (4 * C + 4) * ell j) = (C * (1 / (4 * C + 4))) * ell j := by ring
        _ ≤ 1 / 4 * ell j := mul_le_mul_of_nonneg_right h3 hℓ.le
        _ = ell j / 4 := by ring
    linarith
  -- (a) the bounds on the closed strip
  have ha : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeMap j a θ z - z‖ ≤ C * |θ| ∧
      ‖deriv (probeMap j a θ) z - 1‖ ≤ 1 / 4 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hCb j a θ z hz
    refine ⟨h1, h2.trans ?_⟩
    rw [div_le_iff₀ hℓ]
    linarith
  -- (b) the fixed point
  have hb : ∀ w : ℂ, |w.im| ≤ ell j / 2 → probeInv j a θ w ∈ probeStrip j ∧
      probeMap j a θ (probeInv j a θ w) = w ∧ ‖probeInv j a θ w - w‖ ≤ C * |θ| := by
    intro w hw
    set B := closedBall w (ell j / 4) with hBdef
    set T : ℂ → ℂ := fun z => w - (probeMap j a θ z - z) with hTdef
    have hBim : ∀ z ∈ B, |z.im| ≤ 3 * ell j / 4 := by
      intro z hz
      have h1 : |z.im - w.im| ≤ ell j / 4 := by
        rw [← Complex.sub_im]
        exact (Complex.abs_im_le_norm _).trans (mem_closedBall_iff_norm.1 hz)
      have h2 := abs_sub_abs_le_abs_sub z.im w.im
      linarith
    have hBstrip : ∀ z ∈ B, |z.im| ≤ ell j := fun z hz => (hBim z hz).trans (by linarith)
    have hmaps : MapsTo T B B := by
      intro z hz
      rw [mem_closedBall_iff_norm]
      have : T z - w = -(probeMap j a θ z - z) := by simp only [hTdef]; ring
      rw [this, norm_neg]
      exact ((ha z (hBstrip z hz)).1).trans hCθ
    have hderT : ∀ z, HasDerivAt T (-(deriv (probeMap j a θ) z - 1)) z := by
      intro z
      have h := (hasDerivAt_const z w).sub ((hasDerivAt_probeMap j a θ z).sub (hasDerivAt_id' z))
      rw [(hasDerivAt_probeMap j a θ z).deriv]
      exact h.congr_deriv (by ring)
    have hlip : LipschitzOnWith (1 / 4 : ℝ≥0) T B := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have := (convex_closedBall w (ell j / 4)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := T) (fun z _ => (hderT z).hasDerivWithinAt)
        (fun z hz => by rw [norm_neg]; exact (ha z (hBstrip z hz)).2) hy hx
      simpa using this
    have hcontr : ContractingWith (1 / 4 : ℝ≥0) (hmaps.restrict T B B) :=
      ⟨by norm_num, hlip.mapsToRestrict hmaps⟩
    obtain ⟨z, hzB, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
      (mem_closedBall_self (by positivity)) (edist_ne_top _ _)
    have hTz : T z = z := hfix
    have hφz : probeMap j a θ z = w := by
      have : w - (probeMap j a θ z - z) = z := hTz
      linear_combination -this
    have hzS : z ∈ probeStrip j := by
      show |z.im| < ell j
      linarith [hBim z hzB]
    have hex : ∃ x ∈ probeStrip j, probeMap j a θ x = w := ⟨z, hzS, hφz⟩
    obtain ⟨hmem, heq⟩ := invFunOn_pos hex
    have hψz : probeInv j a θ w = z := hi hmem hzS (heq.trans hφz.symm)
    refine ⟨hmem, heq, ?_⟩
    rw [hψz]
    have : z - w = -(probeMap j a θ z - z) := by rw [hφz]; ring
    rw [this, norm_neg]
    exact (ha z (hBstrip z hzB)).1
  have hc := probeInv_leftInvOn hi
  have hdiff : DifferentiableOn ℂ (probeInv j a θ) (probeMap j a θ '' probeStrip j) :=
    CC.differentiableOn_leftInv (isOpen_probeStrip j) hd hi hc
  refine ⟨ha, hb, hc, hdiff, measurable_probeInv_of hd hi, fun t ht t' ht' => ?_⟩
  -- (d) the lower Lipschitz bound on `[0,1]`
  have hreal : ∀ s : ℝ, |((s : ℂ)).im| ≤ ell j / 2 := fun s => by
    rw [Complex.ofReal_im, abs_zero]; positivity
  obtain ⟨hm, hφ, -⟩ := hb t (hreal t)
  obtain ⟨hm', hφ', -⟩ := hb t' (hreal t')
  have hbd : ∀ z ∈ probeStrip j, ‖deriv (probeMap j a θ) z‖ ≤ 5 / 4 := by
    intro z hz
    have h1 := (ha z (le_of_lt hz)).2
    calc ‖deriv (probeMap j a θ) z‖ = ‖(deriv (probeMap j a θ) z - 1) + 1‖ := by ring_nf
      _ ≤ ‖deriv (probeMap j a θ) z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 / 4 := by rw [norm_one]; linarith
  have hmvt := (convex_probeStrip j).norm_image_sub_le_of_norm_deriv_le
    (f := probeMap j a θ) (fun z _ => (hasDerivAt_probeMap j a θ z).differentiableAt) hbd hm' hm
  rw [hφ, hφ'] at hmvt
  have hn : ‖(t : ℂ) - t'‖ = |t - t'| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hmvt
  have h0 := norm_nonneg (probeInv j a θ t - probeInv j a θ t')
  linarith

end SmallGammaGeodesics
