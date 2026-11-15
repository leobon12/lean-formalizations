/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Complex.DerivLog
import QuantumZipper.Proofs.Complex.KoebeDistortion

/-!
# Growth of conformal maps of the disk: distance to the boundary and `arg f'`

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 28, `source/spec/p145-192.md`,
`#aux-28-proof`, pp. 162–163). For `f` holomorphic and injective on the unit disk:

* "The Koebe quarter and derivative distortion theorems give, for `|ζ| = r`,
  `dist(f(ζ), ∂C) ≥ |f'(0)| (1 − r)² / 16`": here `dist(f(ζ), (f 𝔻)ᶜ) ≥ c |f'(0)| (1 − r)^{1 + C₂}`
  with QuantumZipper's non-sharp constants (`koebeCovConst`, `koebeDistExp`)
  (`koebe_mul_pow_le_infDist`);
* "The standard second-coefficient estimate … In particular `|f''/f'|(ζ) ≤ 6/(1 − |ζ|²)`.
  Integrating a branch of `log f'` along radii yields `|arg f'(ζ) − arg f'(0)| ≤ 3 log((1+r)/(1−r))`":
  here, for every holomorphic logarithm `ℓ` of `f'`, `|ℓ(ζ) − ℓ(0)| ≤ C₂ log(1/(1 − |ζ|))`
  (`norm_derivLog_sub_le`), from QuantumZipper's weak Bieberbach inequality
  `r ‖f''(c)‖ ≤ C₂ ‖f'(c)‖` (`QuantumZipper.CA.Koebe.mul_norm_deriv2_le`) in place of `|a₂| ≤ 2`.
  Only a logarithmic bound with some constant is used by Aux. lemma 28.
-/

noncomputable section

open Complex Metric Set Filter Topology
open scoped Real

namespace InteractingSLE.Sec6

open QuantumZipper.CA.Koebe

/-- The unit disk is simply connected. -/
theorem isSimplyConnected_unitBall : IsSimplyConnected (ball (0 : ℂ) 1) := by
  have : ContractibleSpace (ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The derivative of a logarithm of `g'` is `g''/g'`. -/
theorem deriv_derivLog {g ℓ : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hℓ : IsDerivLog g ℓ D) {w : ℂ} (hw : w ∈ D) :
    HasDerivAt ℓ (deriv (deriv g) w / deriv g w) w := by
  have hℓd : DifferentiableAt ℂ ℓ w := hℓ.1.differentiableAt (hDo.mem_nhds hw)
  have hexp : HasDerivAt (fun z => exp (ℓ z)) (exp (ℓ w) * deriv ℓ w) w :=
    (Complex.hasDerivAt_exp (ℓ w)).comp w hℓd.hasDerivAt
  have heq : (fun z => exp (ℓ z)) =ᶠ[𝓝 w] deriv g :=
    eventually_of_mem (hDo.mem_nhds hw) fun z hz => hℓ.2 z hz
  have hd2 : deriv (deriv g) w = exp (ℓ w) * deriv ℓ w := by
    rw [← heq.deriv_eq]; exact hexp.deriv
  have hne : deriv g w ≠ 0 := by rw [← hℓ.2 w hw]; exact Complex.exp_ne_zero _
  rw [hd2, ← hℓ.2 w hw, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]
  exact hℓd.hasDerivAt

/-- **Logarithmic growth of `log f'`.** For `g` univalent on the unit disk and any holomorphic
logarithm `ℓ` of `g'`, `‖ℓ(ζ) − ℓ(0)‖ ≤ C₂ log(1/(1 − |ζ|))`. -/
theorem norm_derivLog_sub_le {g ℓ : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hinj : InjOn g (ball 0 1)) (hℓ : IsDerivLog g ℓ (ball 0 1)) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    ‖ℓ ζ - ℓ 0‖ ≤ koebeDistExp * (-Real.log (1 - ‖ζ‖)) := by
  have hζ1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
  -- the pointwise bound `‖ℓ'(w)‖ ≤ C₂ / (1 − ‖w‖)`
  have hbound : ∀ w ∈ ball (0 : ℂ) 1,
      ‖deriv (deriv g) w / deriv g w‖ ≤ koebeDistExp / (1 - ‖w‖) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hsub : ball w (1 - ‖w‖) ⊆ ball 0 1 := by
      intro z hz
      rw [mem_ball_zero_iff]
      have := mem_ball.1 hz
      rw [dist_eq_norm] at this
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hK := mul_norm_deriv2_le (hg.mono hsub) (hinj.mono hsub) (by linarith)
    have hne : deriv g w ≠ 0 := by rw [← hℓ.2 w hw]; exact Complex.exp_ne_zero _
    rw [norm_div, div_le_div_iff₀ (norm_pos_iff.2 hne) (by linarith)]
    linarith
  -- the radial path
  set B : ℝ → ℝ := fun s => koebeDistExp * (-Real.log (1 - s * ‖ζ‖))
  set B' : ℝ → ℝ := fun s => koebeDistExp * (‖ζ‖ / (1 - s * ‖ζ‖))
  set f : ℝ → ℂ := fun s => ℓ ((s : ℂ) * ζ) - ℓ 0
  set f' : ℝ → ℂ := fun s => deriv (deriv g) ((s : ℂ) * ζ) / deriv g ((s : ℂ) * ζ) * ζ
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) * ζ ∈ ball (0 : ℂ) 1 := by
    intro s hs
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [norm_nonneg ζ, hs.2]
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < 1 - s * ‖ζ‖ := by
    intro s hs; nlinarith [norm_nonneg ζ, hs.2, hs.1]
  have hfd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s := by
    intro s hs
    have h1 := deriv_derivLog isOpen_ball hℓ (hmem s hs)
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ s := by
      simpa using (hasDerivAt_id (s : ℂ)).comp_ofReal.mul_const ζ
    exact (h1.comp s h2).sub_const _
  have hBd : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt B (B' s) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s * ‖ζ‖) (-‖ζ‖) s := by
      simpa using ((hasDerivAt_id s).mul_const ‖ζ‖).const_sub 1
    have h2 := ((h1.log (hpos s hs).ne').neg).const_mul koebeDistExp
    refine h2.congr_deriv ?_
    simp only [B']
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (a := 0) (b := 1) (f := f)
    (f' := f') (B := B) (B' := B')
    (fun s hs => (hfd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hfd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (by simp [f, B])
    (fun s hs => (hBd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hBd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have hb := hbound _ (hmem s hs')
      have hn : ‖(s : ℂ) * ζ‖ = s * ‖ζ‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]
      rw [hn] at hb
      simp only [f', B', norm_mul]
      calc ‖deriv (deriv g) ((s : ℂ) * ζ) / deriv g ((s : ℂ) * ζ)‖ * ‖ζ‖
          ≤ koebeDistExp / (1 - s * ‖ζ‖) * ‖ζ‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = koebeDistExp * (‖ζ‖ / (1 - s * ‖ζ‖)) := by ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  simpa [f, B] using key

/-- **Koebe's distance bound.** For `f` univalent on the unit disk,
`koebeCovConst ‖f'(0)‖ (1 − |ζ|)^{1 + C₂} ≤ dist(f(ζ), (f 𝔻)ᶜ)`. -/
theorem koebe_mul_pow_le_infDist {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) 1) :
    koebeCovConst * ‖deriv f 0‖ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) ≤
      infDist (f ζ) (f '' ball 0 1)ᶜ := by
  have h1 := koebeCovConst_mul_le_infDist_of_mem hf hinj hζ
  have h2 := distortion_le_norm_deriv hf hinj hζ
  rw [dist_zero_right, div_one] at h2
  rw [dist_zero_right] at h1
  have hζ1 : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
  have hc : 0 ≤ koebeCovConst := by unfold koebeCovConst; positivity
  calc koebeCovConst * ‖deriv f 0‖ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)
      = koebeCovConst * (1 - ‖ζ‖) * (‖deriv f 0‖ * (1 - ‖ζ‖) ^ koebeDistExp) := by
        rw [Real.rpow_add hζ1, Real.rpow_one]; ring
    _ ≤ koebeCovConst * (1 - ‖ζ‖) * ‖deriv f ζ‖ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := h1

/-- `log(1/x) ≤ 4 x^{−1/4}` for `0 < x`. -/
theorem neg_log_le_four_mul_rpow {x : ℝ} (hx : 0 < x) : -Real.log x ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-(1 / 4 : ℝ)))
  rw [Real.log_rpow hx] at h
  have : 0 < x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx _
  linarith

end InteractingSLE.Sec6
