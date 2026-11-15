/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Two

/-!
# (D9), fifth part: the upper bounds — real images and drivers of hulls in a disc

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, Part A.1.3 (`ig1_followup_proofs.txt` L300–L340, ruling
R38): "The same argument at each protected force mark controls all derivative and distance ratios in (D6)." The lower
bounds of the separations `|E|`, `|E_{j,m}|`, `|C_{mn}|` are PROVE-ZHAN-GT4-A6's; here are the upper bounds, uniform over
all drivers whose hulls stay in a fixed disc `B̄(c, R)`:

* `norm_sol_add_sub_le`: at a real point `x` alive at time `t`, `|g_t(x) − c| ≤ |x − c| + 5R` (the boundary value of
  `IsMapOut.norm_sub_center_le`);
* `abs_driver_sub_le`: the driver stays in `[c − 7R, c + 7R]` (the real points `c ± 2R` are alive, their images lie on
  the two sides of the driver and within `7R` of `c`) — the classical bound of the driving function by the radius of
  the hull;
* `norm_fwdMap_real_le`: `|f_t(x)| = |g_t(x) − W_t| ≤ |x − c| + 12R` at a real alive point;
* `norm_fwdMap_sub_ge_of_gap`: the lower bound `|x − y| e^{−2t/γ²} ≤ |f_t(x) − f_t(y)|` for two real points whose images
  stay `γ` away from the driver (the plain-chain form of `ImgData.norm_fwdMap_sub_bounds`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull)

/-! ### Real points of hulls in a disc -/

/-- **The boundary value of the disc bound.** If `K_t ⊆ B̄(c, R)` and the real point `x` is alive at time `t`, then
`|g_t(x) − c| ≤ |x − c| + 5R`, where `g_t(x) = v(t) + W_t` is the boundary value of the mapping-out function
(`IsMapOut.norm_sub_center_le` at the points of `ℍ` near `x`, which are outside `K_t`, and the limit). -/
theorem norm_sol_add_sub_le {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {c R : ℝ} (hR : 0 < R)
    (hK : fwdHull W t ⊆ closedBall (c : ℂ) R) {x : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) t v) :
    ‖v t + W t - c‖ ≤ ‖(x : ℂ) - c‖ + 5 * R := by
  have hg := isMapOut_fwdMap_gen hW ht
  have hhull := isHPHull_fwdHull hW ht
  have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hlim : Tendsto (fun z => ‖fwdMap W t z + W t - c‖) (𝓝[H] (x : ℂ)) (𝓝 ‖v t + W t - c‖) :=
    (((tendsto_fwdMap_of_isForwardSol hW ht hv).add_const _).sub_const _).norm
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hv
  have hsmall : Tendsto (fun z : ℂ => ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * t)) (𝓝 (x : ℂ)) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * t)) := by fun_prop
    simpa using hc.tendsto (x : ℂ)
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), ‖fwdMap W t z + W t - c‖ ≤ ‖z - c‖ + 5 * R := by
    filter_upwards [(hsmall.eventually (gt_mem_nhds hδ)).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hzH
    have hzK : z ∉ fwdHull W t := not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hzH hz
    exact hg.norm_sub_center_le hhull hR hK ⟨hzH, hzK⟩
  have hc : Continuous (fun z : ℂ => ‖z - c‖ + 5 * R) := by fun_prop
  have hcont : Tendsto (fun z : ℂ => ‖z - c‖ + 5 * R) (𝓝[H] (x : ℂ)) (𝓝 (‖(x : ℂ) - c‖ + 5 * R)) :=
    (hc.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hlim hcont hev

/-- **The driver of a hull in a disc.** If `K_τ ⊆ B̄(c, R)` and `|W_0 − c| ≤ R`, then `|W_s − c| ≤ 7R` for every
`s ∈ [0, τ]`: the real points `c ± 2R` are alive up to `τ`, their images `g_s(c ± 2R)` lie on the two sides of the
driver (order of real flows) and within `7R` of `c` (`norm_sol_add_sub_le`). -/
theorem abs_driver_sub_le {W : ℝ → ℝ} (hW : Continuous W) {τ c R : ℝ} (hτ : 0 ≤ τ) (hR : 0 < R)
    (hK : fwdHull W τ ⊆ closedBall (c : ℂ) R) (hW0 : |W 0 - c| ≤ R) {s : ℝ} (hs : s ∈ Icc 0 τ) :
    |W s - c| ≤ 7 * R := by
  have hKs : fwdHull W s ⊆ closedBall (c : ℂ) R := ((QuantumZipper.fwdHull_mono).1 hs.2).trans hK
  -- the alive real points `c ± 2R`
  have hfar : ∀ y : ℝ, |y - c| = 2 * R → Disjoint (ball (y : ℂ) R) (fwdHull W τ) := by
    intro y hy
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have h1 := hK hzK
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball, dist_eq_norm] at hz
    have h2 : ‖((y : ℂ) - c)‖ ≤ ‖z - c‖ + ‖z - (y : ℂ)‖ := by
      calc ‖((y : ℂ) - c)‖ = ‖(z - c) - (z - (y : ℂ))‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖z - (y : ℂ)‖ := norm_sub_le _ _
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hy] at h2
    linarith
  have hW0' := abs_le.1 hW0
  -- the right point
  obtain ⟨v₁, hv₁⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (show c + 2 * R ≠ W 0 by intro h; linarith) hτ hR (hfar _ (by rw [add_sub_cancel_left,
      abs_of_pos (by linarith)]))
  have hv₁s : IsForwardSol W ((c + 2 * R : ℝ) : ℂ) s v₁ := QuantumZipper.isForwardSol_restrict hv₁ hs.1 hs.2
  have hpos := QuantumZipper.re_pos_isForwardSol_real hW hs.1 hv₁s (by linarith) s ⟨hs.1, le_rfl⟩
  have hb₁ := norm_sol_add_sub_le hW hs.1 hR hKs hv₁s
  -- the left point
  obtain ⟨v₂, hv₂⟩ := exists_isForwardSol_of_disjoint_ball_gen hW
    (show c - 2 * R ≠ W 0 by intro h; linarith) hτ hR (hfar _ (by rw [sub_sub_cancel_left, abs_neg,
      abs_of_pos (by linarith)]))
  have hv₂s : IsForwardSol W ((c - 2 * R : ℝ) : ℂ) s v₂ := QuantumZipper.isForwardSol_restrict hv₂ hs.1 hs.2
  have hneg := QuantumZipper.re_neg_isForwardSol_real hW hs.1 hv₂s (by linarith) s ⟨hs.1, le_rfl⟩
  have hb₂ := norm_sol_add_sub_le hW hs.1 hR hKs hv₂s
  -- real parts
  have hre : ∀ w : ℂ, |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm
  have e₁ : (v₁ s + W s - c).re = (v₁ s).re + W s - c := by simp
  have e₂ : (v₂ s + W s - c).re = (v₂ s).re + W s - c := by simp
  have n₁ : ‖((c + 2 * R : ℝ) : ℂ) - c‖ = 2 * R := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos (by linarith)]
  have n₂ : ‖((c - 2 * R : ℝ) : ℂ) - c‖ = 2 * R := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_sub_cancel_left, abs_neg,
      abs_of_pos (by linarith)]
  have r₁ := (abs_le.1 ((hre _).trans hb₁)).2
  have r₂ := (abs_le.1 ((hre _).trans hb₂)).1
  rw [e₁, n₁] at r₁
  rw [e₂, n₂] at r₂
  rw [abs_le]
  constructor <;> linarith

/-- **The image of a real alive point is within `|x − c| + 12R` of the driver** when `K_t ⊆ B̄(c, R)` and
`|W_0 − c| ≤ R`. -/
theorem norm_sol_le {W : ℝ → ℝ} (hW : Continuous W) {t c R : ℝ} (ht : 0 ≤ t) (hR : 0 < R)
    (hK : fwdHull W t ⊆ closedBall (c : ℂ) R) (hW0 : |W 0 - c| ≤ R) {x : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) t v) : ‖v t‖ ≤ |x - c| + 12 * R := by
  have h1 := norm_sol_add_sub_le hW ht hR hK hv
  have h2 := abs_driver_sub_le hW ht hR hK hW0 ⟨ht, le_rfl⟩
  have e : v t = (v t + W t - c) - ((W t - c : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  calc ‖(v t + W t - c) - ((W t - c : ℝ) : ℂ)‖ ≤ ‖v t + W t - c‖ + ‖((W t - c : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ (|x - c| + 5 * R) + 7 * R := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
        exact add_le_add h1 h2
    _ = |x - c| + 12 * R := by ring

/-- **Mutual distances along a plain chain, from below.** Two points alive up to `T` whose images stay at distance
`≥ γ` from the driver keep their mutual distance up to the factor `e^{−2t/γ²}` (QuantumZipper's linear identity
`f_t(ζ₂) − f_t(ζ₁) = (ζ₂ − ζ₁) exp(−∫ 2/(f_s(ζ₂) f_s(ζ₁)))`). -/
theorem norm_sol_sub_bounds {W : ℝ → ℝ} {ζ₁ ζ₂ : ℂ} {T : ℝ} {v₁ v₂ : ℝ → ℂ} (hv₁ : IsForwardSol W ζ₁ T v₁)
    (hv₂ : IsForwardSol W ζ₂ T v₂) {γ : ℝ} (hγ : 0 < γ) (hgap₁ : ∀ s ∈ Icc (0 : ℝ) T, γ ≤ ‖v₁ s‖)
    (hgap₂ : ∀ s ∈ Icc (0 : ℝ) T, γ ≤ ‖v₂ s‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖ζ₂ - ζ₁‖ * Real.exp (-(2 / γ ^ 2 * t)) ≤ ‖v₂ t - v₁ t‖ ∧
      ‖v₂ t - v₁ t‖ ≤ ‖ζ₂ - ζ₁‖ * Real.exp (2 / γ ^ 2 * t) := by
  have hid := QuantumZipper.FwdHolo.sol_sub_eq hv₁ hv₂ t ht
  rw [hid, norm_mul, Complex.norm_exp]
  set I := ∫ σ in (0 : ℝ)..t, 2 / (v₂ σ * v₁ σ) with hIdef
  have hI : ‖I‖ ≤ 2 / γ ^ 2 * t := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 2 / γ ^ 2)
      (f := fun σ => 2 / (v₂ σ * v₁ σ)) (fun σ hσ => by
        rw [uIoc_of_le ht.1] at hσ
        have hσT : σ ∈ Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.trans ht.2⟩
        have h1 := hgap₁ σ hσT
        have h2 := hgap₂ σ hσT
        rw [norm_div, norm_mul, Complex.norm_two]
        have hp : 0 < ‖v₂ σ‖ * ‖v₁ σ‖ := mul_pos (hγ.trans_le h2) (hγ.trans_le h1)
        rw [div_le_div_iff₀ hp (by positivity)]
        nlinarith [mul_le_mul h2 h1 hγ.le (norm_nonneg _)])
    rwa [sub_zero, abs_of_nonneg ht.1] at this
  have hre : |(-I).re| ≤ 2 / γ ^ 2 * t := by
    rw [Complex.neg_re, abs_neg]; exact (Complex.abs_re_le_norm _).trans hI
  rw [abs_le] at hre
  exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre.1) (norm_nonneg _),
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hre.2) (norm_nonneg _)⟩

end InteractingSLE.ZhanGT4
