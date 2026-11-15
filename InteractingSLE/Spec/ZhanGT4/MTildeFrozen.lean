/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTilde
import InteractingSLE.Spec.ZhanGT4.D9Two

/-!
# The factors of `M̃` with the other curve frozen, and their time derivatives

Packet PROVE-ZHAN-GT4-A7. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.2 (`ig1_followup_proofs.txt` L190–L296, R38).

Curve `j` (driver `W`, `W 0 = 0`) grows while the hull `A = K_k` of curve `k` is frozen, with mapping-out function `φ`;
`OwnData W A φ T a W'` provides the image chain (driver `W'`, clock `a`, `K̃_{a(t)} = φ(K_t)`). Every factor of
`M̃` (D6) is a function of the real points of the `φ`-chart: the other source `ζ₀ = φ(x_k)` and the marks
`ζ_m = φ(p_m)`. With `F_t = ownExt … t` (the reflected `h_j`):

* `frzA … k t = Re F_t^{(k)}(W_t)` (`A_{j,k}`; `A_{j,0} = W'(a(t))`, `OwnData.ownExt_driver`);
* `frzImg W' a ζ t = Re g̃_{a(t)}(ζ)` (`A_{k,0}` for `ζ = ζ₀`, `B_{m,0}` for `ζ = ζ_m`);
* `frzImgD W' a ζ t = Re g̃'_{a(t)}(ζ)` (`A_{k,1}`; `B_{m,1}/φ'(p_m)`, the constant `φ'(p_m)` cancels in (D6));
* `frzLogF … t = ∫₀ᵗ (¼(A₂/A₁)² − ⅙A₃/A₁)` (`log F(t, t_k)` by (D5): `∂_{t_j} log F = −⅙ 𝒮h_j(W_j)`).

## Main results

* `OwnData.ownExt_driver`: `F_t(W_t) = W'(a(t))`;
* `OwnData.continuousOn_iterDeriv`: `t ↦ F_t^{(k)}(W_t)` is continuous on `[0, T]`;
* `im_iterDeriv_eq_zero_of_real`: derivatives of a function real on a real segment are real there;
* `fwdMap_real_im`, `logDerivFwd_real_im`, `frzImgD_pos`: the image chain is real and increasing at real alive points;
* `OwnData.hasDerivWithinAt_frzImg`, `OwnData.hasDerivWithinAt_frzImgD` ((D3)), `OwnData.hasDerivWithinAt_frzLogF`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-! ### Definitions -/

/-- `A_{j,k}(t) = Re F_t^{(k)}(W_t)`, `F_t = ownExt … t` (the reflected own-time map `h_j`). -/
def frzA (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (k : ℕ) (t : ℝ) : ℝ :=
  (deriv^[k] (ownExt W W' a φ t) (W t)).re

/-- The image chain at the real point `ζ` of the `φ`-chart: `Re g̃_{a(t)}(ζ)` (`A_{k,0}`, `B_{m,0}`). -/
def frzImg (W' a : ℝ → ℝ) (ζ : ℝ) (t : ℝ) : ℝ := (fwdMap W' (a t) ζ).re + W' (a t)

/-- The derivative of the image chain at `ζ`: `Re g̃'_{a(t)}(ζ)` (`A_{k,1}`, `B_{m,1}/φ'(p_m)`). -/
def frzImgD (W' a : ℝ → ℝ) (ζ : ℝ) (t : ℝ) : ℝ := (deriv (fwdMap W' (a t)) ζ).re

/-- The rate of `log F` along the own time ((D5)): `¼(A₂/A₁)² − ⅙A₃/A₁`. -/
def frzRate (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) : ℝ :=
  1 / 4 * (frzA W W' a φ 2 t / frzA W W' a φ 1 t) ^ 2 - 1 / 6 * (frzA W W' a φ 3 t / frzA W W' a φ 1 t)

/-- `log F(t, t_k) = ∫₀ᵗ (¼(A₂/A₁)² − ⅙A₃/A₁)` ((D4)–(D5), the other time `t_k` frozen). -/
def frzLogF (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, frzRate W W' a φ u

/-! ### Real points -/

/-- **Derivatives of a function that is real on a real segment are real there.** If `G` is holomorphic on
`B(x₀, ρ)` and real at the real points of the disc, then so is every iterated derivative. -/
theorem im_iterDeriv_eq_zero_of_real {G : ℂ → ℂ} {x₀ ρ : ℝ} (hG : DifferentiableOn ℂ G (ball (x₀ : ℂ) ρ))
    (hreal : ∀ y : ℝ, (y : ℂ) ∈ ball (x₀ : ℂ) ρ → (G y).im = 0) (k : ℕ) :
    ∀ y : ℝ, (y : ℂ) ∈ ball (x₀ : ℂ) ρ → (deriv^[k] G y).im = 0 := by
  induction k with
  | zero => simpa using hreal
  | succ k ih =>
    intro y hy
    have hdk : DifferentiableOn ℂ (deriv^[k] G) (ball (x₀ : ℂ) ρ) := by
      clear ih
      induction k with
      | zero => simpa using hG
      | succ j ihj =>
        rw [Function.iterate_succ_apply']
        exact ihj.deriv isOpen_ball
    rw [Function.iterate_succ_apply']
    have hr : 0 < ρ - dist (y : ℂ) x₀ := sub_pos.2 hy
    refine im_deriv_eq_zero_of_real hr (hdk.differentiableAt (isOpen_ball.mem_nhds hy)) fun y' hy' => ih y' ?_
    rw [mem_ball]
    calc dist (y' : ℂ) x₀ ≤ dist (y' : ℂ) y + dist (y : ℂ) x₀ := dist_triangle _ _ _
      _ < (ρ - dist (y : ℂ) x₀) + dist (y : ℂ) x₀ := by
          rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          linarith
      _ = ρ := by ring

/-- The forward map is real at a real point alive on `[0, τ]`. -/
theorem fwdMap_real_im {W : ℝ → ℝ} (hW : Continuous W) {ζ τ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W ζ τ v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) : (fwdMap W s ζ).im = 0 := by
  rw [fwdMap_eq_of_isForwardSol hW hv hs]
  exact im_eq_zero_of_isForwardSol_real hW hv hs

/-- `log g'` is real at a real point alive on `[0, τ]`. -/
theorem logDerivFwd_real_im {W : ℝ → ℝ} (hW : Continuous W) {ζ τ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W ζ τ v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) : (logDerivFwd W s ζ).im = 0 := by
  have heq : ∫ u in (0 : ℝ)..s, 2 / (fwdMap W u ζ) ^ 2 =
      ∫ u in (0 : ℝ)..s, (((2 / ((fwdMap W u ζ).re) ^ 2 : ℝ)) : ℂ) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs.1] at hu
    have him := fwdMap_real_im hW hv ⟨hu.1, hu.2.trans hs.2⟩
    have hre : fwdMap W u ζ = ((fwdMap W u ζ).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hre]
    push_cast
    simp
  rw [logDerivFwd, heq, intervalIntegral.integral_ofReal]
  simp

/-- **The image chain has positive derivative at a real alive point**: `g̃'_s(ζ) = exp(log g̃'_s(ζ))` is real and
positive. -/
theorem deriv_fwdMap_real {W : ℝ → ℝ} (hW : Continuous W) {ζ τ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W ζ τ v)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    (deriv (fwdMap W s) ζ).im = 0 ∧ 0 < (deriv (fwdMap W s) ζ).re := by
  have hτ : 0 ≤ τ := hs.1.trans hs.2
  obtain ⟨δ, hδ, hlow, hζ⟩ := exists_aliveDisc_self hv hτ
  rw [deriv_fwdMap_aliveDisc hW hv hδ hlow hζ hs]
  have him := logDerivFwd_real_im hW hv hs
  have hL : logDerivFwd W s ζ = ((logDerivFwd W s ζ).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hL, ← ofReal_exp]
  simp only [ofReal_im, ofReal_re, true_and]
  exact Real.exp_pos _

/-! ### The own-time quantities -/

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **`A_{j,0} = W'(a(t))`**: the reflected own-time map sends the driver to the image driver. -/
theorem ownExt_driver {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ownExt W W' a φ t (W t) = W' (a t) := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨-, hRlim, -, -⟩ := h.rate t ht R hR
  obtain ⟨-, hEq, -, -, -, hFR⟩ := h.ownExt_props ht (hcl t ht)
  have hU : ball (W t : ℂ) (ρ / 2) ∈ 𝓝 (W t : ℂ) := ball_mem_nhds _ (by positivity)
  have hom : Tendsto (ownMap W W' a φ t) (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
    refine hRlim.congr' ?_
    filter_upwards [inter_mem_nhdsWithin H hU] with z hz
    rw [← hFR R hR ⟨hz.2, hz.1⟩, hEq ⟨hz.2, hz.1⟩]
  have hne : (𝓝[H] (W t : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
    show (0 : ℝ) ≤ ((W t : ℝ) : ℂ).im
    simp
  simp only [ownExt, ofReal_im, lt_irrefl, ↓reduceIte]
  exact hom.limUnder_eq

/-- `frzA … 0 t = W'(a(t))`. -/
theorem frzA_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : frzA W W' a φ 0 t = W' (a t) := by
  simp [frzA, h.ownExt_driver ht]

/-- **The iterated derivatives `F_t^{(k)}(W_t)` are continuous in `t` on `[0, T]`.** -/
theorem continuousOn_iterDeriv (k : ℕ) :
    ContinuousOn (fun t => deriv^[k] (ownExt W W' a φ t) (W t)) (Icc 0 T) := by
  intro t₀ ht₀
  obtain ⟨η, hη, r, hr, hdisj, hWm, -⟩ := h.exists_box ht₀
  have hJ : Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ⊆ Icc 0 T := fun t ht => (mem_box_of_abs_lt ht).1
  have key : ∀ j : ℕ, (∀ s ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)),
      DifferentiableOn ℂ (deriv^[j] (ownExt W W' a φ s)) (ball (W t₀ : ℂ) r)) ∧
      ContinuousOn (fun q : ℝ × ℂ => deriv^[j] (ownExt W W' a φ q.1) q.2)
        (Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ×ˢ ball (W t₀ : ℂ) r) := by
    intro j
    induction j with
    | zero => exact ⟨fun s hs => (h.box_props hJ hdisj hs).1, h.continuousOn_box hJ hdisj⟩
    | succ j ih =>
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact (ih.1 s hs).deriv isOpen_ball
      · have := continuousOn_deriv_of_holo (F := fun s => deriv^[j] (ownExt W W' a φ s)) ih.1 ih.2
        simpa only [Function.iterate_succ_apply'] using this
  have hcl : Continuous fun t : ℝ => (t, (W t : ℂ)) := continuous_id.prodMk (continuous_ofReal.comp h.cont)
  have hc := (key k).2.comp hcl.continuousOn (fun t ht => (⟨ht, hWm t ht⟩ :
    (t, (W t : ℂ)) ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ×ˢ ball (W t₀ : ℂ) r))
  simp only [Function.comp_def] at hc
  exact (hc t₀ (mem_box_self hη ht₀)).mono_of_mem_nhdsWithin (box_mem_nhds hη)

theorem continuousOn_frzA (k : ℕ) : ContinuousOn (frzA W W' a φ k) (Icc 0 T) :=
  continuous_re.comp_continuousOn (h.continuousOn_iterDeriv k)

/-- **`F_t^{(k)}(W_t)` is real.** -/
theorem iterDeriv_driver_im {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (k : ℕ) :
    (deriv^[k] (ownExt W W' a φ t) (W t)).im = 0 := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  obtain ⟨hd, -, -, hreal, -, -⟩ := h.ownExt_props ht (hcl t ht)
  exact im_iterDeriv_eq_zero_of_real hd (fun y hy => hreal _ hy (by simp)) k (W t)
    (mem_ball_self (by positivity))

/-- `A_{j,1} = Re F_t'(W_t) > 0`. -/
theorem frzA_one_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : 0 < frzA W W' a φ 1 t :=
  (h.hasDerivWithinAt_clock ht).2.1

theorem continuousOn_frzRate : ContinuousOn (frzRate W W' a φ) (Icc 0 T) := by
  have h1 := h.continuousOn_frzA 1
  have h2 := h.continuousOn_frzA 2
  have h3 := h.continuousOn_frzA 3
  have hne : ∀ t ∈ Icc (0 : ℝ) T, frzA W W' a φ 1 t ≠ 0 := fun t ht => (h.frzA_one_pos ht).ne'
  exact (continuousOn_const.mul ((h2.div h1 hne).pow 2)).sub (continuousOn_const.mul (h3.div h1 hne))

/-- **(D5) integrated**: `∂_t log F = ¼(A₂/A₁)² − ⅙A₃/A₁`. -/
theorem hasDerivWithinAt_frzLogF {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (frzLogF W W' a φ) (frzRate W W' a φ t) (Icc 0 T) t := by
  have hf := h.continuousOn_frzRate
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hint : IntervalIntegrable (frzRate W W' a φ) MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf.mono (Icc_subset_Icc_right ht.2)
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- **(D3) for `A_{k,0}`, `B_{m,0}`**: `∂_t g̃_{a(t)}(ζ) = 2A₁²/(g̃_{a(t)}(ζ) − A_{j,0})`. -/
theorem hasDerivWithinAt_frzImg {ζ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (frzImg W' a ζ)
      (2 * frzA W W' a φ 1 t ^ 2 / (frzImg W' a ζ t - frzA W W' a φ 0 t)) (Icc 0 T) t := by
  have hd := hasDerivWithinAt_gmap_clock h.contW' hv h.mapsTo_clock ht (h.hasDerivWithinAt_clock ht).1
  have hre := (Complex.reCLM.hasFDerivAt (x := fwdMap W' (a t) ζ + W' (a t))).comp_hasDerivWithinAt t hd
  have him := fwdMap_real_im h.contW' hv (h.mapsTo_clock ht)
  have hf : fwdMap W' (a t) ζ = ((fwdMap W' (a t) ζ).re : ℂ) := by apply Complex.ext <;> simp [him]
  refine (hre.congr_of_mem (fun s _ => ?_) ht).congr_deriv ?_
  · simp [frzImg]
  · rw [h.frzA_zero ht, frzImg, add_sub_cancel_right]
    simp only [Complex.reCLM_apply]
    rw [hf]
    simp only [← ofReal_ofNat, ← ofReal_div, ← ofReal_mul, ofReal_re, frzA, Function.iterate_one]
    ring

/-- **(D3) for `A_{k,1}`, `B_{m,1}`**: `∂_t g̃'_{a(t)}(ζ) = −2A₁² g̃'_{a(t)}(ζ)/(g̃_{a(t)}(ζ) − A_{j,0})²`. -/
theorem hasDerivWithinAt_frzImgD {ζ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (frzImgD W' a ζ)
      (-2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a ζ t / (frzImg W' a ζ t - frzA W W' a φ 0 t) ^ 2)
      (Icc 0 T) t := by
  have hd := hasDerivWithinAt_deriv_fwdMap_clock h.contW' hv h.mapsTo_clock ht (h.hasDerivWithinAt_clock ht).1
  have hre := (Complex.reCLM.hasFDerivAt (x := deriv (fwdMap W' (a t)) ζ)).comp_hasDerivWithinAt t hd
  have haT : 0 ≤ a T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hlow, hζ⟩ := exists_aliveDisc_self hv haT
  have him := fwdMap_real_im h.contW' hv (h.mapsTo_clock ht)
  have hf : fwdMap W' (a t) ζ = ((fwdMap W' (a t) ζ).re : ℂ) := by apply Complex.ext <;> simp [him]
  have hdim := (deriv_fwdMap_real h.contW' hv (h.mapsTo_clock ht)).1
  have hD : deriv (fwdMap W' (a t)) ζ = ((deriv (fwdMap W' (a t)) ζ).re : ℂ) := by
    apply Complex.ext <;> simp [hdim]
  refine hre.congr_deriv ?_
  rw [h.frzA_zero ht, frzImg, add_sub_cancel_right]
  simp only [Complex.reCLM_apply]
  rw [← deriv_fwdMap_aliveDisc h.contW' hv hδ hlow hζ (h.mapsTo_clock ht), hD, hf]
  simp only [← ofReal_ofNat, ← ofReal_div, ← ofReal_mul, ← ofReal_neg, ← ofReal_pow, ofReal_re, frzA, frzImgD,
    Function.iterate_one]
  ring

end OwnData

/-! ### Distinct alive real points stay distinct and off the driver -/

/-- **Distinct alive points have distinct images** (QuantumZipper's linear identity). -/
theorem fwdMap_sub_ne_zero {W : ℝ → ℝ} (hW : Continuous W) {z w : ℂ} {τ : ℝ} {u v : ℝ → ℂ}
    (hu : IsForwardSol W z τ u) (hv : IsForwardSol W w τ v) (hzw : z ≠ w) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    fwdMap W s w - fwdMap W s z ≠ 0 := by
  rw [fwdMap_eq_of_isForwardSol hW hv hs, fwdMap_eq_of_isForwardSol hW hu hs,
    QuantumZipper.FwdHolo.sol_sub_eq hu hv s hs]
  exact mul_ne_zero (sub_ne_zero.2 hzw.symm) (Complex.exp_ne_zero _)

theorem re_ne_zero_of_im_eq_zero {z : ℂ} (hz : z ≠ 0) (him : z.im = 0) : z.re ≠ 0 := fun h' =>
  hz (Complex.ext h' him)

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- `A_{k,0} − A_{j,0} = Re f̃_{a(t)}(ζ)` is nonzero at a real point alive for the image chain. -/
theorem frzImg_sub_ne_zero {ζ : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : frzImg W' a ζ t - frzA W W' a φ 0 t ≠ 0 := by
  rw [h.frzA_zero ht, frzImg, add_sub_cancel_right]
  refine re_ne_zero_of_im_eq_zero ?_ (fwdMap_real_im h.contW' hv (h.mapsTo_clock ht))
  rw [fwdMap_eq_of_isForwardSol h.contW' hv (h.mapsTo_clock ht)]
  exact (hv.2 _ (h.mapsTo_clock ht)).1

/-- Two distinct real points alive for the image chain have distinct images. -/
theorem frzImg_sub_frzImg_ne_zero {ζ ζ' : ℝ} {v v' : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v)
    (hv' : IsForwardSol W' ζ' (a T) v') (hne : ζ ≠ ζ') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    frzImg W' a ζ t - frzImg W' a ζ' t ≠ 0 := by
  have hs := h.mapsTo_clock ht
  have hsub := fwdMap_sub_ne_zero h.contW' hv' hv (by exact_mod_cast hne.symm) hs
  have him : (fwdMap W' (a t) ζ - fwdMap W' (a t) ζ').im = 0 := by
    rw [sub_im, fwdMap_real_im h.contW' hv hs, fwdMap_real_im h.contW' hv' hs, sub_zero]
  have := re_ne_zero_of_im_eq_zero hsub him
  rw [sub_re] at this
  simp only [frzImg]
  intro h0
  exact this (by linarith)

/-! ### The space part on a box -/

section Box

variable {b c y r : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
  (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * r)) ((fun z => fwdMap W t z + W t) '' A))
  (hWm : ∀ t ∈ Icc b c, (W t : ℂ) ∈ ball (y : ℂ) r)
include hJ hdisj

omit h hJ hdisj in
theorem differentiableOn_iterDeriv {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (k : ℕ) : DifferentiableOn ℂ (deriv^[k] G) U := by
  induction k with
  | zero => simpa using hG
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv hU

/-- **The space derivatives on a box**: `x ↦ Re F_s^{(k)}(x)` has derivative `Re F_s^{(k+1)}(x)` at real points of
the box disc. -/
theorem hasDerivAt_re_iterDeriv_box {s : ℝ} (hs : s ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) r) (k : ℕ) :
    HasDerivAt (fun x' : ℝ => (deriv^[k] (ownExt W W' a φ s) x').re)
      (deriv^[k + 1] (ownExt W W' a φ s) x).re x := by
  have hd := differentiableOn_iterDeriv isOpen_ball (h.box_props hJ hdisj hs).1 k
  have hda := (hd.differentiableAt (isOpen_ball.mem_nhds hx)).hasDerivAt
  rw [Function.iterate_succ_apply']
  exact hda.real_of_complex

variable (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) r, dslope (ownExt W W' a φ t) (W t) z ≠ 0)
include hWm hq0

/-- **(D1), real form**: `∂_t Re F_t(x) = Re D̂_t(x)` at real points of the box disc. -/
theorem hasDerivWithinAt_re_ownExt_box {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => (ownExt W W' a φ s x).re) ((dHat (ownExt W W' a φ t) (W t) x).re) (Icc b c) t := by
  have := (Complex.reCLM.hasFDerivAt (x := ownExt W W' a φ t x)).comp_hasDerivWithinAt t
    (h.hasDerivWithinAt_ownExt_box hJ hdisj hWm hq0 ht hx)
  simpa [Function.comp_def] using this

/-- `∂_t Re F_t'(x) = Re ∂_z D̂_t(x)` at real points of the box disc. -/
theorem hasDerivWithinAt_re_deriv_ownExt_box {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ}
    (hx : (x : ℂ) ∈ ball (y : ℂ) r) :
    HasDerivWithinAt (fun s => (deriv (ownExt W W' a φ s) x).re)
      ((deriv (dHat (ownExt W W' a φ t) (W t)) x).re) (Icc b c) t := by
  have := (Complex.reCLM.hasFDerivAt (x := deriv (ownExt W W' a φ t) x)).comp_hasDerivWithinAt t
    (h.hasDerivWithinAt_deriv_ownExt_box hJ hdisj hWm hq0 ht hx)
  simpa [Function.comp_def] using this

/-- **(D2), real form**: `Re D̂_t(W_t) = −3A₂` and `Re ∂_z D̂_t(W_t) = A₂²/(2A₁) − (4/3)A₃`. -/
theorem re_dHat_drive {t : ℝ} (ht : t ∈ Icc b c) :
    (dHat (ownExt W W' a φ t) (W t) (W t)).re = -3 * frzA W W' a φ 2 t ∧
      (deriv (dHat (ownExt W W' a φ t) (W t)) (W t)).re =
        frzA W W' a φ 2 t ^ 2 / (2 * frzA W W' a φ 1 t) - 4 / 3 * frzA W W' a φ 3 t := by
  have ht' := hJ ht
  have hc : ∀ k, deriv^[k] (ownExt W W' a φ t) (W t) = ((frzA W W' a φ k t : ℝ) : ℂ) := fun k => by
    apply Complex.ext
    · simp [frzA]
    · simp [h.iterDeriv_driver_im ht' k]
  have h1 : deriv (ownExt W W' a φ t) (W t) = ((frzA W W' a φ 1 t : ℝ) : ℂ) := hc 1
  have h2 : deriv (deriv (ownExt W W' a φ t)) (W t) = ((frzA W W' a φ 2 t : ℝ) : ℂ) := hc 2
  have h3 : deriv (deriv (deriv (ownExt W W' a φ t))) (W t) = ((frzA W W' a φ 3 t : ℝ) : ℂ) := hc 3
  refine ⟨?_, ?_⟩
  · rw [h.dHat_drive hJ hdisj hWm hq0 ht, h2]
    simp
  · rw [h.deriv_dHat_drive hJ hdisj hWm hq0 ht, h1, h2, h3]
    simp only [← ofReal_pow, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_div, ← ofReal_sub, ofReal_re]

/-- **The drift of `M̃` vanishes along the curve** (frozen other curve; §A.1.2). At every time of a box, the time
derivative of `log M̃` (with (D1)–(D3), (D5) as computed in Lean: `hasDerivWithinAt_frzImg`,
`hasDerivWithinAt_frzImgD`, `hasDerivWithinAt_frzLogF`, `hasDerivWithinAt_re_ownExt_box`,
`hasDerivWithinAt_re_deriv_ownExt_box`) plus `(κ/2)(∂²_x + (∂_x)²) log M̃` vanishes at the driver. Here `ζ₀` is the
other source and `ζ` the marks (distinct real points of the `φ`-chart, alive for the image chain on `[0, a(T)]`). -/
theorem frzGen_eq_zero {κ : ℝ} (hκ : κ ≠ 0) {n : ℕ} (rr : Fin n → ℝ) {ζ₀ : ℝ} {v₀ : ℝ → ℂ}
    (hv₀ : IsForwardSol W' ζ₀ (a T) v₀) {ζ : Fin n → ℝ} {v : Fin n → ℝ → ℂ}
    (hv : ∀ m, IsForwardSol W' (ζ m) (a T) (v m)) (hζ₀ : ∀ m, ζ m ≠ ζ₀) (hζ : Function.Injective ζ)
    {t : ℝ} (ht : t ∈ Icc b c) :
    dualLogTimeT κ rr (frzImgD W' a ζ₀ t) (frzImg W' a ζ₀ t) (fun m => frzImg W' a (ζ m) t)
        (fun m => frzImgD W' a (ζ m) t)
        (-2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a ζ₀ t / (frzImg W' a ζ₀ t - frzA W W' a φ 0 t) ^ 2)
        (frzRate W W' a φ t)
        (2 * frzA W W' a φ 1 t ^ 2 / (frzImg W' a ζ₀ t - frzA W W' a φ 0 t))
        (fun m => 2 * frzA W W' a φ 1 t ^ 2 / (frzImg W' a (ζ m) t - frzA W W' a φ 0 t))
        (fun m => -2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a (ζ m) t /
          (frzImg W' a (ζ m) t - frzA W W' a φ 0 t) ^ 2)
      + dualLogSpaceT κ rr (frzA W W' a φ 0 t) (frzA W W' a φ 1 t) (frzImg W' a ζ₀ t)
          (fun m => frzImg W' a (ζ m) t)
          ((dHat (ownExt W W' a φ t) (W t) (W t)).re) ((deriv (dHat (ownExt W W' a φ t) (W t)) (W t)).re)
          (2 * frzA W W' a φ 1 t ^ 2 / (frzImg W' a ζ₀ t - frzA W W' a φ 0 t))
          (fun m => 2 * frzA W W' a φ 1 t ^ 2 / (frzImg W' a (ζ m) t - frzA W W' a φ 0 t))
      + κ / 2 * (dualLogSpaceXX κ rr (frzA W W' a φ 0 t) (frzA W W' a φ 1 t) (frzA W W' a φ 2 t)
            (frzA W W' a φ 3 t) (frzImg W' a ζ₀ t) (fun m => frzImg W' a (ζ m) t)
          + dualLogSpaceX κ rr (frzA W W' a φ 0 t) (frzA W W' a φ 1 t) (frzA W W' a φ 2 t)
            (frzImg W' a ζ₀ t) (fun m => frzImg W' a (ζ m) t) ^ 2) = 0 := by
  have ht' := hJ ht
  obtain ⟨e1, e2⟩ := h.re_dHat_drive hJ hdisj hWm hq0 ht
  rw [e1, e2]
  have hA1 := (h.frzA_one_pos ht').ne'
  have h21 := (deriv_fwdMap_real h.contW' hv₀ (h.mapsTo_clock ht')).2.ne'
  have hB1 : ∀ m, frzImgD W' a (ζ m) t ≠ 0 := fun m =>
    (deriv_fwdMap_real h.contW' (hv m) (h.mapsTo_clock ht')).2.ne'
  have hE0 : frzA W W' a φ 0 t - frzImg W' a ζ₀ t ≠ 0 := by
    have := h.frzImg_sub_ne_zero hv₀ ht'
    intro h0; exact this (by linarith)
  have hE : ∀ m, frzA W W' a φ 0 t - frzImg W' a (ζ m) t ≠ 0 := fun m => by
    have := h.frzImg_sub_ne_zero (hv m) ht'
    intro h0; exact this (by linarith)
  have h2m : ∀ m, frzImg W' a ζ₀ t - frzImg W' a (ζ m) t ≠ 0 := fun m =>
    h.frzImg_sub_frzImg_ne_zero hv₀ (hv m) (hζ₀ m).symm ht'
  have hmn : ∀ m n, m ≠ n → frzImg W' a (ζ m) t - frzImg W' a (ζ n) t ≠ 0 := fun m n hne =>
    h.frzImg_sub_frzImg_ne_zero (hv m) (hv n) (hζ.ne hne) ht'
  have hsq : -2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a ζ₀ t / (frzImg W' a ζ₀ t - frzA W W' a φ 0 t) ^ 2 =
      -2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a ζ₀ t / (frzA W W' a φ 0 t - frzImg W' a ζ₀ t) ^ 2 := by ring
  have hsqm : (fun m => -2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a (ζ m) t /
      (frzImg W' a (ζ m) t - frzA W W' a φ 0 t) ^ 2) =
      fun m => -2 * frzA W W' a φ 1 t ^ 2 * frzImgD W' a (ζ m) t / (frzA W W' a φ 0 t - frzImg W' a (ζ m) t) ^ 2 := by
    funext m; ring
  rw [hsq, hsqm]
  exact dualGen_eq_zero rr hκ hA1 h21 hB1 hE0 hE h2m hmn

end Box

end OwnData

end InteractingSLE.ZhanGT4
