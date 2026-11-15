/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Bound

/-!
# (D9), third part: boundary derivatives at real points, Koebe at alive points, and the other curve's derivative

Packet PROVE-ZHAN-GT4-A6. Source: Astra, *Follow-up proofs*, Part A.1.3 (`ig1_followup_proofs.txt` L300–L340) and
(D3) for the other curve, `d_j A_{k,1}/A_{k,1} = −2A²_{j,1}/E²_{j,0} dt_j` (L245–L275).

## Main results

* `deriv_eq_of_eq_upper`: two functions differentiable at a real point and equal above it have the same derivative;
* `re_deriv_le_of_subset`: **monotonicity of boundary derivatives in the hull** — for hulls `K ⊆ B` and a real point `x`
  with a disc around it missing `B`, `Re ĝ_B'(x) ≤ Re ĝ_K'(x)` (`Im g_B ≤ Im g_K`, differentiated at `x`);
* `im_deriv_eq_zero_of_real`, `deriv_refl_re_pos`: the boundary derivative of a Schwarz reflection is real and positive;
* `le_norm_fwdMap_real`: **Koebe at a real alive point** — if `B(x, ρ)` misses `K_t` and `W 0 ∉ B(x, ρ/2)`, then
  `(ρ/96) |f_t'(x)| ≤ |f_t(x)|`; `refl_eq_fwdMap_of_real`: the reflection equals `g_t` at real alive points;
* `ImgData`: Specification Aux. lemma 8 with the capacity rate for a driver with **any** starting point (`OwnData`
  without `W 0 = 0`), `exists_imgData`, `OwnData.toImgData`;
* `ImgData.exists_rate_le_one`: the clock rate `ȧ = A²_{1,1}` lies in `[0, 1]` when `E_t` misses a disc around the
  driver;
* `ImgData.exp_neg_le_norm_deriv_fwdMap_image`: **the other curve's derivative factor** — if the image of an alive
  point `ζ` stays at distance `≥ γ` from the image driver, `e^{−2s/γ²} ≤ |f̃'_{a(s)}(ζ)| ≤ e^{2s/γ²}`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdHull logDerivFwd)

/-! ### Derivatives at real points -/

/-- Two functions differentiable at a real point `x`, equal at `x` and on a vertical segment above `x`, have the same
derivative at `x`. -/
theorem deriv_eq_of_eq_upper {F₁ F₂ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (h₁ : DifferentiableAt ℂ F₁ x)
    (h₂ : DifferentiableAt ℂ F₂ x) (hx : F₁ x = F₂ x)
    (heq : ∀ ε ∈ Ioo 0 r, F₁ (x + ε * I) = F₂ (x + ε * I)) : deriv F₁ x = deriv F₂ x := by
  have hp : HasDerivAt (fun ε : ℝ => (x : ℂ) + (ε : ℂ) * I) I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    simpa using this
  have hp0 : (x : ℂ) + ((0 : ℝ) : ℂ) * I = x := by simp
  have hcomp : ∀ F : ℂ → ℂ, DifferentiableAt ℂ F x →
      HasDerivWithinAt (fun ε : ℝ => F ((x : ℂ) + (ε : ℂ) * I)) (deriv F x * I) (Ici 0) 0 := by
    intro F hF
    have hF' : HasDerivAt F (deriv F x) ((x : ℂ) + ((0 : ℝ) : ℂ) * I) := by
      rw [hp0]; exact hF.hasDerivAt
    exact (hF'.comp (0 : ℝ) hp).hasDerivWithinAt
  have hd₁ := hcomp F₁ h₁
  have hd₂ := hcomp F₂ h₂
  have hev : (fun ε : ℝ => F₂ ((x : ℂ) + (ε : ℂ) * I)) =ᶠ[𝓝[Ici 0] 0]
      fun ε : ℝ => F₁ ((x : ℂ) + (ε : ℂ) * I) := by
    have hmem : Ico (0 : ℝ) r ∈ 𝓝[Ici 0] 0 := Ico_mem_nhdsGE hr
    filter_upwards [hmem] with ε hε
    rcases hε.1.eq_or_lt with h0 | hpos
    · rw [← h0, hp0]; exact hx.symm
    · exact (heq ε ⟨hpos, hε.2⟩).symm
  have hd₂' := hd₂.congr_of_eventuallyEq hev.symm (by simp only [hp0]; exact hx)
  have huniq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hd₁ hd₂'
  exact mul_right_cancel₀ Complex.I_ne_zero huniq

/-- **Monotonicity of boundary derivatives in the hull.** For compact `ℍ`-hulls `K ⊆ B` with mapping-out functions
`g_K`, `g_B`, a real point `x` with `B(x, ρ)` missing `B`, and functions `G_K`, `G_B` differentiable at `x`, real at
`x`, equal to `g_K`, `g_B` on `B(x, ρ) ∩ ℍ`: `Re G_B'(x) ≤ Re G_K'(x)`. -/
theorem re_deriv_le_of_subset {K B : Set ℂ} {gK gB GK GB : ℂ → ℂ} (hK : IsHPHull K) (hB : IsHPHull B)
    (hKB : K ⊆ B) (hgK : IsMapOut K gK) (hgB : IsMapOut B gB) {x ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (x : ℂ) ρ) B) (hGK : DifferentiableAt ℂ GK x) (hGB : DifferentiableAt ℂ GB x)
    (hGKx : (GK x).im = 0) (hGBx : (GB x).im = 0) (hGKe : EqOn GK gK (ball (x : ℂ) ρ ∩ H))
    (hGBe : EqOn GB gB (ball (x : ℂ) ρ ∩ H)) : (deriv GB x).re ≤ (deriv GK x).re := by
  refine re_deriv_le_of_im_le hρ hGB hGK hGBx hGKx fun ε hε => ?_
  have hzB : (x : ℂ) + (ε : ℂ) * I ∈ ball (x : ℂ) ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε.1]
    exact hε.2
  have hzH : (x : ℂ) + (ε : ℂ) * I ∈ H := by
    show 0 < ((x : ℂ) + (ε : ℂ) * I).im
    simp [hε.1]
  have hzn : (x : ℂ) + (ε : ℂ) * I ∉ B := fun h => Set.disjoint_left.1 hd hzB h
  rw [hGKe ⟨hzB, hzH⟩, hGBe ⟨hzB, hzH⟩]
  exact im_le_im_of_subset hK hB hKB hgK hgB ⟨hzH, hzn⟩

/-! ### Koebe's estimate at a real alive point of a Loewner chain -/

/-- The value of `g_t` at a real alive point is the boundary limit of `g_t`. -/
theorem fwdMap_add_eq_limUnder {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) t v) :
    limUnder (𝓝[H] (x : ℂ)) (fun z => fwdMap W t z + W t) = fwdMap W t x + W t := by
  have hlim := (tendsto_fwdMap_of_isForwardSol hW ht hv).add (tendsto_const_nhds (x := ((W t : ℝ) : ℂ)))
  have hne : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  rw [hlim.limUnder_eq, fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩]

/-- **Koebe at a real alive point.** If `B(x, ρ)` misses `K_t` and no real point of `B(x, ρ/2)` is `W 0`, then
`(ρ/96) |f_t'(x)| ≤ |f_t(x)|`. -/
theorem le_norm_fwdMap_real {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {x ρ : ℝ} (hρ : 0 < ρ)
    (hd : Disjoint (ball (x : ℂ) ρ) (fwdHull W t))
    (h0 : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (ρ / 2) → y ≠ W 0) :
    ρ / 96 * ‖deriv (fwdMap W t) x‖ ≤ ‖fwdMap W t x‖ := by
  have hρ2 : 0 < ρ / 2 := by linarith
  have hxB : (x : ℂ) ∈ ball (x : ℂ) (ρ / 2) := mem_ball_self hρ2
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball_gen hW (h0 x hxB) ht hρ hd
  obtain ⟨G, hGd, hGg, -, hGx, -, hGinj, hup, hlow, -⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full (isHPHull_fwdHull hW ht) (isMapOut_fwdMap_gen hW ht) hρ hd
  have hGx' : G x = fwdMap W t x + W t := by rw [hGx, fwdMap_add_eq_limUnder hW ht hv]
  have hWnot := driver_not_mem_image_of_refl hW ht hρ hd h0 hGd hGg hup hlow
  -- the derivative of the reflection is that of `f_t`
  obtain ⟨δ, hδ, hlow', hx⟩ := exists_aliveDisc_self hv ht
  have hfd : DifferentiableAt ℂ (fwdMap W t) x :=
    (hasDerivAt_fwdMap_aliveDisc hW hv hδ hlow' hx ⟨ht, le_rfl⟩).differentiableAt
  have hGdx : DifferentiableAt ℂ G x := hGd.differentiableAt (isOpen_ball.mem_nhds hxB)
  have hderiv : deriv G x = deriv (fwdMap W t) x := by
    have h := deriv_eq_of_eq_upper hρ2 hGdx (hfd.add_const ((W t : ℝ) : ℂ)) hGx' fun ε hε => by
      have hzB : (x : ℂ) + (ε : ℂ) * I ∈ ball (x : ℂ) (ρ / 2) := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hε.1]
        exact hε.2
      have hzH : (x : ℂ) + (ε : ℂ) * I ∈ H := by
        show 0 < ((x : ℂ) + (ε : ℂ) * I).im
        simp [hε.1]
      exact hGg ⟨hzB, hzH⟩
    rw [h, deriv_add_const]
  -- Koebe's covering theorem at the centre
  have hcov := QuantumZipper.CA.Koebe.ball_subset_image_koebe hGd hGinj
  have hk : QuantumZipper.CA.Koebe.koebeCovConst = 1 / 48 := rfl
  rw [hk] at hcov
  have hle : 1 / 48 * (ρ / 2) * ‖deriv G x‖ ≤ dist (W t : ℂ) (G x) := by
    by_contra hcon
    exact hWnot (hcov (mem_ball.2 (not_le.1 hcon)))
  have e : (W t : ℂ) - (fwdMap W t x + W t) = -fwdMap W t x := by ring
  rw [hGx', dist_eq_norm, e, norm_neg, hderiv] at hle
  calc ρ / 96 * ‖deriv (fwdMap W t) x‖ = 1 / 48 * (ρ / 2) * ‖deriv (fwdMap W t) x‖ := by ring
    _ ≤ _ := hle

/-- A function differentiable at a real point and real on a real neighbourhood of it has a real derivative there. -/
theorem im_deriv_eq_zero_of_real {G : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (hG : DifferentiableAt ℂ G x)
    (hreal : ∀ y : ℝ, |y - x| < r → (G y).im = 0) : (deriv G x).im = 0 := by
  have hp : HasDerivAt (fun ε : ℝ => (x : ℂ) + (ε : ℂ)) 1 0 := by
    have := (hasDerivAt_id (0 : ℝ)).ofReal_comp.const_add (x : ℂ)
    simpa using this
  have hp0 : (x : ℂ) + ((0 : ℝ) : ℂ) = x := by simp
  have hG' : HasDerivAt G (deriv G x) ((x : ℂ) + ((0 : ℝ) : ℂ)) := by rw [hp0]; exact hG.hasDerivAt
  have h1 := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) (hG'.comp (0 : ℝ) hp)
  have h2 : HasDerivAt (fun ε : ℝ => (G ((x : ℂ) + (ε : ℂ))).im) (deriv G x).im 0 := by
    simpa [Function.comp_def] using h1
  have h3 : HasDerivAt (fun ε : ℝ => (G ((x : ℂ) + (ε : ℂ))).im) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : -r < (0 : ℝ)) hr] with ε hε
    have e : (x : ℂ) + (ε : ℂ) = ((x + ε : ℝ) : ℂ) := by push_cast; ring
    rw [e]
    refine hreal _ ?_
    rw [add_sub_cancel_left, abs_lt]; exact ⟨hε.1, hε.2⟩
  exact h2.unique h3

/-- The derivative of a Schwarz reflection of a mapping-out function at a real point of its disc is real and
positive. -/
theorem deriv_refl_re_pos {E : Set ℂ} {g G : ℂ → ℂ} (hg : IsMapOut E g) {x ρ : ℝ}
    (hρ : 0 < ρ) (hGd : DifferentiableOn ℂ G (ball (x : ℂ) ρ)) (hGinj : InjOn G (ball (x : ℂ) ρ))
    (hGe : EqOn G g (ball (x : ℂ) ρ ∩ H)) (hGreal : ∀ z ∈ ball (x : ℂ) ρ, z.im = 0 → (G z).im = 0)
    (hd : Disjoint (ball (x : ℂ) ρ) E) :
    (deriv G x).im = 0 ∧ 0 < (deriv G x).re := by
  have hxB : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have hGx : DifferentiableAt ℂ G x := hGd.differentiableAt (isOpen_ball.mem_nhds hxB)
  have him : (deriv G x).im = 0 := by
    refine im_deriv_eq_zero_of_real hρ hGx fun y hy => hGreal _ ?_ (by simp)
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hne : deriv G x ≠ 0 := QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hGd hGinj hxB
  have hge : (deriv (fun _ : ℂ => (0 : ℂ)) x).re ≤ (deriv G x).re := by
    refine re_deriv_le_of_im_le hρ (differentiableAt_const _) hGx (by simp) (hGreal _ hxB (by simp))
      fun ε hε => ?_
    have hzB : (x : ℂ) + (ε : ℂ) * I ∈ ball (x : ℂ) ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε.1]
      exact hε.2
    have hzH : (x : ℂ) + (ε : ℂ) * I ∈ H := by
      show 0 < ((x : ℂ) + (ε : ℂ) * I).im
      simp [hε.1]
    rw [hGe ⟨hzB, hzH⟩]
    exact (hg.1.2.mapsTo ⟨hzH, fun h => Set.disjoint_left.1 hd hzB h⟩).le
  rw [deriv_const] at hge
  refine ⟨him, lt_of_le_of_ne (by simpa using hge) fun h => hne ?_⟩
  exact Complex.ext h.symm him

/-- The Schwarz reflection of `g_t` near a real point equals `g_t` at every real alive point of its disc. -/
theorem refl_eq_fwdMap_of_real {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {x δ : ℝ} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (ball (x : ℂ) δ))
    (hGg : EqOn G (fun z => fwdMap W t z + W t) (ball (x : ℂ) δ ∩ H)) {y : ℝ}
    (hy : (y : ℂ) ∈ ball (x : ℂ) δ) {v : ℝ → ℂ} (hv : IsForwardSol W (y : ℂ) t v) :
    G y = fwdMap W t y + W t := by
  have hGc : Tendsto G (𝓝[H] (y : ℂ)) (𝓝 (G y)) :=
    ((hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds hy)).tendsto).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ w in 𝓝[H] (y : ℂ), G w = fwdMap W t w + W t := by
    filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hy)] with w hw
    exact hGg ⟨hw.2, hw.1⟩
  have hne : (𝓝[H] (y : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have hlim := (tendsto_fwdMap_of_isForwardSol hW ht hv).add (tendsto_const_nhds (x := ((W t : ℝ) : ℂ)))
  rw [tendsto_nhds_unique (hGc.congr' hev) hlim, fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩]

/-! ### The separation of the two image tips -/

/-- Points of a ball around a real point `q` that are real lie in `(q − d, q + d)`. -/
theorem abs_sub_lt_of_mem_ball {q d y : ℝ} (hy : (y : ℂ) ∈ ball (q : ℂ) d) : |y - q| < d := by
  rwa [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hy

/-! ### Conformal-image data for a driver with any starting point -/

/-- **The conformal-image data of Specification Aux. lemma 8 with the capacity rate**, for curve `j` (continuous
driver `W`, **any** starting point `W 0`) growing on `[0, T]` and the hull `A` of curve `k` frozen: `OwnData` without
the normalization `W 0 = 0` (which cannot hold for both curves of a two-curve configuration at once). -/
structure ImgData (W : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T : ℝ) (a W' : ℝ → ℝ) : Prop where
  cont : Continuous W
  pos : 0 < T
  hull : IsHPHull A
  mapOut : IsMapOut A φ
  disj : Disjoint (closure A) (closure (fwdHull W T))
  contW' : Continuous W'
  a0 : a 0 = 0
  mono : StrictMonoOn a (Icc 0 T)
  contA : ContinuousOn a (Icc 0 T)
  img : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W' (a t) = φ '' fwdHull W t
  rate : ∀ t ∈ Icc (0 : ℝ) T, ∀ R : ℂ → ℂ, IsMapOut ((fun z => fwdMap W t z + W t) '' A) R →
    (∀ z ∈ H \ (A ∪ fwdHull W t), fwdMap W' (a t) (φ z) + W' (a t) = R (fwdMap W t z + W t)) ∧
    Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
    (∃ δ > 0, ∃ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) ∧ EqOn Rext R (ball (W t : ℂ) δ ∩ H)) ∧
    ∀ δ > 0, ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) → EqOn Rext R (ball (W t : ℂ) δ ∩ H) →
      0 < (deriv Rext (W t)).re ∧ (deriv Rext (W t)).im = 0 ∧
        HasDerivWithinAt a ((deriv Rext (W t)).re ^ 2) (Icc 0 T) t

/-- Existence of the conformal-image data (Specification Aux. lemma 8 with the capacity rate). -/
theorem exists_imgData {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 < T) {A : Set ℂ} (hA : IsHPHull A)
    {φ : ℂ → ℂ} (hφ : IsMapOut A φ) (hd : Disjoint (closure A) (closure (fwdHull W T))) :
    ∃ a W', ImgData W A φ T a W' := by
  obtain ⟨a, W', hW'c, ha0, hamono, hacont, hmain⟩ :=
    ConformalImageFull.exists_loewner_image_rate_of_pos hW hT hA hφ hd
  exact ⟨a, W', ⟨hW, hT, hA, hφ, hd, hW'c, ha0, hamono, hacont, fun t ht => (hmain t ht).2.1,
    fun t ht R hR => (hmain t ht).2.2 R hR⟩⟩

/-- `OwnData` is `ImgData` with `W 0 = 0`. -/
theorem OwnData.toImgData {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData W A φ T a W') : ImgData W A φ T a W' :=
  ⟨h.cont, h.pos, h.hull, h.mapOut, h.disj, h.contW', h.a0, h.mono, h.contA, h.img, h.rate⟩

namespace ImgData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : ImgData W A φ T a W')
include h

theorem disjoint_A_K {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : Disjoint A (fwdHull W t) :=
  Set.disjoint_left.2 fun _ hxA hxK => Set.disjoint_left.1 h.disj (subset_closure hxA)
    (subset_closure ((QuantumZipper.fwdHull_mono.1 ht.2) hxK))

/-- The image `E_t = g_t(A)` of the frozen hull is a compact `ℍ`-hull. -/
theorem isHPHull_E {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IsHPHull ((fun z => fwdMap W t z + W t) '' A) := by
  have hd' : Disjoint (closure (fwdHull W t)) (closure A) :=
    Set.disjoint_left.2 fun x hxK hxA => Set.disjoint_left.1 h.disj hxA
      (closure_mono (QuantumZipper.fwdHull_mono.1 ht.2) hxK)
  exact (isMapOut_fwdMap_gen h.cont ht.1).isHPHull_image_of_disjoint_closure
    (isHPHull_fwdHull h.cont ht.1) h.hull hd'

/-- The clock maps `[0, T]` into `[0, a(T)]`. -/
theorem mapsTo_clock_Icc : MapsTo a (Icc 0 T) (Icc 0 (a T)) := fun s hs => by
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨h.pos.le, le_rfl⟩
  refine ⟨?_, h.mono.monotoneOn hs hTmem hs.2⟩
  rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ hs hs.1

/-- **The clock rate `ȧ(t) = A_{1,1}(t)²` lies in `[0, 1]`** when `E_t` misses a disc around the driver: the rate is
the square of the boundary derivative at `W_t` of a Schwarz reflection of the mapping-out function of `E_t`, which is at
most one by the height comparison `Im R(z) ≤ Im z`. -/
theorem exists_rate_le_one {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hdisj : Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ HasDerivWithinAt a c (Icc 0 T) t := by
  have hE := h.isHPHull_E ht
  obtain ⟨R, hR⟩ := hE.exists_isMapOut
  obtain ⟨G, hGd, hGR, -, -, -, -, -, -, hGreal⟩ :=
    ConformalImageFull.IsMapOut.exists_reflection_full hE hR hr hdisj
  have hr2 : 0 < r / 2 := by linarith
  obtain ⟨-, -, hder⟩ := (h.rate t ht R hR).2.2.2 (r / 2) hr2 G hGd hGR
  have hWB : (W t : ℂ) ∈ ball (W t : ℂ) (r / 2) := mem_ball_self hr2
  have hGx : DifferentiableAt ℂ G (W t) := hGd.differentiableAt (isOpen_ball.mem_nhds hWB)
  have hle := re_deriv_le_of_im_le (G₁ := G) (G₂ := id) (x := W t) hr2 hGx differentiableAt_id
    (hGreal _ hWB (by simp)) (by simp) (fun ε hε => ?_)
  · refine ⟨_, sq_nonneg _, ?_, hder⟩
    have h1 : (deriv G (W t)).re ≤ 1 := by simpa using hle
    obtain ⟨hpos, -, -⟩ := (h.rate t ht R hR).2.2.2 (r / 2) hr2 G hGd hGR
    nlinarith
  · have hzB : (W t : ℂ) + (ε : ℂ) * I ∈ ball (W t : ℂ) (r / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
      exact hε.2
    have hzH : (W t : ℂ) + (ε : ℂ) * I ∈ H := by
      show 0 < ((W t : ℂ) + (ε : ℂ) * I).im
      simp [hε.1]
    have hzE : (W t : ℂ) + (ε : ℂ) * I ∉ (fun z => fwdMap W t z + W t) '' A := fun hE' =>
      Set.disjoint_left.1 hdisj (ball_subset_ball (by linarith) hzB) hE'
    rw [hGR ⟨hzB, hzH⟩]
    exact hR.im_le hE ⟨hzH, hzE⟩

/-- **(D9) for the other curve's derivative factor.** If `ζ` is alive for the image chain up to `a(T)`, the driver has
a clearance `r` from `E_t`, and the image of `ζ` stays at distance `≥ γ` from the image driver (the separation `E`),
then `A(s) = |f̃'_{a(s)}(ζ)|` satisfies `e^{−2s/γ²} ≤ A(s) ≤ e^{2s/γ²}`: `d log A = −2 A²_{1,1} / E² ds` (D3) with
`A_{1,1} ≤ 1`. -/
theorem exp_neg_le_norm_deriv_fwdMap_image {r : ℝ} (hr : 0 < r)
    (hclr : ∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball (W t : ℂ) r) ((fun z => fwdMap W t z + W t) '' A))
    {ζ : ℂ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {γ : ℝ} (hγ : 0 < γ)
    (hgap : ∀ s ∈ Icc (0 : ℝ) T, γ ≤ ‖fwdMap W' (a s) ζ‖) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Real.exp (-(2 / γ ^ 2 * s)) ≤ ‖deriv (fwdMap W' (a s)) ζ‖ ∧
      ‖deriv (fwdMap W' (a s)) ζ‖ ≤ Real.exp (2 / γ ^ 2 * s) := by
  have hmaps := h.mapsTo_clock_Icc
  have hW'c := h.contW'
  choose c hc0 hc1 hcder using fun t (ht : t ∈ Icc (0 : ℝ) T) => h.exists_rate_le_one hr ht (hclr t ht)
  set L : ℝ → ℂ := fun t => logDerivFwd W' (a t) ζ with hLdef
  set L' : ℝ → ℂ := fun t => if ht : t ∈ Icc (0 : ℝ) T then
    ((c t ht : ℝ) : ℂ) * -(2 / fwdMap W' (a t) ζ ^ 2) else 0 with hL'def
  have hL : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt L (L' t) (Icc 0 T) t := by
    intro t ht
    have := hasDerivWithinAt_logDerivFwd_clock hW'c hv hmaps ht (hcder t ht)
    simp only [hL'def, ht, ↓reduceDIte]
    exact this
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖L' t‖ ≤ 2 / γ ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
    simp only [hL'def, ht', ↓reduceDIte]
    have hf := hgap t ht'
    have hfpos : 0 < ‖fwdMap W' (a t) ζ‖ := hγ.trans_le hf
    rw [norm_mul, norm_neg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hc0 t ht'), Complex.norm_two]
    have h1 : 2 / ‖fwdMap W' (a t) ζ‖ ^ 2 ≤ 2 / γ ^ 2 := by
      gcongr
    calc c t ht' * (2 / ‖fwdMap W' (a t) ζ‖ ^ 2) ≤ 1 * (2 / γ ^ 2) :=
          mul_le_mul (hc1 t ht') h1 (by positivity) zero_le_one
      _ = 2 / γ ^ 2 := one_mul _
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hL hbound s hs
  have hL0 : L 0 = 0 := by
    simp only [hLdef, h.a0]
    simp [QuantumZipper.logDerivFwd]
  rw [hL0, sub_zero, sub_zero] at hmv
  have haT : 0 ≤ a T := (hmaps ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨δ, hδ, hlow, hζ⟩ := exists_aliveDisc_self hv haT
  have hderiv : deriv (fwdMap W' (a s)) ζ = Complex.exp (L s) :=
    deriv_fwdMap_aliveDisc hW'c hv hδ hlow hζ (hmaps hs)
  rw [hderiv, Complex.norm_exp]
  have hre : |(L s).re| ≤ 2 / γ ^ 2 * s := (Complex.abs_re_le_norm _).trans hmv
  rw [abs_le] at hre
  exact ⟨Real.exp_le_exp.2 hre.1, Real.exp_le_exp.2 hre.2⟩

end ImgData

end InteractingSLE.ZhanGT4
