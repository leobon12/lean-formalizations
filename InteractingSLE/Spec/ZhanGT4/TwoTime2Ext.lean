/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Own
import InteractingSLE.Spec.ZhanGT4.TwoTime2Dslope
import InteractingSLE.Foundations.Loewner.ConformalImageReflect
import InteractingSLE.Foundations.Loewner.HullExists

/-!
# The own-time map near the driver: a uniform reflected extension

Packet PROVE-ZHAN-GT4-A4, toward (D2) of Astra's follow-up note, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L266): "`h_j` … is analytic across a neighborhood of `W_j`,
because the physical hulls are disjoint … The apparent singularity at `W_j` is removable."

`OwnData W A φ T a W'` packages the output of Aux. lemma 8 (`exists_ownData`). The canonical own-time map is
`ownMap t z = g̃_{a(t)}(φ(g_t⁻¹(z)))` on `ℍ`, and `ownExt t` is its Schwarz reflection (the conjugate below `ℝ`, the
boundary limit on `ℝ`). For `y` within `ρ/2` of `W_t` (`ρ` the clearance of `g_t(A)` from the driver),
`ownExt t` is holomorphic on `B(y, ρ/4)`, conjugation-symmetric, `48`-Lipschitz on the closed upper half of the disc
and equal to every mapping-out function of `g_t(A)` there (`OwnData.ownExt_props`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- The canonical own-time map `h_t(z) = g̃_{a(t)}(φ(g_t⁻¹(z)))`. -/
def ownMap (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  fwdMap W' (a t) (φ (invMap W t z)) + W' (a t)

/-- The Schwarz reflection of `ownMap`: `ownMap` on `ℍ`, `conj ∘ ownMap ∘ conj` below, the boundary limit on `ℝ`. -/
def ownExt (W W' a : ℝ → ℝ) (φ : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then ownMap W W' a φ t z
  else if z.im < 0 then conj (ownMap W W' a φ t (conj z))
  else limUnder (𝓝[H] z) (ownMap W W' a φ t)

/-- The output of Specification Aux. lemma 8 with the capacity rate, for curve `j` (driver `W`) growing and the
hull `A` of curve `k` frozen. -/
structure OwnData (W : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T : ℝ) (a W' : ℝ → ℝ) : Prop where
  cont : Continuous W
  zero : W 0 = 0
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

theorem exists_ownData {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull W T))) : ∃ a W', OwnData W A φ T a W' := by
  obtain ⟨a, W', hW'c, ha0, hamono, hacont, hmain⟩ := ConformalImageFull.exists_loewner_image_rate_of_pos hW hT hA hφ hd
  exact ⟨a, W', ⟨hW, hW0, hT, hA, hφ, hd, hW'c, ha0, hamono, hacont, fun t ht => (hmain t ht).2.1,
    fun t ht R hR => (hmain t ht).2.2 R hR⟩⟩

theorem conj_mem_ball {y : ℝ} {r : ℝ} {z : ℂ} (hz : z ∈ ball (y : ℂ) r) : conj z ∈ ball (y : ℂ) r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rwa [← Complex.conj_ofReal, ← map_sub, Complex.norm_conj]

/-- A conjugation-symmetric function that is `L`-Lipschitz on the closed upper half of a disc centred on `ℝ` is
`2L`-Lipschitz on the whole disc. -/
theorem lipschitz_ball_of_conj {G : ℂ → ℂ} {y r L : ℝ} (hL : 0 ≤ L)
    (hc : ∀ z ∈ ball (y : ℂ) r, G (conj z) = conj (G z))
    (hlip : ∀ z ∈ ball (y : ℂ) r ∩ Hbar, ∀ w ∈ ball (y : ℂ) r ∩ Hbar, ‖G w - G z‖ ≤ L * ‖w - z‖)
    {z w : ℂ} (hz : z ∈ ball (y : ℂ) r) (hw : w ∈ ball (y : ℂ) r) : ‖G w - G z‖ ≤ 2 * L * ‖w - z‖ := by
  -- the lower closed half
  have hlow : ∀ z ∈ ball (y : ℂ) r, ∀ w ∈ ball (y : ℂ) r, z.im ≤ 0 → w.im ≤ 0 → ‖G w - G z‖ ≤ L * ‖w - z‖ := by
    intro z hz w hw hz0 hw0
    have e1 : G z = conj (G (conj z)) := by rw [hc z hz, Complex.conj_conj]
    have e2 : G w = conj (G (conj w)) := by rw [hc w hw, Complex.conj_conj]
    have hz' : conj z ∈ ball (y : ℂ) r ∩ Hbar := ⟨conj_mem_ball hz, by
      show 0 ≤ (conj z).im; rw [Complex.conj_im]; linarith⟩
    have hw' : conj w ∈ ball (y : ℂ) r ∩ Hbar := ⟨conj_mem_ball hw, by
      show 0 ≤ (conj w).im; rw [Complex.conj_im]; linarith⟩
    rw [e1, e2, ← map_sub, Complex.norm_conj]
    have := hlip _ hz' _ hw'
    rwa [← map_sub, Complex.norm_conj] at this
  -- real projections stay in the disc
  have hre : ∀ v ∈ ball (y : ℂ) r, ((v.re : ℝ) : ℂ) ∈ ball (y : ℂ) r := fun v hv => by
    rw [mem_ball, dist_eq_norm] at hv ⊢
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine lt_of_le_of_lt ?_ hv
    have := Complex.abs_re_le_norm (v - y)
    simpa using this
  have hreH : ∀ v : ℂ, ((v.re : ℝ) : ℂ) ∈ Hbar := fun v => by show 0 ≤ ((v.re : ℝ) : ℂ).im; simp
  have hnorm_im : ∀ v : ℂ, ‖v - ((v.re : ℝ) : ℂ)‖ = |v.im| := fun v => by
    have : v - ((v.re : ℝ) : ℂ) = (v.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hwz := Complex.abs_re_le_norm (w - z)
  have hwz' := Complex.abs_im_le_norm (w - z)
  rw [sub_re] at hwz; rw [sub_im] at hwz'
  have hLn : 0 ≤ L * ‖w - z‖ := mul_nonneg hL (norm_nonneg _)
  rcases le_total 0 z.im with hz0 | hz0 <;> rcases le_total 0 w.im with hw0 | hw0
  · exact (hlip z ⟨hz, hz0⟩ w ⟨hw, hw0⟩).trans (by linarith)
  · -- `z` above, `w` below
    have h1 := hlow _ (hre w hw) w hw (by simp) hw0
    have h2 := hlip _ ⟨hre z hz, hreH z⟩ _ ⟨hre w hw, hreH w⟩
    have h3 := hlip z ⟨hz, hz0⟩ _ ⟨hre z hz, hreH z⟩
    rw [hnorm_im] at h1
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [norm_sub_rev ((z.re : ℝ) : ℂ) z, hnorm_im] at h3
    calc ‖G w - G z‖ ≤ ‖G w - G (w.re : ℂ)‖ + ‖G (w.re : ℂ) - G (z.re : ℂ)‖ + ‖G (z.re : ℂ) - G z‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (G w) (G (z.re : ℂ)) (G z)
          have := norm_sub_le_norm_sub_add_norm_sub (G w) (G (w.re : ℂ)) (G (z.re : ℂ))
          linarith
      _ ≤ L * |w.im| + L * |w.re - z.re| + L * |z.im| := add_le_add (add_le_add h1 h2) h3
      _ ≤ 2 * L * ‖w - z‖ := by
          rw [abs_of_nonpos hw0, abs_of_nonneg hz0]
          have : -w.im + z.im ≤ ‖w - z‖ := by rw [abs_le] at hwz'; linarith [hwz'.1]
          nlinarith [abs_nonneg (w.re - z.re)]
  · -- `z` below, `w` above
    have h1 := hlip w ⟨hw, hw0⟩ _ ⟨hre w hw, hreH w⟩
    have h2 := hlip _ ⟨hre z hz, hreH z⟩ _ ⟨hre w hw, hreH w⟩
    have h3 := hlow z hz _ (hre z hz) hz0 (by simp)
    rw [norm_sub_rev (G _) (G w), norm_sub_rev ((w.re : ℝ) : ℂ) w, hnorm_im] at h1
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
    rw [norm_sub_rev ((z.re : ℝ) : ℂ) z, hnorm_im] at h3
    calc ‖G w - G z‖ ≤ ‖G w - G (w.re : ℂ)‖ + ‖G (w.re : ℂ) - G (z.re : ℂ)‖ + ‖G (z.re : ℂ) - G z‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub (G w) (G (z.re : ℂ)) (G z)
          have := norm_sub_le_norm_sub_add_norm_sub (G w) (G (w.re : ℂ)) (G (z.re : ℂ))
          linarith
      _ ≤ L * |w.im| + L * |w.re - z.re| + L * |z.im| := add_le_add (add_le_add h1 h2) h3
      _ ≤ 2 * L * ‖w - z‖ := by
          rw [abs_of_nonneg hw0, abs_of_nonpos hz0]
          have : w.im - z.im ≤ ‖w - z‖ := by rw [abs_le] at hwz'; linarith [hwz'.2]
          nlinarith [abs_nonneg (w.re - z.re)]
  · exact (hlow z hz w hw hz0 hw0).trans (by linarith)

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
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
  exact (isMapOut_fwdMap h.cont h.zero ht.1).isHPHull_image_of_disjoint_closure
    (isHPHull_fwdHull h.cont ht.1) h.hull hd'

/-- **Uniform clearance**: `g_t(A)` stays at distance `≥ ρ` from the driver `W_t` for `t ∈ [0, T]`. -/
theorem exists_clearance : ∃ ρ > 0, ∀ t ∈ Icc (0 : ℝ) T,
    Disjoint (ball (W t : ℂ) ρ) ((fun z => fwdMap W t z + W t) '' A) := by
  have h0 : (0 : ℂ) ∉ closure A := by
    have := ConformalImageFull.disjoint_insert_of_pos h.cont h.pos h.disj
    rw [Set.disjoint_insert_right, h.zero, ofReal_zero] at this
    exact this.1
  obtain ⟨ρ, hρ, hcl⟩ := ConformalImageFull.exists_clearance h.cont h.zero h.pos.le h.hull h.disj h0
  refine ⟨ρ, hρ, fun t ht => Set.disjoint_left.2 fun z hz ⟨x, hx, hxz⟩ => ?_⟩
  have h1 := hcl t ht x hx
  rw [mem_ball, dist_eq_norm, ← hxz, add_sub_cancel_right] at hz
  linarith

theorem invMap_not_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {z : ℂ} (hz : z ∈ H)
    (hzE : z ∉ (fun z => fwdMap W t z + W t) '' A) : invMap W t z ∉ A := fun hA =>
  hzE ⟨invMap W t z, hA, by simp only [fwdMap_invMap h.cont h.zero ht.1 hz, sub_add_cancel]⟩

/-- Every mapping-out function of `g_t(A)` is `ownMap t` off `g_t(A)`. -/
theorem eq_ownMap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {R : ℂ → ℂ}
    (hR : IsMapOut ((fun z => fwdMap W t z + W t) '' A) R) {z : ℂ} (hz : z ∈ H) (hzA : invMap W t z ∉ A) :
    R z = ownMap W W' a φ t z := by
  have hw := invMap_mem h.cont h.zero ht.1 hz
  have h1 := (h.rate t ht R hR).1 (invMap W t z) ⟨hw.1, fun h' => h'.elim hzA hw.2⟩
  rw [fwdMap_invMap h.cont h.zero ht.1 hz, sub_add_cancel] at h1
  exact h1.symm

/-- **The reflected own-time map near a real point away from `g_t(A)`.** -/
theorem ownExt_props {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) :
    DifferentiableOn ℂ (ownExt W W' a φ t) (ball (y : ℂ) (r / 2)) ∧
      EqOn (ownExt W W' a φ t) (ownMap W W' a φ t) (ball (y : ℂ) (r / 2) ∩ H) ∧
      (∀ z ∈ ball (y : ℂ) (r / 2), ownExt W W' a φ t (conj z) = conj (ownExt W W' a φ t z)) ∧
      (∀ z ∈ ball (y : ℂ) (r / 2), z.im = 0 → (ownExt W W' a φ t z).im = 0) ∧
      (∀ z ∈ ball (y : ℂ) (r / 2) ∩ Hbar, ∀ w ∈ ball (y : ℂ) (r / 2) ∩ Hbar,
        ‖ownExt W W' a φ t w - ownExt W W' a φ t z‖ ≤ 48 * ‖w - z‖) ∧
      (∀ R : ℂ → ℂ, IsMapOut ((fun z => fwdMap W t z + W t) '' A) R →
        EqOn (ownExt W W' a φ t) R (ball (y : ℂ) (r / 2) ∩ H)) := by
  set E := (fun z => fwdMap W t z + W t) '' A with hE
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨G, hGd, hGR, hGc, hGr, hGL, hGlim⟩ := IsMapOut.exists_reflection (h.isHPHull_E ht) hR hdisj
  have hsub : ball (y : ℂ) (r / 2) ⊆ ball (y : ℂ) r := fun z hz => by
    rw [mem_ball] at hz ⊢; linarith [dist_nonneg (x := z) (y := (y : ℂ))]
  have hRown : ∀ z ∈ ball (y : ℂ) (r / 2) ∩ H, R z = ownMap W W' a φ t z := fun z hz =>
    h.eq_ownMap ht hR hz.2 (h.invMap_not_mem ht hz.2 fun hzE => Set.disjoint_left.1 hdisj (hsub hz.1) hzE)
  have hEq : EqOn (ownExt W W' a φ t) G (ball (y : ℂ) (r / 2)) := by
    intro z hz
    unfold ownExt
    split_ifs with h1 h2
    · rw [← hRown z ⟨hz, h1⟩, hGR ⟨hz, h1⟩]
    · have hcz : conj z ∈ ball (y : ℂ) (r / 2) ∩ H := ⟨conj_mem_ball hz, by
        show 0 < (conj z).im; rw [Complex.conj_im]; linarith⟩
      rw [← hRown _ hcz, ← hGR hcz, hGc z hz, Complex.conj_conj]
    · have him : z.im = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
      have hT := hGlim z hz him
      have hnhds : 𝓝[ball (y : ℂ) (r / 2) ∩ H] z = 𝓝[H] z :=
        nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz))
      rw [hnhds] at hT
      have hT' : Tendsto (ownMap W W' a φ t) (𝓝[H] z) (𝓝 (G z)) := by
        refine hT.congr' ?_
        rw [← hnhds]
        filter_upwards [self_mem_nhdsWithin] with w hw using hRown w hw
      have hne : (𝓝[H] z).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
        show 0 ≤ z.im; rw [him]
      exact hT'.limUnder_eq
  refine ⟨hGd.congr hEq, fun z hz => ?_, fun z hz => ?_, fun z hz hz0 => ?_, fun z hz w hw => ?_,
    fun R' hR' z hz => ?_⟩
  · simp [ownExt, show (0 : ℝ) < z.im from hz.2]
  · rw [hEq (conj_mem_ball hz), hEq hz, hGc z hz]
  · rw [hEq hz]; exact hGr z hz hz0
  · rw [hEq hz.1, hEq hw.1]; exact hGL z hz w hw
  · rw [hEq hz.1, hGR hz]
    rw [hRown z hz, h.eq_ownMap ht hR' hz.2 (h.invMap_not_mem ht hz.2 fun hzE =>
      Set.disjoint_left.1 hdisj (hsub hz.1) hzE)]

/-- `t ↦ h_t(z)` is continuous at `t₁` for `z ∈ ℍ \ g_{t₁}(A)` (it is even differentiable, (D1)). -/
theorem continuousWithinAt_ownMap_time {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) T) {z : ℂ} (hz : z ∈ H)
    (hzA : invMap W t₁ z ∉ A) : ContinuousWithinAt (fun t => ownMap W W' a φ t z) (Icc 0 T) t₁ := by
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht₁).exists_isMapOut
  obtain ⟨-, -, ⟨δ, hδ, Rext, hRd, hRe⟩, hrate⟩ := h.rate t₁ ht₁ R hR
  obtain ⟨-, -, hder⟩ := hrate δ hδ Rext hRd hRe
  exact (hasDerivWithinAt_ownMap_core h.cont h.zero h.hull h.mapOut (h.disjoint_A_K ⟨h.pos.le, le_rfl⟩)
    h.contW' h.a0 h.mono h.img ht₁ hder hz hzA).continuousWithinAt

/-- Time continuity of the reflected map at non-real points of a disc away from `g_{t₁}(A)`. -/
theorem continuousWithinAt_ownExt_time {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t₁ z + W t₁) '' A)) {z : ℂ}
    (hz : z ∈ ball (y : ℂ) r) (hz0 : z.im ≠ 0) :
    ContinuousWithinAt (fun t => ownExt W W' a φ t z) (Icc 0 T) t₁ := by
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · have hcz : conj z ∈ H := by show 0 < (conj z).im; rw [Complex.conj_im]; linarith
    have hcE : conj z ∉ (fun z => fwdMap W t₁ z + W t₁) '' A := fun hE =>
      Set.disjoint_left.1 hdisj (conj_mem_ball hz) hE
    have hc := (Complex.continuous_conj.continuousAt).comp_continuousWithinAt
      (h.continuousWithinAt_ownMap_time ht₁ hcz (h.invMap_not_mem ht₁ hcz hcE))
    refine hc.congr (fun t _ => ?_) ?_ <;>
      simp [ownExt, not_lt.2 hneg.le, hneg]
  · have hzE : z ∉ (fun z => fwdMap W t₁ z + W t₁) '' A := fun hE => Set.disjoint_left.1 hdisj hz hE
    refine (h.continuousWithinAt_ownMap_time ht₁ hpos (h.invMap_not_mem ht₁ hpos hzE)).congr
      (fun t _ => ?_) ?_ <;> simp [ownExt, hpos]

/-- The reflected map is `96`-Lipschitz on the disc. -/
theorem norm_ownExt_sub_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) {z w : ℂ}
    (hz : z ∈ ball (y : ℂ) (r / 2)) (hw : w ∈ ball (y : ℂ) (r / 2)) :
    ‖ownExt W W' a φ t w - ownExt W W' a φ t z‖ ≤ 96 * ‖w - z‖ := by
  obtain ⟨-, -, hc, -, hL, -⟩ := h.ownExt_props ht hdisj
  have := lipschitz_ball_of_conj (by norm_num : (0 : ℝ) ≤ 48) hc hL hz hw
  linarith

/-- **Joint continuity of the reflected own-time map** on `J × B(y, r/2)`, for a set of times `J ⊆ [0, T]` at which
`g_t(A)` misses `B(y, r)`. -/
theorem continuousOn_ownExt {J : Set ℝ} (hJ : J ⊆ Icc 0 T) {y r : ℝ}
    (hdisj : ∀ t ∈ J, Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) :
    ContinuousOn (fun q : ℝ × ℂ => ownExt W W' a φ q.1 q.2) (J ×ˢ ball (y : ℂ) (r / 2)) := by
  rintro ⟨t₁, z₁⟩ ⟨ht₁, hz₁⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set c := ε / 1200 with hc
  have hcpos : 0 < c := by positivity
  -- a non-real point `z'` near `z₁` in the disc
  obtain ⟨z', hz'B, hz'0, hz'c⟩ : ∃ z' ∈ ball (y : ℂ) (r / 2), z'.im ≠ 0 ∧ ‖z' - z₁‖ < c := by
    by_cases h0 : z₁.im = 0
    · have hm : 0 < r / 2 - dist z₁ y := sub_pos.2 hz₁
      set s := min c (r / 2 - dist z₁ y) / 2 with hs
      have hspos : 0 < s := by positivity
      have hsle : s < c ∧ s < r / 2 - dist z₁ y := ⟨by
        have := min_le_left c (r / 2 - dist z₁ y); linarith, by
        have := min_le_right c (r / 2 - dist z₁ y); linarith⟩
      have hnorm : ‖(z₁ + (s : ℂ) * I) - z₁‖ = s := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hspos]
      refine ⟨z₁ + (s : ℂ) * I, ?_, ?_, by rw [hnorm]; exact hsle.1⟩
      · rw [mem_ball]
        calc dist (z₁ + (s : ℂ) * I) y ≤ dist (z₁ + (s : ℂ) * I) z₁ + dist z₁ y := dist_triangle _ _ _
          _ < r / 2 := by rw [dist_eq_norm, hnorm]; linarith [hsle.2]
      · simp [h0, hspos.ne']
    · exact ⟨z₁, hz₁, h0, by simpa using hcpos⟩
  have htc := Metric.continuousWithinAt_iff.1 ((h.continuousWithinAt_ownExt_time (hJ ht₁) (hdisj t₁ ht₁)
    (ball_subset_ball (by
      have := dist_nonneg (x := z₁) (y := (y : ℂ)); rw [mem_ball] at hz₁; linarith) hz'B) hz'0).mono hJ)
    (ε / 2) (by positivity)
  obtain ⟨η, hη, hηt⟩ := htc
  refine ⟨min η c, by positivity, ?_⟩
  rintro ⟨t, z⟩ ⟨ht, hz⟩ hdist
  have hdt : dist t t₁ < min η c := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hdist
  have hdz : dist z z₁ < min η c := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hdist
  simp only [lt_min_iff] at hdt hdz
  have h1 := h.norm_ownExt_sub_le (hJ ht) (hdisj t ht) hz'B hz
  have h2 := hηt ht hdt.1
  have h3 := h.norm_ownExt_sub_le (hJ ht₁) (hdisj t₁ ht₁) hz₁ hz'B
  rw [dist_eq_norm] at h2 hdz ⊢
  simp only
  have hzz' : ‖z - z'‖ ≤ ‖z - z₁‖ + ‖z' - z₁‖ := by
    calc ‖z - z'‖ = ‖(z - z₁) - (z' - z₁)‖ := by ring_nf
      _ ≤ ‖z - z₁‖ + ‖z' - z₁‖ := norm_sub_le _ _
  calc ‖ownExt W W' a φ t z - ownExt W W' a φ t₁ z₁‖
      ≤ ‖ownExt W W' a φ t z - ownExt W W' a φ t z'‖ + ‖ownExt W W' a φ t z' - ownExt W W' a φ t₁ z'‖ +
          ‖ownExt W W' a φ t₁ z' - ownExt W W' a φ t₁ z₁‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub (ownExt W W' a φ t z) (ownExt W W' a φ t₁ z')
          (ownExt W W' a φ t₁ z₁)
        have := norm_sub_le_norm_sub_add_norm_sub (ownExt W W' a φ t z) (ownExt W W' a φ t z')
          (ownExt W W' a φ t₁ z')
        linarith
    _ < 96 * (c + c) + ε / 2 + 96 * c := by
        refine add_lt_add_of_lt_of_le (add_lt_add_of_le_of_lt (h1.trans ?_) h2) (h3.trans ?_)
        · exact mul_le_mul_of_nonneg_left (hzz'.trans (add_le_add hdz.2.le hz'c.le)) (by norm_num)
        · exact (mul_lt_mul_of_pos_left hz'c (by norm_num)).le
    _ ≤ ε := by rw [hc]; linarith

theorem phi_invMap_not_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {z : ℂ} (hz : z ∈ H) (hzA : invMap W t z ∉ A) :
    φ (invMap W t z) ∉ fwdHull W' (a t) := by
  have hw₀ := invMap_mem h.cont h.zero ht.1 hz
  have hw₀A : invMap W t z ∈ H \ A := ⟨hw₀.1, hzA⟩
  rw [h.img t ht]
  rintro ⟨k, hk, hkw⟩
  have hkA : k ∉ A := fun hkA => Set.disjoint_left.1 (h.disjoint_A_K ht) hkA hk
  have hkH : k ∈ H := (QuantumZipper.fwdHull_mono.2 t) hk
  exact hw₀.2 (h.mapOut.1.2.injOn ⟨hkH, hkA⟩ hw₀A hkw ▸ hk)

/-- **(D1) for the reflected map** at points of the upper half of a disc away from `g_t(A)` containing `W_t`:
`∂_t ĥ_t(z) = 2ĥ_t'(W_t)²/(ĥ_t(z) − ĥ_t(W_t)) − 2ĥ_t'(z)/(z − W_t)`. -/
theorem hasDerivWithinAt_ownExt_upper {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {y r : ℝ}
    (hdisj : Disjoint (ball (y : ℂ) r) ((fun z => fwdMap W t z + W t) '' A)) (hWt : (W t : ℂ) ∈ ball (y : ℂ) (r / 2))
    {z : ℂ} (hz : z ∈ ball (y : ℂ) (r / 2)) (hzH : 0 < z.im) :
    HasDerivWithinAt (fun s => ownExt W W' a φ s z)
      (2 * deriv (ownExt W W' a φ t) (W t) ^ 2 / (ownExt W W' a φ t z - ownExt W W' a φ t (W t)) -
        2 * deriv (ownExt W W' a φ t) z / (z - W t)) (Icc 0 T) t := by
  set F := ownExt W W' a φ t with hFdef
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨hFd, hFH, -, -, -, hFR⟩ := h.ownExt_props ht hdisj
  obtain ⟨-, hlim, -, hrate⟩ := h.rate t ht R hR
  set δ := r / 2 - dist (W t : ℂ) y with hδ
  have hδpos : 0 < δ := sub_pos.2 hWt
  have hδsub : ball (W t : ℂ) δ ⊆ ball (y : ℂ) (r / 2) := fun w hw => by
    rw [mem_ball] at hw ⊢; linarith [dist_triangle w (W t : ℂ) y]
  obtain ⟨-, him, hder⟩ := hrate δ hδpos F (hFd.mono hδsub) (fun w hw => hFR R hR ⟨hδsub hw.1, hw.2⟩)
  have hzE : z ∉ (fun z => fwdMap W t z + W t) '' A := fun hE =>
    Set.disjoint_left.1 hdisj (ball_subset_ball (by
      have := dist_nonneg (x := z) (y := (y : ℂ)); rw [mem_ball] at hz; linarith) hz) hE
  have hzA := h.invMap_not_mem ht hzH hzE
  have hcore := hasDerivWithinAt_ownMap_core h.cont h.zero h.hull h.mapOut (h.disjoint_A_K ⟨h.pos.le, le_rfl⟩)
    h.contW' h.a0 h.mono h.img ht hder hzH hzA
  have hfun : (fun s => ownExt W W' a φ s z) = fun s => ownMap W W' a φ s z := by
    funext s; simp [ownExt, hzH]
  rw [hfun]
  refine hcore.congr_deriv ?_
  -- the ingredients
  have hat : 0 ≤ a t := by rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ ht ht.1
  have hsp := hasDerivAt_ownMap_space h.cont h.zero ht.1 h.hull h.mapOut h.contW' hat hzH hzA
    (h.phi_invMap_not_mem ht hzH hzA)
  have hFz : F z = ownMap W W' a φ t z := hFH ⟨hz, hzH⟩
  have hdF : deriv F z = deriv (fun y => fwdMap W' (a t) (φ (invMap W t y)) + (W' (a t) : ℂ)) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [(isOpen_ball.inter QuantumZipper.isOpen_H).mem_nhds ⟨hz, hzH⟩] with w hw using hFH hw
  have hA1 : deriv F (W t) = ((deriv F (W t)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hA0 : F (W t) = W' (a t) := by
    have hne : (𝓝[H] (W t : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]
      show (0 : ℝ) ≤ (W t : ℂ).im; simp
    have h1 : Tendsto F (𝓝[H] (W t : ℂ)) (𝓝 (F (W t))) :=
      ((hFd.differentiableAt (isOpen_ball.mem_nhds hWt)).continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto F (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) := by
      refine hlim.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hWt), self_mem_nhdsWithin] with w hw hwH
      exact (hFR R hR ⟨hw, hwH⟩).symm
    exact tendsto_nhds_unique h1 h2
  rw [hdF, hsp.deriv, hFz, hA0]
  conv_rhs => rw [hA1]
  have hzW : z - (W t : ℂ) ≠ 0 := fun h0 => by
    have : (z - (W t : ℂ)).im = 0 := by rw [h0, zero_im]
    rw [sub_im, ofReal_im, sub_zero] at this; linarith
  have hE := Complex.exp_ne_zero (logDerivFwd W t (invMap W t z))
  have hcancel : ownMap W W' a φ t z - (W' (a t) : ℂ) = fwdMap W' (a t) (φ (invMap W t z)) := by
    simp only [ownMap]; ring
  rw [hcancel]
  push_cast
  field_simp
  ring

end OwnData

end InteractingSLE.ZhanGT4
