/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Foundations.Loewner.ConformalImage

/-!
# The canonical branch of `log g′` and its measurability

Packet PROVE-RESTART-CPL4. Lemma 7.8 (p. 290) fixes the chart lift: "Normalize the derivative argument to be zero at
infinity". For a compact `ℍ`-hull `A` with mapping-out function `g`, the **canonical logarithm** of `g′` on `ℍ \ A`
(`IsCanonicalDerivLog`) is the holomorphic logarithm that is the principal logarithm of `g′` high up in `ℍ`
(where `|g′ − 1| ≤ 1/4`, `norm_deriv_sub_one_le`); it exists and is unique (`exists_isCanonicalDerivLog`,
`IsCanonicalDerivLog.eqOn`), and its imaginary part tends to `0` at `i∞`.

For decreasing hulls `A n ↓ B` the canonical logarithms converge on `ℍ \ B` (`tendsto_canonical_of_antitone`): join
a point to the region high up by a path; on it, for large `n`, `L_n − L = Log(g_n′/g′)` (both sides are continuous
logarithms of the same function, equal high up), and `g_n′/g′ → 1`. With the dyadic covers of a random compact set
this makes the canonical lift measurable (`measurable_indicator_canonDerivLog`).

## Main results

* `norm_deriv_sub_one_le_of_isMapOut`: `|g′(w) − 1| ≤ 2r / Im w` when `A ⊆ B̄(0, r)` and `Im w > 8r`;
* `IsCanonicalDerivLog`, `exists_isCanonicalDerivLog`, `IsCanonicalDerivLog.eq_log`, `IsCanonicalDerivLog.eqOn`;
* `canonDerivLog`, `isCanonicalDerivLog_canonDerivLog`;
* `tendsto_canonical_of_antitone`;
* `measurable_indicator_canonDerivLog`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### The derivative of a mapping-out function high up in `ℍ` -/

/-- **`g′` is close to `1` high up**: if `A ⊆ B̄(0, r)` and `Im w > 8r`, then `|g′(w) − 1| ≤ 2r / Im w`
(Cauchy's estimate for `g − id` on `B(w, Im w / 2)`, where `|g − id| ≤ r` by [Law05] Proposition 3.46). -/
theorem norm_deriv_sub_one_le_of_isMapOut {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g) {r : ℝ}
    (hr : 0 < r) (hAr : A ⊆ closedBall 0 r) {w : ℂ} (hw : 8 * r < w.im) : ‖deriv g w - 1‖ ≤ 2 * r / w.im := by
  have hwpos : 0 < w.im := by linarith
  set ρ := w.im / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  -- the closed disc `B̄(w, ρ)` lies high up
  have him : ∀ u ∈ closedBall w ρ, w.im / 2 ≤ u.im := by
    intro u hu
    have h1 : |(u - w).im| ≤ ‖u - w‖ := abs_im_le_norm _
    rw [sub_im] at h1
    have h2 : ‖u - w‖ ≤ ρ := by rw [← dist_eq_norm]; exact hu
    have := neg_abs_le (u.im - w.im)
    linarith
  have hsubD : closedBall w ρ ⊆ H \ A := by
    intro u hu
    have hu1 := him u hu
    refine ⟨show 0 < u.im by linarith, fun huA => ?_⟩
    have h1 := mem_closedBall_zero_iff.1 (hAr huA)
    have h2 : u.im ≤ ‖u‖ := (le_abs_self _).trans (abs_im_le_norm u)
    linarith
  have hfar : ∀ u ∈ closedBall w ρ, ‖g u - u‖ ≤ r := by
    intro u hu
    have hu1 := him u hu
    have hAr' : A ⊆ closedBall ((0 : ℝ) : ℂ) r := by rw [ofReal_zero]; exact hAr
    refine IsMapOut.norm_sub_le_of_four_mul_le hA hg hr hAr' (hsubD hu).1 ?_
    rw [ofReal_zero, sub_zero]
    have h2 : u.im ≤ ‖u‖ := (le_abs_self _).trans (abs_im_le_norm u)
    linarith
  have hd : DifferentiableOn ℂ (fun u => g u - u) (H \ A) := hg.1.1.sub differentiableOn_id
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos (hd.diffContOnCl_ball hsubD)
    (fun u hu => hfar u (sphere_subset_closedBall hu))
  have hwD : H \ A ∈ 𝓝 w := mem_of_superset (closedBall_mem_nhds w hρpos) hsubD
  have hdiff : DifferentiableAt ℂ g w := hg.1.1.differentiableAt hwD
  have e : deriv (fun u => g u - u) w = deriv g w - 1 := (hdiff.hasDerivAt.sub (hasDerivAt_id' w)).deriv
  rw [e] at hC
  calc ‖deriv g w - 1‖ ≤ r / ρ := hC
    _ = 2 * r / w.im := by rw [hρ]; field_simp

/-- High up, `g′` has positive real part and is within `1/4` of `1`. -/
theorem norm_deriv_sub_one_le_quarter_of_isMapOut {A : Set ℂ} {g : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g)
    {r : ℝ} (hr : 0 < r) (hAr : A ⊆ closedBall 0 r) {w : ℂ} (hw : 8 * r < w.im) : ‖deriv g w - 1‖ ≤ 1 / 4 := by
  refine (norm_deriv_sub_one_le_of_isMapOut hA hg hr hAr hw).trans ?_
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem mem_slitPlane_of_norm_sub_one_le {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) : z ∈ slitPlane := by
  refine Or.inl ?_
  have h1 : |(z - 1).re| ≤ ‖z - 1‖ := abs_re_le_norm _
  rw [sub_re, one_re] at h1
  have := neg_abs_le (z.re - 1)
  linarith

theorem abs_arg_lt_of_norm_sub_one_le {z : ℂ} (hz : ‖z - 1‖ ≤ 1 / 2) : |arg z| < Real.pi / 2 := by
  refine abs_arg_lt_pi_div_two_iff.2 (Or.inl ?_)
  have h1 : |(z - 1).re| ≤ ‖z - 1‖ := abs_re_le_norm _
  rw [sub_re, one_re] at h1
  have := neg_abs_le (z.re - 1)
  linarith

/-! ### Continuous logarithms on connected sets -/

/-- Two continuous logarithms of the same function on a preconnected set differ by one constant `2Real.piin`. -/
theorem exists_int_eqOn_of_exp_eq {F₁ F₂ : ℂ → ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (h₁ : ContinuousOn F₁ S) (h₂ : ContinuousOn F₂ S) (he : ∀ z ∈ S, exp (F₁ z) = exp (F₂ z)) :
    ∃ n : ℤ, ∀ z ∈ S, F₁ z = F₂ z + n * (2 * Real.pi * I) := by
  have hn : ∀ z ∈ S, ∃ n : ℤ, F₁ z = F₂ z + n * (2 * Real.pi * I) := fun z hz =>
    exp_eq_exp_iff_exists_int.1 (he z hz)
  rcases S.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => hz.elim⟩
  set f : ℂ → ℝ := fun z => (F₁ z - F₂ z).im / (2 * Real.pi) with hf_def
  have hfn : ∀ z ∈ S, ∀ n : ℤ, F₁ z = F₂ z + n * (2 * Real.pi * I) → f z = n := by
    intro z _ n hzn
    simp only [hf_def, hzn, add_sub_cancel_left, mul_im, intCast_re, intCast_im, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, re_ofNat, im_ofNat]
    field_simp
    ring
  have hfc : ContinuousOn f S := (continuous_im.comp_continuousOn (h₁.sub h₂)).div_const _
  have hmaps : MapsTo f S (range ((↑) : ℤ → ℝ)) := by
    intro z hz
    obtain ⟨n, hzn⟩ := hn z hz
    exact ⟨n, (hfn z hz n hzn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  obtain ⟨n₀, hn₀⟩ := hn z₀ hz₀
  refine ⟨n₀, fun z hz => ?_⟩
  obtain ⟨n, hzn⟩ := hn z hz
  have hconst := hS.constant_of_mapsTo hdisc hfc hmaps hz hz₀
  rw [hfn z hz n hzn, hfn z₀ hz₀ n₀ hn₀, Int.cast_inj] at hconst
  rw [hzn, hconst]

/-- If `F₁ = F₂ + 2Real.piin` and the imaginary parts differ by less than `2Real.pi` somewhere, then `n = 0`. -/
theorem int_eq_zero_of_abs_im_sub_lt {a b : ℂ} {n : ℤ} (h : a = b + n * (2 * Real.pi * I))
    (hab : |(a - b).im| < 2 * Real.pi) :
    n = 0 := by
  have him : (a - b).im = n * (2 * Real.pi) := by
    rw [h]; simp
  rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hab
  have h1 : |(n : ℝ)| < 1 := by
    have := Real.pi_pos
    nlinarith
  have h2 : |n| < 1 := by exact_mod_cast h1
  have h3 := abs_lt.1 h2
  omega

/-! ### The canonical logarithm of `g′` -/

/-- `L` is the **canonical logarithm of `g′`** on `ℍ \ A`: a holomorphic logarithm of `g′` that is the principal
logarithm of `g′` high up in `ℍ` (Lemma 7.8: "normalize the derivative argument to be zero at infinity"). -/
def IsCanonicalDerivLog (A : Set ℂ) (g L : ℂ → ℂ) : Prop :=
  IsDerivLog g L (H \ A) ∧ ∃ Y : ℝ, ∀ w : ℂ, Y < w.im → L w = log (deriv g w)

variable {A : Set ℂ} {g : ℂ → ℂ}

theorem isPreconnected_setOf_lt_im (Y : ℝ) : IsPreconnected {w : ℂ | Y < w.im} :=
  (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear Y).isPreconnected

theorem isOpen_setOf_lt_im (Y : ℝ) : IsOpen {w : ℂ | Y < w.im} :=
  isOpen_lt continuous_const continuous_im

/-- High up, the principal logarithm of `g′` is a logarithm of `g′`. -/
theorem isDerivLog_log_deriv (hA : IsHPHull A) (hg : IsMapOut A g) {r : ℝ} (hr : 0 < r)
    (hAr : A ⊆ closedBall 0 r) : IsDerivLog g (fun w => log (deriv g w)) {w : ℂ | 8 * r < w.im} := by
  have hsub : {w : ℂ | 8 * r < w.im} ⊆ H \ A := by
    intro w hw
    have hw' : 8 * r < w.im := hw
    refine ⟨show 0 < w.im by linarith, fun h => ?_⟩
    have h1 := mem_closedBall_zero_iff.1 (hAr h)
    have h2 : w.im ≤ ‖w‖ := (le_abs_self _).trans (abs_im_le_norm w)
    linarith
  have hd : DifferentiableOn ℂ (deriv g) (H \ A) := hg.1.1.deriv hA.isOpen
  refine ⟨fun w hw => ?_, fun w hw => exp_log ?_⟩
  · exact ((hd w (hsub hw)).differentiableAt (hA.isOpen.mem_nhds (hsub hw))).clog
      (mem_slitPlane_of_norm_sub_one_le
        ((norm_deriv_sub_one_le_quarter_of_isMapOut hA hg hr hAr hw).trans (by norm_num))) |>.differentiableWithinAt
  · intro h0
    have := norm_deriv_sub_one_le_quarter_of_isMapOut hA hg hr hAr hw
    rw [h0, zero_sub, norm_neg, norm_one] at this
    norm_num at this

/-- A canonical logarithm is the principal logarithm of `g′` on the whole region `{Im > 8r}` (`A ⊆ B̄(0, r)`). -/
theorem IsCanonicalDerivLog.eq_log {L : ℂ → ℂ} (hL : IsCanonicalDerivLog A g L) (hA : IsHPHull A)
    (hg : IsMapOut A g) {r : ℝ} (hr : 0 < r) (hAr : A ⊆ closedBall 0 r) {w : ℂ} (hw : 8 * r < w.im) :
    L w = log (deriv g w) := by
  obtain ⟨hLd, Y, hY⟩ := hL
  have hlog := isDerivLog_log_deriv hA hg hr hAr
  have hsub : {w : ℂ | 8 * r < w.im} ⊆ H \ A := fun w hw => by
    refine ⟨show 0 < w.im by have : 8 * r < w.im := hw; linarith, fun h => ?_⟩
    have h1 := mem_closedBall_zero_iff.1 (hAr h)
    have h2 : w.im ≤ ‖w‖ := (le_abs_self _).trans (abs_im_le_norm w)
    have : 8 * r < w.im := hw
    linarith
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn (isOpen_setOf_lt_im _) (isPreconnected_setOf_lt_im _)
    (hLd.mono hsub) hlog
  -- at a point higher than both thresholds the two agree, so `n = 0`
  set w₀ : ℂ := ((max (8 * r) Y + 1 : ℝ) : ℂ) * I with hw₀
  have hw₀im : w₀.im = max (8 * r) Y + 1 := by simp [hw₀]
  have h1 : 8 * r < w₀.im := by rw [hw₀im]; linarith [le_max_left (8 * r) Y]
  have h2 : Y < w₀.im := by rw [hw₀im]; linarith [le_max_right (8 * r) Y]
  have e := hn h1
  rw [hY w₀ h2] at e
  have hn0 : (n : ℂ) * (2 * Real.pi * I) = 0 := by
    have := congrArg (fun x => x - log (deriv g w₀)) e
    simp only [sub_self] at this
    rw [this]; ring
  have hn0' : n = 0 := by
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact_mod_cast (mul_eq_zero.1 hn0).resolve_right hpi
  have e' := hn hw
  simp only at e'
  rw [e', hn0']
  simp

/-- **Existence of the canonical logarithm** of `g′` on `ℍ \ A`. -/
theorem exists_isCanonicalDerivLog (hA : IsHPHull A) (hg : IsMapOut A g) : ∃ L, IsCanonicalDerivLog A g L := by
  obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
  have hAr : A ⊆ closedBall 0 R := hAR.trans ball_subset_closedBall
  have hne : ∀ z ∈ H \ A, deriv g z ≠ 0 := fun z hz =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hA.isOpen hg.1.1 hg.1.2.injOn hz
  obtain ⟨L₀, hL₀⟩ := exists_isDerivLog hA.isOpen hA.2.2.2 hg.1.1 hne
  have hsub : {w : ℂ | 8 * R < w.im} ⊆ H \ A := fun w hw => by
    have : 8 * R < w.im := hw
    refine ⟨show 0 < w.im by linarith, fun h => ?_⟩
    have h1 := mem_closedBall_zero_iff.1 (hAr h)
    have h2 : w.im ≤ ‖w‖ := (le_abs_self _).trans (abs_im_le_norm w)
    linarith
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn (isOpen_setOf_lt_im _) (isPreconnected_setOf_lt_im _)
    (hL₀.mono hsub) (isDerivLog_log_deriv hA hg hR hAr)
  refine ⟨fun z => L₀ z - 2 * Real.pi * I * n, ⟨⟨hL₀.1.sub_const _, fun z hz => ?_⟩, 8 * R, fun w hw => ?_⟩⟩
  · rw [exp_sub, hL₀.2 z hz]
    have : exp (2 * Real.pi * I * n) = 1 := by
      rw [show (2 * Real.pi * I * n : ℂ) = n * (2 * Real.pi * I) by ring]
      exact exp_int_mul_two_pi_mul_I n
    rw [this, div_one]
  · have e := hn hw
    simp only at e
    show L₀ w - 2 * ↑Real.pi * I * ↑n = log (deriv g w)
    rw [e]; ring

/-- **Uniqueness of the canonical logarithm.** -/
theorem IsCanonicalDerivLog.eqOn {L₁ L₂ : ℂ → ℂ} (h₁ : IsCanonicalDerivLog A g L₁)
    (h₂ : IsCanonicalDerivLog A g L₂) (hA : IsHPHull A) (hg : IsMapOut A g) : EqOn L₁ L₂ (H \ A) := by
  obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
  have hAr : A ⊆ closedBall 0 R := hAR.trans ball_subset_closedBall
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn hA.isOpen hA.isConnected.isPreconnected h₁.1 h₂.1
  set w₀ : ℂ := ((8 * R + 1 : ℝ) : ℂ) * I with hw₀
  have h1 : 8 * R < w₀.im := by simp [hw₀]
  have hw₀D : w₀ ∈ H \ A := by
    refine ⟨show 0 < w₀.im by linarith, fun h => ?_⟩
    have h1' := mem_closedBall_zero_iff.1 (hAr h)
    have h2 : w₀.im ≤ ‖w₀‖ := (le_abs_self _).trans (abs_im_le_norm w₀)
    linarith
  have e := hn hw₀D
  simp only at e
  rw [h₁.eq_log hA hg hR hAr h1, h₂.eq_log hA hg hR hAr h1] at e
  have hn0 : n = 0 := by
    have h' : (2 * Real.pi * I * n : ℂ) = 0 := by
      have := congrArg (fun x => x - log (deriv g w₀)) e
      simp only [sub_self] at this
      simp only [this, add_sub_cancel_left]
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact_mod_cast (mul_eq_zero.1 h').resolve_left hpi
  intro z hz
  have e' := hn hz
  simp only at e'
  rw [e', hn0]
  simp

/-- The canonical logarithm of the derivative of the canonical mapping-out function of `A` (`0` if `A` is not a
hull). -/
def canonDerivLog (A : Set ℂ) : ℂ → ℂ :=
  open scoped Classical in
  if h : ∃ L, IsCanonicalDerivLog A (ConformalImage.mapOut A) L then h.choose else 0

theorem isCanonicalDerivLog_canonDerivLog (hA : IsHPHull A) :
    IsCanonicalDerivLog A (ConformalImage.mapOut A) (canonDerivLog A) := by
  have h : ∃ L, IsCanonicalDerivLog A (ConformalImage.mapOut A) L :=
    exists_isCanonicalDerivLog hA (ConformalImage.isMapOut_mapOut hA)
  unfold canonDerivLog
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-! ### Convergence along decreasing hulls -/

/-- **The canonical logarithms converge along decreasing hulls.** -/
theorem tendsto_canonical_of_antitone {A : ℕ → Set ℂ} {B : Set ℂ} {g : ℕ → ℂ → ℂ} {g₀ : ℂ → ℂ}
    {L : ℕ → ℂ → ℂ} {L₀ : ℂ → ℂ} (hanti : Antitone A) (hA : ∀ n, IsHPHull (A n)) (hB : IsHPHull B)
    (hI : ⋂ n, A n = B) (hg : ∀ n, IsMapOut (A n) (g n)) (hg₀ : IsMapOut B g₀)
    (hL : ∀ n, IsCanonicalDerivLog (A n) (g n) (L n)) (hL₀ : IsCanonicalDerivLog B g₀ L₀)
    {z : ℂ} (hz : z ∈ H \ B) : Tendsto (fun n => L n z) atTop (𝓝 (L₀ z)) := by
  obtain ⟨R, hR, hA0⟩ := (hA 0).exists_subset_ball
  have hAR : ∀ n, A n ⊆ ball 0 R := fun n => (hanti (Nat.zero_le n)).trans hA0
  have hAr : ∀ n, A n ⊆ closedBall 0 R := fun n => (hAR n).trans ball_subset_closedBall
  have hBr : B ⊆ closedBall 0 R := by
    rw [← hI]; exact (iInter_subset _ 0).trans (hAr 0)
  have hD : IsOpen (H \ B) := hB.isOpen
  have hder := tendstoLocallyUniformlyOn_deriv_of_kernelConvergesTo_H hA hB hAR hg hg₀
    (kernelConvergesTo_H_of_antitone hanti hA hB hI hz)
  -- a point high up, and a path to it
  set v : ℂ := ((8 * R + 1 : ℝ) : ℂ) * I with hv
  have hvim : 8 * R < v.im := by simp [hv]
  have hhigh : ∀ {C : Set ℂ}, C ⊆ closedBall 0 R → v ∈ H \ C := fun {C} hC => by
    refine ⟨show 0 < v.im by linarith, fun h => ?_⟩
    have h1 := mem_closedBall_zero_iff.1 (hC h)
    have h2 : v.im ≤ ‖v‖ := (le_abs_self _).trans (abs_im_le_norm v)
    linarith
  have hvD : v ∈ H \ B := hhigh hBr
  obtain ⟨p, hp⟩ := (hD.isConnected_iff_isPathConnected.1 hB.isConnected).joinedIn z hz v hvD
  set S := range p with hS
  have hSc : IsCompact S := isCompact_range p.continuous
  have hSp : IsPreconnected S := isPreconnected_range p.continuous
  have hSD : S ⊆ H \ B := by rintro _ ⟨t, rfl⟩; exact hp t
  have hzS : z ∈ S := ⟨0, p.source⟩
  have hvS : v ∈ S := ⟨1, p.target⟩
  -- eventually the path avoids the hulls
  obtain ⟨N, hN⟩ : ∃ N, S ⊆ H \ A N := by
    refine hSc.elim_directed_cover (fun n => H \ A n) (fun n => (hA n).isOpen) ?_ ?_
    · intro w hw
      have hwB := hSD hw
      have : w ∉ ⋂ n, A n := by rw [hI]; exact hwB.2
      obtain ⟨n, hn⟩ := not_forall.1 (fun h => this (mem_iInter.2 h))
      exact mem_iUnion.2 ⟨n, hwB.1, hn⟩
    · exact Monotone.directed_le fun m n hmn => sdiff_subset_sdiff_right (hanti hmn)
  have hSn : ∀ n, N ≤ n → S ⊆ H \ A n := fun n hn =>
    hN.trans (sdiff_subset_sdiff_right (hanti hn))
  -- `g₀′` is bounded below on the path
  have hd₀ : ContinuousOn (deriv g₀) (H \ B) := (hg₀.1.1.deriv hD).continuousOn
  have hne₀ : ∀ w ∈ H \ B, deriv g₀ w ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn hD hg₀.1.1 hg₀.1.2.injOn hw
  obtain ⟨w₁, hw₁S, hmin⟩ := hSc.exists_isMinOn ⟨z, hzS⟩ (continuous_norm.comp_continuousOn (hd₀.mono hSD))
  set c := ‖deriv g₀ w₁‖ with hc
  have hcpos : 0 < c := norm_pos_iff.2 (hne₀ w₁ (hSD hw₁S))
  have hcle : ∀ w ∈ S, c ≤ ‖deriv g₀ w‖ := fun w hw => isMinOn_iff.1 hmin w hw
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hD).1 hder S hSD hSc
  have hev := Metric.tendstoUniformlyOn_iff.1 hunif (c / 2) (by positivity)
  -- the ratio `g_n′ / g₀′` is close to `1` on the path
  have hratio : ∀ᶠ n in atTop, ∀ w ∈ S, ‖deriv (g n) w / deriv g₀ w - 1‖ ≤ 1 / 2 := by
    filter_upwards [hev] with n hn w hw
    have h1 := hn w hw
    rw [dist_eq_norm, norm_sub_rev] at h1
    have hne : deriv g₀ w ≠ 0 := hne₀ w (hSD hw)
    rw [show deriv (g n) w / deriv g₀ w - 1 = (deriv (g n) w - deriv g₀ w) / deriv g₀ w by
      field_simp, norm_div, div_le_iff₀ (norm_pos_iff.2 hne)]
    linarith [hcle w hw]
  -- for such `n`, `L_n − L₀ = Log (g_n′ / g₀′)` on the path
  have hkey : ∀ᶠ n in atTop, L n z = L₀ z + log (deriv (g n) z / deriv g₀ z) := by
    filter_upwards [hratio, eventually_ge_atTop N] with n hn hNn
    have hSAn := hSn n hNn
    have hdn : ContinuousOn (deriv (g n)) (H \ A n) := ((hg n).1.1.deriv (hA n).isOpen).continuousOn
    have hF₁ : ContinuousOn (fun w => L n w - L₀ w) S :=
      ((hL n).1.1.continuousOn.mono hSAn).sub (hL₀.1.1.continuousOn.mono hSD)
    have hq : ContinuousOn (fun w => deriv (g n) w / deriv g₀ w) S :=
      (hdn.mono hSAn).div (hd₀.mono hSD) fun w hw => hne₀ w (hSD hw)
    have hF₂ : ContinuousOn (fun w => log (deriv (g n) w / deriv g₀ w)) S :=
      hq.clog fun w hw => mem_slitPlane_of_norm_sub_one_le (hn w hw)
    have hexp : ∀ w ∈ S, exp (L n w - L₀ w) = exp (log (deriv (g n) w / deriv g₀ w)) := by
      intro w hw
      have hne : deriv (g n) w / deriv g₀ w ≠ 0 := by
        intro h0
        have := hn w hw
        rw [h0, zero_sub, norm_neg, norm_one] at this
        norm_num at this
      rw [exp_sub, (hL n).1.2 w (hSAn hw), hL₀.1.2 w (hSD hw), exp_log hne]
    obtain ⟨k, hk⟩ := exists_int_eqOn_of_exp_eq hSp hF₁ hF₂ hexp
    -- `k = 0`, read off high up
    have hk0 : k = 0 := by
      refine int_eq_zero_of_abs_im_sub_lt (hk v hvS) ?_
      rw [(hL n).eq_log (hA n) (hg n) hR (hAr n) hvim, hL₀.eq_log hB hg₀ hR hBr hvim]
      simp only [sub_im, log_im]
      have h1 := abs_arg_lt_of_norm_sub_one_le
        ((norm_deriv_sub_one_le_quarter_of_isMapOut (hA n) (hg n) hR (hAr n) hvim).trans (by norm_num))
      have h2 := abs_arg_lt_of_norm_sub_one_le
        ((norm_deriv_sub_one_le_quarter_of_isMapOut hB hg₀ hR hBr hvim).trans (by norm_num))
      have h3 := abs_arg_lt_of_norm_sub_one_le (hn v hvS)
      have := Real.pi_pos
      rw [abs_lt] at h1 h2 h3 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    have e := hk z hzS
    rw [hk0] at e
    simp only [Int.cast_zero, zero_mul, add_zero] at e
    rw [← e]; ring
  -- the ratio tends to `1`
  have hrat : Tendsto (fun n => deriv (g n) z / deriv g₀ z) atTop (𝓝 1) := by
    have := (hder.tendsto_at hz).div_const (deriv g₀ z)
    rwa [div_self (hne₀ z hz)] at this
  have hlog : Tendsto (fun n => log (deriv (g n) z / deriv g₀ z)) atTop (𝓝 0) := by
    have := ((continuousAt_clog one_mem_slitPlane).tendsto).comp hrat
    rwa [log_one] at this
  have hlim := (tendsto_const_nhds (x := L₀ z)).add hlog
  rw [add_zero] at hlim
  exact hlim.congr' (hkey.mono fun n hn => hn.symm)

/-! ### Measurability of the canonical logarithm for a random compact set -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ}

/-- **The canonical logarithm of `g′` of a random compact set is measurable** at every point of the domain. -/
theorem measurable_indicator_canonDerivLog (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) (z : ℂ) :
    Measurable ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => canonDerivLog (fillH (K ω)) z) := by
  set E := {ω | z ∈ H \ fillH (K ω)}
  have hE : MeasurableSet E := measurableSet_mem_H_diff_fillH hK hKc z
  refine measurable_of_tendsto_metrizable (f := fun n => E.indicator fun ω =>
    canonDerivLog (fillH (coverOf n (dyadicIdx n (K ω)))) z) (fun n => ?_) ?_
  · exact (measurable_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
      fun S => canonDerivLog (fillH (coverOf n S)) z).indicator hE
  · rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, ← dyadicCover_eq_coverOf]
      have hAn := isHPHull_fillH_dyadicCover (hKc ω).isBounded (hKp ω)
      have hB := isHPHull_fillH_of_compact (hKc ω) (hKp ω)
      exact tendsto_canonical_of_antitone fillH_dyadicCover_antitone hAn hB
        (iInter_fillH_dyadicCover (hKc ω)) (fun n => ConformalImage.isMapOut_mapOut (hAn n))
        (ConformalImage.isMapOut_mapOut hB) (fun n => isCanonicalDerivLog_canonDerivLog (hAn n))
        (isCanonicalDerivLog_canonDerivLog hB) hω
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds

end Random

end Restart

end InteractingSLE
