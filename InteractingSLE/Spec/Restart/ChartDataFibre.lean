/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc
import InteractingSLE.Spec.Sec7.InteractionLens

/-!
# Singleton fibres of the boundary extension of an inverse chart

Packet PROVE-RESTART-CPL3 (the pathwise chart data of the first-contact restart; supplement Aux. 80, p. 540: "the
real chart points go to `∂D`", and the active prime end of D.5, interface 2). Let `D ⊆ ℍ` be open and `F` a map,
continuous on `ℍ̄`, holomorphic and injective on `ℍ`, mapping `ℍ` onto `D`, real points into `∂D`, and `∞` to `∞`
(the boundary extension of the inverse of a mapping-out function, `YuanCharacterisation.exists_extension_symm`).
Let `E` be a set disjoint from `D` containing `∂D` (for `D = ℍ \ fill(K)`: `E = ℝ ∪ K`).

* `eq_of_apply_eq_of_linked` (**singleton fibre**): if every point of `E \ {q}` lies in an unbounded preconnected
  subset of `E \ {q}`, then at most one real point is sent to `q`.

  Proof. Suppose `F x = F y = q`, `x < y`. The upper half circle `a` over `[x, y]` is mapped by `F` to a Jordan curve
  `Γ` through `q`, `Γ \ {q} ⊆ D` (`Sec7.isJordanCurve_image_union`, two quarter arcs). Points of `D` outside the half
  disc `Q` are joined to `∞` by vertical rays, whose images are unbounded and avoid `Γ`; so `D` meets the bounded
  component `Int` of `ℂ \ Γ` only in `F(Q)`, and `F(Q) ⊆ Int` since `Γ = ∂ Int` contains points of the open set `D`.
  A real `z ∈ (x, y)` with `F z ≠ q` (`YuanFiber.exists_ne_of_injOn`) then has `F z ∈ Int ∩ E`, and the unbounded
  preconnected set of `E \ {q}` through `F z` avoids `Γ`, hence lies in the bounded `Int`.

* `exists_tendsto_of_fibre` (**forward limit**): if moreover `G` inverts `F` on `D` and moves points by a bounded
  amount, then at a point `q ∈ closure D \ D` with at most one real preimage, `G` converges along `D` to a real point
  `x₀` with `F x₀ = q`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-- Every point of `E` lies in an unbounded preconnected subset of `E`. -/
def IsUnboundedLinked (E : Set ℂ) : Prop :=
  ∀ z ∈ E, ∃ S ⊆ E, IsPreconnected S ∧ z ∈ S ∧ ¬ Bornology.IsBounded S

/-! ### The upper half circle over a real interval -/

section Arc

/-- The upper half circle of centre `m` and radius `r`: `θ ↦ m + r e^{iθ}`, `θ ∈ [0, π]`. -/
def halfCircle (m r : ℝ) (θ : ℝ) : ℂ := (m : ℂ) + (r : ℂ) * exp ((θ : ℂ) * I)

theorem continuous_halfCircle (m r : ℝ) : Continuous (halfCircle m r) := by
  unfold halfCircle
  fun_prop

theorem halfCircle_re (m r θ : ℝ) : (halfCircle m r θ).re = m + r * Real.cos θ := by
  simp [halfCircle, exp_ofReal_mul_I_re]

theorem halfCircle_im (m r θ : ℝ) : (halfCircle m r θ).im = r * Real.sin θ := by
  simp [halfCircle, exp_ofReal_mul_I_im]

theorem halfCircle_zero (m r : ℝ) : halfCircle m r 0 = ((m + r : ℝ) : ℂ) := by
  simp [halfCircle]

theorem halfCircle_pi (m r : ℝ) : halfCircle m r Real.pi = ((m - r : ℝ) : ℂ) := by
  simp [halfCircle, exp_pi_mul_I]
  ring

theorem halfCircle_mem_H {m r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo 0 Real.pi) : halfCircle m r θ ∈ H := by
  show 0 < (halfCircle m r θ).im
  rw [halfCircle_im]
  exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)

theorem halfCircle_mem_Hbar {m r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Icc 0 Real.pi) :
    halfCircle m r θ ∈ Hbar := by
  show 0 ≤ (halfCircle m r θ).im
  rw [halfCircle_im]
  exact mul_nonneg hr (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

theorem halfCircle_injOn {m r : ℝ} (hr : 0 < r) : InjOn (halfCircle m r) (Icc 0 Real.pi) := by
  intro θ hθ θ' hθ' h
  have h1 := congrArg Complex.re h
  rw [halfCircle_re, halfCircle_re] at h1
  have h2 : Real.cos θ = Real.cos θ' := by
    have := mul_left_cancel₀ hr.ne' (add_left_cancel h1)
    exact this
  exact Real.injOn_cos hθ hθ' h2

theorem norm_halfCircle_sub (m : ℝ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖halfCircle m r θ - m‖ = r := by
  simp [halfCircle, norm_exp_ofReal_mul_I, abs_of_nonneg hr]

/-- A point of `ℍ` at distance `r` from the real point `m` lies on the open upper half circle. -/
theorem exists_halfCircle_eq {m r : ℝ} {z : ℂ} (hz : z ∈ H) (hzr : ‖z - m‖ = r) :
    ∃ θ ∈ Ioo 0 Real.pi, halfCircle m r θ = z := by
  have hne : z - m ≠ 0 := fun h => by
    have : (z - m).im = 0 := by rw [h]; rfl
    have h0 : 0 < z.im := hz
    simp at this
    linarith
  have him : 0 < (z - m).im := by simpa using (show 0 < z.im from hz)
  have hpos : 0 < arg (z - m) := by
    refine lt_of_le_of_ne (arg_nonneg_iff.2 him.le) fun h => ?_
    have := (arg_eq_zero_iff.1 h.symm).2
    linarith
  have hlt : arg (z - m) < Real.pi := arg_lt_pi_iff.2 (Or.inr him.ne')
  refine ⟨arg (z - m), ⟨hpos, hlt⟩, ?_⟩
  rw [halfCircle, ← hzr, norm_mul_exp_arg_mul_I]
  ring

end Arc

/-! ### The singleton fibre -/

section Fibre

variable {D E : Set ℂ} {F : ℂ → ℂ} {q : ℂ}

/-- The vertical ray from a point of `ℍ` tends to `∞` inside `ℍ̄`. -/
theorem tendsto_add_mul_I_atTop {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (fun t : ℝ => z + (t : ℂ) * I) atTop (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) := by
  refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
  · refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖z‖) tendsto_abs_atTop_atTop)
    have h1 : ‖(t : ℂ) * I‖ = |t| := by rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
    have h2 := norm_sub_norm_le ((t : ℂ) * I) (-z)
    rw [sub_neg_eq_add, add_comm, norm_neg, h1] at h2
    linarith
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    show 0 ≤ (z + (t : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one, add_zero]
    exact add_nonneg hz ht

/-- **Two real preimages of one point give a contradiction** (the core of `eq_of_apply_eq_of_linked`). -/
theorem false_of_apply_eq_of_lt (hDo : IsOpen D) (hFd : DifferentiableOn ℂ F H)
    (hFc : ContinuousOn F Hbar) (hFi : InjOn F H) (hFD : MapsTo F H D) (hFs : SurjOn F H D)
    (hFbd : MapsTo F (Hbar \ H) (frontier D))
    (hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ))
    (hDE : Disjoint D E) (hfr : frontier D ⊆ E) (hq : IsUnboundedLinked (E \ {q}))
    {x y : ℝ} (hxy : x < y) (hx : F x = q) (hy : F y = q) : False := by
  set m : ℝ := (x + y) / 2 with hm
  set r : ℝ := (y - x) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  set a := halfCircle m r with hadef
  have ha0 : a 0 = (y : ℂ) := by
    rw [hadef, halfCircle_zero]; congr 1; rw [hm, hrdef]; ring
  have haπ : a Real.pi = (x : ℂ) := by
    rw [hadef, halfCircle_pi]; congr 1; rw [hm, hrdef]; ring
  have hreal : ∀ t : ℝ, F t ∈ frontier D := fun t =>
    hFbd ⟨show (0 : ℝ) ≤ (t : ℂ).im by simp, fun h => by
      have : (0 : ℝ) < (t : ℂ).im := h
      simp at this⟩
  have hfrD : ∀ w ∈ frontier D, w ∉ D := fun w hw hwD => by
    rw [hDo.frontier_eq] at hw; exact hw.2 hwD
  have hqD : q ∉ D := hx ▸ hfrD _ (hreal x)
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- the values of `F` on the half circle
  have hend : ∀ θ ∈ Icc 0 Real.pi, F (a θ) = q → θ = 0 ∨ θ = Real.pi := by
    intro θ hθ hFθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · exact Or.inl h0.symm
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · exact Or.inr h1
    exact absurd (hFθ ▸ hFD (halfCircle_mem_H hr ⟨h0, h1⟩)) hqD
  have hFaa : ∀ θ ∈ Icc 0 Real.pi, ∀ θ' ∈ Icc 0 Real.pi, F (a θ) = F (a θ') →
      θ = θ' ∨ F (a θ) = q := by
    intro θ hθ θ' hθ' h
    have hq0 : F (a 0) = q := by rw [ha0, hy]
    have hqπ : F (a Real.pi) = q := by rw [haπ, hx]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · right; rw [← h0]; exact hq0
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · right; rw [h1]; exact hqπ
    have hθH : a θ ∈ H := halfCircle_mem_H hr ⟨h0, h1⟩
    rcases eq_or_lt_of_le hθ'.1 with h0' | h0'
    · rw [← h0', hq0] at h; exact absurd (h ▸ hFD hθH) hqD
    rcases eq_or_lt_of_le hθ'.2 with h1' | h1'
    · rw [h1', hqπ] at h; exact absurd (h ▸ hFD hθH) hqD
    exact Or.inl (halfCircle_injOn hr hθ hθ' (hFi hθH (halfCircle_mem_H hr ⟨h0', h1'⟩) h))
  -- the two quarter arcs
  set u : ℝ → ℂ := fun t => F (a (Real.pi - t * (Real.pi / 2))) with hu
  set v : ℝ → ℂ := fun t => F (a (t * (Real.pi / 2))) with hv
  have hθu : ∀ t ∈ Icc (0 : ℝ) 1, Real.pi - t * (Real.pi / 2) ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
  have hθv : ∀ t ∈ Icc (0 : ℝ) 1, t * (Real.pi / 2) ∈ Icc 0 Real.pi := fun t ht =>
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have haHbar : ∀ θ ∈ Icc 0 Real.pi, a θ ∈ Hbar := fun θ hθ => halfCircle_mem_Hbar hr.le hθ
  have hcu : ContinuousOn u (Icc 0 1) := by
    refine hFc.comp ((continuous_halfCircle m r).comp (by fun_prop)).continuousOn fun t ht => ?_
    exact haHbar _ (hθu t ht)
  have hcv : ContinuousOn v (Icc 0 1) := by
    refine hFc.comp ((continuous_halfCircle m r).comp (by fun_prop)).continuousOn fun t ht => ?_
    exact haHbar _ (hθv t ht)
  have hu0 : u 0 = q := by simp only [hu, zero_mul, sub_zero]; rw [haπ, hx]
  have hv0 : v 0 = q := by simp only [hv, zero_mul]; rw [ha0, hy]
  have hu1 : u 1 = v 1 := by simp only [hu, hv, one_mul]; congr 2; ring
  have hiu : InjOn u (Icc 0 1) := by
    intro t ht t' ht' h
    rcases hFaa _ (hθu t ht) _ (hθu t' ht') h with h1 | h1
    · nlinarith
    · have e1 := hend _ (hθu t ht) h1
      have e2 := hend _ (hθu t' ht') (show F (a (Real.pi - t' * (Real.pi / 2))) = q from h.symm.trans h1)
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> nlinarith [ht.2, ht'.2]
  have hiv : InjOn v (Icc 0 1) := by
    intro t ht t' ht' h
    rcases hFaa _ (hθv t ht) _ (hθv t' ht') h with h1 | h1
    · nlinarith
    · have e1 := hend _ (hθv t ht) h1
      have e2 := hend _ (hθv t' ht') (show F (a (t' * (Real.pi / 2))) = q from h.symm.trans h1)
      rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> nlinarith [ht.1, ht'.1, ht.2, ht'.2]
  have hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1} := by
    rintro w ⟨⟨t, ht, rfl⟩, ⟨t', ht', htt'⟩⟩
    rcases hFaa _ (hθu t ht) _ (hθv t' ht') htt'.symm with h1 | h1
    · right
      have : t = 1 := by nlinarith [ht.2, ht'.2]
      rw [this]
      rfl
    · left; rw [hu0]; exact h1
  set Γ := u '' Icc 0 1 ∪ v '' Icc 0 1 with hΓdef
  have hΓ : LQGMetric.JordanMap.IsJordanCurve Γ :=
    Sec7.isJordanCurve_image_union hcu hcv hiu hiv (hu0.trans hv0.symm) hu1 hint
  -- every point of `Γ` is a value on the half circle
  have hΓa : ∀ w ∈ Γ, ∃ θ ∈ Icc 0 Real.pi, F (a θ) = w := by
    rintro w (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨_, hθu t ht, rfl⟩
    · exact ⟨_, hθv t ht, rfl⟩
  have hΓD : ∀ w ∈ Γ, w ≠ q → w ∈ D := by
    intro w hw hwq
    obtain ⟨θ, hθ, rfl⟩ := hΓa w hw
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · exact absurd (by rw [← h0, ha0, hy]) hwq
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · exact absurd (by rw [h1, haπ, hx]) hwq
    exact hFD (halfCircle_mem_H hr ⟨h0, h1⟩)
  have hoff : ∀ z ∈ H, ‖z - m‖ ≠ r → F z ∉ Γ := by
    intro z hz hzr hzΓ
    obtain ⟨θ, hθ, hθz⟩ := hΓa _ hzΓ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · rw [← h0, ha0, hy] at hθz; exact hqD (hθz ▸ hFD hz)
    rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · rw [h1, haπ, hx] at hθz; exact hqD (hθz ▸ hFD hz)
    have := hFi (halfCircle_mem_H hr ⟨h0, h1⟩) hz hθz
    exact hzr (by rw [← this]; exact norm_halfCircle_sub m hr.le θ)
  obtain ⟨w₁, hw₁, -, -, hbI, -, -, hunion, hfrI, -⟩ := jordan_curve_components hΓ
  set I₀ := connectedComponentIn Γᶜ w₁ with hI₀
  have hI₀Γ : I₀ ⊆ Γᶜ := connectedComponentIn_subset _ _
  -- a preconnected subset of `Γᶜ` meeting `I₀` lies in `I₀`
  have hsubI : ∀ S : Set ℂ, IsPreconnected S → S ⊆ Γᶜ → ∀ w ∈ S, w ∈ I₀ → S ⊆ I₀ := by
    intro S hS hSΓ w hwS hwI
    have := hS.subset_connectedComponentIn hwS hSΓ
    rwa [← connectedComponentIn_eq hwI] at this
  -- (A) points outside the closed half disc are sent off `I₀` (vertical rays)
  have hA : ∀ z ∈ H, r < ‖z - m‖ → F z ∉ I₀ := by
    intro z hz hzr hzI
    set R := (fun t : ℝ => z + (t : ℂ) * I) '' Ici 0 with hR
    have hRH : R ⊆ H := by
      rintro _ ⟨t, ht, rfl⟩
      show 0 < (z + (t : ℂ) * I).im
      simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one, add_zero]
      exact add_pos_of_pos_of_nonneg hz ht
    have hRr : ∀ w ∈ R, r < ‖w - m‖ := by
      rintro _ ⟨t, ht, rfl⟩
      have hz0 : 0 < z.im := hz
      have h1 : ‖z - m‖ ^ 2 = (z.re - m) ^ 2 + z.im ^ 2 := by
        rw [← Complex.sq_norm_sub_sq_re]
        simp [Complex.sq_norm, Complex.normSq_apply]; ring
      have h2 : ‖z + (t : ℂ) * I - m‖ ^ 2 = (z.re - m) ^ 2 + (z.im + t) ^ 2 := by
        simp [Complex.sq_norm, Complex.normSq_apply]; ring
      have ht' : (0 : ℝ) ≤ t := ht
      have h3 : ‖z - m‖ ^ 2 ≤ ‖z + (t : ℂ) * I - m‖ ^ 2 := by
        rw [h1, h2]; nlinarith [mul_nonneg ht' (by linarith : (0 : ℝ) ≤ 2 * z.im + t)]
      have h4 : ‖z - m‖ ≤ ‖z + (t : ℂ) * I - m‖ :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
      linarith
    have hRc : IsPreconnected (F '' R) := by
      refine (isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ) * I).continuousOn).image F
        (hFc.mono (hRH.trans QuantumZipper.H_subset_Hbar))
    have hRΓ : F '' R ⊆ Γᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact hoff w (hRH hw) (hRr w hw).ne'
    have hzR : z ∈ R := ⟨0, mem_Ici.2 le_rfl, by simp⟩
    have hsub := hsubI _ hRc hRΓ (F z) ⟨z, hzR, rfl⟩ hzI
    obtain ⟨B, hB⟩ := (hbI.subset hsub).exists_norm_le
    have hT := (hFinf.comp (tendsto_add_mul_I_atTop (QuantumZipper.H_subset_Hbar hz)))
    have hT' := (tendsto_norm_cobounded_atTop.comp hT).eventually (eventually_gt_atTop B)
    obtain ⟨t, htB, ht⟩ := (hT'.and (eventually_ge_atTop (0 : ℝ))).exists
    exact absurd (hB _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩) (not_le.2 htB)
  -- (B) `D ∩ I₀ ⊆ F(Q)`
  set Q : Set ℂ := {z ∈ H | ‖z - m‖ < r} with hQ
  have hB : ∀ w ∈ D, w ∈ I₀ → w ∈ F '' Q := by
    intro w hwD hwI
    obtain ⟨z, hz, rfl⟩ := hFs hwD
    rcases lt_trichotomy ‖z - m‖ r with h | h | h
    · exact ⟨z, ⟨hz, h⟩, rfl⟩
    · obtain ⟨θ, hθ, hθz⟩ := exists_halfCircle_eq hz h
      have : F z ∈ Γ := by
        rcases le_total θ (Real.pi / 2) with h' | h'
        · refine Or.inr ⟨θ / (Real.pi / 2), ⟨div_nonneg hθ.1.le (by positivity),
            (div_le_one (by positivity)).2 h'⟩, ?_⟩
          simp only [hv]
          rw [div_mul_cancel₀ _ (by positivity), hadef, hθz]
        · refine Or.inl ⟨(Real.pi - θ) / (Real.pi / 2), ⟨div_nonneg (by linarith [hθ.2]) (by positivity),
            (div_le_one (by positivity)).2 (by linarith)⟩, ?_⟩
          simp only [hu]
          rw [div_mul_cancel₀ _ (by positivity), sub_sub_cancel, hadef, hθz]
      exact absurd this (hI₀Γ hwI)
    · exact absurd hwI (hA z hz h)
  -- (C) `F(Q) ⊆ I₀`
  have hQc : IsPreconnected (F '' Q) := by
    have hQconv : Convex ℝ Q := by
      have h1 : Convex ℝ H := convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0
      have h2 : Convex ℝ {z : ℂ | ‖z - m‖ < r} := by
        simpa [Metric.ball, dist_eq_norm] using convex_ball (m : ℂ) r
      exact h1.inter h2
    exact hQconv.isPreconnected.image F (hFc.mono fun z hz => QuantumZipper.H_subset_Hbar hz.1)
  have hQΓ : F '' Q ⊆ Γᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hoff z hz.1 hz.2.ne
  have htopΓ : F (a (Real.pi / 2)) ∈ Γ := Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, by simp only [hu]; congr 2; ring⟩
  have htopD : F (a (Real.pi / 2)) ∈ D := hFD (halfCircle_mem_H hr ⟨by positivity, by linarith⟩)
  have hQI : F '' Q ⊆ I₀ := by
    have hcl : F (a (Real.pi / 2)) ∈ closure I₀ := frontier_subset_closure (hfrI.symm ▸ htopΓ)
    obtain ⟨w, hwD, hwI⟩ := mem_closure_iff_nhds.1 hcl D (hDo.mem_nhds htopD)
    exact hsubI _ hQc hQΓ w (hB w hwD hwI) hwI
  -- (D) a real point of `(x, y)` with `F z₀ ≠ q` is sent into `I₀`
  obtain ⟨z₀, hz₀, hFz₀⟩ := exists_ne_of_injOn hFd hFc hFi hxy q
  have hz₀m : |z₀ - m| < r := by
    rw [abs_lt]; constructor <;> [skip; skip] <;> (rw [hm, hrdef]; linarith [hz₀.1, hz₀.2])
  have hz₀Q : (z₀ : ℂ) ∈ closure Q := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := min (ε / 2) ((r - |z₀ - m|) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
    refine ⟨(z₀ : ℂ) + (δ : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
    · show 0 < ((z₀ : ℂ) + (δ : ℂ) * I).im
      simpa using hδ0
    · calc ‖(z₀ : ℂ) + (δ : ℂ) * I - m‖ ≤ ‖((z₀ - m : ℝ) : ℂ)‖ + ‖(δ : ℂ) * I‖ := by
            rw [show (z₀ : ℂ) + (δ : ℂ) * I - m = ((z₀ - m : ℝ) : ℂ) + (δ : ℂ) * I by push_cast; ring]
            exact norm_add_le _ _
        _ = |z₀ - m| + δ := by
            rw [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
              abs_of_pos hδ0]
        _ < r := by linarith [min_le_right (ε / 2) ((r - |z₀ - m|) / 2)]
    · rw [dist_eq_norm, show (z₀ : ℂ) - ((z₀ : ℂ) + (δ : ℂ) * I) = -((δ : ℂ) * I) by ring, norm_neg,
        norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
      linarith [min_le_left (ε / 2) ((r - |z₀ - m|) / 2)]
  have hz₀bar : (z₀ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (z₀ : ℂ).im by simp
  have hFz₀cl : F z₀ ∈ closure I₀ :=
    closure_mono hQI (((hFc _ hz₀bar).mono fun z hz => QuantumZipper.H_subset_Hbar hz.1).mem_closure_image hz₀Q)
  have hFz₀D : F z₀ ∉ D := hfrD _ (hreal z₀)
  have hFz₀Γ : F z₀ ∉ Γ := fun h => hFz₀D (hΓD _ h hFz₀)
  have hFz₀I : F z₀ ∈ I₀ := by
    have hint : F z₀ ∈ interior I₀ := by
      by_contra hni
      exact hFz₀Γ (hfrI ▸ (⟨hFz₀cl, hni⟩ : F z₀ ∈ closure I₀ \ interior I₀))
    exact interior_subset hint
  -- (E) the unbounded linked set through `F z₀` is trapped in the bounded `I₀`
  obtain ⟨S, hSE, hSc, hz₀S, hSb⟩ := hq (F z₀) ⟨hfr (hreal z₀), hFz₀⟩
  have hSΓ : S ⊆ Γᶜ := by
    intro w hwS hwΓ
    have hwq : w ≠ q := (hSE hwS).2
    exact Set.disjoint_left.1 hDE (hΓD w hwΓ hwq) (hSE hwS).1
  exact hSb (hbI.subset (hsubI S hSc hSΓ _ hz₀S hFz₀I))

/-- **Singleton fibre** (supplement Aux. 80, p. 540; the active prime end of D.5, interface 2). Under the hypotheses
of `false_of_apply_eq_of_lt`, at most one real point is sent to `q`. -/
theorem eq_of_apply_eq_of_linked (hDo : IsOpen D) (hFd : DifferentiableOn ℂ F H)
    (hFc : ContinuousOn F Hbar) (hFi : InjOn F H) (hFD : MapsTo F H D) (hFs : SurjOn F H D)
    (hFbd : MapsTo F (Hbar \ H) (frontier D))
    (hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ))
    (hDE : Disjoint D E) (hfr : frontier D ⊆ E) (hq : IsUnboundedLinked (E \ {q}))
    {x y : ℝ} (hx : F x = q) (hy : F y = q) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact (false_of_apply_eq_of_lt hDo hFd hFc hFi hFD hFs hFbd hFinf hDE hfr hq h hx hy).elim
  · exact h
  · exact (false_of_apply_eq_of_lt hDo hFd hFc hFi hFD hFs hFbd hFinf hDE hfr hq h hy hx).elim

/-- **Forward limit at a boundary point with at most one real preimage.** If `G` inverts `F` on `D` (`G(D) ⊆ ℍ`,
`F ∘ G = id` on `D`) and moves points by at most `M`, then at a point `q ∈ closure D \ D` with at most one real
preimage under `F`, `G` converges along `D` to a real point `x₀` with `F x₀ = q`. -/
theorem exists_tendsto_of_fibre {G : ℂ → ℂ} (hFc : ContinuousOn F Hbar) (hFD : MapsTo F H D)
    (hGD : ∀ z ∈ D, G z ∈ H ∧ F (G z) = z) {M : ℝ} (hGM : ∀ z ∈ D, ‖G z - z‖ ≤ M)
    (hqcl : q ∈ closure D) (hqD : q ∉ D) (hfib : ∀ x y : ℝ, F x = q → F y = q → x = y) :
    ∃ x₀ : ℝ, F x₀ = q ∧ Tendsto G (𝓝[D] q) (𝓝 (x₀ : ℂ)) := by
  have : (𝓝[D] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hqcl
  set s : Set ℂ := closedBall 0 (‖q‖ + 1 + M) ∩ Hbar with hs
  have hsc : IsCompact s := (isCompact_closedBall 0 _).inter_right isClosed_Hbar
  have hev : ∀ᶠ z in 𝓝[D] q, z ∈ D ∧ z ∈ ball q 1 :=
    eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (ball_mem_nhds q one_pos))
  have hmem : ∀ᶠ z in 𝓝[D] q, G z ∈ s := by
    filter_upwards [hev] with z ⟨hzD, hzq⟩
    refine ⟨mem_closedBall_zero_iff.2 ?_, QuantumZipper.H_subset_Hbar (hGD z hzD).1⟩
    have h1 := hGM z hzD
    have h2 : ‖z‖ ≤ ‖q‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z q
      rw [mem_ball, dist_eq_norm] at hzq
      linarith
    calc ‖G z‖ = ‖(G z - z) + z‖ := by ring_nf
      _ ≤ ‖G z - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖q‖ + 1 + M := by linarith
  have hFG : Tendsto (fun z => F (G z)) (𝓝[D] q) (𝓝 q) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hGD z hz).2.symm
  have hGl : ∀ᶠ z in 𝓝[D] q, G z ∈ Hbar := hmem.mono fun z hz => hz.2
  have hreal : ∀ ξ ∈ s, MapClusterPt ξ (𝓝[D] q) G → ξ = (ξ.re : ℂ) ∧ F ξ = q := by
    intro ξ hξ hcl
    have hFξ := eq_of_mapClusterPt hFc hGl hFG hξ.2 hcl
    refine ⟨?_, hFξ⟩
    by_cases him : ξ.im = 0
    · exact Complex.ext (by simp) (by simp [him])
    · have hξH : ξ ∈ H := lt_of_le_of_ne (show (0 : ℝ) ≤ ξ.im from hξ.2) (Ne.symm him)
      exact (hqD (hFξ ▸ hFD hξH)).elim
  obtain ⟨ξ₀, hξ₀s, hξ₀⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 hmem)
  obtain ⟨hξ₀r, hFξ₀⟩ := hreal ξ₀ hξ₀s hξ₀
  refine ⟨ξ₀.re, by rw [← hξ₀r]; exact hFξ₀, hsc.tendsto_nhds_of_unique_mapClusterPt hmem ?_⟩
  intro ξ hξ hcl
  obtain ⟨hξr, hFξ⟩ := hreal ξ hξ hcl
  rw [hξr, hfib ξ.re ξ₀.re (by rw [← hξr]; exact hFξ) (by rw [← hξ₀r]; exact hFξ₀)]

end Fibre

/-! ### Linked complements: real rays -/

section Linked

/-- A real point `c ≠ q` lies on an unbounded real ray avoiding `q`. -/
theorem exists_ray {c q : ℂ} (hc : c.im = 0) (hcq : c ≠ q) :
    ∃ S ⊆ {z : ℂ | z.im = 0} \ {q}, IsPreconnected S ∧ c ∈ S ∧ ¬ Bornology.IsBounded S := by
  set σ : ℝ := if q.re ≤ c.re then 1 else -1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  set S := (fun t : ℝ => ((c.re + σ * t : ℝ) : ℂ)) '' Ici 0 with hS
  have hc' : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hc])
  have hcont : Continuous fun t : ℝ => ((c.re + σ * t : ℝ) : ℂ) := by fun_prop
  refine ⟨S, ?_, isPreconnected_Ici.image _ hcont.continuousOn,
    ⟨0, mem_Ici.2 le_rfl, by show ((c.re + σ * 0 : ℝ) : ℂ) = c; rw [mul_zero, add_zero, ← hc']⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨by simp, fun h => ?_⟩
    have hq : q = ((c.re + σ * t : ℝ) : ℂ) := (mem_singleton_iff.1 h).symm
    have hqre : q.re = c.re + σ * t := by rw [hq]; simp
    have ht' : (0 : ℝ) ≤ t := ht
    by_cases hle : q.re ≤ c.re
    · have hσ' : σ = 1 := by simp [hσ, hle]
      rw [hσ'] at hqre
      have ht0 : t = 0 := by linarith
      apply hcq
      rw [hq, ht0, mul_zero, add_zero, ← hc']
    · have hσ' : σ = -1 := by simp [hσ, hle]
      rw [hσ'] at hqre
      linarith
  · intro hb
    obtain ⟨B, hB⟩ := hb.exists_norm_le
    have h := hB _ ⟨|c.re| + |B| + 1, mem_Ici.2 (by positivity), rfl⟩
    rw [norm_real, Real.norm_eq_abs] at h
    have h1 : |σ * (|c.re| + |B| + 1)| = |c.re| + |B| + 1 := by
      rw [abs_mul, hσ1, one_mul, abs_of_pos (by positivity)]
    have h2 := abs_sub_abs_le_abs_sub (σ * (|c.re| + |B| + 1)) (-c.re)
    rw [abs_neg, sub_neg_eq_add, add_comm (σ * (|c.re| + |B| + 1)) c.re, h1] at h2
    linarith [le_abs_self B]

/-- **Linked complements.** If every point `z ≠ q` of `K` lies in a preconnected subset of `K` avoiding `q` and
containing a real point, then `(ℝ ∪ K) \ {q}` is unbounded-linked. -/
theorem isUnboundedLinked_of_forall {K : Set ℂ} {q : ℂ}
    (hK : ∀ z ∈ K, z ≠ q → ∃ C ⊆ K, IsPreconnected C ∧ z ∈ C ∧ q ∉ C ∧ ∃ c ∈ C, c.im = 0) :
    IsUnboundedLinked (({z : ℂ | z.im = 0} ∪ K) \ {q}) := by
  rintro z ⟨hz | hz, hzq⟩
  · obtain ⟨S, hSs, hSc, hzS, hSb⟩ := exists_ray hz hzq
    exact ⟨S, fun w hw => ⟨Or.inl (hSs hw).1, (hSs hw).2⟩, hSc, hzS, hSb⟩
  · obtain ⟨C, hCK, hCc, hzC, hqC, c, hcC, hc⟩ := hK z hz hzq
    have hcq : c ≠ q := fun h => hqC (h ▸ hcC)
    obtain ⟨S, hSs, hSc, hcS, hSb⟩ := exists_ray hc hcq
    refine ⟨C ∪ S, ?_, hCc.union c hcC hcS hSc, Or.inl hzC, fun hb => hSb (hb.subset subset_union_right)⟩
    rintro w (hw | hw)
    · exact ⟨Or.inr (hCK hw), fun h => hqC ((mem_singleton_iff.1 h) ▸ hw)⟩
    · exact ⟨Or.inl (hSs hw).1, (hSs hw).2⟩

end Linked

end Restart

end InteractingSLE
