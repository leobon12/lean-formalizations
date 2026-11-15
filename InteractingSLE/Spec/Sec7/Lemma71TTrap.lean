/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataFibre

/-!
# A Jordan-curve trap between two distinct real boundary values

Packet PROVE-LEMMA71T. Setting of `Restart.false_of_apply_eq_of_lt`: `D ⊆ ℍ` open, `F` continuous on `ℍ̄`, injective
on `ℍ`, mapping `ℍ` onto `D`, real points into `∂D`, and `∞` to `∞`; `E ⊆ ℍ̄` disjoint from `D`.

* **`exists_trap`**: let `x < y` be real with `F x`, `F y` real and distinct. The image under `F` of the upper half
  circle over `[x, y]`, closed by the lower half circle `lowerArc` between the real points `F x` and `F y`, is a Jordan
  curve `Γ`. Its bounded complementary component `I` contains `F z` for every real `z ∈ (x, y)` with
  `F z ∉ {F x, F y}`, contains `F z` for no real `z ∉ [x, y]`, and traps every preconnected subset of `E` that meets it
  and avoids `F x` and `F y` (such a set misses `Γ`: `Γ ∩ ℍ ⊆ D` and `Γ` is below the real axis elsewhere).

  Proof: as in `Restart.false_of_apply_eq_of_lt` (vertical rays from points outside the closed half disc reach `∞`
  avoiding `Γ`; `D ∩ I` is the image of the open half disc), with the closing lower arc in place of a double point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.Lemma71T

open Restart (halfCircle)

/-! ### The lower half circle between two real points -/

section Lower

/-- The lower half circle from the real point `b` (parameter `0`) to the real point `a` (parameter `1`). -/
def lowerArc (a b : ℝ) (s : ℝ) : ℂ :=
  (((a + b) / 2 + (b - a) / 2 * Real.cos (Real.pi * s) : ℝ) : ℂ) -
    ((|b - a| / 2 * Real.sin (Real.pi * s) : ℝ) : ℂ) * I

theorem continuous_lowerArc (a b : ℝ) : Continuous (lowerArc a b) := by
  unfold lowerArc
  fun_prop

theorem lowerArc_re (a b s : ℝ) : (lowerArc a b s).re = (a + b) / 2 + (b - a) / 2 * Real.cos (Real.pi * s) := by
  rw [lowerArc, sub_re, ofReal_re, mul_re, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem lowerArc_im (a b s : ℝ) : (lowerArc a b s).im = -(|b - a| / 2 * Real.sin (Real.pi * s)) := by
  rw [lowerArc, sub_im, ofReal_im, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  ring

theorem lowerArc_zero (a b : ℝ) : lowerArc a b 0 = (b : ℂ) := by
  apply Complex.ext
  · rw [lowerArc_re]; simp; ring
  · rw [lowerArc_im]; simp

theorem lowerArc_one (a b : ℝ) : lowerArc a b 1 = (a : ℂ) := by
  apply Complex.ext
  · rw [lowerArc_re]; simp; ring
  · rw [lowerArc_im]; simp

theorem lowerArc_im_neg {a b : ℝ} (hab : a ≠ b) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : (lowerArc a b s).im < 0 := by
  rw [lowerArc_im]
  have h1 : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hab))
  have h2 : 0 < Real.sin (Real.pi * s) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hs.1) (by nlinarith [Real.pi_pos, hs.2])
  have := mul_pos (half_pos h1) h2
  linarith

theorem lowerArc_injOn {a b : ℝ} (hab : a ≠ b) : InjOn (lowerArc a b) (Icc 0 1) := by
  intro s hs s' hs' h
  have h1 := congrArg Complex.re h
  rw [lowerArc_re, lowerArc_re] at h1
  have hba : (b - a) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.2 (Ne.symm hab)) two_ne_zero
  have h2 : Real.cos (Real.pi * s) = Real.cos (Real.pi * s') := mul_left_cancel₀ hba (add_left_cancel h1)
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, Real.pi * u ∈ Icc 0 Real.pi := fun u hu =>
    ⟨mul_nonneg Real.pi_pos.le hu.1, by nlinarith [Real.pi_pos, hu.2]⟩
  exact mul_left_cancel₀ Real.pi_pos.ne' (Real.injOn_cos (hmem s hs) (hmem s' hs') h2)

end Lower

/-! ### The trap -/

section Trap

variable {D E : Set ℂ} {F : ℂ → ℂ}

theorem trichotomy_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : s = 0 ∨ s = 1 ∨ s ∈ Ioo (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le hs.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hs.2 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr ⟨h, h'⟩)

/-- **The trap between two distinct real boundary values.** In the setting of `Restart.false_of_apply_eq_of_lt`
(`D ⊆ ℍ`, `E ⊆ ℍ̄` disjoint from `D`), let `x < y` with `F x ≠ F y` both real. There is a bounded set `I` (the bounded
component of the complement of the Jordan curve `F(upper half circle over [x, y]) ∪ lower half circle`) such that
`F z ∈ I` for every real `z ∈ (x, y)` with `F z ∉ {F x, F y}`, `F z ∉ I` for every real `z ∉ [x, y]`, and every
preconnected subset of `E` avoiding `F x` and `F y` that meets `I` lies in `I`. -/
theorem exists_trap (hDo : IsOpen D) (hDH : D ⊆ H) (hFc : ContinuousOn F Hbar) (hFi : InjOn F H)
    (hFD : MapsTo F H D) (hFs : SurjOn F H D) (hFbd : MapsTo F (Hbar \ H) (frontier D))
    (hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ))
    (hDE : Disjoint D E) (hEH : E ⊆ Hbar) {x y : ℝ} (hxy : x < y) (hxr : (F x).im = 0) (hyr : (F y).im = 0)
    (hne : F x ≠ F y) :
    ∃ I : Set ℂ, Bornology.IsBounded I ∧
      (∀ z : ℝ, x < z → z < y → F z ≠ F x → F z ≠ F y → F z ∈ I) ∧
      (∀ z : ℝ, z < x ∨ y < z → F z ∉ I) ∧
      (∀ S : Set ℂ, IsPreconnected S → S ⊆ E → F x ∉ S → F y ∉ S → ∀ w ∈ S, w ∈ I → S ⊆ I) := by
  set m : ℝ := (x + y) / 2 with hm
  set r : ℝ := (y - x) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  set a := halfCircle m r with hadef
  have ha0 : a 0 = (y : ℂ) := by
    rw [hadef, Restart.halfCircle_zero]; congr 1; rw [hm, hrdef]; ring
  have haπ : a Real.pi = (x : ℂ) := by
    rw [hadef, Restart.halfCircle_pi]; congr 1; rw [hm, hrdef]; ring
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hreal : ∀ t : ℝ, F t ∈ frontier D := fun t =>
    hFbd ⟨show (0 : ℝ) ≤ (t : ℂ).im by simp, fun h => by
      have : (0 : ℝ) < (t : ℂ).im := h
      simp at this⟩
  have hfrD : ∀ w ∈ frontier D, w ∉ D := fun w hw hwD => by
    rw [hDo.frontier_eq] at hw; exact hw.2 hwD
  have hxD : F x ∉ D := hfrD _ (hreal x)
  have hyD : F y ∉ D := hfrD _ (hreal y)
  have hFbar : ∀ z ∈ Hbar, 0 ≤ (F z).im := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact (show 0 < (F z).im from hDH (hFD hzH)).le
    · have h1 : F z ∈ closure D := frontier_subset_closure (hFbd ⟨hz, hzH⟩)
      have h2 : closure D ⊆ Hbar := (closure_mono hDH).trans (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar])
      exact h2 h1
  obtain ⟨p, hFx⟩ : ∃ p : ℝ, F x = (p : ℂ) := ⟨(F x).re, Complex.ext (by simp) (by simp [hxr])⟩
  obtain ⟨q, hFy⟩ : ∃ q : ℝ, F y = (q : ℂ) := ⟨(F y).re, Complex.ext (by simp) (by simp [hyr])⟩
  have hpq : p ≠ q := fun h => hne (by rw [hFx, hFy, h])
  -- the two arcs
  set u : ℝ → ℂ := fun s => F (a (Real.pi * s)) with hu
  set v : ℝ → ℂ := lowerArc p q with hv
  have hθ : ∀ s ∈ Icc (0 : ℝ) 1, Real.pi * s ∈ Icc 0 Real.pi := fun s hs =>
    ⟨mul_nonneg hpi.le hs.1, by nlinarith [hs.2]⟩
  have haH : ∀ s ∈ Ioo (0 : ℝ) 1, a (Real.pi * s) ∈ H := fun s hs =>
    Restart.halfCircle_mem_H hr ⟨mul_pos hpi hs.1, by nlinarith [hs.2]⟩
  have hu0 : u 0 = F y := by simp only [hu, mul_zero]; rw [ha0]
  have hu1 : u 1 = F x := by simp only [hu, mul_one]; rw [haπ]
  have hv0 : v 0 = F y := by rw [hFy]; exact lowerArc_zero p q
  have hv1 : v 1 = F x := by rw [hFx]; exact lowerArc_one p q
  have huD : ∀ s ∈ Ioo (0 : ℝ) 1, u s ∈ D := fun s hs => hFD (haH s hs)
  have hcu : ContinuousOn u (Icc 0 1) := by
    refine hFc.comp ((Restart.continuous_halfCircle m r).comp (continuous_const.mul continuous_id)).continuousOn
      fun s hs => ?_
    exact Restart.halfCircle_mem_Hbar hr.le (hθ s hs)
  have hcv : ContinuousOn v (Icc 0 1) := (continuous_lowerArc p q).continuousOn
  have hiu : InjOn u (Icc 0 1) := by
    intro s hs s' hs' h
    rcases trichotomy_Icc hs with rfl | rfl | hs0 <;> rcases trichotomy_Icc hs' with rfl | rfl | hs0'
    · rfl
    · exact (hne (hu1.symm.trans (h.symm.trans hu0))).elim
    · exact (hyD (by rw [← hu0, h]; exact huD s' hs0')).elim
    · exact (hne (hu1.symm.trans (h.trans hu0))).elim
    · rfl
    · exact (hxD (by rw [← hu1, h]; exact huD s' hs0')).elim
    · exact (hyD (by rw [← hu0, ← h]; exact huD s hs0)).elim
    · exact (hxD (by rw [← hu1, ← h]; exact huD s hs0)).elim
    · have h1 := Restart.halfCircle_injOn hr (hθ s hs) (hθ s' hs') (hFi (haH s hs0) (haH s' hs0') h)
      exact mul_left_cancel₀ hpi.ne' h1
  have hiv : InjOn v (Icc 0 1) := lowerArc_injOn hpq
  have hvim : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (v s).im → s = 0 ∨ s = 1 := by
    intro s hs hs'
    rcases trichotomy_Icc hs with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hs' (not_le.2 (lowerArc_im_neg hpq h))
  have huHbar : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (u s).im := fun s hs =>
    hFbar _ (Restart.halfCircle_mem_Hbar hr.le (hθ s hs))
  have hint : u '' Icc 0 1 ∩ v '' Icc 0 1 ⊆ {u 0, u 1} := by
    rintro w ⟨⟨s, hs, rfl⟩, ⟨s', hs', hs'e⟩⟩
    rcases hvim s' hs' (by rw [hs'e]; exact huHbar s hs) with rfl | rfl
    · exact Or.inl (hs'e.symm.trans (hv0.trans hu0.symm))
    · exact Or.inr (hs'e.symm.trans (hv1.trans hu1.symm))
  set Γ := u '' Icc 0 1 ∪ v '' Icc 0 1 with hΓdef
  have hΓ : LQGMetric.JordanMap.IsJordanCurve Γ :=
    Sec7.isJordanCurve_image_union hcu hcv hiu hiv (hu0.trans hv0.symm) (hu1.trans hv1.symm) hint
  -- a point of `Γ` in `D` is on the open upper arc
  have hΓD : ∀ w ∈ Γ, w ∈ D → ∃ s ∈ Ioo (0 : ℝ) 1, u s = w := by
    rintro w (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) hwD
    · rcases trichotomy_Icc hs with rfl | rfl | h
      · exact (hyD (by rw [← hu0]; exact hwD)).elim
      · exact (hxD (by rw [← hu1]; exact hwD)).elim
      · exact ⟨s, h, rfl⟩
    · rcases hvim s hs (show 0 < (v s).im from hDH hwD).le with rfl | rfl
      · exact (hyD (by rw [← hv0]; exact hwD)).elim
      · exact (hxD (by rw [← hv1]; exact hwD)).elim
  -- a value in `ℍ̄` off `D` and off the two endpoints is off `Γ`
  have hnotΓ : ∀ w, w ∉ D → 0 ≤ w.im → w ≠ F x → w ≠ F y → w ∉ Γ := by
    rintro w hwD hw0 hwx hwy (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · rcases trichotomy_Icc hs with rfl | rfl | h
      · exact hwy hu0
      · exact hwx hu1
      · exact hwD (huD s h)
    · rcases hvim s hs hw0 with rfl | rfl
      · exact hwy hv0
      · exact hwx hv1
  -- points of `ℍ` off the half circle are sent off `Γ`
  have hoff : ∀ z ∈ H, ‖z - m‖ ≠ r → F z ∉ Γ := by
    intro z hz hzr hzΓ
    obtain ⟨s, hs, hse⟩ := hΓD _ hzΓ (hFD hz)
    have := hFi (haH s hs) hz hse
    exact hzr (by rw [← this]; exact Restart.norm_halfCircle_sub m hr.le _)
  obtain ⟨w₁, hw₁, -, -, hbI, -, -, -, hfrI, -⟩ := jordan_curve_components hΓ
  set I₀ := connectedComponentIn Γᶜ w₁ with hI₀
  have hI₀Γ : I₀ ⊆ Γᶜ := connectedComponentIn_subset _ _
  have hΓc : IsClosed Γ :=
    ((isCompact_Icc.image_of_continuousOn hcu).union (isCompact_Icc.image_of_continuousOn hcv)).isClosed
  have hI₀o : IsOpen I₀ := hΓc.isOpen_compl.connectedComponentIn
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
        simp [Complex.sq_norm, Complex.normSq_apply]; ring
      have h2 : ‖z + (t : ℂ) * I - m‖ ^ 2 = (z.re - m) ^ 2 + (z.im + t) ^ 2 := by
        simp [Complex.sq_norm, Complex.normSq_apply]; ring
      have ht' : (0 : ℝ) ≤ t := ht
      have h3 : ‖z - m‖ ^ 2 ≤ ‖z + (t : ℂ) * I - m‖ ^ 2 := by
        rw [h1, h2]; nlinarith [mul_nonneg ht' (by linarith : (0 : ℝ) ≤ 2 * z.im + t)]
      have h4 : ‖z - m‖ ≤ ‖z + (t : ℂ) * I - m‖ :=
        (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3
      linarith
    have hRc : IsPreconnected (F '' R) :=
      (isPreconnected_Ici.image _ (by fun_prop : Continuous fun t : ℝ => z + (t : ℂ) * I).continuousOn).image F
        (hFc.mono (hRH.trans QuantumZipper.H_subset_Hbar))
    have hRΓ : F '' R ⊆ Γᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact hoff w (hRH hw) (hRr w hw).ne'
    have hzR : z ∈ R := ⟨0, mem_Ici.2 le_rfl, by simp⟩
    have hsub := hsubI _ hRc hRΓ (F z) ⟨z, hzR, rfl⟩ hzI
    obtain ⟨B, hB⟩ := (hbI.subset hsub).exists_norm_le
    have hT := hFinf.comp (Restart.tendsto_add_mul_I_atTop (QuantumZipper.H_subset_Hbar hz))
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
    · obtain ⟨θ, hθ', hθz⟩ := Restart.exists_halfCircle_eq hz h
      have hπθ : Real.pi * (θ / Real.pi) = θ := by field_simp
      have hmem : F z ∈ Γ := Or.inl ⟨θ / Real.pi, ⟨div_nonneg hθ'.1.le hpi.le, (div_le_one hpi).2 hθ'.2.le⟩, by
        simp only [hu]; rw [hπθ, hadef, hθz]⟩
      exact absurd hmem (hI₀Γ hwI)
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
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have htopΓ : u (1 / 2) ∈ Γ := Or.inl ⟨1 / 2, Ioo_subset_Icc_self hhalf, rfl⟩
  have hQI : F '' Q ⊆ I₀ := by
    have hcl : u (1 / 2) ∈ closure I₀ := frontier_subset_closure (hfrI.symm ▸ htopΓ)
    obtain ⟨w, hwD, hwI⟩ := mem_closure_iff_nhds.1 hcl D (hDo.mem_nhds (huD _ hhalf))
    exact hsubI _ hQc hQΓ w (hB w hwD hwI) hwI
  -- (D) real points of `(x, y)` with a value off the endpoints are sent into `I₀`
  have hin : ∀ z : ℝ, x < z → z < y → F z ≠ F x → F z ≠ F y → F z ∈ I₀ := by
    intro z hxz hzy hzx hzy'
    have hzm : |z - m| < r := by
      rw [abs_lt]; constructor <;> (rw [hm, hrdef]; linarith)
    have hzQ : (z : ℂ) ∈ closure Q := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      set δ := min (ε / 2) ((r - |z - m|) / 2) with hδ
      have hδ0 : 0 < δ := lt_min (by positivity) (by linarith)
      refine ⟨(z : ℂ) + (δ : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
      · show 0 < ((z : ℂ) + (δ : ℂ) * I).im
        simpa using hδ0
      · calc ‖(z : ℂ) + (δ : ℂ) * I - m‖ ≤ ‖((z - m : ℝ) : ℂ)‖ + ‖(δ : ℂ) * I‖ := by
              rw [show (z : ℂ) + (δ : ℂ) * I - m = ((z - m : ℝ) : ℂ) + (δ : ℂ) * I by push_cast; ring]
              exact norm_add_le _ _
          _ = |z - m| + δ := by
              rw [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
                abs_of_pos hδ0]
          _ < r := by linarith [min_le_right (ε / 2) ((r - |z - m|) / 2)]
      · rw [dist_eq_norm, show (z : ℂ) - ((z : ℂ) + (δ : ℂ) * I) = -((δ : ℂ) * I) by ring, norm_neg,
          norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
        linarith [min_le_left (ε / 2) ((r - |z - m|) / 2)]
    have hzbar : (z : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (z : ℂ).im by simp
    have hFzcl : F z ∈ closure I₀ :=
      closure_mono hQI (((hFc _ hzbar).mono fun w hw => QuantumZipper.H_subset_Hbar hw.1).mem_closure_image hzQ)
    have hFzΓ : F z ∉ Γ := hnotΓ _ (hfrD _ (hreal z)) (hFbar _ hzbar) hzx hzy'
    have hint : F z ∈ interior I₀ := by
      by_contra hni
      exact hFzΓ (hfrI ▸ (⟨hFzcl, hni⟩ : F z ∈ closure I₀ \ interior I₀))
    exact interior_subset hint
  -- (E) real points outside `[x, y]` are sent off `I₀`
  have hout : ∀ z : ℝ, z < x ∨ y < z → F z ∉ I₀ := by
    intro z hz hzI
    set O : Set ℂ := {w ∈ H | r < ‖w - m‖} with hO
    have hzm : r < |z - m| := by
      rcases hz with h | h
      · rw [abs_of_neg (by rw [hm]; linarith)]; rw [hm, hrdef]; linarith
      · rw [abs_of_pos (by rw [hm]; linarith)]; rw [hm, hrdef]; linarith
    have hzO : (z : ℂ) ∈ closure O := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      refine ⟨(z : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
      · show 0 < ((z : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add, add_zero]
        linarith
      · calc r < |z - m| := hzm
          _ = |((z : ℂ) + ((ε / 2 : ℝ) : ℂ) * I - m).re| := by
              simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, mul_one, add_zero,
                sub_self]
          _ ≤ ‖(z : ℂ) + ((ε / 2 : ℝ) : ℂ) * I - m‖ := Complex.abs_re_le_norm _
      · rw [dist_eq_norm, show (z : ℂ) - ((z : ℂ) + ((ε / 2 : ℝ) : ℂ) * I) = -(((ε / 2 : ℝ) : ℂ) * I) by ring,
          norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
    have hzbar : (z : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (z : ℂ).im by simp
    have hcl : F z ∈ closure (F '' O) :=
      ((hFc _ hzbar).mono fun w hw => QuantumZipper.H_subset_Hbar hw.1).mem_closure_image hzO
    have hsub : F '' O ⊆ I₀ᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact hA w hw.1 hw.2
    exact closure_minimal hsub hI₀o.isClosed_compl hcl hzI
  -- (F) the trapped sets
  refine ⟨I₀, hbI, hin, hout, fun S hS hSE hxS hyS w hwS hwI => hsubI S hS ?_ w hwS hwI⟩
  intro w' hw'S hw'Γ
  refine hnotΓ w' (Set.disjoint_right.1 hDE (hSE hw'S)) (hEH (hSE hw'S)) ?_ ?_ hw'Γ
  · rintro rfl; exact hxS hw'S
  · rintro rfl; exact hyS hw'S

end Trap

end InteractingSLE.Sec7.Lemma71T

end
