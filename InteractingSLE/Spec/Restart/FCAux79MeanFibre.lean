/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartDataFibre

/-!
# Aux. 79 at the later first-contact lines: fibres of a boundary extension, relative form

Packet PROVE-FCAUX79. Supplement Aux. lemma 80 (p. 540) bounds the number of real preimages of a boundary point `q`
by the number of components of the obstacle with `q` removed. The landed singleton form
(`Restart.eq_of_apply_eq_of_linked`) needs every point of `E \ {q}` to be linked to `∞` inside `E \ {q}`. At the
seed of the first-contact continuation this fails (the new piece is a bounded component once its seed is removed), but
the new piece contains a boundary value outside any pair of preimages on one side of the tip. This file proves the
**relative form** (`false_of_apply_eq_of_lt_rel`): a set linked to a boundary value `F t₀`, `t₀ ∉ [x, y]`, cannot be
trapped by the Jordan curve over `[x, y]` either.

**Provenance.** The proof is a copy of `Restart.false_of_apply_eq_of_lt` (PROVE-RESTART-CPL3,
`Spec/Restart/ChartDataFibre.lean`); only its last step (E) is changed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart.FCAux79

section Fibre

variable {D E : Set ℂ} {F : ℂ → ℂ} {q : ℂ}

/-- **Two real preimages of one point give a contradiction, with a relative linking hypothesis** (a copy of
`Restart.false_of_apply_eq_of_lt`, ChartDataFibre, with its last step changed): it suffices that every point of
`E \ {q}` lies in a preconnected subset of `E \ {q}` that is unbounded **or contains a boundary value `F t₀` at a real
`t₀` outside `[x, y]`** (such a value is a limit of values outside the half disc over `[x, y]`, hence outside the
bounded Jordan component that traps the set). -/
theorem false_of_apply_eq_of_lt_rel (hDo : IsOpen D) (hFd : DifferentiableOn ℂ F H)
    (hFc : ContinuousOn F Hbar) (hFi : InjOn F H) (hFD : MapsTo F H D) (hFs : SurjOn F H D)
    (hFbd : MapsTo F (Hbar \ H) (frontier D))
    (hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ))
    (hDE : Disjoint D E) (hfr : frontier D ⊆ E) {x y : ℝ}
    (hq : ∀ z ∈ E \ {q}, ∃ S ⊆ E \ {q}, IsPreconnected S ∧ z ∈ S ∧
      (¬ Bornology.IsBounded S ∨ ∃ t₀ : ℝ, (t₀ < x ∨ y < t₀) ∧ F t₀ ∈ S))
    (hxy : x < y) (hx : F x = q) (hy : F y = q) : False := by
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
  -- (E) the linked set through `F z₀` is trapped in the bounded `I₀`, but it is unbounded or reaches `F t₀`
  obtain ⟨S, hSE, hSc, hz₀S, hSo⟩ := hq (F z₀) ⟨hfr (hreal z₀), hFz₀⟩
  have hSΓ : S ⊆ Γᶜ := by
    intro w hwS hwΓ
    have hwq : w ≠ q := (hSE hwS).2
    exact Set.disjoint_left.1 hDE (hΓD w hwΓ hwq) (hSE hwS).1
  have hSI := hsubI S hSc hSΓ _ hz₀S hFz₀I
  rcases hSo with hSb | ⟨t₀, ht₀, hFt₀⟩
  · exact hSb (hbI.subset hSI)
  have hΓc : IsClosed Γ :=
    ((isCompact_Icc.image_of_continuousOn hcu).union (isCompact_Icc.image_of_continuousOn hcv)).isClosed
  have hI₀o : IsOpen I₀ := hΓc.isOpen_compl.connectedComponentIn
  have ht₀r : r < |t₀ - m| := by
    rcases ht₀ with h | h
    · rw [abs_of_neg (by rw [hm]; linarith)]; rw [hm, hrdef]; linarith
    · rw [abs_of_pos (by rw [hm]; linarith)]; rw [hm, hrdef]; linarith
  -- `F t₀` is the limit of `F (t₀ + i/(n+1))`, all outside `I₀`
  set zs : ℕ → ℂ := fun n => (t₀ : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hzs
  have hzsH : ∀ n, zs n ∈ H := fun n => by
    show 0 < (zs n).im
    simp only [hzs, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add, add_zero]
    positivity
  have hzsr : ∀ n, r < ‖zs n - m‖ := fun n => by
    refine ht₀r.trans_le ?_
    have := abs_re_le_norm (zs n - m)
    simpa [hzs] using this
  have hzlim : Tendsto zs atTop (𝓝 (t₀ : ℂ)) := by
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds (x := (t₀ : ℂ))).add (h1.mul_const I)
    simpa [hzs] using h2
  have ht₀bar : (t₀ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (t₀ : ℂ).im by simp
  have hFlim : Tendsto (fun n => F (zs n)) atTop (𝓝 (F t₀)) :=
    (hFc _ ht₀bar).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hzlim, Eventually.of_forall fun n => QuantumZipper.H_subset_Hbar (hzsH n)⟩)
  have hcl : F t₀ ∈ closure I₀ᶜ :=
    mem_closure_of_tendsto hFlim (Eventually.of_forall fun n => hA _ (hzsH n) (hzsr n))
  rw [hI₀o.isClosed_compl.closure_eq] at hcl
  exact hcl (hSI hFt₀)

end Fibre

end Restart.FCAux79

end InteractingSLE
