/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Zhan's A.1.6: the normalized seed factors (D13)–(D15)

Packet PROVE-ZHAN-GT4-A12. Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L426–L507, R38): with `Δh(u, v) = (h(u) − h(v))/(u − v)` for `u ≠ v` and `h'(u)` for `u = v`, the degenerate factors of
(D6a) at a seed mark are replaced by `(h'_j(V)/g'_k(x_j))^γ` (D13), `(Δh_j(W_j, V)/g'_k(x_j))^r` (D14),
`(Δh_j(V_m, V_n)/g'_k(x_j))^δ` (D15). "These formulas follow by cancelling the own-map derivative or distance before
letting the original mark approach the source. For example `G'(p)/(g'_j(p) g'_k(p)) = h'_j(g_j(p))/g'_k(p)`,
`(G(p) − G(q))(p − q)/((g_j(p) − g_j(q))(g_k(p) − g_k(q))) = Δh_j(g_j(p), g_j(q))/Δg_k(p, q)`. … The opposite-hull map
`h_j` is analytic across the entire relevant real interval, with positive derivative. Therefore its divided differences
are positive and bounded above and below by the same derivative bounds used in (D9). They extend continuously to all
zero gaps at the time axes."

Here `Δh = dslope h` (Mathlib's divided difference with the derivative on the diagonal):

* `normFactor_deriv_eq`, `normFactor_pair_eq`: the two cancellation identities, for `G = h ∘ g` (real maps);
* `dslope_mem_Icc_of_deriv_mem_Icc`: **bounds**: if `c ≤ h' ≤ C` on an interval, then `c ≤ Δh ≤ C` there
  (positivity for `c > 0`);
* `continuousOn_dslope_uncurry`: **continuity up to zero gaps**: for `h` continuously differentiable on an open
  interval, `(u, v) ↦ Δh(u, v)` is jointly continuous on its square, the diagonal included.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

/-! ### The cancellation identities -/

/-- **(D13), the cancellation**: for `G = h ∘ g` with `G'(p) = h'(g(p)) g'(p)`,
`G'(p)/(g'(p) f'(p)) = h'(g(p))/f'(p)` (`g = g_j` the own map, `f = g_k`). -/
theorem normFactor_deriv_eq {G' h'g g' f' : ℝ} (hG : G' = h'g * g') (hg : g' ≠ 0) :
    G' / (g' * f') = h'g / f' := by
  rw [hG, mul_comm g' f', mul_div_mul_right _ _ hg]

/-- **(D14)–(D15), the cancellation**: for `G = h ∘ g`, `p ≠ q`, `g p ≠ g q`,
`(G p − G q)(p − q)/((g p − g q)(f p − f q)) = Δh(g q, g p)/Δf(q, p)`. -/
theorem normFactor_pair_eq {h g f : ℝ → ℝ} {p q : ℝ} (hpq : p ≠ q) (hg : g p ≠ g q) :
    (h (g p) - h (g q)) * (p - q) / ((g p - g q) * (f p - f q)) = dslope h (g q) (g p) / dslope f q p := by
  rw [dslope_of_ne _ hg, dslope_of_ne _ hpq, slope_def_field, slope_def_field]
  have h1 : g p - g q ≠ 0 := sub_ne_zero.2 hg
  have h2 : p - q ≠ 0 := sub_ne_zero.2 hpq
  by_cases hf : f p - f q = 0
  · rw [hf, mul_zero, div_zero, zero_div, div_zero]
  · field_simp

/-! ### Bounds of divided differences -/

/-- **Divided differences are bounded by the derivative bounds**: if `h` is differentiable on an open interval `I`
(any convex set) with `c ≤ h' ≤ C` there, then `c ≤ Δh(u, v) ≤ C` for `u, v ∈ I`. -/
theorem dslope_mem_Icc_of_deriv_mem_Icc {h : ℝ → ℝ} {I : Set ℝ} (hIc : Convex ℝ I)
    (hd : DifferentiableOn ℝ h I) {c C : ℝ} (hb : ∀ x ∈ I, deriv h x ∈ Icc c C) {u v : ℝ} (hu : u ∈ I)
    (hv : v ∈ I) : dslope h u v ∈ Icc c C := by
  rcases eq_or_ne v u with rfl | hne
  · rw [dslope_same]; exact hb v hv
  rw [dslope_of_ne _ hne]
  -- the mean value theorem on the segment between `u` and `v`
  have key : ∀ {x y : ℝ}, x ∈ I → y ∈ I → x < y → slope h x y ∈ Icc c C := by
    intro x y hx hy hxy
    have hsub : Icc x y ⊆ I := hIc.ordConnected.out hx hy
    obtain ⟨ξ, hξ, hξe⟩ := exists_deriv_eq_slope h hxy (hd.continuousOn.mono hsub)
      ((hd.mono (Ioo_subset_Icc_self.trans hsub)))
    rw [slope_def_field, ← hξe]
    exact hb ξ (hsub (Ioo_subset_Icc_self hξ))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [slope_comm]; exact key hv hu hlt
  · exact key hu hv hgt

/-! ### Continuity of divided differences up to the diagonal -/

/-- **Divided differences are jointly continuous, the diagonal included**, for a function continuously differentiable
on an open set `I` (for instance an open interval). -/
theorem continuousOn_dslope_uncurry {h : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hd : DifferentiableOn ℝ h I) (hc : ContinuousOn (deriv h) I) :
    ContinuousOn (fun p : ℝ × ℝ => dslope h p.1 p.2) (I ×ˢ I) := by
  rintro ⟨u₀, v₀⟩ ⟨hu₀, hv₀⟩
  refine ContinuousAt.continuousWithinAt ?_
  rcases eq_or_ne v₀ u₀ with rfl | hne
  · -- on the diagonal: the mean value theorem and continuity of `h'`
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.1 hI v₀ hu₀
    obtain ⟨δ₂, hδ₂, hcont⟩ := Metric.continuousWithinAt_iff.1 (hc v₀ hu₀) ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp => ?_⟩
    have hp1 : dist p.1 v₀ < min δ₁ δ₂ := lt_of_le_of_lt (le_max_left _ _) hp
    have hp2 : dist p.2 v₀ < min δ₁ δ₂ := lt_of_le_of_lt (le_max_right _ _) hp
    have hJ : ∀ x, dist x v₀ < min δ₁ δ₂ → x ∈ I := fun x hx =>
      hball (mem_ball.2 (lt_of_lt_of_le hx (min_le_left _ _)))
    have hderiv : ∀ x, dist x v₀ < min δ₁ δ₂ → dist (deriv h x) (deriv h v₀) < ε := fun x hx =>
      hcont (hJ x hx) (lt_of_lt_of_le hx (min_le_right _ _))
    simp only [dslope_same]
    rcases eq_or_ne p.2 p.1 with he | hne'
    · rw [he, dslope_same]; exact hderiv _ hp1
    · rw [dslope_of_ne _ hne']
      -- the slope is a derivative at a point between `p.1` and `p.2`
      have hmid : ∀ {x y : ℝ}, dist x v₀ < min δ₁ δ₂ → dist y v₀ < min δ₁ δ₂ → x < y →
          dist (slope h x y) (deriv h v₀) < ε := by
        intro x y hx hy hxy
        have hsub : Icc x y ⊆ ball v₀ (min δ₁ δ₂) := (convex_ball v₀ _).ordConnected.out
          (mem_ball.2 hx) (mem_ball.2 hy)
        have hsubI : Icc x y ⊆ I := fun z hz => hJ z (mem_ball.1 (hsub hz))
        obtain ⟨ξ, hξ, hξe⟩ := exists_deriv_eq_slope h hxy (hd.continuousOn.mono hsubI)
          (hd.mono (Ioo_subset_Icc_self.trans hsubI))
        rw [slope_def_field, ← hξe]
        exact hderiv ξ (mem_ball.1 (hsub (Ioo_subset_Icc_self hξ)))
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · rw [slope_comm]; exact hmid hp2 hp1 hlt
      · exact hmid hp1 hp2 hgt
  · -- off the diagonal: a quotient of continuous functions
    have hU : IsOpen {p : ℝ × ℝ | p.2 ≠ p.1} := isOpen_ne_fun continuous_snd continuous_fst
    have hIU : I ×ˢ I ∩ {p : ℝ × ℝ | p.2 ≠ p.1} ∈ 𝓝 (u₀, v₀) :=
      Filter.inter_mem ((hI.prod hI).mem_nhds ⟨hu₀, hv₀⟩) (hU.mem_nhds hne)
    have heq : (fun p : ℝ × ℝ => (h p.2 - h p.1) / (p.2 - p.1)) =ᶠ[𝓝 (u₀, v₀)]
        fun p : ℝ × ℝ => dslope h p.1 p.2 := by
      filter_upwards [hIU] with p hp
      rw [dslope_of_ne _ hp.2, slope_def_field]
    refine ContinuousAt.congr ?_ heq
    have hh : ContinuousAt h v₀ := hd.continuousOn.continuousAt (hI.mem_nhds hv₀)
    have hh' : ContinuousAt h u₀ := hd.continuousOn.continuousAt (hI.mem_nhds hu₀)
    exact ((hh.comp continuous_snd.continuousAt).sub (hh'.comp continuous_fst.continuousAt)).div
      (continuous_snd.continuousAt.sub continuous_fst.continuousAt) (sub_ne_zero.2 hne)

end InteractingSLE.ZhanGT4
