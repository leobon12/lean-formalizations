/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Supplement §8: deterministic path facts in GB3 and GB6

Packet PROVE-SUPP8 (specification supplement §8.3, `source/spec/p481-528.md` L797–L824, pp. 513–514, and §8.6,
L926–L977, pp. 518–520).

* **GB3, separation of the two left marks**: before the first outer collision the coordinate difference of the two
  left marks satisfies `V₁(t) − V₂(t) = (V₁(s) − V₂(s)) exp(−∫_s^t 2 du/(X₁X₂))`; its pathwise content, that the
  integrated equation `f(r) = f(s) + ∫_s^r a f` with an integrable `a ≤ 0` (here `a = −2/(X₁X₂)`, integrable on
  compact subintervals even through inner seed collisions) preserves strict positivity, is
  `pos_of_eq_add_integral_mul`; the rate identity is `gb3_rate`.
* **GB3, simultaneous visits**: a continuous proper trace `η : [0, ∞) → ℂ` that visits every nonzero rational point
  visits every real point (`gb3_visits_all`); the reason is that the range of a proper continuous path is closed
  (`isClosed_image_Ici_of_tendsto`).
* **GB6, final assertion**: a continuous path whose points at a dense set of times lie in the (closed) range of a
  proper continuous trace lies in that range at all times (`image_subset_of_dense`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric

namespace InteractingSLE

namespace Supp8

/-! ### GB3: the separation identity -/

/-- **GB3**: the difference of two left marks moves at the rate `2/(V₁ − W) − 2/(V₂ − W) = −2(V₁ − V₂)/(X₁X₂)` with
`X_i = W − V_i`. -/
theorem gb3_rate {W V₁ V₂ : ℝ} (h₁ : W - V₁ ≠ 0) (h₂ : W - V₂ ≠ 0) :
    2 / (V₁ - W) - 2 / (V₂ - W) = -(2 * (V₁ - V₂) / ((W - V₁) * (W - V₂))) := by
  have h₁' : V₁ - W ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h₁
  have h₂' : V₂ - W ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h₂
  field_simp
  ring

/-- **GB3, strict separation is preserved.** If `f` is continuous on `[s, t]`, `a ≤ 0` is integrable there, `f`
satisfies the integrated linear equation `f(r) = f(s) + ∫_s^r a f`, and `f(s) > 0`, then `f > 0` on `[s, t]`. (This
is the pathwise content of `f(r) = f(s) exp(∫_s^r a)`.) -/
theorem pos_of_eq_add_integral_mul {f a : ℝ → ℝ} {s t : ℝ} (hf : ContinuousOn f (Icc s t))
    (ha : IntegrableOn a (Icc s t)) (ha0 : ∀ r ∈ Icc s t, a r ≤ 0)
    (heq : ∀ r ∈ Icc s t, f r = f s + ∫ u in s..r, a u * f u) (hfs : 0 < f s) :
    ∀ r ∈ Icc s t, 0 < f r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨r₀, hr₀, hfr₀⟩ := hcon
  set E := Icc s t ∩ f ⁻¹' Iic 0 with hE
  have hEc : IsClosed E := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hEne : E.Nonempty := ⟨r₀, hr₀, hfr₀⟩
  have hEbdd : BddBelow E := ⟨s, fun x hx => hx.1.1⟩
  set r := sInf E with hr
  have hrE : r ∈ E := hEc.csInf_mem hEne hEbdd
  have hrs : s < r := by
    rcases eq_or_lt_of_le hrE.1.1 with h | h
    · exact absurd (h ▸ hrE.2 : f s ≤ 0) (not_le.2 hfs)
    · exact h
  have hpos : ∀ x ∈ Ico s r, 0 < f x := fun x hx => by
    by_contra h
    have : r ≤ x := csInf_le hEbdd ⟨⟨hx.1, hx.2.le.trans hrE.1.2⟩, not_lt.1 h⟩
    linarith [hx.2]
  have hsub : Icc s r ⊆ Icc s t := Icc_subset_Icc_right hrE.1.2
  have haf : IntegrableOn (fun u => a u * f u) (Icc s r) :=
    (ha.mono_set hsub).mul_continuousOn (hf.mono hsub) isCompact_Icc
  have hafi : ∀ x y, x ∈ Icc s r → y ∈ Icc s r → IntervalIntegrable (fun u => a u * f u) volume x y :=
    fun x y hx hy => (haf.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable
  -- `f` is nonincreasing on `[s, r]`.
  have hdiff : ∀ x ∈ Icc s r, ∀ y ∈ Icc s r, f y - f x = ∫ u in x..y, a u * f u := by
    intro x hx y hy
    rw [heq y (hsub hy), heq x (hsub hx)]
    rw [← intervalIntegral.integral_interval_sub_left (hafi s y ⟨le_rfl, hrs.le⟩ hy)
      (hafi s x ⟨le_rfl, hrs.le⟩ hx)]
    ring
  have hfr0 : 0 ≤ f r := by
    have hcl : r ∈ closure (Ico s r) := by rw [closure_Ico hrs.ne]; exact ⟨hrs.le, le_rfl⟩
    have h := ((hf r (hsub ⟨hrs.le, le_rfl⟩)).mono
      (fun x hx => hsub ⟨hx.1, hx.2.le⟩)).mem_closure_image hcl
    exact closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact (hpos x hx).le) isClosed_Ici h
  have hfnn : ∀ u ∈ Icc s r, 0 ≤ f u := fun u hu => by
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact hfr0
    · exact (hpos u ⟨hu.1, h⟩).le
  have hmono : ∀ x ∈ Icc s r, ∀ y ∈ Icc s r, x ≤ y → f y ≤ f x := by
    intro x hx y hy hxy
    have := hdiff x hx y hy
    have hi : ∫ u in x..y, a u * f u ≤ 0 := by
      have : 0 ≤ ∫ u in x..y, -(a u * f u) :=
        intervalIntegral.integral_nonneg hxy fun u hu => by
          have hu' : u ∈ Icc s r := ⟨hx.1.trans hu.1, hu.2.trans hy.2⟩
          nlinarith [ha0 u (hsub hu'), hfnn u hu']
      rw [intervalIntegral.integral_neg] at this
      linarith
    linarith
  -- Choose `s' < r` with `∫_{s'}^r |a| < 1/2`.
  have haabs : IntegrableOn (fun u => |a u|) (Icc s r) := (ha.mono_set hsub).abs
  have hcont : ContinuousOn (fun x => ∫ u in x..r, |a u|) (Icc s r) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left
      (f := fun u => |a u|) (μ := volume) (a := s) (b := r)
      (by rw [uIcc_of_le hrs.le]; exact haabs)
    rwa [uIcc_of_le hrs.le] at h
  have hev : ∀ᶠ x in 𝓝[Icc s r] r, ∫ u in x..r, |a u| < 1 / 2 := by
    have := (hcont r ⟨hrs.le, le_rfl⟩).tendsto
    rw [intervalIntegral.integral_same] at this
    exact this (Iio_mem_nhds (by norm_num))
  have hIcc : Icc s r ∈ 𝓝[<] r := mem_of_superset (Ioo_mem_nhdsLT hrs) Ioo_subset_Icc_self
  have hev' : ∀ᶠ x in 𝓝[<] r, x ∈ Icc s r ∧ ∫ u in x..r, |a u| < 1 / 2 :=
    (eventually_of_mem hIcc fun x hx => hx).and (nhdsWithin_le_of_mem hIcc hev)
  obtain ⟨s', ⟨hs', hint⟩, hs'r⟩ := (hev'.and self_mem_nhdsWithin).exists
  have hs'r' : s' ∈ Ico s r := ⟨hs'.1, hs'r⟩
  have hfs' := hpos s' hs'r'
  -- `f r ≥ f(s') − f(s') ∫_{s'}^r |a| ≥ f(s')/2 > 0`.
  have hbound : |∫ u in s'..r, a u * f u| ≤ f s' * ∫ u in s'..r, |a u| := by
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.abs_integral_le_integral_abs hs'r.le).trans
      (intervalIntegral.integral_mono_on hs'r.le ?_ ?_ fun u hu => ?_)
    · exact (hafi s' r hs' ⟨hrs.le, le_rfl⟩).abs
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hs'r.le).2
        (haabs.mono_set (Icc_subset_Icc_left hs'.1))).const_mul _
    · have hu' : u ∈ Icc s r := ⟨hs'.1.trans hu.1, hu.2⟩
      rw [abs_mul, abs_of_nonneg (hfnn u hu'), mul_comm]
      exact mul_le_mul_of_nonneg_right (hmono s' hs' u hu' hu.1) (abs_nonneg _)
  have hd := hdiff s' hs' r ⟨hrs.le, le_rfl⟩
  have hfr : f r ≤ 0 := hrE.2
  have := abs_le.1 hbound
  nlinarith

/-! ### GB3 and GB6: ranges of proper continuous paths -/

/-- The range of a continuous path `η` on `[0, ∞)` with `‖η t‖ → ∞` is closed. -/
theorem isClosed_image_Ici_of_tendsto {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0))
    (hprop : Tendsto (fun t => ‖η t‖) atTop atTop) : IsClosed (η '' Ici 0) := by
  refine isClosed_iff_clusterPt.2 fun y hy => ?_
  have hy' : y ∈ closure (η '' Ici 0) := mem_closure_iff_clusterPt.2 hy
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hprop.eventually (eventually_gt_atTop (‖y‖ + 1)))
  set T' := max T 0 with hT'
  have hK : IsCompact (η '' Icc 0 T') := isCompact_Icc.image_of_continuousOn (hη.mono Icc_subset_Ici_self)
  have hyK : y ∈ closure (η '' Icc 0 T') := by
    rw [Metric.mem_closure_iff] at hy' ⊢
    intro ε hε
    obtain ⟨_, ⟨t, ht, rfl⟩, hd⟩ := hy' (min ε 1) (lt_min hε one_pos)
    refine ⟨η t, ⟨t, ⟨ht, ?_⟩, rfl⟩, hd.trans_le (min_le_left _ _)⟩
    by_contra h
    push Not at h
    have h1 := hT t ((le_max_left _ _).trans h.le)
    have h2 : ‖η t‖ ≤ ‖y‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (η t) y
      rw [dist_comm, dist_eq_norm] at hd
      linarith [min_le_right ε 1]
    linarith
  rw [hK.isClosed.closure_eq] at hyK
  exact image_mono Icc_subset_Ici_self hyK

/-- **GB3, simultaneous visits**: a continuous proper trace on `[0, ∞)` visiting every nonzero rational point visits
every real point. -/
theorem gb3_visits_all {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0))
    (hprop : Tendsto (fun t => ‖η t‖) atTop atTop) (hq : ∀ q : ℚ, q ≠ 0 → ∃ t ≥ 0, η t = (q : ℂ))
    (x : ℝ) : ∃ t ≥ 0, η t = x := by
  have hcl := isClosed_image_Ici_of_tendsto hη hprop
  suffices hx : (x : ℂ) ∈ closure (η '' Ici 0) by
    rw [hcl.closure_eq] at hx
    obtain ⟨t, ht, h⟩ := hx
    exact ⟨t, ht, h⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show x < x + ε / 2 by linarith)
  obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show x + ε / 2 < x + ε by linarith)
  have hne : q₁ ≠ q₂ := fun h => by
    have : (q₁ : ℝ) < q₂ := hq₁.2.trans hq₂.1
    rw [h] at this; exact lt_irrefl _ this
  have hpick : ∃ q : ℚ, q ≠ 0 ∧ x < q ∧ (q : ℝ) < x + ε := by
    by_cases h : q₁ = 0
    · exact ⟨q₂, fun h2 => hne (h.trans h2.symm), by linarith [hq₂.1], hq₂.2⟩
    · exact ⟨q₁, h, hq₁.1, by linarith [hq₁.2]⟩
  obtain ⟨q, hq0, hxq, hqx⟩ := hpick
  obtain ⟨t, ht, hηt⟩ := hq q hq0
  refine ⟨η t, ⟨t, ht, rfl⟩, ?_⟩
  rw [hηt, dist_eq_norm, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

/-- **GB6, final assertion**: if `α` is continuous on `I`, `I ⊆ closure (D ∩ I)`, and `α q ∈ K` for `q ∈ D ∩ I` with
`K` closed (e.g. the range of a proper continuous counterflow), then `α t ∈ K` for all `t ∈ I`. -/
theorem image_subset_of_dense {α : ℝ → ℂ} {I D : Set ℝ} {K : Set ℂ} (hα : ContinuousOn α I)
    (hD : I ⊆ closure (D ∩ I)) (hK : IsClosed K) (hDK : ∀ q ∈ D ∩ I, α q ∈ K) : α '' I ⊆ K := by
  rintro _ ⟨t, ht, rfl⟩
  have h := ((hα t ht).mono inter_subset_right).mem_closure_image (hD ht)
  exact closure_minimal (by rintro _ ⟨q, hq, rfl⟩; exact hDK q hq) hK h

end Supp8

end InteractingSLE
