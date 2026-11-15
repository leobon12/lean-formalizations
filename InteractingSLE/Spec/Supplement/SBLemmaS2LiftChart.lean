/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftCluster
import InteractingSLE.Foundations.Loewner.HullExists
import InteractingSLE.Foundations.PrimeEnd.Basic

/-!
# Lemma S2's lift: the left entry chart

Packet PROVE-T14-SB5. Facts about a left entry chart `c` of `D_A = ℍ \ fill(A)` at `L` (`IsLeftEntryChart`) used by
the one-sided lift of Lemma S2 (supplement p. 579: "It is proper because `g_A` fixes infinity"):

* **`IsLeftEntryChart.exists_norm_fwd_le`** — `‖c.fwd w‖ ≤ C₁ ‖w‖ + C₂` on `D_A`. The chart is a real Möbius map of the
  mapping-out function `g_K` of the hull `K = fill(A)` (`HChart.exists_realMobius`); since `c.fwd` and `g_K` both
  send `∞` to `∞`, the Möbius map is affine, and `g_K` is within bounded distance of the identity
  (`IsMapOut.exists_norm_sub_le`). In particular `c.inv` sends `∞` to `∞` (the chart is bounded near every finite
  boundary point), the first input of the lift that `PROVE-T14-SB4` reported missing.
* the boundary values `e` of the chart on the untouched interval `(−∞, L)`: `g (e x) = x` for every continuous
  extension `g` of `c.inv` to `closure ℍ` (`eq_of_boundaryValue`), and `e` is continuous (`tendsto_boundaryValue`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### Growth of a chart fixing `∞` -/

section ChartBound

/-- A real Möbius map with nonzero lower-left entry tends to `a / c` at `∞`. -/
theorem tendsto_realMobius_cobounded {a b c d : ℝ} (hc : c ≠ 0) :
    Tendsto (realMobius a b c d) (cobounded ℂ) (𝓝 ((a : ℂ) / c)) := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
  have h1 : Tendsto (fun z : ℂ => (c : ℂ) * z + d) (cobounded ℂ) (cobounded ℂ) :=
    tendsto_affine_cobounded hc'
  have h2 : Tendsto (fun z : ℂ => ((c : ℂ) * z + d)⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded.comp h1
  have h3 : Tendsto (fun z : ℂ => (a : ℂ) / c + ((b : ℂ) - a * d / c) * ((c : ℂ) * z + d)⁻¹) (cobounded ℂ)
      (𝓝 ((a : ℂ) / c)) := by
    simpa using (tendsto_const_nhds (x := (a : ℂ) / c)).add (h2.const_mul ((b : ℂ) - a * d / c))
  refine h3.congr' ?_
  filter_upwards [h1 (show ({0}ᶜ : Set ℂ) ∈ cobounded ℂ from isBounded_singleton)] with z hz
  have hz' : (c : ℂ) * z + d ≠ 0 := hz
  rw [realMobius]
  field_simp
  ring

variable {A : Set ℂ} {L : ℝ} {c : Chart}

/-- The domain of a compact hull contains points of arbitrarily large norm. -/
theorem neBot_cobounded_inf_H_diff {K : Set ℂ} (hK : IsHPHull K) : (cobounded ℂ ⊓ 𝓟 (H \ K)).NeBot := by
  obtain ⟨R, hR, hKR⟩ := hK.exists_subset_ball
  have ht : Tendsto (fun t : ℝ => (t : ℂ) * I) atTop (cobounded ℂ ⊓ 𝓟 (H \ K)) := by
    refine tendsto_inf.2 ⟨tendsto_norm_atTop_iff_cobounded.1 ?_, tendsto_principal.2 ?_⟩
    · have : (fun t : ℝ => ‖(t : ℂ) * I‖) = fun t => |t| := by funext t; simp
      rw [this]
      exact tendsto_abs_atTop_atTop
    · filter_upwards [eventually_gt_atTop R] with t ht
      have hpos : (0 : ℝ) < t := hR.trans ht
      refine ⟨show (0 : ℝ) < ((t : ℂ) * I).im by simp [hpos], fun hK' => ?_⟩
      have := hKR hK'
      rw [mem_ball, dist_zero_right] at this
      have h2 : ‖(t : ℂ) * I‖ = t := by simp [abs_of_pos hpos]
      linarith
  exact ht.neBot

/-- **A left entry chart grows at most linearly** on `D_A` (it is affine in the mapping-out function of `fill(A)`). -/
theorem IsLeftEntryChart.exists_norm_fwd_le (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hc : IsLeftEntryChart A L c) : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w ∈ H \ fillH A, ‖c.1 w‖ ≤ C₁ * ‖w‖ + C₂ := by
  have hK : IsHPHull (fillH A) := isHPHull_fillH_of_isPreconnected hAb hAc
  obtain ⟨gK, hgK⟩ := hK.exists_isMapOut
  obtain ⟨M₀, hM₀⟩ := hgK.exists_norm_sub_le hK
  have hD : IsOpen (H \ fillH A) := hK.2.2.1
  obtain ⟨a, b, c', d, hdet, hEq⟩ :=
    HChart.exists_realMobius (⟨gK, hgK.1⟩ : HChart (H \ fillH A)) hD hc.1.hChart
  have hc'0 : c' = 0 := by
    by_contra hc'
    have hne := neBot_cobounded_inf_H_diff hK
    have h1 : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (cobounded ℂ) := hc.2.2.1
    have h2 : Tendsto gK (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (cobounded ℂ) :=
      (hgK.tendsto_cobounded hK subset_rfl hgK.1.2.mapsTo).mono_right inf_le_left
    have h3 : Tendsto c.1 (cobounded ℂ ⊓ 𝓟 (H \ fillH A)) (𝓝 ((a : ℂ) / c')) := by
      refine ((tendsto_realMobius_cobounded (b := b) (d := d) hc').comp h2).congr' ?_
      filter_upwards [mem_inf_of_right (mem_principal_self (H \ fillH A))] with w hw
      exact (hEq hw).symm
    have h4 := (tendsto_norm_atTop_iff_cobounded.2 h1)
    have h5 := (continuous_norm.tendsto _).comp h3
    exact h4.not_tendsto (disjoint_nhds_atTop _).symm h5
  have had : 0 < a * d := by simpa [hc'0] using hdet
  have hd : d ≠ 0 := fun h => by simp [h] at had
  have hdpos : 0 < |d| := abs_pos.2 hd
  refine ⟨|a| / |d|, (|a| * M₀ + |b|) / |d|, by positivity, fun w hw => ?_⟩
  have hfw : c.1 w = ((a : ℂ) * gK w + b) / d := by
    have h := hEq hw
    change c.1 w = realMobius a b c' d (gK w) at h
    rw [h, realMobius, hc'0]
    simp
  have hg : ‖gK w‖ ≤ ‖w‖ + M₀ := by
    have := hM₀ w hw
    have h2 := norm_sub_norm_le (gK w) w
    linarith
  have hnum : ‖(a : ℂ) * gK w + b‖ ≤ |a| * (‖w‖ + M₀) + |b| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    gcongr
  rw [hfw, norm_div, norm_real, Real.norm_eq_abs,
    show |a| / |d| * ‖w‖ + (|a| * M₀ + |b|) / |d| = (|a| * (‖w‖ + M₀) + |b|) / |d| by field_simp; ring]
  exact div_le_div_of_nonneg_right hnum hdpos.le

end ChartBound

/-! ### Boundary values on the untouched interval -/

section BoundaryValue

variable {A : Set ℂ} {c : Chart} {e : ℝ → ℝ} {g : ℂ → ℂ}

theorem mem_closure_H_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : z ∈ closure H := by
  rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  exact hz

/-- Near a free real point, `ℍ` lies in the chart domain. -/
theorem eventually_mem_of_isFreeAt {x : ℝ} (hx : HalfPlaneSep.IsFreeAt A x) :
    ∀ᶠ w in 𝓝[H] (x : ℂ), w ∈ H \ fillH A := by
  obtain ⟨ε, hε, hs⟩ := hx
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hε)] with w hw
  exact hs ⟨hw.2, hw.1⟩

/-- **The extension of `c.inv` inverts the boundary values**: `g (e x) = x`. -/
theorem eq_of_boundaryValue (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {x : ℝ} (hx : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ)))
    (hxf : HalfPlaneSep.IsFreeAt A x) : g (e x) = x := by
  have hne : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_H_of_im_nonneg (by simp))
  have hev := eventually_mem_of_isFreeAt hxf
  have h1 : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝[{z | 0 ≤ z.im}] (e x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hx, ?_⟩
    filter_upwards [hev] with w hw
    exact le_of_lt (hD.fwd_mem hw)
  have h2 : Tendsto (g ∘ c.1) (𝓝[H] (x : ℂ)) (𝓝 (g (e x))) :=
    (hgc _ (show (0 : ℝ) ≤ ((e x : ℝ) : ℂ).im by simp)).tendsto.comp h1
  have h3 : Tendsto (g ∘ c.1) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [hev] with w hw
    rw [Function.comp_apply, hgi (hD.fwd_mem hw), hD.inv_fwd hw]
    rfl
  exact tendsto_nhds_unique h2 h3

/-- **The boundary values are continuous** on the untouched interval. -/
theorem tendsto_boundaryValue {L : ℝ} (he : ∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) {x : ℝ}
    (hx : x < L) : Tendsto (fun x' : ℝ => (e x' : ℂ)) (𝓝 x) (𝓝 (e x : ℂ)) := by
  refine Metric.tendsto_nhds.2 fun r hr => ?_
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1
    ((Metric.tendsto_nhds.1 (he x hx)) (r / 2) (by positivity))
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < δ / 2), eventually_lt_nhds hx] with x' hx' hx'L
  have hne : (𝓝[H] (x' : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_H_of_im_nonneg (by simp))
  have hlim := he x' hx'L
  have hle : dist ((e x' : ℝ) : ℂ) (e x : ℂ) ≤ r / 2 := by
    refine le_of_tendsto ((continuous_id.dist continuous_const).tendsto _ |>.comp hlim) ?_
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x' : ℂ) (by positivity : 0 < δ / 2))] with w hw
    have hwx : dist w (x : ℂ) < δ := by
      have h1 : dist w (x' : ℂ) < δ / 2 := hw.2
      have h2 : dist (x' : ℂ) (x : ℂ) < δ / 2 := by
        rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, ← Real.dist_eq]; exact hx'
      linarith [dist_triangle w (x' : ℂ) (x : ℂ)]
    exact le_of_lt (hδs ⟨hwx, hw.1⟩)
  exact lt_of_le_of_lt hle (by linarith)

end BoundaryValue

end SB

end Theorem14

end InteractingSLE
