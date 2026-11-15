/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrChain

/-!
# The real two-outer R.6 window, with fixed interval and test points

PROVE-R6-TWO, Astra §5. The open geometric task is exactly
`SameTimeLeftData`, at the common original visit. From that input this
file proves the full later-time (b)–(d), retaining its interval and both
outer test coordinates for every sufficiently close real inner time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Tr

open PocketStopSide R6Fc R6Safe

theorem complement_inclusion_of_local {O I : Chart} {EO : ℂ → ℂ}
    (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar) {x e : ℝ} (he : 0 < e)
    (hloc : (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) e ⊆ I.dom) :
    ∀ p : ℂ, Tendsto O.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) →
      ∃ r > 0, (H \ (I.dom : Set ℂ)) ∩ ball p r ⊆ H \ (O.dom : Set ℂ) := by
  have := neBot_nhdsWithin_H_real x
  intro p hp
  have hpE : p = EO (x : ℂ) := tendsto_nhds_unique hp (tendsto_of_extension hEO hEOc x)
  rw [hpE]
  exact ⟨e, he, fun z hz => ⟨hz.1.1, fun hzO => hz.1.2 (hloc ⟨hzO, hz.2⟩)⟩⟩

/-- All of R.6(b)–(d) on a right neighbourhood of real inner times.
`F.interval`, `F.shared`, and `F.exposed` are outside the time quantifier.
Only the inner real limits and inner force coordinates change. -/
theorem faceAt_left_near {V P : Set ℂ} {I : ℝ → Chart} {p : ℂ}
    (M : InnerChain V P I p) {O : Chart} {EO : ℂ → ℂ}
    (hO : O.IsConformal) (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    {ρL ρR σL σR vL vR : Fin 1 → ℝ} (wR : ℝ → Fin 1 → ℝ) (hρ : ρL 0 = σL 0)
    (F : SameTimeLeftData O (I M.time) EO P p (vL 0) (WangWu.chartAL M.driver M.time)) :
    ∃ θ > 0, ∀ q : ℝ, M.time < q → q < M.time + θ →
      FaceAt ρL ρR σL σR vL vR (fun _ => WangWu.chartAL M.driver q) (wR q)
        O (I q) F.interval F.shared F.exposed := by
  have hdom₀ := M.dom_eq M.time M.time_mem
  have hi₀ : V ∩ M.coord ⁻¹' (H \ QuantumZipper.fwdHull M.driver M.time) ⊆ O.dom := by
    rw [← hdom₀]; exact F.inclusion
  have hc₀ : ∀ x ∈ F.compact, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      O.1 '' (V ∩ M.coord ⁻¹' (H \ QuantumZipper.fwdHull M.driver M.time)) := by
    rw [← hdom₀]; exact F.collars
  obtain ⟨θr, hθr, hreflect⟩ := reflected_faces_near hO hEO hEOc M.coord_bij M.mem_boundary M.coord_cont
    M.inverse_eq M.driver_cont M.driver_zero M.time_pos.le M.tip_cont M.tip_eq hi₀ F.isCompact F.interval_subset
    F.isOpen F.avoids_tip F.landing_mem hc₀ M.horizon_pos M.dom_eq M.conformal M.inverse_cont
    (fun q hq => M.norm_bound hq)
  have hlocY : ∃ e > 0, (O.dom : Set ℂ) ∩ ball (EO (F.shared : ℂ)) e ⊆
      V ∩ M.coord ⁻¹' (H \ QuantumZipper.fwdHull M.driver M.time) := by
    rw [← hdom₀]; exact F.shared_ball
  have hlocX : ∃ e > 0, (O.dom : Set ℂ) ∩ ball (EO (F.exposed : ℂ)) e ⊆
      V ∩ M.coord ⁻¹' (H \ QuantumZipper.fwdHull M.driver M.time) := by
    rw [← hdom₀]; exact F.exposed_ball
  obtain ⟨θb, hθb, ey, hey, ex, hex, hballs⟩ := two_fixed_balls_persist M.coord_bij M.inverse_eq
    M.driver_cont M.driver_zero M.time_pos.le M.tip_cont M.tip_eq
    (F.avoids_tip _ (F.interval_subset F.shared_mem)) (F.avoids_tip _ (F.interval_subset F.exposed_mem)) hlocY hlocX
  let a := min ((WangWu.chartAL M.driver M.time - F.boundary F.shared) / 4)
    (min ((F.boundary F.exposed - WangWu.chartAL M.driver M.time) / 4) (-F.boundary F.exposed / 4))
  have ha : 0 < a := lt_min (by linarith [F.shared_image_lt])
    (lt_min (by linarith [F.lt_exposed_image]) (by linarith [F.exposed_image_neg]))
  have haY : a ≤ (WangWu.chartAL M.driver M.time - F.boundary F.shared) / 4 := min_le_left _ _
  have haX : a ≤ (F.boundary F.exposed - WangWu.chartAL M.driver M.time) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha0 : a ≤ -F.boundary F.exposed / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨θw, hθw, hw⟩ := Metric.continuousAt_iff.1 M.continuousAt_left_mark a ha
  obtain ⟨θf, hθf, hf⟩ := M.forward_change_small ha
  let θ := min (min θr θb) (min θw (min θf M.horizon))
  have hθ : 0 < θ := lt_min (lt_min hθr hθb) (lt_min hθw (lt_min hθf M.horizon_pos))
  have hθr' : θ ≤ θr := (min_le_left _ _).trans (min_le_left _ _)
  have hθb' : θ ≤ θb := (min_le_left _ _).trans (min_le_right _ _)
  have hθw' : θ ≤ θw := (min_le_right _ _).trans (min_le_left _ _)
  have hθf' : θ ≤ θf := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθh' : θ ≤ M.horizon := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨θ, hθ, fun q hlo hhi => ?_⟩
  have hq : q ∈ Ico M.time (M.time + M.horizon) := ⟨hlo.le, hhi.trans_le (add_le_add le_rfl hθh')⟩
  have hqr : q < M.time + θr := hhi.trans_le (add_le_add le_rfl hθr')
  have hqb : q < M.time + θb := hhi.trans_le (add_le_add le_rfl hθb')
  have hqf : q < M.time + θf := hhi.trans_le (add_le_add le_rfl hθf')
  have hqw : dist q M.time < θw := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.2 hlo)]
    have := hhi.trans_le (add_le_add le_rfl hθw')
    linarith
  have hwclose := abs_sub_lt_iff.1 (show |WangWu.chartAL M.driver q - WangWu.chartAL M.driver M.time| < a from hw hqw)
  obtain ⟨hi, hc, hb, G, -, -, -, hreal, hlim⟩ := hreflect q hlo.le hqr
  let gy := (G (F.shared : ℂ)).re
  let gx := (G (F.exposed : ℂ)).re
  have hGy : G (F.shared : ℂ) = (gy : ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hreal _ F.shared_mem)
  have hGx : G (F.exposed : ℂ) = (gx : ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hreal _ F.exposed_mem)
  have hly := hlim _ F.shared_mem
  have hlx := hlim _ F.exposed_mem
  rw [hGy] at hly
  rw [hGx] at hlx
  have hychange := abs_sub_le_iff.1 (reflected_limit_sub_le hO (M.conformal M.time M.time_mem) (M.conformal q hq)
    F.inclusion hi (M.dom_subset hq) (hc _ F.shared_mem) (F.boundary_limit _ F.shared_mem) hly (hf q hlo hqf hq))
  have hxchange := abs_sub_le_iff.1 (reflected_limit_sub_le hO (M.conformal M.time M.time_mem) (M.conformal q hq)
    F.inclusion hi (M.dom_subset hq) (hc _ F.exposed_mem) (F.boundary_limit _ F.exposed_mem) hlx (hf q hlo hqf hq))
  have hypos : gy < WangWu.chartAL M.driver q := by linarith
  have hxpos : WangWu.chartAL M.driver q < gx := by linarith
  have hxneg : gx < 0 := by linarith [F.exposed_image_neg]
  obtain ⟨hballY, hballX⟩ := hballs q hlo.le hqb
  have hlocY' : (O.dom : Set ℂ) ∩ ball (EO (F.shared : ℂ)) ey ⊆ (I q).dom := by
    rw [M.dom_eq q hq]
    exact hballY
  have hlocX' : (O.dom : Set ℂ) ∩ ball (EO (F.exposed : ℂ)) ex ⊆ (I q).dom := by
    rw [M.dom_eq q hq]
    exact hballX
  exact ⟨gy, gx, F.isOpen, F.isPreconnected, hc, hb, F.shared_mem, F.exposed_mem, hly, hlx,
    Or.inr ⟨F.shared_lt, hypos, hρ⟩, Or.inr ⟨F.lt_exposed, F.exposed_neg, hxpos, hxneg⟩,
    complement_inclusion_of_local hEO hEOc hey hlocY', complement_inclusion_of_local hEO hEOc hex hlocX'⟩

end InteractingSLE.Sec7.R6Tr
