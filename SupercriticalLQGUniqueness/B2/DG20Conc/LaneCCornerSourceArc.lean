import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerSafeLastHit
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerStrictEndpoints

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_upper_left_source_separator_arc
    (D : ContMetric) {ρ γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b))
    {c v : ℂ} {r : ℝ} (hr : 0 < r)
    (hρann : ∀ x ∈ Icc a b,
      r < dist (ρ x) c ∧ dist (ρ x) c < 2 * r)
    (hv : 2 * r ≤ dist v c)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hcre0 : 0 ≤ c.re) (hcreNear : c.re ≤ r)
    (hcim1 : c.im ≤ 1) (hTopNear : 1 - c.im ≤ r)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hγright : (γ 1).re = 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hvisit : dist (γ m) c ≤ r) :
    ∃ (δ : ℝ → ℂ) (t₁ : ℝ),
      t₁ ∈ Icc m (1 : ℝ) ∧
      ContinuousOn δ (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        r < dist (δ t) c ∧ dist (δ t) c < 2 * r ∧
          δ t ∈ (rectAB 1 1).toSet) ∧
      δ 0 ∈ (rectAB 1 1).side₁ ∧
      γ t₁ = δ 1 ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∧
      D.len δ 0 1 ≤ D.len ρ a b := by
  obtain ⟨α, hα, hαcar, hαleft, hαtop, hαbelow, _hαright, hcost⟩ :=
    laneC_upper_left_paid_square_crosscut_strict D hab hρ hr hρann hv hsep
      hcre0 hcreNear hcim1 hTopNear hbelow hright
  have hαsq : ∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet :=
    fun t ht => (hαcar t ht).2.2
  have hαann : ∀ t ∈ Icc (0 : ℝ) 1, r < dist (α t) c :=
    fun t ht => (hαcar t ht).1
  obtain ⟨t₁, ht₁, u, hu, hhit, hsafe⟩ :=
    laneC_corner_crosscut_last_safe_hit hα hγ hαsq hγsq hαann
      (mem_rectAB_side₁.mp hαleft).1 hαtop hαbelow hγright
      hm hvisit hcre0 hcreNear (by linarith) hcim1
  let δ := SupercriticalLQGUniqueness.B2.Strong.seg α 0 u
  have hδ : ContinuousOn δ (Icc (0 : ℝ) 1) :=
    SupercriticalLQGUniqueness.B2.Strong.continuousOn_seg hα (by simp) hu
  refine ⟨δ, t₁, ht₁, hδ, ?_, ?_, ?_, hsafe, ?_⟩
  · intro t ht
    exact hαcar _ (SupercriticalLQGUniqueness.B2.Strong.seg_param_mem
      (by simp) hu ht)
  · simpa [δ, SupercriticalLQGUniqueness.B2.Strong.seg] using hαleft
  · simpa [δ, SupercriticalLQGUniqueness.B2.Strong.seg] using hhit
  · exact (SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ α) (by simp) hu).trans hcost

end SupercriticalLQGUniqueness.B2.DG20Conc
