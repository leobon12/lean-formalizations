/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCollar
import InteractingSLE.Spec.Supplement.BHMeanReal

/-!
# SB2(1)'s `finK`: reduction to the pinch points of the retained chart

Packet PROVE-T14-SB2FIN. The field `finK` of `SB.Union.IsRelConfigJ` / `IsRelConfigJC` (finitely many real points off
the relative hull image land on `closure (K_t ∖ A)`) for SB2(1)'s configuration follows from a property of the
retained chart alone: **finitely many pinch points** — real points `v` at which the boundary extension `g` of the chart
inverse is not injective on `ℝ` (`g v' = g v` for some real `v' ≠ v`; the prime-end multiplicities of `∂D_A`).

At a real `x` off the relative hull image, the relative landing `v` is real and off the closed relative hull, and the
joint landing is `p = g(v)`. If `p ∈ closure (K_t ∖ A)` and `v` is not a pinch point, then the chart images of points of
`K_t ∖ A` near `p` (they lie in the relative hull, `hullIn`, and are bounded by the chart's linear growth) cluster only
at the `g`-preimages of `p` in the closed relative hull, which is `{v}` — contradiction. The relative landing determines
`x` (`BHMean.eq_fwdMap_of_extendFrom_notMem_closure`), so the exceptional set injects into the pinch set.

* **`finK_of_finite_pinch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.FinRel

/-- **`finK` from finitely many pinch points of the retained chart.** -/
theorem finK_of_finite_pinch {A₀ : Set ℂ} {L : ℝ} {c : Chart} {g : ℂ → ℂ} (hAb : IsBounded A₀)
    (hAc : IsPreconnected (A₀ ∪ {z : ℂ | z.im ≤ 0})) (hc : IsLeftEntryChart A₀ L c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {w Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {t u : ℝ}
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 < u)
    (hKin : ∀ z ∈ fwdHull w t, z ∉ fillH A₀ → c.1 z ∈ fwdHull Wr u)
    (hpinch : {v : ℝ | ∃ v' : ℝ, v' ≠ v ∧ g v' = g v}.Finite) :
    {x : ℝ | extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) ∧
      extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr u) (x : ℂ) ∈ closure (fwdHull w t \ fillH A₀)}.Finite := by
  have hD := hc.1
  obtain ⟨C₁, C₂, hC₁, hbd⟩ := hc.exists_norm_fwd_le hAb hAc
  set S := {x : ℝ | extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) ∧
      extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr u) (x : ℂ) ∈ closure (fwdHull w t \ fillH A₀)} with hSdef
  set φ : ℝ → ℝ := fun x => (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re with hφ
  have hreal : ∀ x ∈ S, extendFrom H (fwdMapInv Wr u) (x : ℂ) = ((φ x : ℝ) : ℂ) := fun x hx => by
    have him := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu.le hx.1
    exact Complex.ext (by simp [hφ]) (by simp [him])
  have hre0 : ∀ x ∈ S, φ x ≠ 0 := fun x hx h0 => by
    apply hx.1
    rw [hreal x hx, h0, Complex.ofReal_zero]
    exact ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hu
  have hinj : InjOn φ S := fun x hx x' hx' he => by
    rw [Supp8.BHMean.eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu.le hx.1 (hre0 x hx),
      Supp8.BHMean.eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu.le hx'.1 (hre0 x' hx')]
    simp only [hφ] at he
    rw [he]
  have hclH : closure (fwdHull Wr u) ⊆ {z : ℂ | 0 ≤ z.im} :=
    closure_minimal (fun z hz => le_of_lt (show 0 < z.im from (isHPHull_fwdHull hWr hu.le).1 hz))
      (isClosed_le continuous_const Complex.continuous_im)
  refine Set.Finite.of_finite_image (hpinch.subset ?_) hinj
  rintro _ ⟨x, hx, rfl⟩
  by_contra hnp
  have hnp' : ∀ v' : ℝ, g v' = g (φ x) → v' = φ x := fun v' hv' => by
    by_contra hne
    exact hnp ⟨v', hne, hv'⟩
  set p := extendFrom H (Supp8.BHMean.jointInv c.2.1 Wr u) (x : ℂ) with hpdef
  have hpg : p = g (φ x) := by
    rw [hpdef, extendFrom_jointInv_eq hgc hgi hWr hWr0 hηr hu.le (show (0 : ℝ) ≤ ((x : ℂ)).im by simp),
      hreal x hx]
  have hne : (𝓝[fwdHull w t \ fillH A₀] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx.2
  set l := 𝓝[fwdHull w t \ fillH A₀] p
  set M : ℝ := C₁ * (‖p‖ + 1) + C₂
  have hevD : ∀ᶠ z in l, z ∈ H \ fillH A₀ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨hz.1.1, hz.2⟩
  have hev : ∀ᶠ z in l, c.1 z ∈ closedBall (0 : ℂ) M ∩ closure (fwdHull Wr u) := by
    filter_upwards [self_mem_nhdsWithin, hevD, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p one_pos)] with z hz hzD hzb
    refine ⟨mem_closedBall_zero_iff.2 ((hbd z hzD).trans ?_), subset_closure (hKin z hz.1 hz.2)⟩
    have : ‖z‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z p
      rw [mem_ball, dist_eq_norm] at hzb
      linarith
    nlinarith
  obtain ⟨ξ, -, hξ⟩ := ((isCompact_closedBall (0 : ℂ) M).inter_right isClosed_closure).exists_mapClusterPt
    (tendsto_principal.2 hev)
  have hgF : Tendsto (g ∘ c.1) l (𝓝 p) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [hevD] with z hzD
    simp only [Function.comp, id]
    rw [hgi (hD.fwd_mem hzD), hD.inv_fwd hzD]
  obtain ⟨hξp, hξK⟩ := SB.mem_fiber_of_mapClusterPt isClosed_closure (hgc.mono hclH)
    (hev.mono fun z hz => hz.2) hgF hξ
  have hξp' : g ξ = p := hξp
  have hξim : ξ.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) (hclH hξK)
    have h1 := SB.g_ofReal_notMem hD hgc hgi (φ x)
    rw [← hpg, ← hξp', hgi hpos] at h1
    exact h1 (hD.inv_mem hpos)
  have hξr : ξ = ((ξ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hξim])
  have hre : ξ.re = φ x := hnp' ξ.re (by rw [← hξr, hξp', hpg])
  apply hx.1
  rw [hreal x hx, ← hre, ← hξr]
  exact hξK

end InteractingSLE.Theorem14.SB.FinRel
