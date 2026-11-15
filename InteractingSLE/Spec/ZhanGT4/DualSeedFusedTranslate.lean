/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessMap
import InteractingSLE.Spec.ZhanGT4.DualD6

/-!
# Seed-access transport with the actual change of source coordinates

Packet PROVE-ZHAN-GT4-A22. The second growing driver is `W₂ - W₂(0)`.
Its frozen first-chart accesses are `V₁(s) - W₂(0)`. This file carries
that translation explicitly, as required by `OwnData.zero`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
namespace OwnData

/-- First-chart clearance gives aliveness of the translated access in
the actual second image chain. The original sources may be distinct. -/
theorem exists_translated_access_sol_of_clear {W₁ W₂ b U : ℝ → ℝ} {s T v ρ : ℝ}
    (h₂ : ImgData (fun t => W₂ t - W₂ 0) (fwdHull (fun t => W₁ t - W₂ 0) s)
      (frzChart (fun t => W₁ t - W₂ 0) s) T b U)
    (hρ : 0 < ρ)
    (hc : Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ T)) :
    ∃ q, IsForwardSol U ((v - W₂ 0 : ℝ) : ℂ) (b T) q := by
  apply exists_transposed_sol_of_clear h₂ hρ
  refine Set.disjoint_left.2 fun z hz hzK => ?_
  have hm : z + (W₂ 0 : ℂ) ∈ (fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ T := by
    rw [← image_add_frzChart_sub_const W₁ W₂ (W₂ 0) s T]
    exact ⟨z, hzK, rfl⟩
  apply Set.disjoint_left.1 hc _ hm
  rw [mem_ball, dist_eq_norm] at hz ⊢
  convert hz using 2
  push_cast
  ring

/-- The reflected first map agrees with the translated second image
flow near any protected real seed access, not just the first driver. -/
theorem eqOn_ownExt_translated_access {W₁ W₂ a W' b U : ℝ → ℝ} {s t S T v ρ : ℝ}
    (h₁ : OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S a W') (hs : s ∈ Icc (0 : ℝ) S)
    (h₂ : OwnData (fun u => W₂ u - W₂ 0) (fwdHull (fun u => W₁ u - W₂ 0) s)
      (frzChart (fun u => W₁ u - W₂ 0) s) T b U) (ht : t ∈ Icc (0 : ℝ) T)
    (hρ : 0 < ρ)
    (hc : Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t))
    {q : ℝ → ℂ} (hq : IsForwardSol U ((v - W₂ 0 : ℝ) : ℂ) (b T) q) :
    ∃ ε > (0 : ℝ), EqOn (ownExt W₁ W' a (frzChart W₂ t) s)
      (fun z => fwdMap U (b t) (z - W₂ 0) + (U (b t) + W₂ 0)) (ball (v : ℂ) ε) := by
  have hbt := h₂.mapsTo_clock ht
  have hbT := h₂.mapsTo_clock ⟨h₂.pos.le, le_rfl⟩
  have hR0 := isMapOut_fwdMap_gen h₂.contW' hbt.1
  rw [h₂.img t ht] at hR0
  have hR := isMapOut_add_const hR0 (W₂ 0)
  rw [image_add_frzChart_sub_const] at hR
  have he : (fun z : ℂ => fwdMap U (b t) (z - W₂ 0) + U (b t) + W₂ 0) =
      fun z => fwdMap U (b t) (z - W₂ 0) + (U (b t) + W₂ 0) := by funext z; ring
  rw [he] at hR
  obtain ⟨δ, hδ, hlow, -⟩ := exists_aliveDisc_self hq hbT.1
  have hd := differentiableOn_fwdMap_aliveDisc h₂.contW' hq hδ hlow hbt
  have hRd : DifferentiableOn ℂ
      (fun z => fwdMap U (b t) (z - W₂ 0) + ((U (b t) : ℂ) + (W₂ 0 : ℂ)))
      (ball (v : ℂ) (aliveRad (b T) δ)) := by
    refine (hd.comp (differentiableOn_id.sub_const _) fun z hz => ?_).add_const _
    rw [mem_ball, dist_eq_norm] at hz ⊢
    convert hz using 2
    simp only [id_eq]
    push_cast
    ring
  exact h₁.eqOn_ownExt_at_clear_of_isMapOut hs hρ hc hR (aliveRad_pos hδ) hRd

/-- Values and derivatives of an integrated first seed are the actual
second image-flow access factors, with the hydrodynamic translation. -/
theorem seed_access_value_deriv_translated {W₁ W₂ b U : ℝ → ℝ} {as Ws : ℝ → ℝ → ℝ}
    {S s T v ρ : ℝ}
    (h₁ : ∀ t ∈ Icc (0 : ℝ) T, OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S (as t) (Ws t))
    (hs : s ∈ Icc (0 : ℝ) S)
    (h₂ : OwnData (fun t => W₂ t - W₂ 0) (fwdHull (fun t => W₁ t - W₂ 0) s)
      (frzChart (fun t => W₁ t - W₂ 0) s) T b U) (hρ : 0 < ρ)
    (hc : ∀ t ∈ Icc (0 : ℝ) T,
      Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W₁ s z + W₁ s) '' fwdHull W₂ t)) :
    ∃ q, IsForwardSol U ((v - W₂ 0 : ℝ) : ℂ) (b T) q ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s v).re = frzImg U b (v - W₂ 0) t + W₂ 0 ∧
        (deriv (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s) v).re = frzImgD U b (v - W₂ 0) t := by
  obtain ⟨q, hq⟩ := exists_translated_access_sol_of_clear h₂.toImgData hρ (hc T ⟨h₂.pos.le, le_rfl⟩)
  refine ⟨q, hq, fun t ht => ?_⟩
  obtain ⟨ε, hε, he⟩ := (h₁ t ht).eqOn_ownExt_translated_access hs h₂ ht hρ (hc t ht) hq
  have hval := congrArg Complex.re (he (mem_ball_self hε))
  have hder := congrArg Complex.re (iterate_deriv_eq_of_eqOn_ball hε he 1)
  constructor
  · simpa only [frzImg, sub_re, add_re, ofReal_re, ofReal_sub, add_assoc] using hval
  · have hf : (fun z : ℂ => fwdMap U (b t) (z - W₂ 0) + ((U (b t) : ℂ) + (W₂ 0 : ℂ))) =
        fun z => fwdMap U (b t) (z + ((-W₂ 0 : ℝ) : ℂ)) + ((U (b t) : ℂ) + (W₂ 0 : ℂ)) := by
      simp only [ofReal_neg, sub_eq_add_neg]
    rw [hf, iterate_deriv_comp_add_const] at hder
    simpa only [Nat.zero_add, Function.iterate_one, frzImgD, ofReal_neg, sub_eq_add_neg, ofReal_add] using hder

end OwnData
end InteractingSLE.ZhanGT4
