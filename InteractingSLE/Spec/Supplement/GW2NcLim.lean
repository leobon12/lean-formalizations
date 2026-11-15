/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeLim

/-!
# The relative chart along a safe path converging to a sphere point other than the tip

Packet PROVE-GW2-NEARIMG2, decision D69 (RELDET's `CanonContactStatement`). The filter form of
`GW2Ni.tendsto_relBdry_of_transient`. Let `P` be a path of safe points (off the closed retained hull) along a filter
`l`, continuous on arbitrarily small preconnected sets of `l`, whose sphere image `−1/P` tends to a point `q`. If the
boundary extension `F̄_s` of the retained inverse map does not send `0` to `q` (`F̄_s(0)` is the retained tip), then
`relBdry U s (P ·)` converges along `l` to a finite nonzero limit.

Proof: as for `tendsto_relBdry_of_transient`. `G = −1/relBdry(P ·)` is `f_s` at the sphere point `−1/P`, bounded by
`‖1/P‖ + C`, with `F̄_s ∘ G = −1/P → q`; Yuan's cluster-set lemma gives a limit `ξ` of `G` with `F̄_s(ξ) = q`, and
`ξ ≠ 0` since `F̄_s(0) ≠ q`.

* **`tendsto_relBdry_of_tendsto_inv`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Ni

open Supp8.GB6 Supp8.GB6.CoordB

variable {U : ℝ → ℝ} {s : ℝ}

/-- **The relative chart along a safe path converges** when the path's sphere image tends to a point that the
boundary extension `F̄_s` of the inverse map does not reach from `0`: the limit is finite and nonzero. -/
theorem tendsto_relBdry_of_tendsto_inv (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s)
    (hB : HasBdryLimits (fwdMapInv U s))
    (hR : ∀ x : ℂ, x.im = 0 → extendFrom H (fwdMapInv U s) x ∉ extendFrom H (fwdMapInv U s) '' H)
    {ι : Type*} [TopologicalSpace ι] {l : Filter ι} [l.NeBot] {P : ι → ℂ}
    (hconn : ∀ U' ∈ l, ∃ S ∈ l, S ⊆ U' ∧ IsPreconnected S ∧ ContinuousOn P S)
    (hP : ∀ᶠ t in l, P t ∈ relSafe U s ∧ P t ≠ 0) {q : ℂ} (hq : Tendsto (fun t => -(P t)⁻¹) l (𝓝 q))
    (htip : extendFrom H (fwdMapInv U s) 0 ≠ q) :
    ∃ ξ : ℂ, ξ ≠ 0 ∧ Tendsto (fun t => relBdry U s (P t)) l (𝓝 ξ) := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hs
  set F := extendFrom H (fwdMapInv U s) with hF
  have hext : ∀ v ∈ H, F v = fwdMapInv U s v := fun v hv => extendFrom_fwdMapInv_eq hU hU0 hs hv
  have hd : DifferentiableOn ℂ F H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hs).congr fun v hv => hext v hv
  have hinj : InjOn F H := fun a ha b hb hab => by
    rw [hext a ha, hext b hb] at hab
    have := congrArg (fwdMap U s) hab
    rwa [QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs ha, QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hs hb] at this
  set G : ι → ℂ := fun t => -(relBdry U s (P t))⁻¹ with hG
  have hspec : ∀ t, P t ∈ relSafe U s → P t ≠ 0 → relBdry U s (P t) ≠ 0 ∧ G t ∈ Hbar ∧
      ‖G t‖ ≤ ‖(P t)⁻¹‖ + C ∧ F (G t) = -(P t)⁻¹ := fun t h1 h2 => relBdry_spec hU hU0 hs hB hC h1 h2
  have hconnG : ∀ U' ∈ l, ∃ S ∈ l, S ⊆ U' ∧ IsPreconnected S ∧ ContinuousOn G S := by
    intro U' hU'
    obtain ⟨S, hSl, hSU, hSc, hPS⟩ := hconn (U' ∩ {t | P t ∈ relSafe U s ∧ P t ≠ 0}) (inter_mem hU' hP)
    refine ⟨S, hSl, fun t ht => (hSU ht).1, hSc, ?_⟩
    have hB' : ContinuousOn (fun t => relBdry U s (P t)) S :=
      (continuousOn_relBdry hU hU0 hs).comp hPS fun t ht => (hSU ht).2.1
    exact (hB'.inv₀ fun t ht => (hspec t (hSU ht).2.1 (hSU ht).2.2).1).neg
  have hGH : ∀ᶠ t in l, G t ∈ Hbar := hP.mono fun t ht => (hspec t ht.1 ht.2).2.1
  have hnorm : ∀ᶠ t in l, ‖(P t)⁻¹‖ ≤ ‖q‖ + 1 := by
    have h := (hq.norm).eventually (gt_mem_nhds (lt_add_one ‖q‖))
    filter_upwards [h] with t ht
    rw [norm_neg] at ht
    exact ht.le
  have hGR : ∀ᶠ t in l, ‖G t‖ ≤ ‖q‖ + 1 + C := by
    filter_upwards [hP, hnorm] with t ht hn
    exact (hspec t ht.1 ht.2).2.2.1.trans (add_le_add hn le_rfl)
  have hFG : Tendsto (fun t => F (G t)) l (𝓝 q) := by
    refine hq.congr' ?_
    filter_upwards [hP] with t ht
    exact (hspec t ht.1 ht.2).2.2.2.symm
  obtain ⟨ξ, -, hFξ, hGξ⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter hd hB.continuousOn hinj hR
    hconnG hGH hGR hFG
  have hξ0 : ξ ≠ 0 := fun h => htip (by rw [h] at hFξ; exact hFξ)
  refine ⟨-ξ⁻¹, neg_ne_zero.2 (inv_ne_zero hξ0), ((hGξ.inv₀ hξ0).neg).congr' ?_⟩
  filter_upwards [hP] with t _
  simp only [hG, inv_neg, inv_inv, neg_neg]

end InteractingSLE.Theorem14.GW2Ni
