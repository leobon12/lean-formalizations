/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcMain
import InteractingSLE.Spec.Sec7.Aux119Reflect

/-!
# The common collar of two simple paths along a shared arc, and the (RS13.3) assembly

Packet PROVE-STRIPSYS11. Specification §7.4, the proof of Aux. lemma 130 ((RS13.3), `source/spec/p385-432.md`
L440–L456, p. 411) and the proof of Aux. lemma 119 (L14–L33, pp. 385–386):

> A smaller proper subarc has a common right-side collar which meets no other portions of either path […] In each own
> chart the right-side height is `λ − θχ`, with its inherited derivative-logarithm lift. The transition between the two
> charts reflects analytically across the flattened common arc and has positive real derivative there. Its argument in
> the inherited branches is consequently `2πn` for an integer `n`, constant on the smaller arc. Expressing both germs in
> one chart therefore forces `θ₁ − π/2 = 2πn`.  (RS13.3)

> The transition `g_p ∘ g_i^{-1}` is the map of the additional filled half-plane hull, with hydrodynamic normalization.
> The chosen side collar survives that filling. Aux. lemma 57 consequently gives argument exactly zero for its
> derivative on the flattened collar, not only zero modulo `2π`.  (Aux. lemma 119)

PROVE-LEMMA76B proved this chart geometry for a *reverse* common arc (`ReverseArc.reverseArcChart_of_mem_H`): an
approach to the arc from the joint unbounded domain, along which both own charts tend to real points and the two
derivative-argument lifts agree, by comparing each own chart with the joint hull map (Aux. lemma 57). The comparison
step uses only three facts about the approach point `z₀`: it lies on both stopped prefixes, near `z₀` the two prefixes
coincide (`A ∩ B(z₀, ρ) = B ∩ B(z₀, ρ)`: "a common collar which meets no other portions of either path"), and the
approach comes from the joint unbounded domain `ℍ ∖ fill(A ∪ B)`. This file isolates that step for an arbitrary shared
arc (in particular one traversed in the same direction, as in (RS13.3)):

* `exists_real_tendsto_of_mem` : along an ultrafilter converging to a point of the stopped prefix from outside its
  filled hull, the own chart tends to a real point (no orientation input);
* **`commonArcChart_of_approach`** (the common collar, both charts): at a point `z₀` of both prefixes near which
  the prefixes coincide, along any ultrafilter approaching `z₀` from `ℍ ∖ fill(A ∪ B)`, both own charts tend to real
  points and the two derivative-argument lifts differ by a quantity tending to `0` (the integer of (RS13.3) is `0`);
* **`false_of_commonArc_sideHeights`** ((RS13.3), assembled): if moreover the two single-path means agree in boundary
  value along the approach and have the side heights `λ − θ₁χ`, `λ − (π/2)χ` in their own charts, with
  `−π/2 < θ₁ < π/2`, the configuration is impossible.

The remaining geometric input of (RS13.3) is the exposure of the common subarc to the joint unbounded domain (see the
handoff `PROVE-STRIPSYS11.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal Real

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep Restart ReverseArc

namespace StripCollar

/-! ### The own chart along an approach to its prefix -/

section Real

variable {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

/-- **The own chart tends to a real point** along any ultrafilter converging to a point `z₀` of the stopped prefix from
outside its filled hull. -/
theorem exists_real_tendsto_of_mem (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hi : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) {z₀ : ℂ} (hz₀ : z₀ ∈ α '' Icc 0 q)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q)] z₀) :
    ∃ y : ℝ, Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ)) := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
    hi ha hb (sub_left_injective hab)
  have hch := isChart hg hWc hW0 hinj' hq hq0
  set U' : Ultrafilter ℂ := U.map fun z => z - x with hU'def
  have htr : Tendsto (fun z : ℂ => z - x) (𝓝[H \ fillH (α '' Icc 0 q)] z₀)
      (𝓝[H \ fillH ((fun t => α t - x) '' Icc 0 q)] (z₀ - x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_sub_right (x : ℂ)).tendsto z₀).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun z hz => (mem_H_diff_fillH_phys_iff x q z).1 hz
  have hU' : (U' : Filter ℂ) ≤ 𝓝[H \ fillH ((fun t => α t - x) '' Icc 0 q)] (z₀ - x) := by
    rw [hU'def, Ultrafilter.coe_map]
    exact (Filter.map_mono hU).trans htr
  obtain ⟨y, hyH, hyt, hΦy⟩ := hch.cluster U' (z₀ - x) hU'
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have hmem := hch.inv_mem (show y ∈ H from hpos)
    rw [hΦy] at hmem
    obtain ⟨t, ht, hte⟩ := hz₀
    refine hmem.2 ⟨hmem.1, Or.inl (subset_closure ⟨t, ht, ?_⟩)⟩
    show α t - x = z₀ - x
    rw [hte]
  refine ⟨y.re, ?_⟩
  have hyre : (y.re : ℂ) = y := Complex.ext (by simp) (by simp [hyim])
  rw [hyre]
  have := hyt
  rw [hU'def, Ultrafilter.coe_map, tendsto_map'_iff] at this
  exact this

end Real

/-! ### The common collar: both own charts against the joint hull map -/

section Collar

/-- **One own chart against the joint hull map** (the comparison step of PROVE-LEMMA76B's reverse-arc chart, for any
arc): if the stopped prefix `γ([0, q])` lies in the compact set `A ∪ B`, coincides with it near `z₀`, and its own chart
tends to a real point `y` along an ultrafilter approaching `z₀` from `ℍ ∖ fill(A ∪ B)`, then the canonical lift of the
joint hull map and the own lift have the same imaginary part in the limit (Aux. lemma 57: the joint hull adds to
`fill γ([0, q])` a hull whose image stays away from `y`). -/
theorem tendsto_im_sub_joint {A B : Set ℂ} (hABc : IsCompact (A ∪ B)) (hKΓ : IsHPHull (fillH (A ∪ B)))
    {gK LK : ℂ → ℂ} (hgK : IsMapOut (fillH (A ∪ B)) gK) (hLK : IsCanonicalDerivLog (fillH (A ∪ B)) gK LK)
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (A ∪ B)] z₀)
    {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0} {y : ℝ}
    (hg : IsGeneratingTrace W ζ (fun t => γ t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0)
    (hi : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ}) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (hsub : γ '' Icc 0 q ⊆ A ∪ B)
    (hloc : (A ∪ B) ∩ ball z₀ ρ ⊆ γ '' Icc 0 q)
    (hfy : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ))) :
    Tendsto (fun z => (LK z).im - (QuantumZipper.logDerivFwd (fun r : ℝ => W r.toNNReal) q (z - x)).im) U
      (𝓝 0) := by
  have hF : (U : Filter ℂ) ≤ 𝓟 (H \ fillH (A ∪ B)) := hU.trans inf_le_right
  obtain ⟨κ, hK, hgm, hL⟩ := exists_physChart hg hWc hW0 hq
  obtain ⟨Φ, hΦc, hΦH, -, hinv, hmaps⟩ := exists_physInv hg hWc hW0 hi hq hq0
  obtain ⟨ε, hε, hno⟩ := exists_ball_notMem_of_approach hABc.isClosed hsub hmaps hΦc hΦH hinv hρ hloc U hU hfy
  have hd : Disjoint (ball (((y + κ : ℝ)) : ℂ) ε)
      ((fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) '' (fillH (A ∪ B) \
        fillH (γ '' Icc 0 q))) := by
    rw [Set.disjoint_left]
    rintro w hwb ⟨z, ⟨hzK, hzA⟩, rfl⟩
    refine hno z ⟨hzK.1, hzA⟩ hzK ?_
    rw [mem_ball, dist_eq_norm] at hwb ⊢
    convert hwb using 2
    push_cast; ring
  have hq' : Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) U
      (𝓝[H] (((y + κ : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hfy.add_const (κ : ℂ)
      convert this using 2
      push_cast; ring
    · filter_upwards [hF (mem_principal_self _)] with z hz
      exact hgm.1.2.mapsTo ⟨hz.1, fun h => hz.2 (fillH_mono hsub h)⟩
  exact tendsto_im_sub_of_le hK hKΓ (fillH_mono hsub) hgm hgK hL hLK hF hε hd hq'

/-- **The common collar of two simple paths along a shared arc** ((RS13.3) and Aux. lemma 119, for any orientation of
the shared arc). Let `α`, `β` be simple generating traces from real seeds `x₁`, `x₂`, stopped at `q₁`, `q₂`, and let
`z₀` lie on `α([0, q₁])` with the two prefixes coinciding near `z₀` ("a common collar which meets no other portions
of either path"). Along any ultrafilter approaching `z₀` from the joint unbounded domain `ℍ ∖ fill(α([0, q₁]) ∪
β([0, q₂]))`, both own charts tend to real points and the derivative-argument lifts of the two own charts differ by a
quantity tending to `0`. -/
theorem commonArcChart_of_approach (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (q₁ q₂ : ℝ≥0) (hq₁ : (q₁ : ℝ≥0∞) < ζ₁) (hq₂ : (q₂ : ℝ≥0∞) < ζ₂) (hq₁0 : 0 < q₁) (hq₂0 : 0 < q₂)
    {z₀ : ℂ} (hz₀ : z₀ ∈ α '' Icc 0 q₁) {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : α '' Icc 0 q₁ ∩ ball z₀ ρ = β '' Icc 0 q₂ ∩ ball z₀ ρ)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] z₀) :
    ∃ y₁ y₂ : ℝ,
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)) U (𝓝 (y₁ : ℂ)) ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)) U (𝓝 (y₂ : ℂ)) ∧
      Tendsto (fun z => (QuantumZipper.logDerivFwd (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)).im -
        (QuantumZipper.logDerivFwd (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)).im) U (𝓝 0) := by
  have hp₁ : IsPathGood α ζ₁ x₁ := ⟨hi₁, W₁, hW₁c, hW₁0, hg₁⟩
  have hp₂ : IsPathGood β ζ₂ x₂ := ⟨hi₂, W₂, hW₂c, hW₂0, hg₂⟩
  set A := α '' Icc 0 q₁ with hAdef
  set B := β '' Icc 0 q₂ with hBdef
  have hc₁ := IsPathGood.continuousOn_Icc hp₁ hq₁.le
  have hc₂ := IsPathGood.continuousOn_Icc hp₂ hq₂.le
  have hABc : IsCompact (A ∪ B) :=
    (IsPathGood.isCompact_image hp₁ hq₁.le).union (IsPathGood.isCompact_image hp₂ hq₂.le)
  have hKΓ : IsHPHull (fillH (A ∪ B)) := by
    refine isHPHull_fillH_of_isPreconnected hABc.isBounded ?_
    have hApc : IsPreconnected A := isPreconnected_Icc.image _ hc₁
    have hBpc : IsPreconnected B := isPreconnected_Icc.image _ hc₂
    have hlow : IsPreconnected {z : ℂ | z.im ≤ 0} := isPreconnected_lowerHalf
    have hx₁ : (x₁ : ℂ) ∈ A := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₁⟩
    have hx₂ : (x₂ : ℂ) ∈ B := ⟨0, ⟨le_rfl, zero_le⟩, IsPathGood.zero hp₂⟩
    have h1 := hApc.union (x₁ : ℂ) hx₁ (show (x₁ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp) hlow
    have h2 := h1.union (x₂ : ℂ) (Or.inr (show (x₂ : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)) hx₂ hBpc
    rwa [union_right_comm] at h2
  set gK := ConformalImage.mapOut (fillH (A ∪ B)) with hgKdef
  have hgK : IsMapOut (fillH (A ∪ B)) gK := ConformalImage.isMapOut_mapOut hKΓ
  obtain ⟨LK, hLK⟩ := exists_isCanonicalDerivLog hKΓ hgK
  have hz₀B : z₀ ∈ B := by
    have : z₀ ∈ A ∩ ball z₀ ρ := ⟨hz₀, mem_ball_self hρ⟩
    rw [hagree] at this
    exact this.1
  have hUA : (U : Filter ℂ) ≤ 𝓝[H \ fillH A] z₀ :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  have hUB : (U : Filter ℂ) ≤ 𝓝[H \ fillH B] z₀ :=
    hU.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_right)))
  obtain ⟨y₁, hf₁⟩ := exists_real_tendsto_of_mem hg₁ hW₁c hW₁0 hi₁ hq₁ hq₁0 hz₀ U hUA
  obtain ⟨y₂, hf₂⟩ := exists_real_tendsto_of_mem hg₂ hW₂c hW₂0 hi₂ hq₂ hq₂0 hz₀B U hUB
  have hloc₁ : (A ∪ B) ∩ ball z₀ ρ ⊆ A := by
    rintro z ⟨hz | hz, hzb⟩
    · exact hz
    · have : z ∈ B ∩ ball z₀ ρ := ⟨hz, hzb⟩
      rw [← hagree] at this
      exact this.1
  have hloc₂ : (A ∪ B) ∩ ball z₀ ρ ⊆ B := by
    rintro z ⟨hz | hz, hzb⟩
    · have : z ∈ A ∩ ball z₀ ρ := ⟨hz, hzb⟩
      rw [hagree] at this
      exact this.1
    · exact hz
  have hl₁ := tendsto_im_sub_joint hABc hKΓ hgK hLK hρ U hU hg₁ hW₁c hW₁0 hi₁ hq₁ hq₁0 subset_union_left hloc₁ hf₁
  have hl₂ := tendsto_im_sub_joint hABc hKΓ hgK hLK hρ U hU hg₂ hW₂c hW₂0 hi₂ hq₂ hq₂0 subset_union_right hloc₂ hf₂
  refine ⟨y₁, y₂, hf₁, hf₂, ?_⟩
  have := hl₂.sub hl₁
  rw [sub_zero] at this
  refine this.congr fun z => ?_
  ring

end Collar

/-! ### (RS13.3), assembled -/

section RS133

/-- **(RS13.3), assembled** (proof of Aux. lemma 130, p. 411). Let `α` and `β` be simple generating traces stopped at
`q₁`, `q₂`, sharing an arc near `z₀` ("a common right-side collar which meets no other portions of either path"), and
let `U` approach `z₀` from the joint unbounded domain. Suppose that along `U` the two single-path means `v₁`, `v₂` agree
in boundary value ("nested local-set boundary comparison identifies the union mean with each single-path mean on this
collar") and have the side heights `λ − θ₁χ` and `λ − (π/2)χ` in their own charts, written with the own derivative
lifts (`vᵢ + u₀ + χ Im Lᵢ → λ − θᵢχ`). If `−π/2 < θ₁ < π/2` and `χ ≠ 0`, this is impossible: the common collar makes
the two lifts agree in the limit (`commonArcChart_of_approach`), so `θ₁ = π/2`. -/
theorem false_of_commonArc_sideHeights (α β : ℝ≥0 → ℂ) (x₁ x₂ : ℝ) (W₁ W₂ : ℝ≥0 → ℝ) (ζ₁ ζ₂ : ℝ≥0∞)
    (hg₁ : IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁)) (hW₁c : ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁})
    (hW₁0 : W₁ 0 = 0) (hg₂ : IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂))
    (hW₂c : ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂}) (hW₂0 : W₂ 0 = 0)
    (hi₁ : InjOn α {t | (t : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn β {t | (t : ℝ≥0∞) ≤ ζ₂})
    (q₁ q₂ : ℝ≥0) (hq₁ : (q₁ : ℝ≥0∞) < ζ₁) (hq₂ : (q₂ : ℝ≥0∞) < ζ₂) (hq₁0 : 0 < q₁) (hq₂0 : 0 < q₂)
    {z₀ : ℂ} (hz₀ : z₀ ∈ α '' Icc 0 q₁) {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : α '' Icc 0 q₁ ∩ ball z₀ ρ = β '' Icc 0 q₂ ∩ ball z₀ ρ)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[H \ fillH (α '' Icc 0 q₁ ∪ β '' Icc 0 q₂)] z₀)
    {v₁ v₂ u₀ : ℂ → ℝ} {χ lam θ₁ : ℝ} (hχ : χ ≠ 0) (hθ₁ : -(π / 2) < θ₁) (hθ₁' : θ₁ < π / 2)
    (hv : Tendsto (fun z => v₁ z - v₂ z) U (𝓝 0))
    (h₁ : Tendsto (fun z => v₁ z + u₀ z +
      χ * (QuantumZipper.logDerivFwd (fun r : ℝ => W₁ r.toNNReal) q₁ (z - x₁)).im) U (𝓝 (lam - θ₁ * χ)))
    (h₂ : Tendsto (fun z => v₂ z + u₀ z +
      χ * (QuantumZipper.logDerivFwd (fun r : ℝ => W₂ r.toNNReal) q₂ (z - x₂)).im) U (𝓝 (lam - π / 2 * χ))) :
    False := by
  obtain ⟨-, -, -, -, hL⟩ := commonArcChart_of_approach α β x₁ x₂ W₁ W₂ ζ₁ ζ₂ hg₁ hW₁c hW₁0 hg₂ hW₂c hW₂0 hi₁ hi₂
    q₁ q₂ hq₁ hq₂ hq₁0 hq₂0 hz₀ hρ hagree U hU
  refine Aux119.false_of_common_side_half_pi (F := (U : Filter ℂ)) (n := 0) hχ hθ₁ hθ₁' hv h₁ h₂ ?_
  simpa using hL

end RS133

end StripCollar

end Sec7

end InteractingSLE
