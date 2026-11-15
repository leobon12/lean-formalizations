/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS5Proof

/-!
# SB2's relative hulls: the hull transport through a retained chart

Packet PROVE-T14-SB2FIN. Lemma SB2 (supplement pp. 630–633, `source/spec/p625-671.md` L113–L150), "Geometry of the
erasure": "the erased initial portion lies in `K_A`, and the later tail lies in `closure D_A` with the unique lift
selected by its free one-sided collar". In a chart `c` of `D_A = ℍ ∖ fill A` whose inverse has the continuous boundary
extension `g` to `closure ℍ` (S2), let a closed physical set `X` meet `D_A` only in `g`-images of a closed relative
set `Y ⊆ closure ℍ`. Then the filling of `X` meets `D_A` inside the chart preimage of the filling of `Y`
(`fwd_mem_fillH_of_mem_fillH`): a point of `D_A` whose chart image lies in the unbounded component of `ℍ ∖ Y` is
joined to `∞` off `X` by the inverse image of that component (the chart inverse grows at least linearly, so the
image is unbounded). Conversely a point of `D_A` whose chart image is on the frontier of the filling of `Y` lies on
`X` when `g(Y ∩ ℍ) ⊆ X` (`mem_of_fwd_mem_frontier_fillH`: the frontier of a filling inside `ℍ` lies on the set).

These are the fields `hullIn` and `hullFr` of `SB.Union.IsRelConfigJ` (PROVE-T14-SB2UNION) once `X` is the physical
prefix and `Y` the relative prefix (`SB2FinChain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H isOpen_H)

namespace InteractingSLE.Theorem14.SB.FinRel

/-! ### The frontier of a filling -/

/-- **The frontier of a filling inside `ℍ` lies on the closure of the set**: a point of `ℍ ∖ closure Y` lies in an
open component of `ℍ ∖ closure Y`, which is either bounded (inside the filling) or unbounded (outside it). -/
theorem frontier_fillH_inter_H_subset (Y : Set ℂ) : frontier (fillH Y) ∩ H ⊆ closure Y := by
  rintro y ⟨hfr, hyH⟩
  by_contra hyY
  have hU : IsOpen (H \ closure Y) := isOpen_H.sdiff isClosed_closure
  have hyU : y ∈ H \ closure Y := ⟨hyH, hyY⟩
  have hCo : IsOpen (connectedComponentIn (H \ closure Y) y) := hU.connectedComponentIn
  have hyC : y ∈ connectedComponentIn (H \ closure Y) y := mem_connectedComponentIn hyU
  have hCsub : ∀ w ∈ connectedComponentIn (H \ closure Y) y,
      connectedComponentIn (H \ closure Y) w = connectedComponentIn (H \ closure Y) y :=
    fun w hw => (connectedComponentIn_eq hw).symm
  by_cases hb : IsBounded (connectedComponentIn (H \ closure Y) y)
  · have hsub : connectedComponentIn (H \ closure Y) y ⊆ fillH Y := fun w hw =>
      ⟨(connectedComponentIn_subset _ _ hw).1, Or.inr ((hCsub w hw).symm ▸ hb)⟩
    exact hfr.2 (mem_interior_iff_mem_nhds.2 (mem_of_superset (hCo.mem_nhds hyC) hsub))
  · obtain ⟨w, hwC, hwF⟩ := mem_closure_iff_nhds.1 hfr.1 _ (hCo.mem_nhds hyC)
    rcases hwF.2 with hwY | hwb
    · exact (connectedComponentIn_subset _ _ hwC).2 hwY
    · exact hb ((hCsub w hwC) ▸ hwb)

/-- A point of `ℍ` outside the filling lies in the unbounded component of `ℍ ∖ closure Y`. -/
theorem not_isBounded_of_notMem_fillH {Y : Set ℂ} {y : ℂ} (hyH : y ∈ H) (hy : y ∉ fillH Y) :
    y ∉ closure Y ∧ ¬ IsBounded (connectedComponentIn (H \ closure Y) y) := by
  refine ⟨fun h => hy ⟨hyH, Or.inl h⟩, fun h => hy ⟨hyH, Or.inr h⟩⟩

/-- A point of `ℍ` off `closure X` whose component in `ℍ ∖ closure X` contains an unbounded preconnected set is not
in the filling of `X`. -/
theorem notMem_fillH_of_isPreconnected {X S : Set ℂ} {z : ℂ} (hzS : z ∈ S) (hS : IsPreconnected S)
    (hSX : S ⊆ H \ closure X) (hSb : ¬ IsBounded S) : z ∉ fillH X := by
  rintro ⟨-, hzX | hb⟩
  · exact (hSX hzS).2 hzX
  · exact hSb (hb.subset (hS.subset_connectedComponentIn hzS hSX))

/-! ### The transport through a retained chart -/

section Transport

variable {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}

/-- The chart inverse is injective on `ℍ`. -/
theorem inv_injOn (hD : IsDomainChart (H \ fillH A) c) : InjOn c.2.1 H := hD.1.injOn

/-- **A point of the physical set inside `D_A` is not a chart inverse of a relative point off `Y`**: if `X ∩ D_A` is
covered by `g '' Y`, then `c.inv w ∉ X` for `w ∈ ℍ ∖ Y` (a relative point of `Y` in `ℍ` maps injectively, a real
one lands off `D_A`). -/
theorem inv_notMem_of_notMem (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {X Y : Set ℂ} (hYH : ∀ y ∈ Y, 0 ≤ y.im) (hXY : X ∩ (H \ fillH A) ⊆ g '' Y) {w : ℂ}
    (hw : w ∈ H) (hwY : w ∉ Y) : c.2.1 w ∉ X := by
  intro hX
  obtain ⟨y, hyY, hgy⟩ := hXY ⟨hX, hD.inv_mem hw⟩
  rcases (hYH y hyY).lt_or_eq with hyH | hy0
  · have hyH' : y ∈ H := hyH
    rw [hgi hyH'] at hgy
    exact hwY ((inv_injOn hD hyH' hw hgy) ▸ hyY)
  · have hy : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [← hy0])
    have := SB.g_ofReal_notMem hD hgc hgi y.re
    rw [← hy, hgy] at this
    exact this (hD.inv_mem hw)

/-- **The hull transport into the relative filling** (`hullIn`): let `X` be closed, `Y` closed in `closure ℍ`, and
`X ∩ D_A ⊆ g '' Y`. If `c.inv` grows at least linearly (`‖w‖ ≤ C₁ ‖c.inv w‖ + C₂` on `ℍ`), then every point of
`fill X` in `D_A` has its chart image in `fill Y`. -/
theorem fwd_mem_fillH_of_mem_fillH (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂)
    {X Y : Set ℂ}
    (hXc : IsClosed X) (hYc : IsClosed Y) (hYH : ∀ y ∈ Y, 0 ≤ y.im) (hXY : X ∩ (H \ fillH A) ⊆ g '' Y) {z : ℂ}
    (hz : z ∈ fillH X) (hzA : z ∉ fillH A) : c.1 z ∈ fillH Y := by
  have hzD : z ∈ H \ fillH A := ⟨hz.1, hzA⟩
  have hyH : c.1 z ∈ H := hD.fwd_mem hzD
  by_contra hy
  obtain ⟨hyY, hyb⟩ := not_isBounded_of_notMem_fillH hyH hy
  rw [hYc.closure_eq] at hyY hyb
  set C := connectedComponentIn (H \ Y) (c.1 z)
  have hCH : C ⊆ H := fun w hw => (connectedComponentIn_subset _ _ hw).1
  have hCY : ∀ w ∈ C, w ∉ Y := fun w hw => (connectedComponentIn_subset _ _ hw).2
  refine notMem_fillH_of_isPreconnected (S := c.2.1 '' C) ⟨c.1 z, mem_connectedComponentIn ⟨hyH, hyY⟩,
    hD.inv_fwd hzD⟩ ((isPreconnected_connectedComponentIn).image _ (hD.1.1.continuousOn.mono hCH)) ?_ ?_ hz
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨(hD.inv_mem (hCH hw)).1, ?_⟩
    rw [hXc.closure_eq]
    exact inv_notMem_of_notMem hD hgc hgi hYH hXY (hCH hw) (hCY w hw)
  · intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    refine hyb (isBounded_iff_forall_norm_le.2 ⟨C₁ * R + C₂, fun w hw => ?_⟩)
    have h1 := hgrow w (hCH hw)
    have h2 := hR _ (mem_image_of_mem _ hw)
    nlinarith

/-- **A frontier point of the relative filling comes from `X`** (`hullFr`): if `g` maps `Y ∩ ℍ` into `X`, a point of
`D_A` whose chart image is on the frontier of `fill Y` lies in `X`. -/
theorem mem_of_fwd_mem_frontier_fillH (hD : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H) {X Y : Set ℂ}
    (hYc : IsClosed Y) (hYX : ∀ y ∈ Y, y ∈ H → g y ∈ X) {z : ℂ} (hz : z ∈ H \ fillH A)
    (hfr : c.1 z ∈ frontier (fillH Y)) : z ∈ X := by
  have hyH : c.1 z ∈ H := hD.fwd_mem hz
  have hyY : c.1 z ∈ Y := hYc.closure_eq ▸ frontier_fillH_inter_H_subset Y ⟨hfr, hyH⟩
  have := hYX _ hyY hyH
  rwa [hgi hyH, hD.inv_fwd hz] at this

/-- The frontier form with the filling: such a point lies in `fill X`. -/
theorem mem_fillH_of_fwd_mem_frontier_fillH (hD : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H)
    {X Y : Set ℂ} (hYc : IsClosed Y) (hYX : ∀ y ∈ Y, y ∈ H → g y ∈ X) {z : ℂ} (hz : z ∈ H \ fillH A)
    (hfr : c.1 z ∈ frontier (fillH Y)) : z ∈ fillH X :=
  ⟨hz.1, Or.inl (subset_closure (mem_of_fwd_mem_frontier_fillH hD hgi hYc hYX hz hfr))⟩

end Transport

end InteractingSLE.Theorem14.SB.FinRel
