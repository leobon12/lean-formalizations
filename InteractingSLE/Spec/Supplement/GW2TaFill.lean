/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.SafeFamily
import InteractingSLE.Spec.Supplement.GW2SzLoc

/-!
# The filling of a set, read through countably many avoidance tests

Packet PROVE-GW2-RELDET, ruling R113 (the named filled-hull locality `GW2SzLoc.SchedHullLocalStatement`). A Loewner
hull `K` fills its curve `S`: `ℍ \ K` is the unbounded component of `ℍ \ S` (`IsFilling K S`). A point of `ℍ` lies
outside `K` iff it can be joined to a far half-plane `{Im > n}` inside `ℍ \ S`. The joining set can be taken from a
COUNTABLE family of open test regions, the components at `z` of a finite union of rational balls together with
`{Im > n}` (`fillTube`). This turns every avoidance event of `K` into countably many avoidance events of `S`, for
open sets containing the tested one, which is what the marked locality of `K` needs (`GW2TaFillLoc`).

* `fillTube F n z`, `IsFillTube` (the balls lie in `ℍ`, `z` is in the union, the half-plane is in the component);
  `isOpen_fillTube`, `fillTube_subset_H`;
* **`not_mem_iff_exists_fillTube`**: for `z ∈ ℍ`, `z ∉ K` iff some test region of `z` avoids `S`;
* **`disjoint_fill_iff`**: for an open `U ⊆ ℍ`, `K` avoids `U` iff `S` avoids `U` and every point of a fixed countable
  dense sequence lying in `U` has a test region `T` with `S` avoiding `U ∪ T`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Coupling

/-- **A test region of `z`**: the component at `z` of a finite union of rational balls and the half-plane
`{Im > n}`. -/
def fillTube (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ) (z : ℂ) : Set ℂ :=
  connectedComponentIn (ballsU F ∪ {w : ℂ | (n : ℝ) < w.im}) z

/-- The test region is admissible: its balls lie in `ℍ`, it contains `z` and the whole half-plane `{Im > n}`. -/
def IsFillTube (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ) (z : ℂ) : Prop :=
  ballsU F ⊆ H ∧ z ∈ ballsU F ∪ {w : ℂ | (n : ℝ) < w.im} ∧ {w : ℂ | (n : ℝ) < w.im} ⊆ fillTube F n z

theorem isOpen_halfIm (r : ℝ) : IsOpen {w : ℂ | r < w.im} := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_halfIm (r : ℝ) : IsPreconnected {w : ℂ | r < w.im} :=
  (convex_halfSpace_im_gt r).isPreconnected

theorem isOpen_fillTube (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ) (z : ℂ) : IsOpen (fillTube F n z) :=
  ((isOpen_ballsU F).union (isOpen_halfIm _)).connectedComponentIn

theorem halfIm_subset_H (n : ℕ) : {w : ℂ | (n : ℝ) < w.im} ⊆ H := fun w hw =>
  show (0 : ℝ) < w.im from lt_of_le_of_lt n.cast_nonneg hw

theorem fillTube_subset_H {F : Finset (ℚ × ℚ × ℚ)} (hF : ballsU F ⊆ H) (n : ℕ) (z : ℂ) : fillTube F n z ⊆ H :=
  (connectedComponentIn_subset _ _).trans (union_subset hF (halfIm_subset_H n))

section Fill

variable {S K : Set ℂ} (hfill : IsFilling K S) (hSo : IsOpen (H \ S)) {R : ℝ} (hR : {w : ℂ | R < w.im} ⊆ H \ K)

include hfill in
/-- The complement of the filling is a component of `ℍ \ S`, open when `ℍ \ S` is. -/
theorem compl_fill_eq : ∃ z₀ ∈ H \ S, connectedComponentIn (H \ S) z₀ = H \ K := by
  obtain ⟨z₀, hz₀, he⟩ := hfill.1
  refine ⟨z₀, ?_, he⟩
  rw [← he] at hz₀
  exact connectedComponentIn_subset _ _ hz₀

include hfill in
theorem compl_fill_subset : H \ K ⊆ H \ S := by
  obtain ⟨z₀, -, he⟩ := compl_fill_eq hfill
  rw [← he]
  exact connectedComponentIn_subset _ _

include hfill hR in
/-- **Sufficiency**: a test region of `z` avoiding `S` puts `z` outside the filling. -/
theorem not_mem_of_fillTube {F : Finset (ℚ × ℚ × ℚ)} {n : ℕ} {z : ℂ} (hT : IsFillTube F n z)
    (hST : Disjoint S (fillTube F n z)) : z ∉ K := by
  obtain ⟨z₀, -, he⟩ := compl_fill_eq hfill
  set T := fillTube F n z with hTdef
  have hTH : T ⊆ H \ S := fun y hy => ⟨fillTube_subset_H hT.1 n z hy, fun hyS => hST.le_bot ⟨hyS, hy⟩⟩
  have hzT : z ∈ T := mem_connectedComponentIn hT.2.1
  have hTc : T ⊆ connectedComponentIn (H \ S) z :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hzT hTH
  -- a far point of the half-plane lies in `T` and outside `K`
  set w : ℂ := ⟨0, max R n + 1⟩ with hw
  have hwn : (n : ℝ) < w.im := by simp only [hw]; linarith [le_max_right R n]
  have hwR : R < w.im := by simp only [hw]; linarith [le_max_left R n]
  have hwT : w ∈ T := hT.2.2 hwn
  have hwK : w ∈ connectedComponentIn (H \ S) z₀ := by rw [he]; exact hR hwR
  have hzS : z ∈ H \ S := hTH hzT
  have e1 : connectedComponentIn (H \ S) z = connectedComponentIn (H \ S) w := connectedComponentIn_eq (hTc hwT)
  have e2 : connectedComponentIn (H \ S) z₀ = connectedComponentIn (H \ S) w := connectedComponentIn_eq hwK
  have hz : z ∈ H \ K := by
    rw [← he, e2, ← e1]
    exact mem_connectedComponentIn hzS
  exact hz.2

include hfill hSo hR in
/-- **Necessity**: a point of `ℍ` outside the filling has a test region avoiding `S`. -/
theorem exists_fillTube_of_not_mem {z : ℂ} (hzH : z ∈ H) (hzK : z ∉ K) :
    ∃ (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ), IsFillTube F n z ∧ Disjoint S (fillTube F n z) := by
  obtain ⟨z₀, hz₀, he⟩ := compl_fill_eq hfill
  set O := connectedComponentIn (H \ S) z₀ with hOdef
  have hOo : IsOpen O := hSo.connectedComponentIn
  have hOc : IsConnected O := isConnected_connectedComponentIn_iff.2 hz₀
  have hzO : z ∈ O := by rw [he]; exact ⟨hzH, hzK⟩
  -- a far point of the half-plane, joined to `z` inside `O`
  obtain ⟨n, hn⟩ := exists_nat_ge R
  set w : ℂ := ⟨0, (n : ℝ) + 1⟩ with hw
  have hwO : w ∈ O := by
    rw [he]
    exact hR (show R < w.im by simp only [hw]; linarith)
  have hhalf : {v : ℂ | (n : ℝ) < v.im} ⊆ O := fun v hv => by
    rw [he]
    exact hR (show R < v.im from lt_of_le_of_lt hn hv)
  obtain ⟨γ, hγ⟩ := ((hOo.isConnected_iff_isPathConnected).1 hOc).joinedIn z hzO w hwO
  obtain ⟨F, hcov, hFO⟩ := exists_rationalBalls (isCompact_range γ.continuous) hOo
    (by rintro _ ⟨t, rfl⟩; exact hγ t)
  have hFU : ballsU F ⊆ O := (ballsU_subset_ballsK F).trans hFO
  have hOH : O ⊆ H \ S := connectedComponentIn_subset _ _
  have hFH : ballsU F ⊆ H := fun y hy => (hOH (hFU hy)).1
  set B := ballsU F ∪ {v : ℂ | (n : ℝ) < v.im} with hB
  have hzB : z ∈ B := Or.inl (hcov ⟨0, γ.source⟩)
  have hrange : range γ ⊆ fillTube F n z :=
    (isPreconnected_range γ.continuous).subset_connectedComponentIn ⟨0, γ.source⟩
      (hcov.trans subset_union_left)
  have hwT : w ∈ fillTube F n z := hrange ⟨1, γ.target⟩
  have hhalfT : {v : ℂ | (n : ℝ) < v.im} ⊆ fillTube F n z := by
    rw [fillTube, connectedComponentIn_eq hwT]
    exact (isPreconnected_halfIm _).subset_connectedComponentIn
      (show (n : ℝ) < w.im by simp only [hw]; linarith) subset_union_right
  refine ⟨F, n, ⟨hFH, hzB, hhalfT⟩, ?_⟩
  rw [disjoint_comm, disjoint_left]
  intro y hy hyS
  have hyB : y ∈ B := connectedComponentIn_subset _ _ hy
  rcases hyB with hyF | hyh
  · exact (hOH (hFU hyF)).2 hyS
  · exact (hOH (hhalf hyh)).2 hyS

include hfill hSo hR in
theorem not_mem_iff_exists_fillTube {z : ℂ} (hzH : z ∈ H) :
    z ∉ K ↔ ∃ (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ), IsFillTube F n z ∧ Disjoint S (fillTube F n z) :=
  ⟨exists_fillTube_of_not_mem hfill hSo hR hzH, fun ⟨_, _, hT, hST⟩ => not_mem_of_fillTube hfill hR hT hST⟩

include hfill hSo hR in
/-- **Avoidance of the filling through countably many avoidance tests of `S`.** -/
theorem disjoint_fill_iff {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    Disjoint K U ↔ Disjoint S U ∧ ∀ i : ℕ, TopologicalSpace.denseSeq ℂ i ∈ U →
      ∃ (F : Finset (ℚ × ℚ × ℚ)) (n : ℕ), IsFillTube F n (TopologicalSpace.denseSeq ℂ i) ∧
        Disjoint S (U ∪ fillTube F n (TopologicalSpace.denseSeq ℂ i)) := by
  obtain ⟨z₀, hz₀, he⟩ := compl_fill_eq hfill
  have hSK : ∀ y ∈ H, y ∈ S → y ∈ K := fun y hyH hyS => by
    by_contra hyK
    exact (compl_fill_subset hfill ⟨hyH, hyK⟩).2 hyS
  constructor
  · intro hKU
    have hSU : Disjoint S U := by
      rw [disjoint_left]
      exact fun y hyS hyU => disjoint_left.1 hKU (hSK y (hUH hyU) hyS) hyU
    refine ⟨hSU, fun i hi => ?_⟩
    obtain ⟨F, n, hT, hST⟩ := exists_fillTube_of_not_mem hfill hSo hR (hUH hi)
      (fun hiK => disjoint_left.1 hKU hiK hi)
    exact ⟨F, n, hT, disjoint_union_right.2 ⟨hSU, hST⟩⟩
  · rintro ⟨hSU, htest⟩
    rw [disjoint_left]
    intro x hxK hxU
    have hxS : x ∈ H \ S := ⟨hUH hxU, fun hxS => disjoint_left.1 hSU hxS hxU⟩
    set C := connectedComponentIn (H \ S) x with hC
    -- the component of `x` misses the complement of the filling, so it lies in `K`
    have hCK : C ⊆ K := by
      intro y hy
      by_contra hyK
      have hyO : y ∈ connectedComponentIn (H \ S) z₀ := by
        rw [he]
        exact ⟨(connectedComponentIn_subset _ _ hy).1, hyK⟩
      have e1 : C = connectedComponentIn (H \ S) y := connectedComponentIn_eq hy
      have e2 : connectedComponentIn (H \ S) z₀ = connectedComponentIn (H \ S) y := connectedComponentIn_eq hyO
      have hxO : x ∈ connectedComponentIn (H \ S) z₀ := by
        rw [e2, ← e1]
        exact mem_connectedComponentIn hxS
      rw [he] at hxO
      exact hxO.2 hxK
    obtain ⟨i, hi⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open
      (hSo.connectedComponentIn.inter hU) ⟨x, mem_connectedComponentIn hxS, hxU⟩
    obtain ⟨F, n, hT, hST⟩ := htest i hi.2
    exact not_mem_of_fillTube hfill hR hT (disjoint_union_right.1 hST).2 (hCK hi.1)

end Fill

end InteractingSLE.Theorem14.GW2Rd
