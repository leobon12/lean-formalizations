/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Pocket births along a generating trace (Aux. lemma 48, (PK3))

Packet PROVE-SEC7-A (specification §7.1, proof of Aux. lemma 48, `source/spec/p193-240.md` L711–L731,
pp. 230–231). The deterministic geometry of a newly disconnected pocket. Let `η` be a continuous
generating trace of the Loewner chain driven by `w` (`IsGeneratingTrace w T η`), let `z ∈ ℍ` have finite
swallowing time `σ_z < T` with `z ∉ R_{σ_z} = η([0, σ_z])`, and let `P` be the component of
`Ω_{σ_z} = ℍ \ R_{σ_z}` containing `z`.

* "Every point of `P` has the same first swallowing time `σ_z`" (`swallowTime_eq_of_mem_pocket`): any two
  points of `P` are joined inside `P`, which avoids every earlier trace, so before `σ_z` one of them is in
  the active component iff the other is.
* (PK3): `P ⊂ D_t = ℍ \ K_t` for `t < σ_z` (`pocket_subset_activeDomain`), and `P ⊆ K_{σ_z}`
  (`pocket_subset_fwdHull`), so for a continuous driver `P` is a bounded component
  (`isBounded_pocket`): "at time `σ_z` the point `z` belongs to the filled hull but not to the trace, so
  its component is bounded".
* "Conversely, a bounded component of `Ω_t` has one well-defined birth time: choose any point in it and
  take its first swallowing time" — the same lemma, read for any two points of `P`.

The key step is `notMem_of_isFilling_of_isPreconnected`: if `K` is the filling of `A`, a preconnected
set avoiding `A` lies either inside `K` or inside `ℍ \ K`.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H swallowTime fwdHull)

namespace InteractingSLE

namespace Sec7

/-- If `K` is the filling of `A` (`ℍ \ K` is the unbounded component of `ℍ \ A`), a preconnected set
`P ⊆ ℍ \ A` lies on one side of `K`: if one point of `P` is outside `K`, so is every point. -/
theorem notMem_of_isFilling_of_isPreconnected {K A P : Set ℂ} (hK : IsFilling K A)
    (hP : IsPreconnected P) (hPA : P ⊆ H \ A) {z z' : ℂ} (hz : z ∈ P) (hz' : z' ∈ P)
    (hzK : z ∉ K) : z' ∉ K := by
  obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hK
  have hzH : z ∈ H \ K := ⟨(hPA hz).1, hzK⟩
  rw [← hcomp] at hzH
  have hsub : P ⊆ connectedComponentIn (H \ A) z := hP.subset_connectedComponentIn hz hPA
  have h' : z' ∈ connectedComponentIn (H \ A) z₀ := by
    rw [connectedComponentIn_eq hzH]
    exact hsub hz'
  rw [hcomp] at h'
  exact h'.2

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

theorem mem_fwdHull_coe_iff {z : ℂ} {t : ℝ≥0} :
    z ∈ fwdHull (fun s : ℝ => w s.toNNReal) (t : ℝ) ↔ z ∈ H ∧ swallowTime (fun s : ℝ => w s.toNNReal) z ≤ t := by
  simp only [QuantumZipper.fwdHull, mem_ofPred_eq, ENNReal.ofReal_coe_nnreal]

/-- A pocket `P` (the component of `ℍ \ η([0, σ])` containing `z`) avoids the trace up to every time
`t ≤ σ`. -/
theorem pocket_subset_compl_image {z : ℂ} {σ t : ℝ≥0} (htσ : t ≤ σ) :
    connectedComponentIn (H \ η '' Icc 0 σ) z ⊆ H \ η '' Icc 0 t := fun _ hx =>
  ⟨(connectedComponentIn_subset _ _ hx).1, fun hx' =>
    (connectedComponentIn_subset _ _ hx).2 (image_mono (Icc_subset_Icc_right htσ) hx')⟩

/-- Two points of a pocket born at `σ < T` are on the same side of every hull `K_t`, `t ≤ σ`. -/
theorem mem_fwdHull_iff_of_mem_pocket (hη : IsGeneratingTrace w T η) {z z' : ℂ} {σ t : ℝ≥0}
    (hσT : (σ : ℝ≥0∞) < T) (htσ : t ≤ σ)
    (hz' : z' ∈ connectedComponentIn (H \ η '' Icc 0 σ) z) :
    z ∈ fwdHull (fun s : ℝ => w s.toNNReal) (t : ℝ) ↔ z' ∈ fwdHull (fun s : ℝ => w s.toNNReal) (t : ℝ) := by
  have hz : z ∈ connectedComponentIn (H \ η '' Icc 0 σ) z :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨z', hz'⟩)
  have htT : (t : ℝ≥0∞) < T := lt_of_le_of_lt (by exact_mod_cast htσ) hσT
  have hK := hη.2.2 t htT
  have hP := isPreconnected_connectedComponentIn (F := H \ η '' Icc 0 σ) (x := z)
  have hPA := pocket_subset_compl_image (η := η) (z := z) htσ
  constructor
  · intro h
    by_contra h'
    exact notMem_of_isFilling_of_isPreconnected hK hP hPA hz' hz h' h
  · intro h
    by_contra h'
    exact notMem_of_isFilling_of_isPreconnected hK hP hPA hz hz' h' h

/-- **Every point of a newborn pocket has the same first swallowing time** (proof of Aux. lemma 48,
p. 231). If `z` is swallowed at `σ < T` without being on the trace, every point `z'` of its component
`P` of `ℍ \ η([0, σ])` is swallowed at `σ` too. -/
theorem swallowTime_eq_of_mem_pocket (hη : IsGeneratingTrace w T η) {z z' : ℂ} {σ : ℝ≥0}
    (hσT : (σ : ℝ≥0∞) < T) (hzσ : swallowTime (fun s : ℝ => w s.toNNReal) z = σ)
    (hz' : z' ∈ connectedComponentIn (H \ η '' Icc 0 σ) z) :
    swallowTime (fun s : ℝ => w s.toNNReal) z' = σ := by
  have hzP : z ∈ connectedComponentIn (H \ η '' Icc 0 σ) z :=
    mem_connectedComponentIn (connectedComponentIn_nonempty_iff.1 ⟨z', hz'⟩)
  have hzH : z ∈ H := (connectedComponentIn_subset _ _ hzP).1
  have hz'H : z' ∈ H := (connectedComponentIn_subset _ _ hz').1
  -- `z' ∈ K_σ`
  have hle : swallowTime (fun s : ℝ => w s.toNNReal) z' ≤ σ := by
    have hzK : z ∈ fwdHull (fun s : ℝ => w s.toNNReal) (σ : ℝ) := mem_fwdHull_coe_iff.2 ⟨hzH, hzσ.le⟩
    exact (mem_fwdHull_coe_iff.1 ((mem_fwdHull_iff_of_mem_pocket hη hσT le_rfl hz').1 hzK)).2
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)
  -- otherwise `z'` is swallowed at a time `t < σ` at which `z` is still active
  have hfin : swallowTime (fun s : ℝ => w s.toNNReal) z' ≠ ⊤ := ne_top_of_lt hlt
  set t : ℝ≥0 := (swallowTime (fun s : ℝ => w s.toNNReal) z').toNNReal with htdef
  have ht : (t : ℝ≥0∞) = swallowTime (fun s : ℝ => w s.toNNReal) z' := ENNReal.coe_toNNReal hfin
  have htσ : t < σ := by
    have : (t : ℝ≥0∞) < σ := ht ▸ hlt
    exact_mod_cast this
  have hz'K : z' ∈ fwdHull (fun s : ℝ => w s.toNNReal) (t : ℝ) := mem_fwdHull_coe_iff.2 ⟨hz'H, ht.ge⟩
  have hzK := (mem_fwdHull_iff_of_mem_pocket hη hσT htσ.le hz').2 hz'K
  have : (σ : ℝ≥0∞) ≤ t := hzσ ▸ (mem_fwdHull_coe_iff.1 hzK).2
  exact absurd (by exact_mod_cast this : σ ≤ t) (not_le.2 htσ)

/-- **(PK3)**: before its birth time `σ`, a pocket lies in the active domain `D_t = ℍ \ K_t`. -/
theorem pocket_subset_activeDomain (hη : IsGeneratingTrace w T η) {z : ℂ} {σ t : ℝ≥0}
    (hσT : (σ : ℝ≥0∞) < T) (hzσ : swallowTime (fun s : ℝ => w s.toNNReal) z = σ) (htσ : t < σ) :
    connectedComponentIn (H \ η '' Icc 0 σ) z ⊆ H \ fwdHull (fun s : ℝ => w s.toNNReal) (t : ℝ) := by
  intro z' hz'
  refine ⟨(connectedComponentIn_subset _ _ hz').1, fun hK => ?_⟩
  have := (mem_fwdHull_coe_iff.1 hK).2
  rw [swallowTime_eq_of_mem_pocket hη hσT hzσ hz'] at this
  exact absurd (by exact_mod_cast this : σ ≤ t) (not_le.2 htσ)

/-- At its birth time `σ`, a pocket lies in the filled hull `K_σ`. -/
theorem pocket_subset_fwdHull (hη : IsGeneratingTrace w T η) {z : ℂ} {σ : ℝ≥0}
    (hσT : (σ : ℝ≥0∞) < T) (hzσ : swallowTime (fun s : ℝ => w s.toNNReal) z = σ) :
    connectedComponentIn (H \ η '' Icc 0 σ) z ⊆ fwdHull (fun s : ℝ => w s.toNNReal) (σ : ℝ) :=
  fun _ hz' =>
  mem_fwdHull_coe_iff.2 ⟨(connectedComponentIn_subset _ _ hz').1,
    (swallowTime_eq_of_mem_pocket hη hσT hzσ hz').le⟩

/-- For a continuous driver, a newborn pocket is bounded ("its component is bounded", p. 231). -/
theorem isBounded_pocket (hη : IsGeneratingTrace w T η) (hw : Continuous w) {z : ℂ} {σ : ℝ≥0}
    (hσT : (σ : ℝ≥0∞) < T) (hzσ : swallowTime (fun s : ℝ => w s.toNNReal) z = σ) :
    Bornology.IsBounded (connectedComponentIn (H \ η '' Icc 0 σ) z) :=
  (isBounded_fwdHull (hw.comp continuous_real_toNNReal) (σ : ℝ)).subset
    (pocket_subset_fwdHull hη hσT hzσ)

end Sec7

end InteractingSLE
