import HigherDimLQGContinuity.Labels.Mesh

/-!
# Fixed dyadic mesh scale

A dyadic mesh can be made small enough for the access cost and the buffered
annulus. This is the scale-selection part of Part B's fixed site data.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- A positive dyadic mesh meets both fixed smallness requirements. -/
theorem exists_siteMesh_dyadic {d : ℕ} (Hup s ε₀ : ℝ)
    (hs : 0 < s) (hε : 0 < ε₀) :
    ∃ k : ℕ, let δ : ℝ := (1 / 2) ^ k
      0 < δ ∧ Real.sqrt d * δ ≤ 1 / 40 ∧
        Hup * (10 * Real.sqrt d * δ) ^ s ≤ ε₀ := by
  have hp : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscale : Tendsto (fun k : ℕ =>
      (10 * Real.sqrt d) * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul (10 * Real.sqrt d)
  have hrpow : Tendsto (fun k : ℕ =>
      ((10 * Real.sqrt d) * (1 / 2 : ℝ) ^ k) ^ s) atTop (𝓝 0) := by
    have hcont := Real.continuousAt_rpow_const 0 s (Or.inr hs.le)
    simpa only [Real.zero_rpow hs.ne', Function.comp_def] using hcont.tendsto.comp hscale
  have hcost : Tendsto (fun k : ℕ =>
      Hup * ((10 * Real.sqrt d) * (1 / 2 : ℝ) ^ k) ^ s) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrpow.const_mul Hup
  have hsmall : Tendsto (fun k : ℕ =>
      Real.sqrt d * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul (Real.sqrt d)
  have heventCost : ∀ᶠ k : ℕ in atTop,
      Hup * ((10 * Real.sqrt d) * (1 / 2 : ℝ) ^ k) ^ s ≤ ε₀ := by
    filter_upwards [hcost.eventually (eventually_lt_nhds hε)] with k hk
    exact hk.le
  have heventSmall : ∀ᶠ k : ℕ in atTop,
      Real.sqrt d * (1 / 2 : ℝ) ^ k ≤ 1 / 40 := by
    filter_upwards [hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 40))]
      with k hk
    exact hk.le
  obtain ⟨k, hkCost, hkSmall⟩ := (heventCost.and heventSmall).exists
  refine ⟨k, ?_, hkSmall, ?_⟩
  · positivity
  · simpa only [mul_assoc] using hkCost

/-- The fixed dyadic site mesh together with one spanning tree. -/
structure SiteMeshData (d : ℕ) (Hup s ε₀ : ℝ) where
  kMesh : ℕ
  δm : ℝ
  δm_eq : δm = (1 / 2 : ℝ) ^ kMesh
  δm_pos : 0 < δm
  δm_small : Real.sqrt d * δm ≤ 1 / 40
  access_cost : Hup * (10 * Real.sqrt d * δm) ^ s ≤ ε₀
  tree : SimpleGraph
    (HigherDimLQGMetric.Topology.meshVertices δm (siteMeshRing d δm))
  tree_le : tree ≤ HigherDimLQGMetric.Topology.meshGraph δm (siteMeshRing d δm)
  tree_isTree : tree.IsTree

/-- The fixed site mesh and tree can be chosen before the tolerance parameter. -/
theorem exists_siteMeshData {d : ℕ} (hd : 2 ≤ d) (Hup s ε₀ : ℝ)
    (hs : 0 < s) (hε : 0 < ε₀) :
    Nonempty (SiteMeshData d Hup s ε₀) := by
  obtain ⟨k, hδ, hsmall, hcost⟩ := exists_siteMesh_dyadic Hup s ε₀ hs hε
  let δ : ℝ := (1 / 2) ^ k
  have hδ' : 0 < δ := hδ
  have hsmall' : Real.sqrt d * δ ≤ 1 / 40 := hsmall
  have hcost' : Hup * (10 * Real.sqrt d * δ) ^ s ≤ ε₀ := hcost
  have hconnScale : 6 * Real.sqrt d * δ ≤ 1 := by linarith
  obtain ⟨T, hT, hTree⟩ := exists_siteMesh_tree hd hδ' hconnScale
  exact ⟨{
    kMesh := k
    δm := δ
    δm_eq := rfl
    δm_pos := hδ'
    δm_small := hsmall'
    access_cost := hcost'
    tree := T
    tree_le := hT
    tree_isTree := hTree
  }⟩

end HigherDimLQGContinuity
