import HigherDimLQGMetric.Shell.EpsilonChain
import LQGMetric.Metric.CurveNatural
import Mathlib.Analysis.Convex.PathConnected

/-!
# Euclidean Lipschitz paths in connected open subsets

A connected open subset of Euclidean space admits a finite polygonal path
between any two of its points. Constant-speed reparametrization then gives
a Lipschitz path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric AffineMap unitInterval
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- A straight segment has finite Euclidean path length. -/
theorem w2_pathLength_segment_ne_top (x y : Rd d) :
    pathLength (Path.segment x y) ≠ ∞ := by
  have hLip := (lipschitzWith_lineMap (𝕜 := ℝ) x y).lipschitzOnWith (s := Icc (0 : ℝ) 1)
  have hvar : eVariationOn (lineMap x y : ℝ → Rd d) (Icc 0 1) ≤
      (nndist x y : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) := by
    simpa only [Function.comp_id] using
      hLip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1)
        (fun t ht => ht)
  have hvar' : eVariationOn (Path.segment x y).extend (Icc (0 : ℝ) 1) ≤
      (nndist x y : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn (Path.eqOn_extend_segment x y)]
    exact hvar
  have hfin : (nndist x y : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) ≠ ∞ := by
    rw [eVariationOn_id_Icc]
    norm_num
  exact ne_top_of_le_ne_top hfin hvar'

/-- The Euclidean segment has no more length than its endpoint distance. -/
theorem w2_pathLength_segment_le (x y : Rd d) :
    pathLength (Path.segment x y) ≤ ENNReal.ofReal (dist x y) := by
  have hLip := (lipschitzWith_lineMap (𝕜 := ℝ) x y).lipschitzOnWith (s := Icc (0 : ℝ) 1)
  have hvar : eVariationOn (lineMap x y : ℝ → Rd d) (Icc 0 1) ≤
      (nndist x y : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) := by
    simpa only [Function.comp_id] using
      hLip.comp_eVariationOn_le (g := id) (s := Icc (0 : ℝ) 1) (fun t ht => ht)
  have hvar' : eVariationOn (Path.segment x y).extend (Icc (0 : ℝ) 1) ≤
      (nndist x y : ℝ≥0∞) * eVariationOn id (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn (Path.eqOn_extend_segment x y)]
    exact hvar
  simpa [pathLength, curveLength, eVariationOn_id_Icc, edist_dist] using hvar'

/-- Connected open Euclidean sets have a Lipschitz path between any two points. -/
theorem w2_exists_lipschitz_path {U : Set (Rd d)} (hU : IsOpen U)
    (hUc : IsConnected U) {x y : Rd d} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ (Λ : ℝ) (P : ℝ → Rd d), 0 ≤ Λ ∧
      LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1) ∧
      P 0 = x ∧ P 1 = y ∧ MapsTo P (Icc 0 1) U := by
  classical
  have hpc : IsPathConnected U := (hU.isConnected_iff_isPathConnected).1 hUc
  let γ₀ : Path x y := (hpc.joinedIn x hx y hy).somePath
  let K : Set (Rd d) := range γ₀
  have hKc : IsCompact K := isCompact_range γ₀.continuous
  have hKconn : IsConnected K := isConnected_range γ₀.continuous
  have hKU : K ⊆ U := by
    rintro v ⟨t, rfl⟩
    exact (hpc.joinedIn x hx y hy).somePath_mem t
  obtain ⟨δ, hδ, hthick⟩ := hKc.exists_thickening_subset_open hU hKU
  let R : Rd d → Rd d → Prop := fun a b => a ∈ K ∧ b ∈ K ∧ dist a b < δ
  have hchain : Relation.ReflTransGen R x y :=
    connected_epsilon_chain hKconn hδ
      (by exact ⟨0, γ₀.source⟩) (by exact ⟨1, γ₀.target⟩)
  have hreach : ∀ a b : Rd d, b ∈ K → Relation.ReflTransGen R a b → a ∈ K →
      ∃ γ : Path a b, range γ ⊆ U ∧ pathLength γ ≠ ∞ := by
    intro a b hb hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro ha
        refine ⟨Path.refl b, ?_, ?_⟩
        · rw [Path.refl_range]
          exact singleton_subset_iff.mpr (hKU ha)
        · rw [pathLength_refl]
          exact ENNReal.zero_ne_top
    | head h _ ih =>
        rename_i a₀ c₀ htail
        intro _
        obtain ⟨ha, hc, hac⟩ := h
        obtain ⟨γ, hγU, hγL⟩ := ih hc
        have hseg : segment ℝ a₀ c₀ ⊆ U := by
          have hball : segment ℝ a₀ c₀ ⊆ ball a₀ δ :=
            (convex_ball a₀ δ).segment_subset (mem_ball_self hδ)
              (by simpa only [mem_ball, dist_comm] using hac)
          exact hball.trans ((ball_subset_thickening ha δ).trans hthick)
        refine ⟨(Path.segment a₀ c₀).trans γ, ?_, ?_⟩
        · rw [Path.trans_range, Path.range_segment]
          exact union_subset hseg hγU
        · rw [pathLength_trans]
          exact ENNReal.add_ne_top.mpr ⟨w2_pathLength_segment_ne_top a₀ c₀, hγL⟩
  obtain ⟨γ, hγU, hγL⟩ := hreach x y ⟨1, γ₀.target⟩ hchain ⟨0, γ₀.source⟩
  obtain ⟨γ', _, hγ'img, hγ'Lip⟩ := exists_lipschitz_path γ hγL
  let Λ : ℝ := (pathLength γ).toReal
  let P : ℝ → Rd d := γ'.extend
  have hΛ : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hP : LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1) := by
    rw [show Real.toNNReal Λ = (pathLength γ).toNNReal by
      exact ENNReal.toNNReal_toReal_eq _]
    intro s hs t ht
    simpa only [P, Path.extend_apply _ hs, Path.extend_apply _ ht, Subtype.edist_eq] using
      hγ'Lip (⟨s, hs⟩ : I) (⟨t, ht⟩ : I)
  refine ⟨Λ, P, hΛ, hP, ?_, ?_, ?_⟩
  · exact γ'.extend_zero
  · exact γ'.extend_one
  · intro s hs
    change γ'.extend s ∈ U
    rw [Path.extend_apply _ hs]
    exact hγU (hγ'img (mem_range_self (⟨s, hs⟩ : I)))

/-- Compact connected subsets of an open set have finite-length polygonal paths
between their points, staying in the open set. -/
theorem w2_finite_path_compact {K U : Set (Rd d)} (hK : IsCompact K)
    (hKc : IsConnected K) (hU : IsOpen U) (hKU : K ⊆ U)
    {x y : Rd d} (hx : x ∈ K) (hy : y ∈ K) :
    ∃ γ : Path x y, range γ ⊆ U ∧ pathLength γ ≠ ∞ := by
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let R : Rd d → Rd d → Prop := fun a b => a ∈ K ∧ b ∈ K ∧ dist a b < δ
  have hchain : Relation.ReflTransGen R x y := connected_epsilon_chain hKc hδ hx hy
  have hreach : ∀ a b : Rd d, b ∈ K → Relation.ReflTransGen R a b → a ∈ K →
      ∃ γ : Path a b, range γ ⊆ U ∧ pathLength γ ≠ ∞ := by
    intro a b hb hab
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro ha
        refine ⟨Path.refl b, ?_, ?_⟩
        · rw [Path.refl_range]
          exact singleton_subset_iff.mpr (hKU ha)
        · rw [pathLength_refl]
          exact ENNReal.zero_ne_top
    | head h _ ih =>
        rename_i a₀ c₀ htail
        intro _
        obtain ⟨ha, hc, hac⟩ := h
        obtain ⟨γ, hγU, hγL⟩ := ih hc
        have hseg : segment ℝ a₀ c₀ ⊆ U := by
          have hball : segment ℝ a₀ c₀ ⊆ ball a₀ δ :=
            (convex_ball a₀ δ).segment_subset (mem_ball_self hδ)
              (by simpa only [mem_ball, dist_comm] using hac)
          exact hball.trans ((ball_subset_thickening ha δ).trans hthick)
        refine ⟨(Path.segment a₀ c₀).trans γ, ?_, ?_⟩
        · rw [Path.trans_range, Path.range_segment]
          exact union_subset hseg hγU
        · rw [pathLength_trans]
          exact ENNReal.add_ne_top.mpr ⟨w2_pathLength_segment_ne_top a₀ c₀, hγL⟩
  exact hreach x y hy hchain hx

end HigherDimLQGMetric
