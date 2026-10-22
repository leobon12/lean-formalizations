import HigherDimLQGMetric.Sharp.W2Path

/-! Uniform finite-length paths on compact connected sets inside an open domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric unitInterval
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

/-- Compactness upgrades pointwise finite polygonal paths to a uniform length
bound. Local straight segments connect arbitrary endpoints to finitely many
reference paths. -/
theorem w2_uniform_finite_paths {K U : Set (Rd d)}
    (hK : IsCompact K) (hKc : IsConnected K) (hKn : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ∃ γ : Path x y, range γ ⊆ U ∧ pathLength γ ≤ ENNReal.ofReal Λ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hKn
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let γ (i : K) : Path i.1 x₀ :=
    Classical.choose (w2_finite_path_compact hK hKc hU hKU i.2 hx₀)
  have hγU (i : K) : range (γ i) ⊆ U :=
    (Classical.choose_spec (w2_finite_path_compact hK hKc hU hKU i.2 hx₀)).1
  have hγfin (i : K) : pathLength (γ i) ≠ ∞ :=
    (Classical.choose_spec (w2_finite_path_compact hK hKc hU hKU i.2 hx₀)).2
  have hcover : K ⊆ ⋃ i : K, ball i.1 (δ / 2) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by positivity)⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover
    (fun i : K => ball i.1 (δ / 2)) (fun _ => isOpen_ball) hcover
  let L : ℝ≥0∞ := ∑ i ∈ F, pathLength (γ i)
  have hLfin : L ≠ ∞ := ENNReal.sum_ne_top.mpr (fun i _ => hγfin i)
  have hγL (i : K) (hi : i ∈ F) : pathLength (γ i) ≤ L := by
    dsimp [L]
    exact Finset.single_le_sum (f := fun j : K => pathLength (γ j))
      (fun j hj => by exact bot_le) hi
  let T : ℝ≥0∞ := ENNReal.ofReal δ + L + L
  have hTfin : T ≠ ∞ := by
    dsimp [T]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hLfin⟩, hLfin⟩
  let Λ : ℝ := T.toReal
  have hΛ : 0 ≤ Λ := ENNReal.toReal_nonneg
  refine ⟨Λ, hΛ, ?_⟩
  intro x hx y hy
  have hxF := hF hx
  obtain ⟨i, hxiF⟩ := Set.mem_iUnion.mp hxF
  obtain ⟨hiF, hxi⟩ := Set.mem_iUnion.mp hxiF
  have hyF := hF hy
  obtain ⟨j, hyjF⟩ := Set.mem_iUnion.mp hyF
  obtain ⟨hjF, hyj⟩ := Set.mem_iUnion.mp hyjF
  have hxi' : x ∈ ball i.1 δ :=
    ball_subset_ball (by linarith only [hδ]) hxi
  have hyj' : y ∈ ball j.1 δ :=
    ball_subset_ball (by linarith only [hδ]) hyj
  have hseg₁ : segment ℝ x i.1 ⊆ U := by
    have hb : segment ℝ x i.1 ⊆ ball i.1 δ :=
      (convex_ball i.1 δ).segment_subset hxi' (mem_ball_self hδ)
    exact hb.trans ((ball_subset_thickening i.2 δ).trans hthick)
  have hseg₂ : segment ℝ j.1 y ⊆ U := by
    have hb : segment ℝ j.1 y ⊆ ball j.1 δ :=
      (convex_ball j.1 δ).segment_subset (mem_ball_self hδ) hyj'
    exact hb.trans ((ball_subset_thickening j.2 δ).trans hthick)
  let q : Path x y := (Path.segment x i.1).trans
    ((γ i).trans ((γ j).symm.trans (Path.segment j.1 y)))
  have hqU : range q ⊆ U := by
    dsimp [q]
    simp only [Path.trans_range, Path.symm_range, Path.range_segment]
    exact union_subset hseg₁ (union_subset (hγU i) (union_subset (hγU j) hseg₂))
  have hxiδ : dist x i.1 ≤ δ / 2 := (by simpa only [mem_ball] using hxi : dist x i.1 < δ / 2).le
  have hjyδ : dist j.1 y ≤ δ / 2 := by
    have h := (by simpa only [mem_ball, dist_comm] using hyj : dist j.1 y < δ / 2)
    exact h.le
  have hhalf : (0 : ℝ) ≤ δ / 2 := by positivity
  have htwice : ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) =
      ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_add hhalf hhalf]
    congr 1
    ring
  have hqL : pathLength q ≤ T := by
    calc
      pathLength q = pathLength (Path.segment x i.1) +
          (pathLength (γ i) + (pathLength (γ j) + pathLength (Path.segment j.1 y))) := by
            simp only [q, pathLength_trans, pathLength_symm]
      _ ≤ ENNReal.ofReal (δ / 2) + (L + (L + ENNReal.ofReal (δ / 2))) := by
            gcongr
            · exact (w2_pathLength_segment_le x i.1).trans
                (ENNReal.ofReal_le_ofReal hxiδ)
            · exact hγL i hiF
            · exact hγL j hjF
            · exact (w2_pathLength_segment_le j.1 y).trans
                (ENNReal.ofReal_le_ofReal hjyδ)
      _ = T := by
            calc
              _ = ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) + L + L := by abel
              _ = T := by rw [htwice]
  exact ⟨q, hqU, by simpa only [Λ, ENNReal.ofReal_toReal hTfin] using hqL⟩

/-- Uniform Lipschitz parameterization of the paths above. -/
theorem w2_uniform_lipschitz_paths {K U : Set (Rd d)}
    (hK : IsCompact K) (hKc : IsConnected K) (hKn : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ∃ P : ℝ → Rd d, LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1) ∧
        P 0 = x ∧ P 1 = y ∧ MapsTo P (Icc (0 : ℝ) 1) U := by
  obtain ⟨Λ, hΛ, hpath⟩ := w2_uniform_finite_paths hK hKc hKn hU hKU
  refine ⟨Λ, hΛ, ?_⟩
  intro x hx y hy
  obtain ⟨q, hqU, hqL⟩ := hpath x hx y hy
  have hqfin : pathLength q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hqL
  obtain ⟨q', _, hq'img, hq'Lip⟩ := exists_lipschitz_path q hqfin
  let P : ℝ → Rd d := q'.extend
  have hcoef : (pathLength q).toNNReal ≤ Real.toNNReal Λ := by
    have h := ENNReal.toNNReal_mono ENNReal.ofReal_ne_top hqL
    rw [← ENNReal.toNNReal_toReal_eq (ENNReal.ofReal Λ),
      ENNReal.toReal_ofReal hΛ] at h
    exact h
  have hP : LipschitzOnWith (Real.toNNReal Λ) P (Icc 0 1) := by
    intro s hs t ht
    have h := hq'Lip (⟨s, hs⟩ : I) (⟨t, ht⟩ : I)
    have h' : edist (P s) (P t) ≤ (pathLength q).toNNReal * edist s t := by
      simpa only [P, Path.extend_apply _ hs, Path.extend_apply _ ht, Subtype.edist_eq] using h
    exact h'.trans (by gcongr)
  refine ⟨P, hP, q'.extend_zero, q'.extend_one, ?_⟩
  intro s hs
  change q'.extend s ∈ U
  rw [Path.extend_apply _ hs]
  exact hqU (hq'img (mem_range_self (⟨s, hs⟩ : I)))

end HigherDimLQGMetric
