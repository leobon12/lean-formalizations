import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover.E1eBorelCantelli




 


set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
open LQGMetric (DistC)

 

theorem e1e_cover_from_site_tail {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (A c : ℝ) (hc : 0 ≤ c)
    (r : ℕ → ℕ → ℝ) (N : ℕ → ℂ → ℕ → Ω → ℝ)
    (good : ℕ → ℂ → ℕ → Set Ω)
    (hrpos : ∀ n j, 0 < r n j)
    (hrange : ∀ (n j : ℕ), j ≤ n →
      (10 : ℝ) ^ (-(2 * (n : ℤ))) ≤ r n j ∧
      r n j ≤ (10 : ℝ) ^ (-(n : ℤ)))
    (hgood : ∀ n x j ω, ω ∈ good n x j →
      BiLipschitz.PaidSeparators.GoodScalar (D (h ω)) (D' (h ω)) A x (r n j) (N n x j ω)
        (hrpos n j))
    (hsite : ∀ n x,
      P {ω | ∀ j ≤ n, ω ∉ good n x j} ≤
        ENNReal.ofReal (c * (1 / 100000000 : ℝ) ^ n)) :
    ∀ᵐ ω ∂P, BiLipschitz.PaidSeparators.GoodGridCover (D (h ω)) (D' (h ω)) A := by
  filter_upwards [e1e_grid_eventual P good c hc hsite] with ω hω
  intro m
  obtain ⟨n₀, hn₀⟩ := hω m
  refine ⟨n₀, ?_⟩
  intro n hn
  let S := meshBox m n
  let e : Fin S.card ≃ {q // q ∈ S} := S.equivFin.symm
  have hall : ∀ q : {q // q ∈ S},
      ∃ j ≤ n, ω ∈ good n (LQGMetric.GM.gridPt (meshStep n) q.val) j := by
    intro q
    exact hn₀ n hn q.val q.property
  let j : Fin S.card → ℕ := fun i => Classical.choose (hall (e i))
  let x : Fin S.card → ℂ := fun i => LQGMetric.GM.gridPt (meshStep n) (e i).val
  let r' : Fin S.card → ℝ := fun i => r n (j i)
  let N' : Fin S.card → ℝ := fun i => N n (x i) (j i) ω
  have hj : ∀ i, j i ≤ n ∧ ω ∈ good n (x i) (j i) := by
    intro i
    exact Classical.choose_spec (hall (e i))
  have hr' : ∀ i, 0 < r' i := fun i => hrpos n (j i)
  refine ⟨S.card, x, r', N', hr', ?_, ?_, ?_⟩
  · intro i
    exact hrange n (j i) (hj i).1
  · intro i
    exact hgood n (x i) (j i) ω (hj i).2
  · intro y hy
    obtain ⟨q, hq, hdist⟩ := e1e_mesh_cover m n y hy
    let i : Fin S.card := S.equivFin ⟨q, hq⟩
    refine ⟨i, ?_⟩
    have hi : e i = (⟨q, hq⟩ : {q // q ∈ S}) := by
      simp [e, i]
    have hδ : meshStep n < r' i / 2 :=
      e1e_mesh_inside (hrange n (j i) (hj i).1).1
    change dist y (LQGMetric.GM.gridPt (meshStep n) (e i).val) < r' i / 2
    rw [hi]
    exact hdist.trans_lt hδ

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.GridCover
