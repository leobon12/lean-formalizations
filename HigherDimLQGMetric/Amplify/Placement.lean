import HigherDimLQGMetric.Amplify.PairLaw

/-! Deterministic placement of finitely many trial centers in each compact box. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Every nonempty interior in positive dimensional Euclidean space contains
infinitely many possible trial centers. -/
theorem amplify_interior_infinite (hd : 1 ≤ d) {K : Set (Rd d)}
    (hK : (interior K).Nonempty) : (interior K).Infinite := by
  let j : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  let f : ℝ → Rd d := fun t => x + EuclideanSpace.single j t
  have hf : Function.Injective f := by
    intro t u htu
    have hsingle : EuclideanSpace.single j t =
        EuclideanSpace.single j u := add_left_cancel htu
    have hcoord := congrArg (fun y : Rd d => y.ofLp j) hsingle
    simpa only [PiLp.single_apply, ite_true] using hcoord
  have himage : f '' Ioo 0 ε ⊆ interior K := by
    rintro y ⟨t, ht, rfl⟩
    apply hball
    have hnorm : ‖EuclideanSpace.single j t‖ = t := by
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht.1]
    change dist (f t) x < ε
    rw [dist_eq_norm]
    simpa only [f, add_sub_cancel_left, hnorm] using ht.2
  exact (Set.Ioo_infinite hε).image hf.injOn |>.mono himage

/-- Each box supplies any prescribed finite number of distinct interior
centers. The embeddings are independent of all metric randomness. -/
theorem amplify_exists_centers (hd : 1 ≤ d) {M : ℕ}
    (K : Fin M → Set (Rd d))
    (hK : ∀ i, (interior (K i)).Nonempty) (N : ℕ) :
    ∃ w : Fin M → Fin N → Rd d,
      (∀ i k, w i k ∈ interior (K i)) ∧
      (∀ i, Function.Injective (w i)) := by
  classical
  let e : ∀ i : Fin M, ℕ ↪ (interior (K i)) :=
    fun i => (amplify_interior_infinite hd (hK i)).natEmbedding _
  refine ⟨fun i k => (e i k).1, ?_, ?_⟩
  · intro i k
    exact (e i k).2
  · intro i k l hkl
    apply Fin.ext
    exact (e i).injective (Subtype.ext hkl)

/-- A finite list of distinct interior points admits one radius for all its
box inclusions and pairwise disjoint balls. -/
theorem amplify_finite_ball_separation {ι : Type*} [Fintype ι]
    (w : ι → Rd d) (hw : Function.Injective w)
    (K : ι → Set (Rd d)) (hK : ∀ i, w i ∈ interior (K i)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ i, Metric.ball (w i) ε ⊆ K i) ∧
      Pairwise (fun i j => Disjoint (Metric.ball (w i) ε)
        (Metric.ball (w j) ε)) := by
  classical
  let εK : ι → ℝ := fun i =>
    (Metric.isOpen_iff.mp isOpen_interior (w i) (hK i)).choose
  have hεK (i : ι) : 0 < εK i :=
    (Metric.isOpen_iff.mp isOpen_interior (w i) (hK i)).choose_spec.1
  have hballK (i : ι) : Metric.ball (w i) (εK i) ⊆ K i :=
    ((Metric.isOpen_iff.mp isOpen_interior (w i) (hK i)).choose_spec.2).trans
      interior_subset
  let SK : Finset ℝ := insert 1 (Finset.univ.image εK)
  have hSK : SK.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  let eK := SK.min' hSK
  have heKpos : 0 < eK := by
    have hm := SK.min'_mem hSK
    rcases Finset.mem_insert.mp hm with hm | hm
    · simpa only [eK, hm] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hm
      simpa only [eK, ← hi] using hεK i
  have heKle (i : ι) : eK ≤ εK i :=
    Finset.min'_le SK _ (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  let distPair : ι × ι → ℝ := fun p => dist (w p.1) (w p.2) / 3
  let T : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  let SD : Finset ℝ := insert 1 (T.image distPair)
  have hSD : SD.Nonempty := ⟨1, Finset.mem_insert_self 1 _⟩
  let eD := SD.min' hSD
  have heDpos : 0 < eD := by
    have hm := SD.min'_mem hSD
    rcases Finset.mem_insert.mp hm with hm | hm
    · simpa only [eD, hm] using (show (0 : ℝ) < 1 by norm_num)
    · obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      have hdist : 0 < dist (w p.1) (w p.2) := dist_pos.mpr (hw.ne hne)
      simpa only [eD, ← he, distPair] using (div_pos hdist (by norm_num : (0 : ℝ) < 3))
  have heDle (i j : ι) (hij : i ≠ j) : eD ≤ dist (w i) (w j) / 3 := by
    apply Finset.min'_le SD
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
  let ε := min eK eD
  have hε : 0 < ε := lt_min heKpos heDpos
  refine ⟨ε, hε, ?_, ?_⟩
  · intro i
    exact (Metric.ball_subset_ball ((min_le_left _ _).trans (heKle i))).trans
      (hballK i)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxi : dist x (w i) < ε := Metric.mem_ball.mp hx
    have hxj : dist x (w j) < ε := Metric.mem_ball.mp hy
    have htri := dist_triangle (w i) x (w j)
    have hsep := heDle i j hij
    rw [dist_comm (w i) x] at htri
    have hsmall : ε ≤ dist (w i) (w j) / 3 :=
      (min_le_right _ _).trans hsep
    linarith

end HigherDimLQGMetric
