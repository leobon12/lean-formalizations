import SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour.PathSplice




 





set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
open LQGMetric.MetricGeometry

 
theorem boundary_edge_of_reflTransGen {ι : Type*} (R : ι → ι → Prop)
    (S : Set ι) {i j : ι} (hi : i ∈ S) (hj : j ∉ S)
    (hij : Relation.ReflTransGen R i j) :
    ∃ u v, u ∈ S ∧ v ∉ S ∧ R u v := by
  induction hij with
  | refl => exact False.elim (hj hi)
  | @tail b c hab hbc ih =>
      by_cases hb : b ∈ S
      · exact ⟨b, c, hb, hj, hbc⟩
      · exact ih hb


 

theorem finite_connected_paths_tour {ι X : Type*} [Fintype ι]
    [PseudoEMetricSpace X] {a b : ι → X} (P : (i : ι) → Path (a i) (b i))
    (hne : Nonempty ι)
    (hconn : ∀ i j : ι,
      Relation.ReflTransGen
        (fun u v => (range (P u) ∩ range (P v)).Nonempty) i j) :
    ∃ (x y : X) (pi : Path x y),
      range pi = ⋃ i : ι, range (P i) ∧
      pathLength pi ≤ 2 * ∑ i : ι, pathLength (P i) := by
  classical
  let R : ι → ι → Prop := fun u v => (range (P u) ∩ range (P v)).Nonempty
  let Good (S : Finset ι) : Prop :=
    ∃ (x y : X) (pi : Path x y),
      range pi = ⋃ i ∈ S, range (P i) ∧
      pathLength pi ≤ 2 * ∑ i ∈ S, pathLength (P i)
  have hone (i : ι) : Good {i} := by
    refine ⟨a i, b i, P i, ?_, ?_⟩
    · simp
    · simp only [Finset.sum_singleton]
      calc
        pathLength (P i) ≤ pathLength (P i) + pathLength (P i) := by
          exact le_add_of_nonneg_right (show (0:ℝ≥0∞) ≤ pathLength (P i) from bot_le)
        _ = 2 * pathLength (P i) := by ring
  obtain ⟨i₀⟩ := hne
  let candidates : Finset (Finset ι) := Finset.univ.filter Good
  have hcand : candidates.Nonempty := by
    refine ⟨{i₀}, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hone i₀
  obtain ⟨S, hSgood, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcand
  have hgood : Good S := (Finset.mem_filter.mp hSgood).2
  have hSnonempty : S.Nonempty := by
    by_contra hE
    rcases hgood with ⟨x,y,pi,htrace,-⟩
    have hzero : (⋃ i ∈ S, range (P i)) = (∅ : Set X) := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hE]
    have hnem : (range pi).Nonempty := ⟨pi 0, mem_range_self 0⟩
    rw [htrace, hzero] at hnem
    exact hnem.ne_empty rfl
  by_contra hnot
  have hproper : S ≠ Finset.univ := by
    intro heq
    subst S
    exact hnot (by simpa [Good] using hgood)
  have hout : ∃ j : ι, j ∉ S := by
    by_contra hall
    push Not at hall
    exact hproper (Finset.eq_univ_of_forall hall)
  obtain ⟨j,hj⟩ := hout
  obtain ⟨i,hi⟩ := hSnonempty
  obtain ⟨u,v,hu,hv,hcontact⟩ :=
    boundary_edge_of_reflTransGen R (S : Set ι) hi hj (hconn i j)
  obtain ⟨x,y,pi,htrace,hLen⟩ := hgood
  obtain ⟨q,hqu,hqv⟩ := hcontact
  obtain ⟨s,hs⟩ : q ∈ range pi := by
    rw [htrace]
    exact Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem hu hqu)
  obtain ⟨t,ht⟩ : q ∈ range (P v) := hqv
  have hjoin : pi s = P v t := hs.trans ht.symm
  have hnew : Good (insert v S) := by
    refine ⟨pi 0, pi 1, spliceAt pi (P v) s t hjoin, ?_, ?_⟩
    · rw [spliceAt_range, htrace]
      ext z
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
      aesop
    · rw [spliceAt_length]
      have hsum : ∑ i ∈ insert v S, pathLength (P i) =
          pathLength (P v) + ∑ i ∈ S, pathLength (P i) := by
        simp [Finset.sum_insert hv]
      rw [hsum]
      calc
        pathLength pi + 2 * pathLength (P v)
            ≤ 2 * (∑ i ∈ S, pathLength (P i)) + 2 * pathLength (P v) :=
              add_le_add hLen le_rfl
        _ = 2 * (pathLength (P v) + ∑ i ∈ S, pathLength (P i)) := by ring
  have hnewcand : insert v S ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnew
  have hcard := hmax (insert v S) hnewcand
  have hstrict : S.card < (insert v S).card := by simp [Finset.card_insert_of_notMem hv]
  exact (not_le_of_gt hstrict) hcard


end SupercriticalLQGUniqueness.Uniqueness.Objects.NetworkTour
