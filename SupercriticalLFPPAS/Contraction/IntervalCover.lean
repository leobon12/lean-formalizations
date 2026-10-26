import Mathlib

/-! Finite greedy selection for the interval cover in Lemma 4.1. -/

set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLFPPAS.Contraction

/-- An interval is represented by its two endpoints. -/
abbrev D4Interval := ℝ × ℝ

/-- The length of an endpoint interval. -/
def d4IntervalLength (I : D4Interval) : ℝ := I.2 - I.1

/-- The midpoint of an endpoint interval. -/
def d4IntervalMidpoint (I : D4Interval) : ℝ := (I.1 + I.2) / 2

/-- The open interval represented as a metric ball. -/
def d4IntervalBall (I : D4Interval) : Set ℝ :=
  ball (d4IntervalMidpoint I) (d4IntervalLength I / 2)

private theorem d4IntervalBall_nonempty (I : D4Interval) (hI : I.1 < I.2) :
    (d4IntervalBall I).Nonempty := by
  refine ⟨d4IntervalMidpoint I, mem_ball_self ?_⟩
  dsimp [d4IntervalLength, d4IntervalMidpoint]
  linarith

theorem d4IntervalBall_eq_Ioo (I : D4Interval) :
    d4IntervalBall I = Ioo I.1 I.2 := by
  ext x
  simp [d4IntervalBall, d4IntervalLength, d4IntervalMidpoint, Metric.mem_ball,
    Real.dist_eq, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith

/-- A finite greedy run repeatedly chooses a longest interval and discards every interval
intersecting it. The remaining intervals are processed by the tail of the run. -/
inductive D4GreedyRun : Finset D4Interval → List D4Interval → Prop
  | empty : D4GreedyRun ∅ []
  | select {F R : Finset D4Interval} {I : D4Interval} {tail : List D4Interval}
      (hI : I ∈ F)
      (hmax : ∀ J ∈ F, d4IntervalLength J ≤ d4IntervalLength I)
      (hRsub : R ⊆ F)
      (hRdisj : ∀ J ∈ R, Disjoint (d4IntervalBall I) (d4IntervalBall J))
      (hRcover : ∀ J ∈ F, Disjoint (d4IntervalBall I) (d4IntervalBall J) → J ∈ R)
      (htail : D4GreedyRun R tail) :
      D4GreedyRun F (I :: tail)

/-- A greedy run selects pairwise disjoint intervals and every input interval meets a selected
interval at least as long. -/
theorem d4_greedyRun_spec {F : Finset D4Interval} {l : List D4Interval}
    (hpositive : ∀ I ∈ F, I.1 < I.2) (hRun : D4GreedyRun F l) :
    (∀ I ∈ l, I ∈ F) ∧ l.Nodup ∧
      l.Pairwise (fun I J => Disjoint (d4IntervalBall I) (d4IntervalBall J)) ∧
      ∀ I ∈ F, ∃ J ∈ l,
        (d4IntervalBall I ∩ d4IntervalBall J).Nonempty ∧
          d4IntervalLength I ≤ d4IntervalLength J := by
  classical
  induction hRun with
  | empty =>
      simp
  | @select F R I tail hI hmax hRsub hRdisj hRcover htail ih =>
      have hIpos : I.1 < I.2 := hpositive I hI
      have hIball : (d4IntervalBall I).Nonempty := d4IntervalBall_nonempty I hIpos
      obtain ⟨x, hx⟩ := hIball
      have hposR : ∀ J ∈ R, J.1 < J.2 := by
        intro J hJ
        exact hpositive J (hRsub hJ)
      obtain ⟨hsubTail, hnodup, hpair, hcover⟩ := ih hposR
      have hInotR : I ∉ R := by
        intro hIR
        exact (Set.disjoint_left.mp (hRdisj I hIR)) hx hx
      have hInotTail : I ∉ tail := fun hmem => hInotR (hsubTail I hmem)
      refine ⟨?_, List.nodup_cons.mpr ⟨hInotTail, hnodup⟩, ?_, ?_⟩
      · intro J hJ
        simp only [List.mem_cons] at hJ
        rcases hJ with rfl | hJ
        · exact hI
        · exact hRsub (hsubTail J hJ)
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair⟩
        intro J hJ
        exact hRdisj J (hsubTail J hJ)
      · intro J hJF
        by_cases hdis : Disjoint (d4IntervalBall I) (d4IntervalBall J)
        · have hJR : J ∈ R := hRcover J hJF hdis
          obtain ⟨Q, hQ, hmeet, hlen⟩ := hcover J hJR
          exact ⟨Q, List.mem_cons_of_mem _ hQ, hmeet, hlen⟩
        · have hmeet : (d4IntervalBall I ∩ d4IntervalBall J).Nonempty :=
            Set.not_disjoint_iff_nonempty_inter.mp hdis
          exact ⟨I, List.mem_cons_self, by simpa only [Set.inter_comm] using hmeet,
            hmax J hJF⟩

/-- Every finite family of nondegenerate intervals has a greedy run. -/
theorem d4_exists_greedyRun (F : Finset D4Interval)
    (hpositive : ∀ I ∈ F, I.1 < I.2) : ∃ l, D4GreedyRun F l := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
      by_cases hne : F.Nonempty
      · obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image F d4IntervalLength hne
        let R := F.filter fun J => Disjoint (d4IntervalBall I) (d4IntervalBall J)
        have hIball : (d4IntervalBall I).Nonempty :=
          d4IntervalBall_nonempty I (hpositive I hI)
        obtain ⟨x, hx⟩ := hIball
        have hInotR : I ∉ R := by
          intro hIR
          change I ∈ F.filter (fun J => Disjoint (d4IntervalBall I) (d4IntervalBall J)) at hIR
          exact (Set.disjoint_left.mp (Finset.mem_filter.mp hIR).2) hx hx
        have hRsub : R ⊆ F := by
          intro J hJ
          change J ∈ F.filter (fun J => Disjoint (d4IntervalBall I) (d4IntervalBall J)) at hJ
          exact (Finset.mem_filter.mp hJ).1
        have hRcover : ∀ J ∈ F, Disjoint (d4IntervalBall I) (d4IntervalBall J) → J ∈ R := by
          intro J hJ hdis
          change J ∈ F.filter (fun J => Disjoint (d4IntervalBall I) (d4IntervalBall J))
          exact Finset.mem_filter.mpr ⟨hJ, hdis⟩
        have hRdisj : ∀ J ∈ R, Disjoint (d4IntervalBall I) (d4IntervalBall J) := by
          intro J hJ
          change J ∈ F.filter (fun J => Disjoint (d4IntervalBall I) (d4IntervalBall J)) at hJ
          exact (Finset.mem_filter.mp hJ).2
        have hRproper : R ⊂ F := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hRsub, ?_⟩
          intro hEq
          exact hInotR (hEq ▸ hI)
        have hRpos : ∀ J ∈ R, J.1 < J.2 := by
          intro J hJ
          exact hpositive J (Finset.mem_filter.mp hJ).1
        obtain ⟨tail, htail⟩ := ih R hRproper hRpos
        exact ⟨I :: tail,
          D4GreedyRun.select hI hmax hRsub hRdisj hRcover htail⟩
      · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst F
        exact ⟨[], D4GreedyRun.empty⟩

/-- If two intervals meet and the first is no longer than the second, the first lies in the
threefold enlargement of the second. -/
private theorem d4_interval_subset_triple_ball (I J : D4Interval)
    (hmeet : (d4IntervalBall I ∩ d4IntervalBall J).Nonempty)
    (hlen : d4IntervalLength I ≤ d4IntervalLength J) :
    d4IntervalBall I ⊆ ball (d4IntervalMidpoint J) (3 * (d4IntervalLength J / 2)) := by
  intro x hx
  change dist x (d4IntervalMidpoint I) < d4IntervalLength I / 2 at hx
  obtain ⟨y, hyI, hyJ⟩ := hmeet
  change dist y (d4IntervalMidpoint I) < d4IntervalLength I / 2 at hyI
  change dist y (d4IntervalMidpoint J) < d4IntervalLength J / 2 at hyJ
  have hcenter : dist (d4IntervalMidpoint I) (d4IntervalMidpoint J) <
      d4IntervalLength I / 2 + d4IntervalLength J / 2 := by
    calc
      dist (d4IntervalMidpoint I) (d4IntervalMidpoint J) ≤
          dist (d4IntervalMidpoint I) y + dist y (d4IntervalMidpoint J) := dist_triangle _ _ _
      _ < d4IntervalLength I / 2 + d4IntervalLength J / 2 :=
        add_lt_add (by simpa only [dist_comm] using hyI) hyJ
  have hhalf : d4IntervalLength I / 2 ≤ d4IntervalLength J / 2 := by linarith
  apply Metric.mem_ball.mpr
  calc
    dist x (d4IntervalMidpoint J) ≤
        dist x (d4IntervalMidpoint I) + dist (d4IntervalMidpoint I) (d4IntervalMidpoint J) :=
      dist_triangle _ _ _
    _ < d4IntervalLength I / 2 +
        (d4IntervalLength I / 2 + d4IntervalLength J / 2) := add_lt_add hx hcenter
    _ ≤ 3 * (d4IntervalLength J / 2) := by nlinarith

/-- The greedy run covers any interval covered by the original finite family after tripling
the selected intervals. -/
theorem d4_greedyRun_covers_triple_enlargements
    {F : Finset D4Interval} {l : List D4Interval} {a b : ℝ}
    (hpositive : ∀ I ∈ F, I.1 < I.2) (hRun : D4GreedyRun F l)
    (hcover : Icc a b ⊆ ⋃ I ∈ F, Ioo I.1 I.2) :
    Icc a b ⊆ ⋃ J ∈ l,
      ball (d4IntervalMidpoint J) (3 * (d4IntervalLength J / 2)) := by
  obtain ⟨hsub, _, _, hselect⟩ := d4_greedyRun_spec hpositive hRun
  intro x hx
  obtain ⟨I, hIF, hxI⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hIpos := hpositive I hIF
  have hxBall : x ∈ d4IntervalBall I := by
    rw [d4IntervalBall_eq_Ioo]
    exact hxI
  obtain ⟨J, hJ, hmeet, hlen⟩ := hselect I hIF
  have hJpos : J.1 < J.2 := hpositive J (hsub J hJ)
  refine Set.mem_iUnion₂.mpr ⟨J, hJ, ?_⟩
  exact d4_interval_subset_triple_ball I J hmeet hlen hxBall

/-- The total length of the selected intervals controls the length of a covered interval by the
factor three. This is the `|J| ≤ 3S` estimate in the greedy covering argument. -/
theorem d4_greedyRun_interval_length_bound
    {F : Finset D4Interval} {l : List D4Interval} {a b : ℝ}
    (hpositive : ∀ I ∈ F, I.1 < I.2) (hRun : D4GreedyRun F l)
    (hcover : Icc a b ⊆ ⋃ I ∈ F, Ioo I.1 I.2) :
    b - a ≤ 3 * ∑ I ∈ l.toFinset, d4IntervalLength I := by
  let U := l.toFinset
  obtain ⟨hsub, _, _, _⟩ := d4_greedyRun_spec hpositive hRun
  have hcover' : Icc a b ⊆ ⋃ I ∈ U,
      ball (d4IntervalMidpoint I) (3 * (d4IntervalLength I / 2)) := by
    intro x hx
    obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.mp
      (d4_greedyRun_covers_triple_enlargements hpositive hRun hcover hx)
    exact Set.mem_iUnion₂.mpr ⟨J, List.mem_toFinset.mpr hJ, hxJ⟩
  have hmeasure : volume (Icc a b) ≤
      ∑ I ∈ U, volume (ball (d4IntervalMidpoint I)
        (3 * (d4IntervalLength I / 2))) :=
    (measure_mono hcover').trans (measure_biUnion_finset_le U _)
  have hsum :
      (∑ I ∈ U, volume (ball (d4IntervalMidpoint I)
          (3 * (d4IntervalLength I / 2)))) =
        ENNReal.ofReal (3 * ∑ I ∈ U, d4IntervalLength I) := by
    calc
      _ = ∑ I ∈ U, ENNReal.ofReal (3 * d4IntervalLength I) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [Real.volume_ball]
        congr 1
        ring
      _ = ENNReal.ofReal (∑ I ∈ U, 3 * d4IntervalLength I) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro I hI
        have hIF : I ∈ F := hsub I (List.mem_toFinset.mp hI)
        have hIpos := hpositive I hIF
        dsimp [d4IntervalLength]
        linarith
      _ = ENNReal.ofReal (3 * ∑ I ∈ U, d4IntervalLength I) := by
        congr 1
        simp only [Finset.mul_sum]
  have hsum_nonneg : 0 ≤ 3 * ∑ I ∈ U, d4IntervalLength I := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro I hI
    have hIF : I ∈ F := hsub I (List.mem_toFinset.mp hI)
    have hIpos := hpositive I hIF
    dsimp [d4IntervalLength]
    linarith
  rw [Real.volume_Icc, hsum] at hmeasure
  exact (ENNReal.ofReal_le_ofReal_iff hsum_nonneg).mp hmeasure

end SupercriticalLFPPAS.Contraction
