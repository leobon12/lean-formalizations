import SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes.Projection
import LQGMetric.Prob.PolishContinuousMap




 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes

abbrev RealPath := C(ℝ, ℂ)

example : PolishSpace RealPath := inferInstance
example : StandardBorelSpace RealPath := inferInstance

 
def OpenIntervalTrace (O : Set ℂ) (p : RealPath × (ℝ × ℝ)) : Prop :=
  ∀ t ∈ Set.Ioo p.2.1 p.2.2, p.1 t ∈ O

 
theorem openIntervalTrace_iff_rational_intervals
    (O : Set ℂ) (p : RealPath × (ℝ × ℝ)) :
    OpenIntervalTrace O p ↔
      ∀ q r : ℚ, p.2.1 < (q : ℝ) → q ≤ r → (r : ℝ) < p.2.2 →
        MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O := by
  constructor
  · intro h q r hq hqr hr t ht
    apply h t
    exact ⟨lt_of_lt_of_le hq ht.1, lt_of_le_of_lt ht.2 hr⟩
  · intro h t ht
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn ht.1
    obtain ⟨r, hr₁, hr₂⟩ := exists_rat_btwn ht.2
    have hqr : q ≤ r := by
      exact_mod_cast le_of_lt (hq₂.trans hr₁)
    exact h q r hq₁ hqr hr₂ ⟨le_of_lt hq₂, le_of_lt hr₁⟩

theorem openIntervalTrace_borel {O : Set ℂ} (hO : IsOpen O) :
    MeasurableSet {p : RealPath × (ℝ × ℝ) | OpenIntervalTrace O p} := by
  have hcount : MeasurableSet {p : RealPath × (ℝ × ℝ) |
      ∀ q r : ℚ, p.2.1 < (q : ℝ) → q ≤ r → (r : ℝ) < p.2.2 →
        MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O} := by
    have hi : MeasurableSet (⋂ q : ℚ, ⋂ r : ℚ,
        {p : RealPath × (ℝ × ℝ) |
          p.2.1 < (q : ℝ) → q ≤ r → (r : ℝ) < p.2.2 →
            MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O}) := by
      apply MeasurableSet.iInter
      intro q
      apply MeasurableSet.iInter
      intro r
      by_cases hqr : q ≤ r
      · have htime : MeasurableSet {p : RealPath × (ℝ × ℝ) |
            p.2.1 < (q : ℝ) ∧ (r : ℝ) < p.2.2} :=
          (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
            (measurableSet_lt measurable_const
              (measurable_snd.comp measurable_snd))
        have hpath : MeasurableSet {p : RealPath × (ℝ × ℝ) |
            MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O} :=
          ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hO).measurableSet).preimage
            measurable_fst
        have hgoal : {p : RealPath × (ℝ × ℝ) |
            p.2.1 < (q : ℝ) → q ≤ r → (r : ℝ) < p.2.2 →
              MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O} =
            {p | p.2.1 < (q : ℝ) ∧ (r : ℝ) < p.2.2}ᶜ ∪
              {p | MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O} := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff,
            not_and_or, hqr, true_implies]
          tauto
        rw [hgoal]
        exact htime.compl.union hpath
      · have hgoal : {p : RealPath × (ℝ × ℝ) |
            p.2.1 < (q : ℝ) → q ≤ r → (r : ℝ) < p.2.2 →
              MapsTo p.1 (Set.Icc (q : ℝ) (r : ℝ)) O} = Set.univ := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          intro _ h
          exact False.elim (hqr h)
        rw [hgoal]
        exact MeasurableSet.univ
    convert hi using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  convert hcount using 1
  ext p
  exact openIntervalTrace_iff_rational_intervals O p

abbrev ExcursionInput := RealPath × (Fin 5 → ℝ)

 
def ExcursionRelation (O V : Set ℂ) (p : ExcursionInput) : Prop :=
  0 ≤ p.2 1 ∧ p.2 1 ≤ p.2 2 ∧ p.2 2 ≤ p.2 3 ∧
  p.2 3 ≤ p.2 4 ∧ p.2 4 ≤ p.2 0 ∧
  p.1 (p.2 1) ∈ frontier O ∧ p.1 (p.2 4) ∈ frontier O ∧
  OpenIntervalTrace O (p.1, (p.2 1, p.2 4)) ∧
  p.1 (p.2 2) ∈ closure V ∧ p.1 (p.2 3) ∈ closure V ∧
  OpenIntervalTrace (closure V)ᶜ (p.1, (p.2 1, p.2 2)) ∧
  OpenIntervalTrace (closure V)ᶜ (p.1, (p.2 3, p.2 4))

private theorem coord_measurable (i : Fin 5) :
    Measurable (fun p : ExcursionInput => p.2 i) :=
  (measurable_pi_apply i).comp measurable_snd

private theorem path_eval_measurable (i : Fin 5) :
    Measurable (fun p : ExcursionInput => p.1 (p.2 i)) :=
  continuous_eval.measurable.comp
    (measurable_fst.prodMk (coord_measurable i))

private theorem interval_pair_measurable (i j : Fin 5) :
    Measurable (fun p : ExcursionInput => (p.1, (p.2 i, p.2 j))) :=
  measurable_fst.prodMk ((coord_measurable i).prodMk (coord_measurable j))

theorem excursionRelation_borel {O V : Set ℂ} (hO : IsOpen O) :
    MeasurableSet {p : ExcursionInput | ExcursionRelation O V p} := by
  have h0 : MeasurableSet {p : ExcursionInput | (0 : ℝ) ≤ p.2 1} :=
    measurableSet_le measurable_const (coord_measurable 1)
  have h1 : MeasurableSet {p : ExcursionInput | p.2 1 ≤ p.2 2} :=
    measurableSet_le (coord_measurable 1) (coord_measurable 2)
  have h2 : MeasurableSet {p : ExcursionInput | p.2 2 ≤ p.2 3} :=
    measurableSet_le (coord_measurable 2) (coord_measurable 3)
  have h3 : MeasurableSet {p : ExcursionInput | p.2 3 ≤ p.2 4} :=
    measurableSet_le (coord_measurable 3) (coord_measurable 4)
  have h4 : MeasurableSet {p : ExcursionInput | p.2 4 ≤ p.2 0} :=
    measurableSet_le (coord_measurable 4) (coord_measurable 0)
  have h5 : MeasurableSet {p : ExcursionInput | p.1 (p.2 1) ∈ frontier O} :=
    isClosed_frontier.measurableSet.preimage (path_eval_measurable 1)
  have h6 : MeasurableSet {p : ExcursionInput | p.1 (p.2 4) ∈ frontier O} :=
    isClosed_frontier.measurableSet.preimage (path_eval_measurable 4)
  have h7 : MeasurableSet {p : ExcursionInput |
      OpenIntervalTrace O (p.1, (p.2 1, p.2 4))} :=
    (openIntervalTrace_borel hO).preimage (interval_pair_measurable 1 4)
  have h8 : MeasurableSet {p : ExcursionInput | p.1 (p.2 2) ∈ closure V} :=
    isClosed_closure.measurableSet.preimage (path_eval_measurable 2)
  have h9 : MeasurableSet {p : ExcursionInput | p.1 (p.2 3) ∈ closure V} :=
    isClosed_closure.measurableSet.preimage (path_eval_measurable 3)
  have h10 : MeasurableSet {p : ExcursionInput |
      OpenIntervalTrace (closure V)ᶜ (p.1, (p.2 1, p.2 2))} :=
    (openIntervalTrace_borel isClosed_closure.isOpen_compl).preimage
      (interval_pair_measurable 1 2)
  have h11 : MeasurableSet {p : ExcursionInput |
      OpenIntervalTrace (closure V)ᶜ (p.1, (p.2 3, p.2 4))} :=
    (openIntervalTrace_borel isClosed_closure.isOpen_compl).preimage
      (interval_pair_measurable 3 4)
  have hall := h0.inter (h1.inter (h2.inter (h3.inter (h4.inter
    (h5.inter (h6.inter (h7.inter (h8.inter (h9.inter (h10.inter h11))))))))))
  convert hall using 1
  ext p
  simp only [ExcursionRelation, Set.mem_inter_iff, Set.mem_ofPred_eq]


end SupercriticalLQGUniqueness.Uniqueness.Measurability.GeodesicCodes
