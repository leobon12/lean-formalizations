import SupercriticalLQGUniqueness.B2.PfeAxioms.S2MetricBorel

 














set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
def ballInf (F : ℕ → ℂ × ℂ → EReal) (n : ℕ) (q : ℂ × ℂ) (ρ : ℝ) : EReal :=
  ⨅ p ∈ Metric.ball q ρ, F n p

 
def gammaLowerFun (F : ℕ → ℂ × ℂ → EReal) (q : ℂ × ℂ) : EReal :=
  ⨆ k : ℕ, liminf (fun n => ballInf F n q (1 / ((k : ℝ) + 1))) atTop

theorem ballInf_anti (F : ℕ → ℂ × ℂ → EReal) (n : ℕ) {q q' : ℂ × ℂ} {ρ ρ' : ℝ}
    (h : Metric.ball q' ρ' ⊆ Metric.ball q ρ) :
    ballInf F n q ρ ≤ ballInf F n q' ρ' :=
  biInf_mono h

theorem lowerSemicontinuous_gammaLowerFun (F : ℕ → ℂ × ℂ → EReal) :
    LowerSemicontinuous (gammaLowerFun F) := by
  intro q t ht
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 ht
  have hr : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by positivity
  filter_upwards [Metric.ball_mem_nhds q hr] with q' hq'
  refine lt_of_lt_of_le hk (le_trans ?_ (le_iSup _ (2 * k + 1)))
  apply Filter.liminf_le_liminf (Eventually.of_forall fun n => ballInf_anti F n ?_)
  intro p hp
  rw [Metric.mem_ball] at hp hq' ⊢
  have h2 : (((2 * k + 1 : ℕ) : ℝ) + 1) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  rw [h2] at hp
  calc dist p q ≤ dist p q' + dist q' q := dist_triangle _ _ _
    _ < 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) := add_lt_add hp hq'
    _ = 1 / ((k : ℝ) + 1) := by field_simp; ring

 
def gammaLower (F : ℕ → ℂ × ℂ → EReal) : LSCFun :=
  ⟨gammaLowerFun F, lowerSemicontinuous_gammaLowerFun F⟩

 
def openInf (F : ℕ → ℂ × ℂ → EReal) (n : ℕ) (O : Set (ℂ × ℂ)) : EReal :=
  ⨅ p ∈ O, F n p

 


theorem iInf_compact_gammaLowerFun (F : ℕ → ℂ × ℂ → EReal) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) :
    ⨅ q ∈ K, gammaLowerFun F q =
      ⨆ j : ℕ, liminf (fun n => openInf F n (Metric.thickening (1 / ((j : ℝ) + 1)) K))
        atTop := by
  apply le_antisymm
  · rcases K.eq_empty_or_nonempty with hKe | hKne
    · subst hKe
      refine le_trans ?_ (le_iSup _ 0)
      simp [openInf, Metric.thickening_empty]
    apply le_of_forall_lt_imp_le_of_dense
    intro t ht
    have hq : ∀ q ∈ K, ∃ k : ℕ, ∀ᶠ n in atTop, t < ballInf F n q (1 / ((k : ℝ) + 1)) := by
      intro q hqK
      have h1 : t < gammaLowerFun F q := lt_of_lt_of_le ht (iInf₂_le q hqK)
      obtain ⟨k, hk⟩ := lt_iSup_iff.1 h1
      exact ⟨k, eventually_lt_of_lt_liminf hk⟩
    choose! kq hkq using hq
    let r : ℂ × ℂ → ℝ := fun q => 1 / ((kq q : ℝ) + 1)
    have hr : ∀ q, 0 < r q := fun q => by positivity
    obtain ⟨s, hsK, hcover⟩ := hK.elim_nhds_subcover (fun q => Metric.ball q (r q / 2))
      (fun q _ => Metric.ball_mem_nhds q (half_pos (hr q)))
    have hsne : s.Nonempty := by
      obtain ⟨q, hq⟩ := hKne
      obtain ⟨q', hq', -⟩ := mem_iUnion₂.1 (hcover hq)
      exact ⟨q', hq'⟩
    let δ : ℝ := s.inf' hsne (fun q => r q / 2)
    have hδ : 0 < δ := (Finset.lt_inf'_iff hsne).2 fun q _ => half_pos (hr q)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
    have hev : ∀ᶠ n in atTop, ∀ q ∈ s, t < ballInf F n q (1 / ((kq q : ℝ) + 1)) :=
      (s.eventually_all).2 fun q hqs => hkq q (hsK q hqs)
    refine le_trans ?_ (le_iSup _ j)
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    filter_upwards [hev] with n hn
    refine le_iInf₂ fun p hp => ?_
    obtain ⟨y, hyK, hpy⟩ := Metric.mem_thickening_iff.1 hp
    obtain ⟨q, hqs, hyq⟩ := mem_iUnion₂.1 (hcover hyK)
    have hpq : p ∈ Metric.ball q (r q) := by
      rw [Metric.mem_ball] at hyq ⊢
      have hδq : δ ≤ r q / 2 := Finset.inf'_le _ hqs
      calc dist p q ≤ dist p y + dist y q := dist_triangle _ _ _
        _ < 1 / ((j : ℝ) + 1) + r q / 2 := add_lt_add hpy hyq
        _ ≤ r q := by linarith
    exact (hn q hqs).le.trans (iInf₂_le p hpq)
  · refine iSup_le fun j => le_iInf₂ fun q hqK => ?_
    refine le_trans ?_ (le_iSup _ j)
    apply Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)
    exact biInf_mono (Metric.ball_subset_thickening hqK _)

 

theorem forall_lt_iff_lt_iInf {u : ℂ × ℂ → EReal} (hu : LowerSemicontinuous u)
    {K : Set (ℂ × ℂ)} (hK : IsCompact K) (t : EReal) (ht : t ≠ ⊤) :
    (∀ q ∈ K, t < u q) ↔ t < ⨅ q ∈ K, u q := by
  constructor
  · intro h
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · subst hKe
      simpa using lt_top_iff_ne_top.2 ht
    obtain ⟨a, haK, hmin⟩ := (hu.lowerSemicontinuousOn K).exists_isMinOn hKne hK
    exact lt_of_lt_of_le (h a haK) (le_iInf₂ fun q hq => hmin hq)
  · intro h q hq
    exact lt_of_lt_of_le h (iInf₂_le q hq)

 

theorem measurable_lscFun_of_tests [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {X : Type*} [MeasurableSpace X] (G : X → LSCFun)
    (hHit : ∀ O : Set (ℂ × ℂ), IsOpen O → ∀ r : ℚ,
      MeasurableSet {x | ∃ q ∈ O, (G x).1 q < (((r : ℝ) : EReal))})
    (hMiss : ∀ K : Set (ℂ × ℂ), IsCompact K → ∀ r : ℚ,
      MeasurableSet {x | ∀ q ∈ K, (((r : ℝ) : EReal)) < (G x).1 q}) :
    Measurable G := by
  obtain ⟨B, S, hBc, hSc, hBb, hSk, -, ht⟩ := LscTop.exists_tests_eq_generateFrom
  have hsc : SecondCountableTopology LSCFun := inferInstance
  have hborel := borel_eq_generateFrom_of_subbasis ht
  have hm : (‹MeasurableSpace LSCFun› : MeasurableSpace LSCFun) =
      MeasurableSpace.generateFrom (Uniqueness.Toolkit.CountableBase.Tests B S) :=
    (BorelSpace.measurable_eq (α := LSCFun)).trans hborel
  have hgen : @Measurable X LSCFun _
      (MeasurableSpace.generateFrom (Uniqueness.Toolkit.CountableBase.Tests B S)) G := by
    apply measurable_generateFrom
    rintro U (⟨⟨⟨O, hO⟩, r⟩, rfl⟩ | ⟨⟨⟨K, hK⟩, r⟩, rfl⟩)
    · exact hHit O (hBb.isOpen hO) r
    · exact hMiss K (hSk K hK) r
  exact hgen.mono le_rfl hm.le

 
theorem iInf_open_eq_iInf_ballFamily {u : ℂ × ℂ → EReal} {O : Set (ℂ × ℂ)}
    (hO : IsOpen O) :
    ⨅ q ∈ O, u q = ⨅ (j : ℕ × ℕ) (_ : ballFamily j ⊆ O), ⨅ q ∈ ballFamily j, u q := by
  apply le_antisymm
  · exact le_iInf₂ fun j hj => biInf_mono hj
  · refine le_iInf₂ fun q hq => ?_
    obtain ⟨j, hqj, hjO⟩ := exists_ballFamily hO hq
    exact iInf₂_le_of_le j hjO (iInf₂_le q hqj)

 

theorem measurable_gammaLower [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    {X : Type*} [MeasurableSpace X] (F : X → ℕ → ℂ × ℂ → EReal)
    (hF : ∀ n (O : Set (ℂ × ℂ)), IsOpen O → Measurable fun x => openInf (F x) n O) :
    Measurable fun x => gammaLower (F x) := by
  have hcomp : ∀ K : Set (ℂ × ℂ), IsCompact K →
      Measurable fun x => ⨅ q ∈ K, gammaLowerFun (F x) q := by
    intro K hK
    simp_rw [iInf_compact_gammaLowerFun _ hK]
    exact Measurable.iSup fun j => Measurable.liminf fun n =>
      hF n _ Metric.isOpen_thickening
  apply measurable_lscFun_of_tests
  · intro O hO r
    have h : {x | ∃ q ∈ O, (gammaLower (F x)).1 q < (((r : ℝ) : EReal))} =
        (fun x => ⨅ q ∈ O, gammaLowerFun (F x) q) ⁻¹' Iio (((r : ℝ) : EReal)) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Iio, iInf_lt_iff, exists_prop]
      rfl
    rw [h]
    have hm : Measurable fun x => ⨅ q ∈ O, gammaLowerFun (F x) q := by
      simp_rw [iInf_open_eq_iInf_ballFamily (u := gammaLowerFun _) hO]
      refine Measurable.iInf fun j => ?_
      by_cases hj : ballFamily j ⊆ O
      · simp only [hj, iInf_pos]
        exact hcomp _ (isCompact_ballFamily j)
      · simp only [hj, iInf_false]
        exact measurable_const
    exact hm measurableSet_Iio
  · intro K hK r
    have h : {x | ∀ q ∈ K, (((r : ℝ) : EReal)) < (gammaLower (F x)).1 q} =
        (fun x => ⨅ q ∈ K, gammaLowerFun (F x) q) ⁻¹' Ioi (((r : ℝ) : EReal)) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Ioi]
      exact forall_lt_iff_lt_iInf (lowerSemicontinuous_gammaLowerFun (F x)) hK _
        (EReal.coe_ne_top _)
    rw [h]
    exact hcomp K hK measurableSet_Ioi

end SupercriticalLQGUniqueness.B2.PfeAxioms
