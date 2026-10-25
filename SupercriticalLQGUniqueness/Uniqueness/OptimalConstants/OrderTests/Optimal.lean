import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.OrderTests
open LQGMetric (DistC)

def basis : Set (Set (ℂ × ℂ)) := TopologicalSpace.countableBasis (ℂ × ℂ)
theorem basis_countable : basis.Countable := TopologicalSpace.countable_countableBasis _
theorem basis_isBasis : TopologicalSpace.IsTopologicalBasis basis :=
  TopologicalSpace.isBasis_countableBasis _

def basisInf (D : LSCMetric) (U : Set (ℂ × ℂ)) : ℝ≥0∞ :=
  ⨅ q ∈ U, D q

theorem allPairs_le_iff_basisInf_le (D E : LSCMetric) (a : ℝ≥0∞)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    (∀ q : ℂ × ℂ, D q ≤ a * E q) ↔
      ∀ U ∈ basis, basisInf D U ≤ a * basisInf E U := by
  constructor
  · intro h U hU
    unfold basisInf
    rw [ENNReal.mul_iInf_of_ne ha0 hat]
    simp_rw [ENNReal.mul_iInf_of_ne ha0 hat]
    exact iInf_mono fun q => iInf_mono fun hq => h q
  · intro h q
    by_contra hq
    have hlt : a * E q < D q := lt_of_not_ge hq
    obtain ⟨t, ht1, ht2⟩ := exists_between hlt
    have hopen : IsOpen {x : ℂ × ℂ | t < D x} :=
      D.lowerSemicontinuous.isOpen_preimage t
    obtain ⟨U, hU, hqU, hUsub⟩ := basis_isBasis.exists_subset_of_mem_open ht2 hopen
    have hInft : t ≤ basisInf D U := by
      unfold basisInf
      exact le_iInf fun x => le_iInf fun hx => (hUsub hx).le
    have hEin : basisInf E U ≤ E q := by
      unfold basisInf
      exact iInf₂_le q hqU
    have hcmp := h U hU
    exact (not_le_of_gt ht1) (hInft.trans (hcmp.trans (mul_le_mul_right hEin a)))

theorem measurableSet_allPairs_le (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) (a : ℝ≥0∞)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    MeasurableSet {g : DistC | ∀ q : ℂ × ℂ, D g q ≤ a * E g q} := by
  have hEq : {g : DistC | ∀ q : ℂ × ℂ, D g q ≤ a * E g q} =
      ⋂ U ∈ basis, {g : DistC | basisInf (D g) U ≤ a * basisInf (E g) U} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
    exact allPairs_le_iff_basisInf_le (D g) (E g) a ha0 hat
  rw [hEq]
  apply MeasurableSet.biInter basis_countable
  intro U hU
  have hO : IsOpen U := TopologicalSpace.isOpen_of_mem_countableBasis hU
  have hD' : Measurable fun g : DistC => basisInf (D g) U :=
    (LSCMetric.measurable_iInf_of_isOpen hO).comp hD
  have hE' : Measurable fun g : DistC => basisInf (E g) U :=
    (LSCMetric.measurable_iInf_of_isOpen hO).comp hE
  exact measurableSet_le hD' (measurable_const.mul hE')


 
def upperOrder (D E : LSCMetric) : ℝ≥0∞ := by
  classical
  exact ⨅ q : ℚ, if 0 < q ∧ (∀ p : ℂ × ℂ,
      E p ≤ ENNReal.ofReal (q : ℝ) * D p)
    then ENNReal.ofReal (q : ℝ) else ⊤

 
def lowerOrder (D E : LSCMetric) : ℝ≥0∞ := by
  classical
  exact ⨆ q : ℚ, if 0 < q ∧ (∀ p : ℂ × ℂ,
      ENNReal.ofReal (q : ℝ) * D p ≤ E p)
    then ENNReal.ofReal (q : ℝ) else 0

theorem measurable_upperOrder (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) :
    Measurable fun g : DistC => upperOrder (D g) (E g) := by
  unfold upperOrder
  apply Measurable.iInf
  intro q
  by_cases hq : 0 < q
  · have hq0 : ENNReal.ofReal (q : ℝ) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by exact_mod_cast hq)).ne'
    have hset : MeasurableSet {g : DistC | 0 < q ∧
        (∀ p : ℂ × ℂ, E g p ≤ ENNReal.ofReal (q : ℝ) * D g p)} := by
      simpa only [hq, true_and] using
        measurableSet_allPairs_le E D hE hD _ hq0 ENNReal.ofReal_ne_top
    exact Measurable.ite hset measurable_const measurable_const
  · simpa only [hq, false_and, ↓reduceIte] using
      (measurable_const : Measurable fun _ : DistC => (⊤ : ℝ≥0∞))

theorem measurableSet_allPairs_mul_le (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) (a : ℝ≥0∞)
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    MeasurableSet {g : DistC | ∀ p : ℂ × ℂ, a * D g p ≤ E g p} := by
  have hinv0 : a⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hat
  have hinvt : a⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr ha0
  have hEq : {g : DistC | ∀ p : ℂ × ℂ, a * D g p ≤ E g p} =
      {g : DistC | ∀ p : ℂ × ℂ, D g p ≤ a⁻¹ * E g p} := by
    ext g
    simp only [mem_ofPred_eq]
    exact forall_congr' fun p => ENNReal.mul_le_iff_le_inv ha0 hat
  rw [hEq]
  exact measurableSet_allPairs_le D E hD hE a⁻¹ hinv0 hinvt

theorem measurable_lowerOrder (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) :
    Measurable fun g : DistC => lowerOrder (D g) (E g) := by
  unfold lowerOrder
  apply Measurable.iSup
  intro q
  by_cases hq : 0 < q
  · have hq0 : ENNReal.ofReal (q : ℝ) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by exact_mod_cast hq)).ne'
    have hset : MeasurableSet {g : DistC | 0 < q ∧
        (∀ p : ℂ × ℂ, ENNReal.ofReal (q : ℝ) * D g p ≤ E g p)} := by
      simpa only [hq, true_and] using
        measurableSet_allPairs_mul_le D E hD hE _ hq0 ENNReal.ofReal_ne_top
    exact Measurable.ite hset measurable_const measurable_const
  · simpa only [hq, false_and, ↓reduceIte] using
      (measurable_const : Measurable fun _ : DistC => (0 : ℝ≥0∞))


theorem rat_pos_of_ennreal_pos {q : ℚ}
    (h : (0 : ℝ≥0∞) < ENNReal.ofReal (q : ℝ)) : 0 < q := by
  have hr : (0 : ℝ) < (q : ℝ) := ENNReal.ofReal_pos.mp h
  exact_mod_cast hr

theorem ennreal_eq_inf_rational_above (x : ℝ≥0∞) :
    x = ⨅ q : ℚ, if 0 < q ∧ x ≤ ENNReal.ofReal (q : ℝ)
      then ENNReal.ofReal (q : ℝ) else ⊤ := by
  classical
  refine le_antisymm ?_ ?_
  · apply le_iInf
    intro q
    split_ifs with h
    · exact h.2
    · exact le_top
  · by_contra hn
    have hlt : x < ⨅ q : ℚ, if 0 < q ∧ x ≤ ENNReal.ofReal (q : ℝ)
        then ENNReal.ofReal (q : ℝ) else ⊤ := lt_of_not_ge hn
    obtain ⟨q, hq0, hxq, hqI⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    have hxq' : x < ENNReal.ofReal (q : ℝ) := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hxq
    have hqI' : ENNReal.ofReal (q : ℝ) <
        (⨅ q : ℚ, if 0 < q ∧ x ≤ ENNReal.ofReal (q : ℝ)
          then ENNReal.ofReal (q : ℝ) else ⊤) := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hqI
    have hqpos := rat_pos_of_ennreal_pos (lt_of_le_of_lt bot_le hxq')
    have hIle : (⨅ q : ℚ, if 0 < q ∧ x ≤ ENNReal.ofReal (q : ℝ)
        then ENNReal.ofReal (q : ℝ) else ⊤) ≤ ENNReal.ofReal (q : ℝ) := by
      simpa [hqpos, hxq'.le] using
        (iInf_le (fun q : ℚ => if 0 < q ∧ x ≤ ENNReal.ofReal (q : ℝ)
          then ENNReal.ofReal (q : ℝ) else ⊤) q)
    exact (not_lt_of_ge hIle) hqI'

theorem ennreal_eq_sup_rational_below (x : ℝ≥0∞) :
    x = ⨆ q : ℚ, if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ x
      then ENNReal.ofReal (q : ℝ) else 0 := by
  classical
  refine le_antisymm ?_ ?_
  · by_contra hn
    have hlt : (⨆ q : ℚ, if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ x
        then ENNReal.ofReal (q : ℝ) else 0) < x := lt_of_not_ge hn
    obtain ⟨q, hq0, hIq, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    have hIq' : (⨆ q : ℚ, if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ x
        then ENNReal.ofReal (q : ℝ) else 0) < ENNReal.ofReal (q : ℝ) := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hIq
    have hqx' : ENNReal.ofReal (q : ℝ) < x := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hqx
    have hqpos := rat_pos_of_ennreal_pos (lt_of_le_of_lt bot_le hIq')
    have hIge : ENNReal.ofReal (q : ℝ) ≤
        (⨆ q : ℚ, if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ x
          then ENNReal.ofReal (q : ℝ) else 0) := by
      simpa [hqpos, hqx'.le] using
        (le_iSup (fun q : ℚ => if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ x
          then ENNReal.ofReal (q : ℝ) else 0) q)
    exact (not_lt_of_ge hIge) hIq'
  · apply iSup_le
    intro q
    split_ifs with h
    · exact h.2
    · exact bot_le


theorem upperOptimal_le_iff_allPairs
    {D E : LSCMetric} {c C : ℝ≥0∞} (hc : 0 < c)
    (hB : OptimalConstants.Ratios.BiLipBound D E c C)
    (hpair : ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair D u v) (a : ℝ≥0∞) :
    OptimalConstants.Ratios.upperOptimal D E ≤ a ↔ ∀ p : ℂ × ℂ, E p ≤ a * D p := by
  constructor
  · intro h p
    exact (OptimalConstants.Ratios.optimal_allPairs_of_biLipBound hc hB hpair p.1 p.2).2.trans
      (mul_le_mul_left h (D p))
  · intro h
    have hB' : OptimalConstants.Ratios.BiLipBound D E c a := by
      intro z w
      exact ⟨(hB z w).1, h (z, w)⟩
    exact (OptimalConstants.Ratios.optimal_mem_Icc_of_biLipBound hB').2

theorem le_lowerOptimal_iff_allPairs
    {D E : LSCMetric} {c C : ℝ≥0∞} (hc : 0 < c)
    (hB : OptimalConstants.Ratios.BiLipBound D E c C)
    (hpair : ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair D u v) (a : ℝ≥0∞) :
    a ≤ OptimalConstants.Ratios.lowerOptimal D E ↔ ∀ p : ℂ × ℂ, a * D p ≤ E p := by
  constructor
  · intro h p
    exact (mul_le_mul_left h (D p)).trans
      (OptimalConstants.Ratios.optimal_allPairs_of_biLipBound hc hB hpair p.1 p.2).1
  · intro h
    have hB' : OptimalConstants.Ratios.BiLipBound D E a C := by
      intro z w
      exact ⟨h (z, w), (hB z w).2⟩
    exact (OptimalConstants.Ratios.optimal_mem_Icc_of_biLipBound hB').1

 
theorem optimal_eq_order_of_biLip
    {D E : LSCMetric} {c C : ℝ≥0∞} (hc : 0 < c)
    (hB : OptimalConstants.Ratios.BiLipBound D E c C)
    (hpair : ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair D u v) :
    OptimalConstants.Ratios.lowerOptimal D E = lowerOrder D E ∧
      OptimalConstants.Ratios.upperOptimal D E = upperOrder D E := by
  classical
  constructor
  · calc
      OptimalConstants.Ratios.lowerOptimal D E =
          ⨆ q : ℚ, if 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ OptimalConstants.Ratios.lowerOptimal D E
            then ENNReal.ofReal (q : ℝ) else 0 :=
          ennreal_eq_sup_rational_below _
      _ = lowerOrder D E := by
        unfold lowerOrder
        congr 1
        funext q
        have hiff :
            (0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ OptimalConstants.Ratios.lowerOptimal D E) ↔
            (0 < q ∧ ∀ p : ℂ × ℂ, ENNReal.ofReal (q : ℝ) * D p ≤ E p) :=
          and_congr_right fun _ => le_lowerOptimal_iff_allPairs hc hB hpair _
        by_cases hp : 0 < q ∧ ENNReal.ofReal (q : ℝ) ≤ OptimalConstants.Ratios.lowerOptimal D E
        · simp [hp, hiff.mp hp]
        · have hp' := mt hiff.mpr hp
          simp only [ite_eq_right hp, ite_eq_right hp']
  · calc
      OptimalConstants.Ratios.upperOptimal D E =
          ⨅ q : ℚ, if 0 < q ∧ OptimalConstants.Ratios.upperOptimal D E ≤ ENNReal.ofReal (q : ℝ)
            then ENNReal.ofReal (q : ℝ) else ⊤ :=
          ennreal_eq_inf_rational_above _
      _ = upperOrder D E := by
        unfold upperOrder
        congr 1
        funext q
        have hiff :
            (0 < q ∧ OptimalConstants.Ratios.upperOptimal D E ≤ ENNReal.ofReal (q : ℝ)) ↔
            (0 < q ∧ ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal (q : ℝ) * D p) :=
          and_congr_right fun _ => upperOptimal_le_iff_allPairs hc hB hpair _
        by_cases hp : 0 < q ∧ OptimalConstants.Ratios.upperOptimal D E ≤ ENNReal.ofReal (q : ℝ)
        · simp [hp, hiff.mp hp]
        · have hp' := mt hiff.mpr hp
          simp only [ite_eq_right hp, ite_eq_right hp']


 

theorem aeMeasurable_optima (P : Measure DistC) (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) {c C : ℝ≥0∞} (hc : 0 < c)
    (hEBL : ∀ᵐ g ∂P, OptimalConstants.Ratios.BiLipBound (D g) (E g) c C)
    (hFinitePair : ∀ᵐ g ∂P, ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D g) u v) :
    AEMeasurable (fun g : DistC => OptimalConstants.Ratios.lowerOptimal (D g) (E g)) P ∧
      AEMeasurable (fun g : DistC => OptimalConstants.Ratios.upperOptimal (D g) (E g)) P := by
  have hEqLower : (fun g : DistC => lowerOrder (D g) (E g)) =ᵐ[P]
      (fun g : DistC => OptimalConstants.Ratios.lowerOptimal (D g) (E g)) := by
    filter_upwards [hEBL, hFinitePair] with g hb hp
    exact (optimal_eq_order_of_biLip hc hb hp).1.symm
  have hEqUpper : (fun g : DistC => upperOrder (D g) (E g)) =ᵐ[P]
      (fun g : DistC => OptimalConstants.Ratios.upperOptimal (D g) (E g)) := by
    filter_upwards [hEBL, hFinitePair] with g hb hp
    exact (optimal_eq_order_of_biLip hc hb hp).2.symm
  exact ⟨((measurable_lowerOrder D E hD hE).aemeasurable).congr hEqLower,
    ((measurable_upperOrder D E hD hE).aemeasurable).congr hEqUpper⟩

 
theorem measurable_completed_optima (P : Measure DistC) (D E : DistC → LSCMetric)
    (hD : Measurable D) (hE : Measurable E) {c C : ℝ≥0∞} (hc : 0 < c)
    (hEBL : ∀ᵐ g ∂P, OptimalConstants.Ratios.BiLipBound (D g) (E g) c C)
    (hFinitePair : ∀ᵐ g ∂P, ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D g) u v) :
    @Measurable (NullMeasurableSpace DistC P) ℝ≥0∞ _ _
      (fun g => OptimalConstants.Ratios.lowerOptimal (D g) (E g)) ∧
    @Measurable (NullMeasurableSpace DistC P) ℝ≥0∞ _ _
      (fun g => OptimalConstants.Ratios.upperOptimal (D g) (E g)) := by
  obtain ⟨hl, hu⟩ := aeMeasurable_optima P D E hD hE hc hEBL hFinitePair
  exact ⟨hl.nullMeasurable.measurable', hu.nullMeasurable.measurable'⟩


 

theorem ae_allPairs_of_constant_nodes (P : Measure DistC)
    (D E : DistC → LSCMetric) {c C cMinus cPlus : ℝ≥0∞}
    (hc : 0 < c)
    (hEBL : ∀ᵐ g ∂P, OptimalConstants.Ratios.BiLipBound (D g) (E g) c C)
    (hFinitePair : ∀ᵐ g ∂P, ∃ u v : ℂ, OptimalConstants.Ratios.RatioPair (D g) u v)
    (hMinusConstNode : ∀ᵐ g ∂P, OptimalConstants.Ratios.lowerOptimal (D g) (E g) = cMinus)
    (hPlusConstNode : ∀ᵐ g ∂P, OptimalConstants.Ratios.upperOptimal (D g) (E g) = cPlus) :
    ∀ᵐ g ∂P, ∀ z w : ℂ,
      cMinus * D g (z, w) ≤ E g (z, w) ∧
      E g (z, w) ≤ cPlus * D g (z, w) := by
  exact OptimalConstants.Ratios.ae_allPairs_of_ae_optima P D E hc hEBL hFinitePair
    hMinusConstNode hPlusConstNode


 

theorem ae_const_of_zero_one_rat_cuts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ≥0∞) (hX : Measurable X)
    {c C : ℝ≥0∞} (hc : 0 < c) (hC : C < ⊤)
    (hBounds : ∀ᵐ ω ∂P, c ≤ X ω ∧ X ω ≤ C)
    (hCuts : ∀ q : ℚ, 0 < q →
      P {ω : Ω | ENNReal.ofReal (q : ℝ) < X ω} = 0 ∨
      P {ω : Ω | ENNReal.ofReal (q : ℝ) < X ω} = 1) :
    ∃ L : ℝ≥0∞, 0 < L ∧ L < ⊤ ∧ ∀ᵐ ω ∂P, X ω = L := by
  classical
  let G : ℚ → Set Ω := fun q => {ω | ENNReal.ofReal (q : ℝ) < X ω}
  have hG (q : ℚ) : MeasurableSet (G q) :=
    measurableSet_lt measurable_const hX
  let L : ℝ≥0∞ := ⨆ q : ℚ,
    if 0 < q ∧ P (G q) = 1 then ENNReal.ofReal (q : ℝ) else 0
  have hLower : ∀ᵐ ω ∂P, ∀ q : ℚ,
      0 < q ∧ P (G q) = 1 → ENNReal.ofReal (q : ℝ) < X ω := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < q ∧ P (G q) = 1
    · filter_upwards [(mem_ae_iff_prob_eq_one (hG q)).mpr hq.2] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun ω h => (hq h).elim
  have hUpper : ∀ᵐ ω ∂P, ∀ q : ℚ,
      0 < q ∧ P (G q) ≠ 1 → X ω ≤ ENNReal.ofReal (q : ℝ) := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < q ∧ P (G q) ≠ 1
    · have hzero : P (G q) = 0 :=
        (hCuts q hq.1).resolve_right hq.2
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with ω hω _
      exact le_of_not_gt hω
    · exact Filter.Eventually.of_forall fun ω h => (hq h).elim
  have hEq : ∀ᵐ ω ∂P, X ω = L := by
    filter_upwards [hLower, hUpper] with ω hlow hupp
    have hLle : L ≤ X ω := by
      apply iSup_le
      intro q
      by_cases hq : 0 < q ∧ P (G q) = 1
      · simp only [hq]
        exact (hlow q hq).le
      · simp only [hq, ↓reduceIte]
        exact bot_le
    refine le_antisymm ?_ hLle
    by_contra hn
    have hlt : L < X ω := lt_of_not_ge hn
    obtain ⟨q, hqnonneg, hLq, hqX⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hlt
    have hLq' : L < ENNReal.ofReal (q : ℝ) := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hLq
    have hqX' : ENNReal.ofReal (q : ℝ) < X ω := by
      simpa only [← ENNReal.ofNNReal_toNNReal] using hqX
    have hqpos := rat_pos_of_ennreal_pos (lt_of_le_of_lt bot_le hLq')
    by_cases hqone : P (G q) = 1
    · have hqle : ENNReal.ofReal (q : ℝ) ≤ L := by
        dsimp [L]
        simpa [hqpos, hqone] using
          (le_iSup (fun q : ℚ => if 0 < q ∧ P (G q) = 1
            then ENNReal.ofReal (q : ℝ) else 0) q)
      exact (not_lt_of_ge hqle) hLq'
    · exact (not_lt_of_ge (hupp q ⟨hqpos, hqone⟩)) hqX'
  obtain ⟨ω, hωEq, hωB⟩ := (hEq.and hBounds).exists
  refine ⟨L, ?_, ?_, hEq⟩
  · rw [← hωEq]
    exact hc.trans_le hωB.1
  · rw [← hωEq]
    exact hωB.2.trans_lt hC

end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.OrderTests
