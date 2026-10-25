import SupercriticalLQGUniqueness.B2.Median.MedianTransfer

 




set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 


theorem measure_open_interval_eq_zero_of_medians
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    {a b : ℝ≥0∞} (hab : a < b)
    (ha : IsMedian P Z a) (hb : IsMedian P Z b) :
    P {ω | a < Z ω ∧ Z ω < b} = 0 := by
  let A : Set Ω := {ω | Z ω ≤ a}
  let B : Set Ω := {ω | b ≤ Z ω}
  have hA : NullMeasurableSet A P :=
    ha.1.nullMeasurableSet_preimage measurableSet_Iic
  have hB : NullMeasurableSet B P :=
    ha.1.nullMeasurableSet_preimage measurableSet_Ici
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro ω hωA hωB
    exact (not_le_of_gt hab) (hωB.trans hωA)
  have hmass : (1 : ℝ≥0∞) ≤ P A + P B := by
    have hhalf : (1 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
      ENNReal.inv_two_add_inv_two.symm
    rw [hhalf]
    exact add_le_add ha.2.1 hb.2.2
  have hU : P (A ∪ B) = 1 := by
    apply le_antisymm
    · simpa only [measure_univ] using
        (measure_mono (subset_univ (A ∪ B)) : P (A ∪ B) ≤ P univ)
    · rw [measure_union₀ hB hAB.aedisjoint]
      exact hmass
  have hcomp : P (A ∪ B)ᶜ = 0 := by
    rw [measure_compl₀ (hA.union hB) (by rw [hU]; exact ENNReal.one_ne_top), hU]
    simp
  have hsub : {ω | a < Z ω ∧ Z ω < b} ⊆ (A ∪ B)ᶜ := by
    intro ω hω
    change ¬ (ω ∈ A ∨ ω ∈ B)
    exact not_or.mpr ⟨not_le.mpr hω.1, not_le.mpr hω.2⟩
  exact le_zero_iff.mp ((measure_mono hsub).trans_eq hcomp)

theorem eq_of_noGap_medians
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → 0 < P {ω | Z ω ≤ x} →
      0 < P {ω | x < Z ω ∧ Z ω < y})
    {a b : ℝ≥0∞} (ha : IsMedian P Z a) (hb : IsMedian P Z b) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpos : 0 < P {ω | Z ω ≤ a} :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) ha.2.1
    have hzero := measure_open_interval_eq_zero_of_medians P Z hab ha hb
    exact False.elim ((hng a b hab hpos).ne' hzero)
  · exact hab
  · have hpos : 0 < P {ω | Z ω ≤ b} :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) hb.2.1
    have hzero := measure_open_interval_eq_zero_of_medians P Z hab hb ha
    exact False.elim ((hng b a hab hpos).ne' hzero)

theorem eq_one_of_noGap_and_medians
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → 0 < P {ω | Z ω ≤ x} →
      0 < P {ω | x < Z ω ∧ Z ω < y})
    (C : ℝ) (hC : 0 < C)
    (hmed : IsMedian P Z 1)
    (hmedC : IsMedian P (fun ω => ENNReal.ofReal C * Z ω) 1) :
    C = 1 := by
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hscaled := isMedian_mul P (fun ω => c * Z ω) 1 c⁻¹
    (ENNReal.inv_ne_zero.mpr hcTop) (ENNReal.inv_ne_top.mpr hc0) hmedC
  have hmedInv : IsMedian P Z c⁻¹ := by
    have hfun : (fun ω => c⁻¹ * (c * Z ω)) = Z := by
      funext ω
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
    simpa only [hfun, mul_one] using hscaled
  have hInv : (1 : ℝ≥0∞) = c⁻¹ := eq_of_noGap_medians P Z hng hmed hmedInv
  have hc1 : c = 1 := by
    have := congrArg Inv.inv hInv
    simpa using this.symm
  exact ENNReal.ofReal_eq_one.mp hc1

 



theorem eq_of_noGap_finite_medians
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | Z ω ≤ x} → 0 < P {ω | x < Z ω ∧ Z ω < y})
    {a b : ℝ≥0∞} (haFin : a ≠ ∞) (hbFin : b ≠ ∞)
    (ha : IsMedian P Z a) (hb : IsMedian P Z b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hpos : 0 < P {ω | Z ω ≤ a} :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) ha.2.1
    have hzero := measure_open_interval_eq_zero_of_medians P Z hab ha hb
    exact False.elim ((hng a b hab hbFin hpos).ne' hzero)
  · exact hab
  · have hpos : 0 < P {ω | Z ω ≤ b} :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 2⁻¹) hb.2.1
    have hzero := measure_open_interval_eq_zero_of_medians P Z hab hb ha
    exact False.elim ((hng b a hab haFin hpos).ne' hzero)

theorem eq_one_of_noGap_finite_and_medians
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | Z ω ≤ x} → 0 < P {ω | x < Z ω ∧ Z ω < y})
    (C : ℝ) (hC : 0 < C)
    (hmed : IsMedian P Z 1)
    (hmedC : IsMedian P (fun ω => ENNReal.ofReal C * Z ω) 1) :
    C = 1 := by
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hscaled := isMedian_mul P (fun ω => c * Z ω) 1 c⁻¹
    (ENNReal.inv_ne_zero.mpr hcTop) (ENNReal.inv_ne_top.mpr hc0) hmedC
  have hmedInv : IsMedian P Z c⁻¹ := by
    have hfun : (fun ω => c⁻¹ * (c * Z ω)) = Z := by
      funext ω
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
    simpa only [hfun, mul_one] using hscaled
  have hInv : (1 : ℝ≥0∞) = c⁻¹ :=
    eq_of_noGap_finite_medians P Z hng (by norm_num)
      (ENNReal.inv_ne_top.mpr hc0) hmed hmedInv
  have hc1 : c = 1 := by
    have := congrArg Inv.inv hInv
    simpa using this.symm
  exact ENNReal.ofReal_eq_one.mp hc1

theorem measure_le_add_between_add_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞) (hZ : AEMeasurable Z P)
    {x y : ℝ≥0∞} (hxy : x < y) :
    P {ω | Z ω ≤ x} + P {ω | x < Z ω ∧ Z ω < y} +
      P {ω | y ≤ Z ω} = 1 := by
  let A : Set Ω := {ω | Z ω ≤ x}
  let C : Set Ω := {ω | x < Z ω ∧ Z ω < y}
  let B : Set Ω := {ω | y ≤ Z ω}
  have hC : NullMeasurableSet C P :=
    hZ.nullMeasurableSet_preimage measurableSet_Ioo
  have hdisj : Disjoint A C := by
    refine Set.disjoint_left.mpr ?_
    intro ω ha hc
    exact (not_lt.mpr ha) hc.1
  have hunion : A ∪ C = Bᶜ := by
    ext ω
    simp only [A, B, C, mem_union, mem_ofPred_eq, mem_compl_iff]
    constructor
    · intro h
      rcases h with h | h
      · exact not_le.mpr (lt_of_le_of_lt h hxy)
      · exact not_le.mpr h.2
    · intro h
      have hlt : Z ω < y := lt_of_not_ge h
      by_cases hx : Z ω ≤ x
      · exact Or.inl hx
      · exact Or.inr ⟨lt_of_not_ge hx, hlt⟩
  change P A + P C + P B = 1
  rw [← measure_union₀ hC hdisj.aedisjoint, hunion]
  have hB : NullMeasurableSet B P :=
    hZ.nullMeasurableSet_preimage measurableSet_Ici
  simpa [add_comm] using measure_add_measure_compl₀ hB

theorem measure_between_eq_zero_of_two_medians
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞) {x y : ℝ≥0∞} (hxy : x < y)
    (hx : IsMedian P Z x) (hy : IsMedian P Z y) :
    P {ω | x < Z ω ∧ Z ω < y} = 0 := by
  have h := measure_le_add_between_add_ge P Z hx.1 hxy
  have h' : (2⁻¹ : ℝ≥0∞) + P {ω | x < Z ω ∧ Z ω < y} + 2⁻¹ ≤ 1 :=
    (add_le_add (add_le_add hx.2.1 le_rfl) hy.2.2).trans h.le
  have hhalf : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := by
    simpa [one_div] using (ENNReal.add_halves (1 : ℝ≥0∞))
  rw [add_right_comm, hhalf] at h'
  have h'' : 1 + P {ω | x < Z ω ∧ Z ω < y} ≤ 1 + 0 := by
    simpa using h'
  exact le_antisymm ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp h'') bot_le

 

theorem median_eq_one_of_noGap_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | Z ω ≤ x} →
      0 < P {ω | x < Z ω ∧ Z ω < y})
    (hmed1 : IsMedian P Z 1) (m : ℝ≥0∞) (hmfin : m ≠ ∞)
    (hmedm : IsMedian P Z m) : m = 1 := by
  rcases lt_trichotomy m 1 with hlt | heq | hgt
  · have hzero := measure_between_eq_zero_of_two_medians P Z hlt hmedm hmed1
    have hpos := hng m 1 hlt ENNReal.one_ne_top
      ((ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top).trans_le hmedm.2.1)
    exact False.elim (hpos.ne' hzero)
  · exact heq
  · have hzero := measure_between_eq_zero_of_two_medians P Z hgt hmed1 hmedm
    have hlow : 0 < P {ω | Z ω ≤ (1 : ℝ≥0∞)} :=
      (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top).trans_le hmed1.2.1
    have hpos := hng 1 m hgt hmfin hlow
    exact False.elim (hpos.ne' hzero)

 

theorem eq_one_of_noGap_finite_and_scaled_medians
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | Z ω ≤ x} →
      0 < P {ω | x < Z ω ∧ Z ω < y})
    (C : ℝ) (hC : 0 < C)
    (hmed1 : IsMedian P Z 1)
    (hmedScaled : IsMedian P
      (fun ω => ENNReal.ofReal C * Z ω) 1) : C = 1 := by
  let c : ℝ≥0∞ := ENNReal.ofReal C
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hcTop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hci0 : c⁻¹ ≠ 0 := by simp [hcTop]
  have hciTop : c⁻¹ ≠ ∞ := by simp [hc0]
  have hmInv := isMedian_mul P (fun ω => c * Z ω) 1 c⁻¹
    hci0 hciTop hmedScaled
  have hmInv' : IsMedian P Z c⁻¹ := by
    simpa only [ENNReal.inv_mul_cancel_left hc0 hcTop, mul_one] using hmInv
  have hEq := median_eq_one_of_noGap_finite P Z hng hmed1 c⁻¹ hciTop hmInv'
  have hcEq : c = 1 := ENNReal.inv_eq_one.mp hEq
  have hreal := congrArg ENNReal.toReal hcEq
  simpa [c, ENNReal.toReal_ofReal hC.le] using hreal

 
theorem eq_one_of_noGap_finite_and_median_ofReal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ≥0∞)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | Z ω ≤ x} →
      0 < P {ω | x < Z ω ∧ Z ω < y})
    (C : ℝ) (hC : 0 < C)
    (hmed1 : IsMedian P Z 1)
    (hmedC : IsMedian P Z (ENNReal.ofReal C)) : C = 1 := by
  have he := eq_of_noGap_finite_medians P Z hng
    ENNReal.one_ne_top ENNReal.ofReal_ne_top hmed1 hmedC
  have hreal := congrArg ENNReal.toReal he
  simpa [ENNReal.toReal_ofReal hC.le] using hreal.symm

end SupercriticalLQGUniqueness.B2.Median
