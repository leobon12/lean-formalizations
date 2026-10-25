import SupercriticalLQGUniqueness.B2.WeakStrong.Key
import SupercriticalLQGUniqueness.Frozen.WeakLQGMetric_unique
import SupercriticalLQGUniqueness.B2.Strong.Annulus

 





















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn ofCont addFun addConst IsGFFPlusCont affineComp circleAvg restrictTo
  affinePt)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

 
def powIoi (b : Set.Ioi (0 : ℝ)) (n : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(b : ℝ) ^ n, Set.mem_Ioi.mpr (pow_pos b.2 n)⟩

 
def mulIoi (b c : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(b : ℝ) * c, Set.mem_Ioi.mpr (mul_pos b.2 c.2)⟩

 
def oneIoi : Set.Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩

 
def unitAnnulus : EuclideanAnnulus := ⟨(0, (1, 2)), one_pos, one_lt_two⟩

 
theorem dilMetric_dilMetric_apply (D : DistC → LSCMetric) (Q : ℝ) (b β : Set.Ioi (0 : ℝ))
    (h : DistC) (p : ℂ × ℂ) :
    dilMetric (dilMetric D Q b) Q β h p = dilMetric D Q (mulIoi β b) h p := by
  simp only [dilMetric_apply]
  rw [dilField_dilField Q b.2 β.2]
  simp only [mulIoi, smul_smul, mul_inv_rev]

theorem dilMetric_one_apply (D : DistC → LSCMetric) (Q : ℝ) (h : DistC) (p : ℂ × ℂ) :
    dilMetric D Q oneIoi h p = D h p := by
  simp only [dilMetric_apply, oneIoi, dilField_one, inv_one, one_smul]

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

 
theorem exists_dilConst (hQ : IsLFPPExponent ξ Q) (hD : IsWeakLQGMetric ξ Q D)
    (b : Set.Ioi (0 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ,
          (dilMetric D Q b (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v) :=
  weakLQGMetric_unique ξ Q hQ _ _ (isWeakLQGMetric_dilMetric hD b) hD

 

theorem dilMetric_pow_of_dilConst {b : Set.Ioi (0 : ℝ)} {C : ℝ} (hC0 : 0 < C)
    (hC : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (dilMetric D Q b (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v)) :
    ∀ n : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (dilMetric D Q (powIoi b n) (h ω)).1 (u, v) =
          ENNReal.ofReal (C ^ n) * (D (h ω)).1 (u, v) := by
  intro n
  induction n with
  | zero =>
    intro Ω _ P _ h _
    refine Eventually.of_forall fun ω u v => ?_
    have e : powIoi b 0 = oneIoi := Subtype.ext (pow_zero _)
    rw [e, pow_zero, ENNReal.ofReal_one, one_mul]
    exact dilMetric_one_apply D Q (h ω) (u, v)
  | succ n ih =>
    intro Ω _ P _ h hh
    have hg := isGFFPlusCont_dilField hh Q (powIoi b n).2
    filter_upwards [hC P _ hg, ih P h hh] with ω h₁ h₂ u v
    have e : powIoi b (n + 1) = mulIoi (powIoi b n) b := Subtype.ext (pow_succ _ _)
    rw [e, ← dilMetric_dilMetric_apply]
    change dilMetric D Q b (dilField Q (powIoi b n) (h ω)) _ = _
    rw [h₁, pow_succ, ENNReal.ofReal_mul (pow_nonneg hC0.le _), mul_comm (ENNReal.ofReal (C ^ n)),
      mul_assoc]
    congr 1
    exact h₂ u v

theorem exists_pow_mul_gt {C : ℝ} (hC : 1 < C) {Y : ℝ≥0∞} (hY : 0 < Y) (M : ℝ) :
    ∃ n : ℕ, ENNReal.ofReal M < ENNReal.ofReal (C ^ n) * Y := by
  by_cases hYt : Y = ⊤
  · refine ⟨0, ?_⟩
    rw [hYt, pow_zero, ENNReal.ofReal_one, one_mul]
    exact ENNReal.ofReal_lt_top
  · have hy : 0 < Y.toReal := ENNReal.toReal_pos hY.ne' hYt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / Y.toReal) hC
    refine ⟨n, ?_⟩
    have hM : M < C ^ n * Y.toReal := (div_lt_iff₀ hy).1 hn
    rw [← ENNReal.ofReal_toReal hYt, ← ENNReal.ofReal_mul (pow_nonneg (by linarith) _)]
    exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos (pow_pos (by linarith) _) hy)).2 hM

theorem exists_pow_mul_lt {C : ℝ} (hC0 : 0 < C) (hC : C < 1) {Y : ℝ≥0∞} (hY : Y < ⊤) {m : ℝ}
    (hm : 0 < m) : ∃ n : ℕ, ENNReal.ofReal (C ^ n) * Y < ENNReal.ofReal m := by
  have hy : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hm (by linarith : (0 : ℝ) < Y.toReal + 1)) hC
  refine ⟨n, ?_⟩
  have hCn : 0 ≤ C ^ n := pow_nonneg hC0.le _
  have hlt : C ^ n * Y.toReal < m := by
    have h1 : C ^ n * (Y.toReal + 1) < m := (lt_div_iff₀ (by linarith)).1 hn
    nlinarith
  rw [← ENNReal.ofReal_toReal hY.ne, ← ENNReal.ofReal_mul hCn]
  exact (ENNReal.ofReal_lt_ofReal_iff hm).2 hlt

 

theorem const_eq_one_of_dilConst (hD : IsWeakLQGMetric ξ Q D) {b : Set.Ioi (0 : ℝ)} {C : ℝ}
    (hC0 : 0 < C)
    (hC : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (dilMetric D Q b (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k : Ω → DistC}
    (hk : IsNormalizedWholePlaneGFF k P) : C = 1 := by
  set A := unitAnnulus
  have hplus : IsGFFPlusCont k P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hk.1
  have hmeas : Measurable k := hk.1.measurable
  have hpow := dilMetric_pow_of_dilConst hC0 hC
  set Y : Ω → ℝ≥0∞ := fun ω => normAcross ξ Q D A oneIoi (k ω)
  set Z : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (C ^ n) * Y ω
  have hT := (tight_normAcross hD hk A).1
  
  have hZ : ∀ n : ℕ, Z n =ᵐ[P] (normAcross ξ Q D A (divIoi oneIoi (powIoi b n))) ∘
      fun ω => B2.Strong.rescaledField (k ω) (powIoi b n) := by
    intro n
    filter_upwards [ae_normalized_dilMetric hD hk (powIoi b n) oneIoi, hpow n P k hplus]
      with ω hK hP
    have hc0 : ENNReal.ofReal (C ^ n) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hC0 n)).ne'
    have hx := (hK A).1
    rw [Uniqueness.Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale (D (k ω)) _ _ hc0
      ENNReal.ofReal_ne_top hP] at hx
    rw [Function.comp_apply, ← hx]
    simp only [Z, Y, normAcross]
    ring
  have hlaw : ∀ n : ℕ, P.map (Z n) =
      P.map (fun ω => normAcross ξ Q D A (divIoi oneIoi (powIoi b n)) (k ω)) := by
    intro n
    rw [Measure.map_congr (hZ n)]
    exact map_comp_eq_of_map_eq ((B2.Strong.measurable_rescaledField _).comp hmeas) hmeas
      (LQGMetric.CircleAvg.map_affine_sub_circleAvg (isNormalizedWholePlaneGFF_iff_old.mp hk)
        (powIoi b n).2 0) (measurable_normAcross hD.1 A _)
  have hZm : ∀ n, AEMeasurable (Z n) P := fun n =>
    (((measurable_normAcross hD.1 A _).comp
      ((B2.Strong.measurable_rescaledField _).comp hmeas)).aemeasurable).congr (hZ n).symm
  have hZT : IsTwoSidedTight P Z :=
    isTwoSidedTight_of_map_eq_index P Z _ hT _ hZm hlaw
  obtain ⟨M, hM, hbd⟩ := hZT.2 (1 / 4) (by norm_num)
  have hYpos : ∀ ω, 0 < Y ω := fun ω =>
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr
      (mul_pos (Real.rpow_pos_of_pos oneIoi.2 _) (Real.exp_pos _))).ne'
      (B2.Strong.acrossDist_pos _ _).ne'
  have hYfin : ∀ᵐ ω ∂P, Y ω < ⊤ :=
    Uniqueness.OptimalConstants.Determinism.ae_lt_top_of_twoSidedTight P _ hT oneIoi
  have hquarter : ENNReal.ofReal (1 / 4) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
  rcases lt_trichotomy C 1 with hlt | heq | hgt
  · 
    set T : ℕ → Set Ω := fun n => {ω | Z n ω < ENNReal.ofReal M⁻¹}
    have hmono : Monotone T := by
      intro n m hnm ω (hω : Z n ω < _)
      show Z m ω < _
      refine lt_of_le_of_lt (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (pow_le_pow_of_le_one hC0.le hlt.le hnm)) _) hω
    have hnull : P (⋃ n, T n)ᶜ = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hYfin)
      by_contra hfin
      obtain ⟨n, hn⟩ := exists_pow_mul_lt hC0 hlt (not_not.1 hfin) (inv_pos.mpr hM)
      exact hω (mem_iUnion.2 ⟨n, hn⟩)
    have hone : 1 ≤ P (⋃ n, T n) :=
      calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
        _ ≤ P (⋃ n, T n) + P (⋃ n, T n)ᶜ := by
          rw [← union_compl_self (⋃ n, T n)]; exact measure_union_le _ _
        _ = P (⋃ n, T n) := by rw [hnull, add_zero]
    have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
    have : P (⋃ n, T n) ≤ ENNReal.ofReal (1 / 4) :=
      le_of_tendsto' hlim fun n => (hbd n).2
    exact absurd (hone.trans this) (not_le.2 hquarter)
  · exact heq
  · 
    set S : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal M < Z n ω}
    have hmono : Monotone S := by
      intro n m hnm ω (hω : _ < Z n ω)
      show _ < Z m ω
      exact lt_of_lt_of_le hω (mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (pow_le_pow_right₀ hgt.le hnm)) _)
    have huniv : (⋃ n, S n) = univ := by
      refine eq_univ_of_forall fun ω => mem_iUnion.2 ?_
      exact exists_pow_mul_gt hgt (hYpos ω) M
    have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
    have : P (⋃ n, S n) ≤ ENNReal.ofReal (1 / 4) :=
      le_of_tendsto' hlim fun n => (hbd n).1
    rw [huniv, measure_univ] at this
    exact absurd this (not_le.2 hquarter)

end SupercriticalLQGUniqueness.B2.WeakStrong
