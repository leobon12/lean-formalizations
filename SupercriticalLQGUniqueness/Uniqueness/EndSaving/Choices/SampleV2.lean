import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.QPosBridgeV2
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import LQGMetric.Papers.GM.S5.Prop43bGeo




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 

 

theorem weylScale_ge_exp_mul (D : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ x : ℂ, -M ≤ f x) (p : ℂ × ℂ) :
    ENNReal.ofReal (Real.exp (-(ξ * M))) * D p ≤ weylScale ξ f D p := by
  unfold weylScale
  refine le_iInf fun P => le_iInf fun L => le_iInf fun hcurve => le_iInf fun hunit =>
    le_iInf fun h0 => le_iInf fun hL => ?_
  have hL0 : 0 ≤ L := hcurve.1
  have hp : p = (P 0, P L) := by
    rw [h0, hL]
  have hdist : D p ≤ ENNReal.ofReal L := by
    have hvar := hunit (left_mem_Icc.mpr hL0) (right_mem_Icc.mpr hL0)
    rw [Set.inter_self, NNReal.coe_one, one_mul, sub_zero] at hvar
    have hle := eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.mpr hL0)
      (right_mem_Icc.mpr hL0)
    rw [hvar] at hle
    rw [hp]
    exact hle
  have hint : ENNReal.ofReal (Real.exp (-(ξ * M))) * ENNReal.ofReal L ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
    calc ENNReal.ofReal (Real.exp (-(ξ * M))) * ENNReal.ofReal L
        = ∫⁻ _t in Icc 0 L, ENNReal.ofReal (Real.exp (-(ξ * M))) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero]
      _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
          apply lintegral_mono
          intro t
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_left (hM (P t)) hξ
          linarith
  calc ENNReal.ofReal (Real.exp (-(ξ * M))) * D p
      ≤ ENNReal.ofReal (Real.exp (-(ξ * M))) * ENNReal.ofReal L := by gcongr
    _ ≤ _ := hint

 
theorem barrier_of_mul_le (D₁ D₂ : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hcTop : c ≠ ⊤) (hcomp : ∀ p : ℂ × ℂ, c * D₁ p ≤ D₂ p)
    (hB : BiLipschitz.Barrier.Barrier D₁) : BiLipschitz.Barrier.Barrier D₂ := by
  intro n₀ M
  obtain ⟨M', hM'⟩ : ∃ M' : ℕ, (M : ℝ≥0∞) ≤ c * M' := by
    obtain ⟨M', hM'⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top
      (ENNReal.natCast_ne_top M) hc0).ne
    refine ⟨M', ?_⟩
    have h1 : (M : ℝ≥0∞) / c ≤ M' := hM'.le
    calc (M : ℝ≥0∞) = c * ((M : ℝ≥0∞) / c) := (ENNReal.mul_div_cancel hc0 hcTop).symm
      _ ≤ c * M' := by gcongr
  obtain ⟨n, hn, hlt⟩ := hB n₀ M'
  refine ⟨n, hn, ?_⟩
  have hacross : c * acrossDist D₁ (BiLipschitz.Barrier.dyadicAnnulus n) ≤
      acrossDist D₂ (BiLipschitz.Barrier.dyadicAnnulus n) := by
    unfold acrossDist
    refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    calc c * (⨅ (x ∈ (BiLipschitz.Barrier.dyadicAnnulus n).innerBoundary)
          (y ∈ (BiLipschitz.Barrier.dyadicAnnulus n).outerBoundary), D₁ (x, y))
        ≤ c * D₁ (x, y) := by
          gcongr
          exact iInf₂_le_of_le x hx (iInf₂_le y hy)
      _ ≤ D₂ (x, y) := hcomp (x, y)
  calc (M : ℝ≥0∞) ≤ c * M' := hM'
    _ < c * acrossDist D₁ (BiLipschitz.Barrier.dyadicAnnulus n) :=
        ENNReal.mul_lt_mul_right hc0 hcTop hlt
    _ ≤ _ := hacross

 

 

structure RegularAt (D : DistC → LSCMetric) (ξ : ℝ) (g : DistC) : Prop where
  barrier : BiLipschitz.Barrier.Barrier (D g)
  length : (D g).IsLengthSpace
  weyl : ∀ f : C(ℂ, ℝ), weylScale ξ f (D g) = (D (LQGMetric.addFun g f)).1

 
theorem RegularAt.forget {D : DistC → LSCMetric} {ξ : ℝ} {g : DistC}
    (hg : RegularAt D ξ g) : Continuous (BiLipschitz.Barrier.forget (D g)) :=
  BiLipschitz.Barrier.continuous_forget_of_barrier _ hg.barrier hg.length

 
theorem RegularAt.continuousOn {D : DistC → LSCMetric} {ξ : ℝ} {g : DistC}
    (hg : RegularAt D ξ g) {P : ℝ → ℂ} {a b : ℝ} (hP : (D g).IsCurve P a b) :
    ContinuousOn P (Icc a b) :=
  BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hg.barrier hg.length hP

 
theorem testCont_bounded_below (φ : TestC) :
    ∃ M : ℝ, ∀ x : ℂ, -M ≤ LQGMetric.testCont φ x := by
  obtain ⟨C, hC⟩ := (φ.continuous.norm).bddAbove_range_of_hasCompactSupport
    φ.hasCompactSupport.norm
  refine ⟨C, fun x => ?_⟩
  have hx : ‖φ x‖ ≤ C := hC ⟨x, rfl⟩
  have habs : |φ x| ≤ C := by simpa [Real.norm_eq_abs] using hx
  exact (neg_le_of_abs_le habs)

 
theorem ae_regularAt_self {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, RegularAt D (ξ : ℝ) (h ω) := by
  have hQ : 0 < Q := EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1
  filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ P h hh, hD.2.1 P h hplus,
    hD.2.2.2.1 P h hplus] with ω hB hL hW
  exact ⟨hB, hL, hW⟩

 


theorem ae_regularAt_shift {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (φ : TestC) :
    ∀ᵐ ω ∂P, RegularAt D (ξ : ℝ)
      (LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) := by
  have hplusφ : LQGMetric.IsGFFPlusCont
      (fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)) P :=
    LQGMetric.GM.isGFFPlusCont_addFun_test hh.1 φ
  obtain ⟨M, hM⟩ := testCont_bounded_below φ
  filter_upwards [ae_regularAt_self hD P h hh, hD.2.1 P _ hplusφ,
    hD.2.2.2.1 P _ hplusφ] with ω hreg hL hW
  refine ⟨?_, hL, hW⟩
  apply barrier_of_mul_le (D (h ω)) _ (ENNReal.ofReal (Real.exp (-((ξ : ℝ) * M))))
    (by simpa using Real.exp_pos _) ENNReal.ofReal_ne_top _ hreg.barrier
  intro p
  have hge := weylScale_ge_exp_mul (D (h ω)) ξ ξ.property.le
    (LQGMetric.testCont φ) M hM p
  rw [hreg.weyl] at hge
  exact hge

 
theorem ae_regularAt_family {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    {ι : Type*} [Countable ι] (Φ : ι → TestC) :
    ∀ᵐ ω ∂P, RegularAt D (ξ : ℝ) (h ω) ∧ ∀ i : ι, RegularAt D (ξ : ℝ)
      (LQGMetric.addFun (h ω) (LQGMetric.testCont (Φ i))) := by
  filter_upwards [ae_regularAt_self hD P h hh,
    ae_all_iff.mpr (fun i => ae_regularAt_shift hD P h hh (Φ i))] with ω h0 h1
  exact ⟨h0, h1⟩

 

theorem ofCont_add (f g : C(ℂ, ℝ)) :
    LQGMetric.ofCont (f + g) = LQGMetric.ofCont f + LQGMetric.ofCont g := by
  unfold LQGMetric.ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

theorem ofCont_zero : LQGMetric.ofCont 0 = 0 := by
  have h := ofCont_add 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem addFun_addFun (g : DistC) (f₁ f₂ : C(ℂ, ℝ)) :
    LQGMetric.addFun (LQGMetric.addFun g f₁) f₂ = LQGMetric.addFun g (f₁ + f₂) := by
  simp only [LQGMetric.addFun, ofCont_add, add_assoc]

theorem addFun_zero (g : DistC) : LQGMetric.addFun g 0 = g := by
  simp only [LQGMetric.addFun, ofCont_zero, add_zero]

theorem testCont_neg (φ : TestC) :
    LQGMetric.testCont (-φ) = -LQGMetric.testCont φ := by
  ext x; rfl

theorem testCont_add (φ ψ : TestC) :
    LQGMetric.testCont (φ + ψ) = LQGMetric.testCont φ + LQGMetric.testCont ψ := by
  ext x; rfl

theorem testCont_sub (φ ψ : TestC) :
    LQGMetric.testCont (φ - ψ) = LQGMetric.testCont φ - LQGMetric.testCont ψ := by
  ext x; rfl

theorem testCont_apply (φ : TestC) (x : ℂ) : LQGMetric.testCont φ x = φ x := rfl

theorem subTest_eq_addFun (g : DistC) (φ : TestC) :
    LQGMetric.GM.subTest g φ = LQGMetric.addFun g (LQGMetric.testCont (-φ)) := by
  rw [LQGMetric.GM.subTest, testCont_neg]

 
theorem addFun_subTest_self (g : DistC) (φ : TestC) :
    LQGMetric.addFun (LQGMetric.GM.subTest g φ) (LQGMetric.testCont φ) = g := by
  rw [LQGMetric.GM.subTest, addFun_addFun, neg_add_cancel, addFun_zero]

 
theorem addFun_subTest_part (g : DistC) (φ ψ : TestC) :
    LQGMetric.addFun (LQGMetric.GM.subTest g (φ + ψ)) (LQGMetric.testCont ψ) =
      LQGMetric.GM.subTest g φ := by
  rw [LQGMetric.GM.subTest, LQGMetric.GM.subTest, addFun_addFun, testCont_add]
  congr 1
  abel

 
theorem subTest_addFun (g : DistC) (φ ψ : TestC) :
    LQGMetric.GM.subTest (LQGMetric.addFun g (LQGMetric.testCont φ)) ψ =
      LQGMetric.addFun g (LQGMetric.testCont (φ - ψ)) := by
  rw [LQGMetric.GM.subTest, addFun_addFun, testCont_sub, sub_eq_add_neg]


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices
