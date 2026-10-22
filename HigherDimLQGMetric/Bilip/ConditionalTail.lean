import HigherDimLQGMetric.Bilip.Conditional

/-!
# Exponential tails for conditionally local metric events

The conditional probability of a shell failure is clipped to `[0,1]` on the
exceptional null set, then the Gaussian shell Hölder inequality is applied to
the resulting field-measurable factors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric.BilipProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure[mΩ] Ω)
  [IsProbabilityMeasure P]

def clipCondProb (G : MeasurableSpace Ω) (E : Set Ω) (ω : Ω) : ℝ :=
  max 0 (min 1 ((P⟦E | G⟧) ω))

omit [IsProbabilityMeasure P] in
theorem measurable_clipCondProb (G : MeasurableSpace Ω) (E : Set Ω) :
    Measurable[G] (@clipCondProb Ω mΩ P G E) := by
  unfold clipCondProb
  exact measurable_const.max (measurable_const.min stronglyMeasurable_condExp.measurable)

omit [IsProbabilityMeasure P] in
theorem clipCondProb_mem_Icc (G : MeasurableSpace Ω) (E : Set Ω) (ω : Ω) :
    @clipCondProb Ω mΩ P G E ω ∈ Set.Icc (0 : ℝ) 1 := by
  dsimp [clipCondProb]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clipCondProb_ae_eq (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[mΩ] E) :
    @clipCondProb Ω mΩ P G E =ᵐ[P] P⟦E | G⟧ := by
  filter_upwards [QuantumZipper.Thm18Asm.condExp_indicator_one_mem_Icc hG hE] with ω hω
  dsimp [clipCondProb]
  rw [min_eq_right hω.2, max_eq_right hω.1]

theorem integral_clipCondProb (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[mΩ] E) :
    ∫ ω, @clipCondProb Ω mΩ P G E ω ∂P = P.real E := by
  calc
    ∫ ω, @clipCondProb Ω mΩ P G E ω ∂P = ∫ ω, (P⟦E | G⟧) ω ∂P :=
      integral_congr_ae (clipCondProb_ae_eq (mΩ := mΩ) P G hG hE)
    _ = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂P := integral_condExp hG
    _ = P.real E := by
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (1 : ℝ) (μ := P) hE)

theorem integral_clipCondProb_pow_le (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    {E : Set Ω} (hE : MeasurableSet[mΩ] E) (K : ℝ) (hK : 1 ≤ K) :
    ∫ ω, (@clipCondProb Ω mΩ P G E ω) ^ K ∂P ≤ P.real E := by
  let f : Ω → ℝ := @clipCondProb Ω mΩ P G E
  have hfm : Measurable[mΩ] f :=
    (measurable_clipCondProb (mΩ := mΩ) P G E).mono hG le_rfl
  have hf01 (ω : Ω) : f ω ∈ Set.Icc (0 : ℝ) 1 :=
    clipCondProb_mem_Icc (mΩ := mΩ) P G E ω
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf01 ω).1]
        exact (hf01 ω).2)
  have hpowm : Measurable[mΩ] (fun ω => f ω ^ K) := by fun_prop
  have hpowint : Integrable (fun ω => f ω ^ K) P :=
    Integrable.of_bound hpowm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf01 ω).1 K)]
        exact (Real.rpow_le_self_of_le_one (hf01 ω).1 (hf01 ω).2 hK).trans
          (hf01 ω).2)
  calc
    ∫ ω, f ω ^ K ∂P ≤ ∫ ω, f ω ∂P :=
      integral_mono hpowint hfint fun ω =>
        Real.rpow_le_self_of_le_one (hf01 ω).1 (hf01 ω).2 hK
    _ = P.real E := integral_clipCondProb (mΩ := mΩ) P G hG hE

/-- Joint locality plus the Gaussian functional inequality bounds the
probability that every event in a finite set is a failure. -/
theorem local_failureIntersection
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (G A B : ℕ → MeasurableSpace Ω)
    (hG : ∀ i, G i ≤ H) (hA : ∀ i, A i ≤ mΩ)
    (hB : ∀ i, B i ≤ mΩ)
    (hCI : ∀ i, CondIndepEv (G i) (A i) (H ⊔ B i) P)
    (hNest : ∀ i j, i ≠ j → A j ≤ aeClosure P (H ⊔ B i))
    (E : ℕ → Set Ω) (hE : ∀ i, MeasurableSet[G i ⊔ A i] (E i))
    (K t : ℝ) (hK : 1 ≤ K)
    (hfail : ∀ i, P.real (E i) ≤ Real.exp (-K * t))
    (hdec : ∀ I : Finset ℕ,
      ∫ ω, ∏ i ∈ I, @clipCondProb Ω mΩ P (G i) (E i) ω ∂P ≤
        ∏ i ∈ I,
          (∫ ω, (@clipCondProb Ω mΩ P (G i) (E i) ω) ^ K ∂P) ^ K⁻¹)
    (I : Finset ℕ) :
    P.real (⋂ i ∈ I, E i) ≤ Real.exp (-t * I.card) := by
  classical
  let f : ℕ → Ω → ℝ := fun i => @clipCondProb Ω mΩ P (G i) (E i)
  have hEamb (i : ℕ) : MeasurableSet[mΩ] (E i) :=
    (sup_le ((hG i).trans hH) (hA i)) (E i) (hE i)
  have hfH (i : ℕ) : f i =ᵐ[P] P⟦E i | H⟧ :=
    (clipCondProb_ae_eq (mΩ := mΩ) P (G i) ((hG i).trans hH) (hEamb i)).trans
      (condExp_full_eq_local (mΩ := mΩ) P (hG i) hH (hA i) (hB i)
        (hCI i) (hE i)).symm
  have hIE : MeasurableSet[mΩ] (⋂ i ∈ I, E i) :=
    Finset.measurableSet_biInter I (fun i _ => hEamb i)
  have hleft : (∫ ω, ∏ i ∈ I, f i ω ∂P) = P.real (⋂ i ∈ I, E i) := by
    have hprod : (fun ω => ∏ i ∈ I, f i ω) =ᵐ[P]
        fun ω => ∏ i ∈ I, (P⟦E i | H⟧) ω := by
      filter_upwards [ae_all_iff.2 hfH] with ω hω
      exact Finset.prod_congr rfl (fun i _ => hω i)
    calc
      ∫ ω, ∏ i ∈ I, f i ω ∂P =
          ∫ ω, ∏ i ∈ I, (P⟦E i | H⟧) ω ∂P := integral_congr_ae hprod
      _ = ∫ ω, (P⟦⋂ i ∈ I, E i | H⟧) ω ∂P :=
        integral_congr_ae (condExp_biInter_eq_prod (mΩ := mΩ) P H hH
          G A B hG hA hB hCI hNest E hE I).symm
      _ = ∫ ω, (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) ω ∂P :=
        integral_condExp hH
      _ = P.real (⋂ i ∈ I, E i) := by
        simpa only [smul_eq_mul, mul_one] using
          (integral_indicator_const (1 : ℝ) (μ := P) hIE)
  have hfactor (i : ℕ) :
      (∫ ω, f i ω ^ K ∂P) ≤ Real.exp (-K * t) :=
    (integral_clipCondProb_pow_le (mΩ := mΩ) P (G i) ((hG i).trans hH)
      (hEamb i) K hK).trans (hfail i)
  have hKi : 0 ≤ K⁻¹ := by positivity
  have hexp : (Real.exp (-K * t)) ^ K⁻¹ = Real.exp (-t) := by
    rw [← Real.exp_mul]
    congr 1
    have hK0 : K ≠ 0 := by linarith
    field_simp
  have hright :
      (∏ i ∈ I, (∫ ω, f i ω ^ K ∂P) ^ K⁻¹) ≤
        Real.exp (-t * I.card) := by
    calc
      (∏ i ∈ I, (∫ ω, f i ω ^ K ∂P) ^ K⁻¹) ≤
          ∏ i ∈ I, Real.exp (-t) := by
            apply Finset.prod_le_prod₀
            · intro i _
              exact Real.rpow_nonneg (integral_nonneg fun ω =>
                Real.rpow_nonneg (clipCondProb_mem_Icc (mΩ := mΩ) P (G i) (E i) ω).1 K) _
            intro i _
            exact (Real.rpow_le_rpow (integral_nonneg fun ω =>
              Real.rpow_nonneg (clipCondProb_mem_Icc (mΩ := mΩ) P (G i) (E i) ω).1 K)
              (hfactor i) hKi).trans_eq hexp
      _ = Real.exp (-t * I.card) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
        congr 1
        ring
  calc
    P.real (⋂ i ∈ I, E i) = ∫ ω, ∏ i ∈ I, f i ω ∂P := hleft.symm
    _ ≤ ∏ i ∈ I, (∫ ω, f i ω ^ K ∂P) ^ K⁻¹ := hdec I
    _ ≤ Real.exp (-t * I.card) := hright

open Classical in
theorem bilipUnionTail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Set Ω)
    (A θ t : ℝ) (ht : 0 < t)
    (htc : t * (1 - θ) = A + 1)
    (hsubset : ∀ I : Finset ℕ,
      P.real {ω | ∀ i ∈ I, ω ∉ G i} ≤ Real.exp (-t * I.card))
    (n : ℕ) :
    P {ω | (((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ) < θ * n} ≤
      ENNReal.ofReal (Real.exp (-A * n)) := by
  classical
  let M : Finset (Finset ℕ) :=
    ((Finset.range n).powerset).filter
      (fun I => (1 - θ) * n < (I.card : ℝ))
  let S : Finset ℕ → Set Ω := fun I => {ω | ∀ i ∈ I, ω ∉ G i}
  let Bad : Set Ω :=
    {ω | (((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ) < θ * n}
  have hcover : Bad ⊆ ⋃ I ∈ M, S I := by
    intro ω hbad
    let B : Finset ℕ := (Finset.range n).filter (fun i => ω ∉ G i)
    have hBsub : B ⊆ Finset.range n := Finset.filter_subset _ _
    have hsum : ((B.card : ℝ) +
        (((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ)) = n := by
      have hs := Finset.card_filter_add_card_filter_not
        (s := Finset.range n) (fun i => ω ∈ G i)
      simp only [Finset.card_range] at hs
      have hsR :
          ((((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ) +
            (B.card : ℝ)) = n := by exact_mod_cast hs
      linarith
    have hBcard : (1 - θ) * n < (B.card : ℝ) := by
      dsimp [Bad] at hbad
      linarith
    have hBM : B ∈ M := by
      simp only [M, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hBsub, hBcard⟩
    simp only [Set.mem_iUnion]
    refine ⟨B, hBM, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hMcard : (M.card : ℝ) ≤ (2 : ℝ) ^ n := by
    have hsub : M ⊆ (Finset.range n).powerset := Finset.filter_subset _ _
    have hc := Finset.card_le_card hsub
    rw [Finset.card_powerset, Finset.card_range] at hc
    exact_mod_cast hc
  have hterm (I : Finset ℕ) (hIM : I ∈ M) :
      P.real (S I) ≤ Real.exp (-(A + 1) * n) := by
    have hcard : (1 - θ) * n ≤ (I.card : ℝ) :=
      (Finset.mem_filter.mp hIM).2.le
    have hmul : -t * (I.card : ℝ) ≤ -t * ((1 - θ) * n) := by
      exact mul_le_mul_of_nonpos_left hcard (by linarith)
    calc
      P.real (S I) ≤ Real.exp (-t * I.card) := hsubset I
      _ ≤ Real.exp (-t * ((1 - θ) * n)) := Real.exp_le_exp.mpr hmul
      _ = Real.exp (-(A + 1) * n) := by
        congr 1
        calc
          -t * ((1 - θ) * (n : ℝ)) = -(t * (1 - θ)) * n := by ring
          _ = -(A + 1) * n := by rw [htc]
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
    calc
      (2 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by gcongr
      _ = Real.exp (n : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have hfinal : (2 : ℝ) ^ n * Real.exp (-(A + 1) * n) ≤
      Real.exp (-A * n) := by
    calc
      (2 : ℝ) ^ n * Real.exp (-(A + 1) * n) ≤
          Real.exp (n : ℝ) * Real.exp (-(A + 1) * n) := by
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = Real.exp (-A * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
  change P Bad ≤ ENNReal.ofReal (Real.exp (-A * n))
  rw [← ofReal_measureReal (μ := P) (s := Bad)]
  apply ENNReal.ofReal_le_ofReal
  calc
    P.real Bad ≤ P.real (⋃ I ∈ M, S I) :=
      measureReal_mono hcover (measure_ne_top P _)
    _ ≤ ∑ I ∈ M, P.real (S I) := measureReal_biUnion_finset_le M S
    _ ≤ ∑ I ∈ M, Real.exp (-(A + 1) * n) :=
      Finset.sum_le_sum (fun I hIM => hterm I hIM)
    _ = M.card * Real.exp (-(A + 1) * n) := by simp [nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ n * Real.exp (-(A + 1) * n) :=
      mul_le_mul_of_nonneg_right hMcard (Real.exp_nonneg _)
    _ ≤ Real.exp (-A * n) := hfinal


end HigherDimLQGMetric.BilipProb
