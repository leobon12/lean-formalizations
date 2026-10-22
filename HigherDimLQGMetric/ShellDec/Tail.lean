import HigherDimLQGMetric.ShellDec.Functional

/-!
# Exponential shell good-event tail
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

open Classical in
private theorem shellIndicatorProduct {Ω : Type*} (G : ℕ → Set Ω)
    (I : Finset ℕ) (ω : Ω) :
    (∏ i ∈ I, if ω ∈ G i then (0 : ℝ) else 1) =
      ({ω | ∀ i ∈ I, ω ∉ G i}.indicator (fun _ => (1 : ℝ))) ω := by
  classical
  by_cases h : ∀ i ∈ I, ω ∉ G i
  · have hprod : (∏ i ∈ I, if ω ∈ G i then (0 : ℝ) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [h i hi]
    rw [hprod]
    simp only [Set.indicator_apply]
    split_ifs with hh
    · rfl
    · exact (hh h).elim
  · push Not at h
    obtain ⟨i, hi, hGi⟩ := h
    have hz : (∏ j ∈ I, if ω ∈ G j then (0 : ℝ) else 1) = 0 := by
      exact Finset.prod_eq_zero hi (by simp [hGi])
    rw [hz]
    simp only [Set.indicator_apply]
    split_ifs with hall
    · exact ((hall i hi) hGi).elim
    · rfl

open Classical in
private theorem shellFailureIntersectionProb {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Set Ω)
    (hG : ∀ i, MeasurableSet (G i)) (K t : ℝ) (hK : 0 < K)
    (hfail : ∀ i, P.real (G i)ᶜ ≤ Real.exp (-K * t))
    (hdec : ∀ I : Finset ℕ,
      ∫ ω, ∏ i ∈ I, (if ω ∈ G i then (0 : ℝ) else 1) ∂P ≤
        ∏ i ∈ I,
          (∫ ω, (if ω ∈ G i then (0 : ℝ) else 1) ^ K ∂P) ^ K⁻¹)
    (I : Finset ℕ) :
    P.real {ω | ∀ i ∈ I, ω ∉ G i} ≤ Real.exp (-t * I.card) := by
  classical
  let S : Set Ω := {ω | ∀ i ∈ I, ω ∉ G i}
  have hS : MeasurableSet S := by
    have hset : S = ⋂ i ∈ I, (G i)ᶜ := by
      ext ω
      simp [S]
    rw [hset]
    exact Finset.measurableSet_biInter I (fun i _ => (hG i).compl)
  have hleft :
      (∫ ω, ∏ i ∈ I, (if ω ∈ G i then (0 : ℝ) else 1) ∂P) = P.real S := by
    have heq : (fun ω => ∏ i ∈ I, (if ω ∈ G i then (0 : ℝ) else 1)) =
        S.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      exact shellIndicatorProduct G I ω
    rw [heq]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (μ := P) hS)
  have hfactor (i : ℕ) :
      (∫ ω, (if ω ∈ G i then (0 : ℝ) else 1) ^ K ∂P) = P.real (G i)ᶜ := by
    have heq : (fun ω => (if ω ∈ G i then (0 : ℝ) else 1) ^ K) =
        (G i)ᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hω : ω ∈ G i
      · simp [hω, hK.ne']
      · simp [hω]
    rw [heq]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (μ := P) (hG i).compl)
  have hKi : 0 ≤ K⁻¹ := by positivity
  have hexp : (Real.exp (-K * t)) ^ K⁻¹ = Real.exp (-t) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hright :
      (∏ i ∈ I,
        (∫ ω, (if ω ∈ G i then (0 : ℝ) else 1) ^ K ∂P) ^ K⁻¹) ≤
        Real.exp (-t * I.card) := by
    simp_rw [hfactor]
    calc
      (∏ i ∈ I, (P.real (G i)ᶜ) ^ K⁻¹) ≤
          ∏ i ∈ I, Real.exp (-t) := by
            apply Finset.prod_le_prod₀
            · intro i _
              exact Real.rpow_nonneg (measureReal_nonneg) _
            intro i _
            exact (Real.rpow_le_rpow (measureReal_nonneg) (hfail i) hKi).trans_eq hexp
      _ = Real.exp (-t * I.card) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
        congr 1
        ring
  calc
    P.real S = ∫ ω, ∏ i ∈ I, (if ω ∈ G i then (0 : ℝ) else 1) ∂P := hleft.symm
    _ ≤ ∏ i ∈ I, (∫ ω, (if ω ∈ G i then (0 : ℝ) else 1) ^ K ∂P) ^ K⁻¹ := hdec I
    _ ≤ Real.exp (-t * I.card) := hright

open Classical in
private theorem shellUnionTail {Ω : Type*} [MeasurableSpace Ω]
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

private theorem shellSigma0_le_ambient {d : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {h : Ω → DistRd d} (hh : Measurable h)
    (V : Set (Rd d)) :
    fieldSigma0 h V ≤ (inferInstance : MeasurableSpace Ω) := by
  unfold fieldSigma0
  apply Measurable.comap_le
  refine measurable_pi_iff.2 fun φ => ?_
  exact (measurable_distOn_apply φ.1.1).comp hh

/-- Appendix A, Lemma A.1: exponentially many high-probability shells succeed. -/
theorem lemmaA1 {d : ℕ} (hd : 1 ≤ d) : ShellInputA1 d := by
  classical
  intro a b q ha ha1 hb1 hq hq1 A θ hA hθ hθ1
  obtain ⟨K, hK, hdec⟩ := shellDecouplingFun hd a b q ha ha1 hb1 hq hq1
  let t : ℝ := (A + 1) / (1 - θ)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have htc : t * (1 - θ) = A + 1 := by
    dsimp [t]
    have hne : 1 - θ ≠ 0 := by linarith
    field_simp
  let p : ℝ := 1 - Real.exp (-K * t)
  have hδlt : Real.exp (-K * t) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p < 1 := by
    have hpos := Real.exp_pos (-K * t)
    dsimp [p]
    linarith
  refine ⟨p, hp1, ?_⟩
  intro Ω _ P _ h hh z r hr hstep E hE hprob n
  have hex (i : ℕ) : ∃ G : Set Ω,
      MeasurableSet[fieldSigma0 h (ann z (a * r i) (b * r i))] G ∧
        E i =ᵐ[P] G := hE i
  choose G hGm hEG using hex
  have hGamb (i : ℕ) : MeasurableSet (G i) :=
    shellSigma0_le_ambient hh.measurable _ (G i) (hGm i)
  have hfail (i : ℕ) : P.real (G i)ᶜ ≤ Real.exp (-K * t) := by
    have hprobG : ENNReal.ofReal p ≤ P (G i) := by
      rw [← measure_congr (hEG i)]
      exact hprob i
    have hprobR : p ≤ P.real (G i) := by
      have h := ENNReal.toReal_mono (measure_ne_top P _) hprobG
      simpa only [ENNReal.toReal_ofReal hp0, Measure.real] using h
    rw [probReal_compl_eq_one_sub (hGamb i)]
    dsimp [p] at hprobR
    linarith
  let F : ℕ → Ω → ℝ := fun i ω => if ω ∈ G i then 0 else 1
  have hFM (i : ℕ) : ∃ H : Ω → ℝ,
      Measurable[fieldSigma0 h (ann z (a * r i) (b * r i))] H ∧
        F i =ᵐ[P] H := by
    refine ⟨F i, ?_, Filter.EventuallyEq.rfl⟩
    exact Measurable.ite (hGm i) measurable_const measurable_const
  have hF01 (i : ℕ) (ω : Ω) : 0 ≤ F i ω ∧ F i ω ≤ 1 := by
    by_cases hω : ω ∈ G i <;> simp [F, hω]
  have hsub (I : Finset ℕ) :
      P.real {ω | ∀ i ∈ I, ω ∉ G i} ≤ Real.exp (-t * I.card) := by
    apply shellFailureIntersectionProb P G hGamb K t (by linarith) hfail
    intro J
    exact hdec P h hh z r hr hstep J F hFM hF01
  have htail := shellUnionTail P G A θ t ht htc hsub n
  have hBadAE :
      {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < θ * n} =ᵐ[P]
        {ω | (((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ) < θ * n} := by
    filter_upwards [ae_all_iff.2 hEG] with ω hω
    have heq : (Finset.range n).filter (fun i => ω ∈ E i) =
        (Finset.range n).filter (fun i => ω ∈ G i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr_right fun _ => Iff.of_eq (hω i)
    simp only [heq]
  calc
    P {ω | (((Finset.range n).filter (fun i => ω ∈ E i)).card : ℝ) < θ * n} =
        P {ω | (((Finset.range n).filter (fun i => ω ∈ G i)).card : ℝ) < θ * n} :=
      measure_congr hBadAE
    _ ≤ ENNReal.ofReal (Real.exp (-A * n)) := htail

end HigherDimLQGMetric
