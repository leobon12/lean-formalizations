import HigherDimLQGContinuity.Caps.Locality
import HigherDimLQGMetric.ShellDec.Functional

/-!
# Event form of Gaussian shell decoupling (packet P4)

This adapter applies `shellDecouplingFun` to measurable representatives of
almost-sure shell-local events. It retains the exact power `|T| / K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem p4_fieldSigma0_le_ambient {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistRd d} (hh : Measurable h) (V : Set (Rd d)) :
    fieldSigma0 h V ≤ (inferInstance : MeasurableSpace Ω) := by
  unfold fieldSigma0
  apply Measurable.comap_le
  refine measurable_pi_iff.2 fun φ => ?_
  exact (measurable_distOn_apply φ.1.1).comp hh

/-- Shell decoupling for finite intersections of almost-sure local events. -/
theorem p4_shell_event_bound {d : ℕ} (hd : 1 ≤ d)
    {a b q : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 1 < b)
    (hq : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ (z : Rd d) (r : ℕ → ℝ), (∀ i, 0 < r i) →
        (∀ i, r (i + 1) ≤ q * r i) →
      ∀ (B : ℕ → Set Ω),
        (∀ i, AEEventIn P (fieldSigma0 h (ann z (a * r i) (b * r i))) (B i)) →
      ∀ (T : Finset ℕ) (p : ℝ), 0 ≤ p →
        (∀ i ∈ T, P (B i) ≤ ENNReal.ofReal p) →
        P {ω | ∀ i ∈ T, ω ∈ B i} ≤ ENNReal.ofReal (p ^ ((T.card : ℝ) / K)) := by
  classical
  obtain ⟨K, hK, hdec⟩ := shellDecouplingFun hd a b q ha ha1 hb hq hq1
  refine ⟨K, hK, ?_⟩
  intro Ω _ P _ h hh z r hr hstep B hB T p hp0 hp
  choose G hG hBG using hB
  have hGamb (i : ℕ) : MeasurableSet (G i) :=
    p4_fieldSigma0_le_ambient hh.measurable _ (G i) (hG i)
  let S : Set Ω := {ω | ∀ i ∈ T, ω ∈ G i}
  have hS : MeasurableSet S := by
    have heq : S = ⋂ i ∈ T, G i := by ext ω; simp [S]
    rw [heq]
    exact Finset.measurableSet_biInter T (fun i hi => hGamb i)
  have hBS : {ω | ∀ i ∈ T, ω ∈ B i} =ᵐ[P] S := by
    have hall : ∀ᵐ ω ∂P, ∀ i, (ω ∈ B i) = (ω ∈ G i) := ae_all_iff.2 hBG
    filter_upwards [hall] with ω hω
    simp only [S, Set.mem_ofPred_eq]
    apply propext
    constructor
    · intro h i hi
      simpa only [hω i] using h i hi
    · intro h i hi
      simpa only [← hω i] using h i hi
  let F : ℕ → Ω → ℝ := fun i ω => if ω ∈ G i then 1 else 0
  have hFm (i : ℕ) : ∃ H : Ω → ℝ,
      Measurable[fieldSigma0 h (ann z (a * r i) (b * r i))] H ∧
        F i =ᵐ[P] H := by
    exact ⟨F i, Measurable.ite (hG i) measurable_const measurable_const,
      Filter.EventuallyEq.rfl⟩
  have hF01 (i : ℕ) (ω : Ω) : 0 ≤ F i ω ∧ F i ω ≤ 1 := by
    by_cases hi : ω ∈ G i <;> simp [F, hi]
  have hpoint (ω : Ω) : (∏ i ∈ T, F i ω) = S.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases hω : ω ∈ S
    · have hprod : (∏ i ∈ T, F i ω) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        simp [F, hω i hi]
      rw [hprod, Set.indicator_of_mem hω]
    · have hnot : ∃ i ∈ T, ω ∉ G i := by
        change ¬∀ i ∈ T, ω ∈ G i at hω
        push Not at hω
        exact hω
      obtain ⟨i, hi, hGi⟩ := hnot
      have hzero : (∏ j ∈ T, F j ω) = 0 :=
        Finset.prod_eq_zero hi (by simp [F, hGi])
      rw [hzero, Set.indicator_of_notMem hω]
  have hleft : (∫ ω, ∏ i ∈ T, F i ω ∂P) = P.real S := by
    have heq : (fun ω => ∏ i ∈ T, F i ω) = S.indicator (fun _ => (1 : ℝ)) :=
      funext hpoint
    rw [heq]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (μ := P) hS)
  have hfactor (i : ℕ) : (∫ ω, (F i ω) ^ K ∂P) = P.real (G i) := by
    have heq : (fun ω => (F i ω) ^ K) = (G i).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hi : ω ∈ G i
      · simp [F, hi]
      · simp [F, hi, (by linarith : K ≠ 0)]
    rw [heq]
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (μ := P) (hGamb i))
  have hpointprob (i : ℕ) (hi : i ∈ T) : P.real (G i) ≤ p := by
    have hmeas : P (G i) ≤ ENNReal.ofReal p := by
      rw [← measure_congr (hBG i)]
      exact hp i hi
    have h := ENNReal.toReal_mono (by finiteness) hmeas
    simpa only [ENNReal.toReal_ofReal hp0, Measure.real] using h
  have hright : (∏ i ∈ T, (∫ ω, (F i ω) ^ K ∂P) ^ K⁻¹) ≤
      p ^ ((T.card : ℝ) / K) := by
    simp_rw [hfactor]
    have hKi : 0 ≤ K⁻¹ := by positivity
    calc
      (∏ i ∈ T, (P.real (G i)) ^ K⁻¹) ≤ ∏ _i ∈ T, p ^ K⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact Real.rpow_nonneg (measureReal_nonneg) _
        · intro i hi
          exact Real.rpow_le_rpow (measureReal_nonneg) (hpointprob i hi) hKi
      _ = p ^ ((T.card : ℝ) / K) := by
        rw [Finset.prod_const]
        rw [← Real.rpow_mul_natCast hp0]
        congr 1
        ring
  have hreal : P.real S ≤ p ^ ((T.card : ℝ) / K) := by
    calc
      P.real S = ∫ ω, ∏ i ∈ T, F i ω ∂P := hleft.symm
      _ ≤ ∏ i ∈ T, (∫ ω, (F i ω) ^ K ∂P) ^ K⁻¹ :=
        hdec P h hh z r hr hstep T F hFm hF01
      _ ≤ p ^ ((T.card : ℝ) / K) := hright
  calc
    P {ω | ∀ i ∈ T, ω ∈ B i} = P S := measure_congr hBS
    _ = ENNReal.ofReal (P.real S) := (ofReal_measureReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (p ^ ((T.card : ℝ) / K)) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
