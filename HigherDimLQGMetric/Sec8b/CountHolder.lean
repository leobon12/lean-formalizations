import HigherDimLQGMetric.CM.Holder
import Mathlib.Analysis.MeanInequalities

/-!
# Section 8: Hölder on a finite counting measure

This module bounds a finite sum of Cameron–Martin shifted event probabilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory

/-- Finite counting-measure Hölder in the exponents of Lemma 7.1. -/
theorem s7b_sum_rpow_le {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) {p : ℝ} (hp : 1 < p) :
    ∑ i ∈ S, (a i) ^ (1 - p⁻¹) ≤
      (S.card : ℝ) ^ p⁻¹ * (∑ i ∈ S, a i) ^ (1 - p⁻¹) := by
  let q : ℝ := p.conjExponent
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hq0 : 0 < q := by dsimp [q, Real.conjExponent]; positivity
  have htq : (1 - p⁻¹) * q = 1 := by
    dsimp [q, Real.conjExponent]
    field_simp
  have hqinv : 1 / q = 1 - p⁻¹ := by
    dsimp [q, Real.conjExponent]
    field_simp
  have h := Real.inner_le_Lp_mul_Lq S (fun _ => (1 : ℝ))
      (fun i => a i ^ (1 - p⁻¹)) (Real.HolderConjugate.conjExponent hp)
  have hsum : (∑ i ∈ S, |a i ^ (1 - p⁻¹)| ^ q) = ∑ i ∈ S, a i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (Real.rpow_nonneg (ha i hi) _), ← Real.rpow_mul (ha i hi),
      htq, Real.rpow_one]
  have hcard : (∑ i ∈ S, |(1 : ℝ)| ^ p) = (S.card : ℝ) := by simp
  rw [hcard, hsum, hqinv] at h
  simpa only [one_mul, one_div] using h

open Classical in
/-- The expected number of occurrences is the sum of their probabilities. -/
theorem s7b_sum_probability_le {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset ι)
    (E : ι → Set Ω) (hE : ∀ i ∈ S, MeasurableSet (E i)) {K : ℝ}
    (hcount : ∀ᵐ ω ∂P, ((S.filter fun i => ω ∈ E i).card : ℝ) ≤ K) :
    ∑ i ∈ S, P.real (E i) ≤ K := by
  classical
  have hint : ∀ i ∈ S, Integrable ((E i).indicator fun _ : Ω => (1 : ℝ)) P := by
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (hE i hi)
  have hsum : Integrable (fun ω => ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω) P :=
    integrable_finsetSum S hint
  have hpoint : ∀ ω : Ω,
      (∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω) =
        ((S.filter fun i => ω ∈ E i).card : ℝ) := by
    intro ω
    simp only [Set.indicator_apply, Finset.sum_boole]
  calc
    ∑ i ∈ S, P.real (E i) =
        ∫ ω, ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P := by
          rw [integral_finsetSum S hint]
          exact (Finset.sum_congr rfl fun i hi => integral_indicator_one (hE i hi)).symm
    _ ≤ ∫ _ω : Ω, K ∂P :=
      integral_mono_ae hsum (integrable_const K)
        (hcount.mono fun ω hw => (hpoint ω).trans_le hw)
    _ = K := by simp

open Classical in
/-- Markov's inequality for the number of occurring events. -/
theorem s7b_markov_count {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Finset ι)
    (E : ι → Set Ω) (hE : ∀ i ∈ S, MeasurableSet (E i)) (t : ℝ) :
    t * P.real {ω | t ≤ ((S.filter fun i => ω ∈ E i).card : ℝ)} ≤
      ∑ i ∈ S, P.real (E i) := by
  classical
  have hint : ∀ i ∈ S, Integrable ((E i).indicator fun _ : Ω => (1 : ℝ)) P := by
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (hE i hi)
  have hsum : Integrable (fun ω => ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω) P :=
    integrable_finsetSum S hint
  have hpoint : ∀ ω : Ω,
      (∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω) =
        ((S.filter fun i => ω ∈ E i).card : ℝ) := by
    intro ω
    simp only [Set.indicator_apply, Finset.sum_boole]
  have hnonneg : ∀ᵐ ω ∂P,
      0 ≤ ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω :=
    ae_of_all _ fun ω => by rw [hpoint]; exact Nat.cast_nonneg _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hsum t
  have hevent : {ω | t ≤ ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω} =
      {ω | t ≤ ((S.filter fun i => ω ∈ E i).card : ℝ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hpoint]
  rw [hevent] at hmarkov
  calc
    t * P.real {ω | t ≤ ((S.filter fun i => ω ∈ E i).card : ℝ)} ≤
        ∫ ω, ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P := hmarkov
    _ = ∑ i ∈ S, P.real (E i) := by
      rw [integral_finsetSum S hint]
      exact Finset.sum_congr rfl fun i hi => integral_indicator_one (hE i hi)

open Classical in
/-- Proposition 8.6's Cameron–Martin step, with the dimension premise required by
the sphere-average normalization. The shifts may differ between the events. -/
theorem cm_holder_count {d : ℕ} (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) {ι : Type*} (S : Finset ι)
    (A : ι → Set (DistRd d)) (hA : ∀ i, MeasurableSet (A i))
    (F : ι → C(HigherDimLFPP.Rd d, ℝ)) {C : ℝ}
    (hF : ∀ i, IsCMBounded (F i) C) {pH : ℝ} (hp : 1 < pH)
    {K0 : ℝ} (_hK0 : 0 ≤ K0)
    (hcount : ∀ᵐ ω ∂P,
      ((S.filter (fun i => shiftNorm (h ω) (F i) ∈ A i)).card : ℝ) ≤ K0) :
    ∑ i ∈ S, P.real {ω | h ω ∈ A i} ≤
      Real.exp ((pH - 1) / 2 * C ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹) := by
  let E : ι → Set Ω := fun i => {ω | shiftNorm (h ω) (F i) ∈ A i}
  have hEm : ∀ i ∈ S, MeasurableSet (E i) := by
    intro i _
    exact (hA i).preimage ((measurable_addConst_left _).comp
      ((measurable_addFun_left (F i)).comp hh.1.measurable))
  have hsum : ∑ i ∈ S, P.real (E i) ≤ K0 :=
    s7b_sum_probability_le P S E hEm hcount
  have ht : 0 ≤ 1 - pH⁻¹ := by
    have hp0 : 0 < pH := by linarith
    have hinv : pH⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp
    linarith
  have hpoint : ∀ i ∈ S, P.real {ω | h ω ∈ A i} ≤
      Real.exp ((pH - 1) / 2 * C ^ 2) * (P.real (E i)) ^ (1 - pH⁻¹) := by
    intro i _
    have hcm := lemma71 hd hh (F i) (hF i) hp (A i) (hA i)
    have hfin : ENNReal.ofReal (Real.exp ((pH - 1) / 2 * C ^ 2)) *
        P {ω | shiftNorm (h ω) (F i) ∈ A i} ^ (1 - pH⁻¹) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ht (measure_ne_top P _))
    have hr := ENNReal.toReal_mono hfin hcm
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ← ENNReal.toReal_rpow] at hr
    exact hr
  calc
    ∑ i ∈ S, P.real {ω | h ω ∈ A i} ≤
        ∑ i ∈ S, Real.exp ((pH - 1) / 2 * C ^ 2) *
          (P.real (E i)) ^ (1 - pH⁻¹) := Finset.sum_le_sum hpoint
    _ = Real.exp ((pH - 1) / 2 * C ^ 2) *
          ∑ i ∈ S, (P.real (E i)) ^ (1 - pH⁻¹) := by rw [Finset.mul_sum]
    _ ≤ Real.exp ((pH - 1) / 2 * C ^ 2) *
          ((S.card : ℝ) ^ pH⁻¹ * (∑ i ∈ S, P.real (E i)) ^ (1 - pH⁻¹)) := by
            apply mul_le_mul_of_nonneg_left
              (s7b_sum_rpow_le S (fun i => P.real (E i))
                (fun _ _ => measureReal_nonneg) hp)
              (Real.exp_pos _).le
    _ ≤ Real.exp ((pH - 1) / 2 * C ^ 2) *
          (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹) := by
            have hpow := Real.rpow_le_rpow
              (Finset.sum_nonneg fun _ _ => measureReal_nonneg) hsum ht
            have hc : 0 ≤ Real.exp ((pH - 1) / 2 * C ^ 2) * (S.card : ℝ) ^ pH⁻¹ :=
              mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow hc

open Classical in
/-- Finite-class Cameron–Martin and Markov bound, in outer-measure form.
The event `B` can be raw and need not be measurable. -/
theorem s7b_cm_markov_count {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P)
    {ι : Type*} (S : Finset ι) (A : ι → Set (DistRd d))
    (hA : ∀ i, MeasurableSet (A i))
    (F : ι → C(HigherDimLFPP.Rd d, ℝ)) {C : ℝ}
    (hF : ∀ i, IsCMBounded (F i) C)
    {pH : ℝ} (hp : 1 < pH) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hcount : ∀ᵐ ω ∂P,
      ((S.filter fun i => shiftNorm (h ω) (F i) ∈ A i).card : ℝ) ≤ K0)
    {B : Set Ω} {t : ℝ} (ht : 0 < t)
    (hB : B ⊆ {ω | t ≤ ((S.filter fun i => h ω ∈ A i).card : ℝ)}) :
    P B ≤ ENNReal.ofReal
      (Real.exp ((pH - 1) / 2 * C ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹) / t) := by
  let E : ι → Set Ω := fun i => {ω | h ω ∈ A i}
  let V : Set Ω := {ω | t ≤ ((S.filter fun i => ω ∈ E i).card : ℝ)}
  have hEm : ∀ i ∈ S, MeasurableSet (E i) :=
    fun i _ => (hA i).preimage hh.1.measurable
  have hmarkov := s7b_markov_count P S E hEm t
  have hsum := cm_holder_count hd hh S A hA F hF hp hK0 hcount
  have hreal : P.real V ≤
      (Real.exp ((pH - 1) / 2 * C ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹)) / t := by
    apply (le_div_iff₀ ht).2
    simpa only [mul_comm] using hmarkov.trans hsum
  have hVfin : P V ≠ ⊤ := measure_ne_top P V
  calc
    P B ≤ P V := measure_mono hB
    _ = ENNReal.ofReal (P.real V) := (ENNReal.ofReal_toReal hVfin).symm
    _ ≤ ENNReal.ofReal
        (Real.exp ((pH - 1) / 2 * C ^ 2) *
          (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹) / t) :=
      ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGMetric
