import HigherDimLQGContinuity.Overlap.PinTransfer

/-!
# Finite overlap under the radius-ten pin (packet Q8b)

This file transports the sealed unit-pinned Cameron–Martin count bound to the
radius-ten-pinned law. The optimal choice of Hölder exponent is handled below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

open Classical in
private theorem q8b_measurable_count {d : ℕ} {ι : Type} (S : Finset ι)
    (A : ι → Set (DistRd d)) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fun g : DistRd d => ((S.filter fun i => g ∈ A i).card : ℝ)) := by
  classical
  have heq : (fun g : DistRd d => ((S.filter fun i => g ∈ A i).card : ℝ)) =
      (fun g => ∑ i ∈ S, (A i).indicator (fun _ => (1 : ℝ)) g) := by
    funext g
    simp only [Set.indicator_apply, Finset.sum_boole]
  rw [heq]
  exact Finset.measurable_sum S (fun i _ => measurable_const.indicator (hA i))

open Classical in
private theorem q8b_shifted_count_ae {d : ℕ} (hd : 3 ≤ d)
    {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d))
    (A' : ι → Set (DistRd d))
    (hA' : ∀ i g, g ∈ A' i ↔ pin 10 g ∈ A i)
    (F : ι → C(Rd d, ℝ))
    (hsupp : ∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4)
    {U : ℝ}
    (hup : ∀ᵐ g ∂(pinLaw d 10),
      ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ U) :
    ∀ᵐ g ∂(normLGFLaw d),
      ((S.filter fun i => shiftNorm g (F i) ∈ A' i).card : ℝ) ≤ U := by
  classical
  have hpins := q8b_pin_shiftNorm_finite_ae (by omega : 2 ≤ d) S F hsupp
  apply ((ae_pin_of_ae hup).and hpins).mono
  intro g hboth
  have hcountEq := q8b_card_filter_iff S
    (fun i => shiftNorm g (F i) ∈ A' i)
    (fun i => addFun (pin 10 g) (F i) ∈ A i)
    (fun i hi => (hA' i _).trans
      (Iff.of_eq (congrArg (fun x : DistRd d => x ∈ A i) (hboth.2 i hi))))
  exact hcountEq.le.trans hboth.1

open Classical in
private theorem q8b_pinned_holder_event_bound {d : ℕ} (hd : 3 ≤ d)
    {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d))
    (hA : ∀ i, MeasurableSet (A i)) (F : ι → C(Rd d, ℝ))
    {M : ℝ} (hF : ∀ i, IsCMBounded (F i) M)
    (hsupp : ∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4)
    {L U pH : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hp : 1 < pH)
    (hup : ∀ᵐ g ∂(pinLaw d 10),
      ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ U) :
    pinLaw d 10 {g | L ≤ ((S.filter fun i => g ∈ A i).card : ℝ)} ≤ ENNReal.ofReal
      (Real.exp ((pH - 1) / 2 * M ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * U ^ (1 - pH⁻¹) / L) := by
  classical
  let G : Set (DistRd d) :=
    {g | L ≤ ((S.filter fun i => g ∈ A i).card : ℝ)}
  have hG : MeasurableSet G := by
    dsimp [G]
    exact measurableSet_le measurable_const (q8b_measurable_count S A hA)
  let A' : ι → Set (DistRd d) := fun i => (pin (d := d) 10) ⁻¹' (A i)
  have hA' : ∀ i, MeasurableSet (A' i) :=
    fun i => (hA i).preimage (measurable_pin 10)
  have hcount : ∀ᵐ g ∂(normLGFLaw d),
      ((S.filter fun i => shiftNorm g (F i) ∈ A' i).card : ℝ) ≤ U :=
    q8b_shifted_count_ae hd S A A' (fun i g => Iff.rfl) F hsupp hup
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  have hh : IsNormalizedLGF (id : DistRd d → DistRd d) (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega)).2.1
  have hCM := s7b_cm_markov_count (by omega : 2 ≤ d) hh S A' hA' F hF hp hU
    hcount hL (B := (pin (d := d) 10) ⁻¹' G) (by
      intro g hg
      exact hg)
  change pinLaw d 10 G ≤ _
  rw [pinLaw, Measure.map_apply (measurable_pin 10) hG]
  exact hCM

open Classical in
private theorem q8b_pinned_holder_bound {d : ℕ} (hd : 3 ≤ d)
    {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d))
    (hA : ∀ i, MeasurableSet (A i)) (F : ι → C(Rd d, ℝ))
    {M : ℝ} (hF : ∀ i, IsCMBounded (F i) M)
    (hsupp : ∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4)
    {L U pH : ℝ} (hL : 0 < L) (hU : 0 ≤ U) (hp : 1 < pH)
    (B : Set (DistRd d))
    (hlow : ∀ᵐ g ∂(pinLaw d 10), g ∈ B →
      L ≤ ((S.filter fun i => g ∈ A i).card : ℝ))
    (hup : ∀ᵐ g ∂(pinLaw d 10),
      ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ U) :
    pinLaw d 10 B ≤ ENNReal.ofReal
      (Real.exp ((pH - 1) / 2 * M ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * U ^ (1 - pH⁻¹) / L) := by
  have hBG : B ≤ᵐ[pinLaw d 10]
      {g | L ≤ ((S.filter fun i => g ∈ A i).card : ℝ)} :=
    hlow.mono fun g hg hmem => hg hmem
  exact (measure_mono_ae hBG).trans
    (q8b_pinned_holder_event_bound hd S A hA F hF hsupp hL hU hp hup)

open Classical in
private theorem q8b_count_card_bound {d : ℕ} (hd : 3 ≤ d)
    {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d))
    {L : ℝ} (hL : 0 < L) (B : Set (DistRd d))
    (hlow : ∀ᵐ g ∂(pinLaw d 10), g ∈ B →
      L ≤ ((S.filter fun i => g ∈ A i).card : ℝ)) :
    pinLaw d 10 B ≤ ENNReal.ofReal ((S.card : ℝ) / L) := by
  classical
  letI : IsProbabilityMeasure (pinLaw d 10) := isProbabilityMeasure_pinLaw (by omega) 10
  by_cases hNL : (S.card : ℝ) < L
  · have hempty : B ≤ᵐ[pinLaw d 10] (∅ : Set (DistRd d)) := by
      apply hlow.mono
      intro g hg hB
      have hc : ((S.filter fun i => g ∈ A i).card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_filter_le S (fun i => g ∈ A i)
      exact False.elim ((not_le_of_gt (lt_of_le_of_lt hc hNL)) (hg hB))
    have hzero : pinLaw d 10 B = 0 := le_zero_iff.mp (by simpa using measure_mono_ae hempty)
    rw [hzero]
    exact bot_le
  · have hLN : L ≤ (S.card : ℝ) := le_of_not_gt hNL
    have hratio : (1 : ℝ) ≤ (S.card : ℝ) / L := by
      exact (le_div_iff₀ hL).2 (by simpa using hLN)
    calc
      pinLaw d 10 B ≤ (1 : ENNReal) := prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((S.card : ℝ) / L) := ENNReal.ofReal_le_ofReal hratio

private theorem q8b_holder_opt_real {M U N L : ℝ}
    (hM : 0 < M) (hU : 1 ≤ U) (hN : 1 < N) (hL : 0 < L) :
    let s := Real.sqrt (2 * Real.log N)
    let p := 1 + s / M
    Real.exp ((p - 1) / 2 * M ^ 2) * N ^ p⁻¹ * U ^ (1 - p⁻¹) / L ≤
      U / L * Real.exp (M * s) := by
  dsimp
  let s := Real.sqrt (2 * Real.log N)
  let p := 1 + s / M
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * Real.log N := Real.sq_sqrt (by positivity)
  have hp : 1 < p := by dsimp [p]; have := div_pos hs hM; linarith
  have hp0 : 0 < p := by linarith
  have hpMul : M * s * p = M * s + s ^ 2 := by
    dsimp [p]
    field_simp
  have hkey : 2 * Real.log N ≤ M * s * p := by
    rw [hpMul, ← hs2]
    have := mul_nonneg hM.le hs.le
    linarith
  have hExp : Real.log N * p⁻¹ ≤ M * s / 2 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hp0).2
    nlinarith only [hkey]
  have hNpow : N ^ p⁻¹ ≤ Real.exp (M * s / 2) := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hN)]
    exact Real.exp_le_exp.mpr hExp
  have hUpow : U ^ (1 - p⁻¹) ≤ U := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hU
      (show 1 - p⁻¹ ≤ (1 : ℝ) by have := inv_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using hpow
  have hfirst : (p - 1) / 2 * M ^ 2 = M * s / 2 := by
    dsimp [p]
    field_simp
    ring
  have hprod : Real.exp ((p - 1) / 2 * M ^ 2) * N ^ p⁻¹ * U ^ (1 - p⁻¹) ≤
      Real.exp (M * s) * U := by
    rw [hfirst]
    calc
      Real.exp (M * s / 2) * N ^ p⁻¹ * U ^ (1 - p⁻¹) ≤
          Real.exp (M * s / 2) * Real.exp (M * s / 2) * U := by gcongr
      _ = Real.exp (M * s) * U := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  have hdiv := div_le_div_of_nonneg_right hprod hL.le
  calc
    _ ≤ Real.exp (M * s) * U / L := hdiv
    _ = U / L * Real.exp (M * s) := by ring_nf

private theorem q8b_holder_zero_limit {x N U L : ℝ}
    (hN : 0 < N) (hU : 0 < U)
    (hbound : ∀ n : ℕ,
      x ≤ N ^ (((n + 2 : ℕ) : ℝ)⁻¹) *
        U ^ (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) / L) :
    x ≤ U / L := by
  have hinv : Filter.Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ)⁻¹))
      Filter.atTop (nhds (0 : ℝ)) := by
    exact (Filter.tendsto_add_atTop_iff_nat 2).2 tendsto_inv_atTop_nhds_zero_nat
  have hNpow : Filter.Tendsto (fun n : ℕ => N ^ (((n + 2 : ℕ) : ℝ)⁻¹))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_zero] using
      ((Real.continuous_const_rpow hN.ne').tendsto 0).comp hinv
  have hone : Filter.Tendsto (fun n : ℕ => 1 - (((n + 2 : ℕ) : ℝ)⁻¹))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
  have hUpow : Filter.Tendsto (fun n : ℕ => U ^ (1 - (((n + 2 : ℕ) : ℝ)⁻¹)))
      Filter.atTop (nhds U) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      ((Real.continuous_const_rpow hU.ne').tendsto 1).comp hone
  have hlim : Filter.Tendsto
      (fun n : ℕ => N ^ (((n + 2 : ℕ) : ℝ)⁻¹) *
        U ^ (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) / L)
      Filter.atTop (nhds (U / L)) := by
    convert (hNpow.mul hUpow).div_const L using 1; simp
  exact ge_of_tendsto' hlim hbound

open Classical in
private theorem q8b_pinned_zero_energy_bound {d : ℕ} (hd : 3 ≤ d)
    {ι : Type} (S : Finset ι) (A : ι → Set (DistRd d))
    (hA : ∀ i, MeasurableSet (A i)) (F : ι → C(Rd d, ℝ))
    (hF : ∀ i, IsCMBounded (F i) 0)
    (hsupp : ∀ i, tsupport (F i) ⊆ ball (0 : Rd d) 4)
    {L U : ℝ} (hL : 0 < L) (hU : 0 < U) (hS : 0 < S.card)
    (B : Set (DistRd d))
    (hlow : ∀ᵐ g ∂(pinLaw d 10), g ∈ B →
      L ≤ ((S.filter fun i => g ∈ A i).card : ℝ))
    (hup : ∀ᵐ g ∂(pinLaw d 10),
      ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ U) :
    pinLaw d 10 B ≤ ENNReal.ofReal (U / L) := by
  classical
  have hSreal : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS
  letI : IsProbabilityMeasure (pinLaw d 10) := isProbabilityMeasure_pinLaw (by omega) 10
  have hBfin : pinLaw d 10 B ≠ ⊤ := measure_ne_top _ _
  have hreal : (pinLaw d 10 B).toReal ≤ U / L := by
    apply q8b_holder_zero_limit hSreal hU
    intro n
    have hp : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
    have h := q8b_pinned_holder_bound hd S A hA F hF hsupp hL hU.le hp B hlow hup
    have hnum : 0 ≤ (S.card : ℝ) ^ (((n + 2 : ℕ) : ℝ)⁻¹) *
        U ^ (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) / L := by positivity
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Real.exp_zero,
      one_mul, ENNReal.toReal_ofReal hnum] using hr
  calc
    pinLaw d 10 B = ENNReal.ofReal (pinLaw d 10 B).toReal :=
      (ENNReal.ofReal_toReal hBfin).symm
    _ ≤ ENNReal.ofReal (U / L) := ENNReal.ofReal_le_ofReal hreal

/-- Lemma 4.4 in the radius-ten pin convention, with all degenerate cases. -/
theorem lemma44_pinned_holds {d : ℕ} (hd : 3 ≤ d) : Lemma44Pinned d := by
  classical
  intro ι S A hA F M hM hF hsupp L U hL hU B hlow hup
  by_cases hU1 : U < 1
  · have hup0 : ∀ᵐ g ∂(pinLaw d 10),
        ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) ≤ 0 := by
      apply hup.mono
      intro g hg
      have hc : ((S.filter fun i => addFun g (F i) ∈ A i).card : ℝ) < 1 :=
        lt_of_le_of_lt hg hU1
      have hn : (S.filter fun i => addFun g (F i) ∈ A i).card < 1 := by
        exact_mod_cast hc
      have hz : (S.filter fun i => addFun g (F i) ∈ A i).card = 0 := by omega
      simp only [hz, Nat.cast_zero, le_refl]
    have hzero : pinLaw d 10 B ≤ 0 := by
      have h := q8b_pinned_holder_bound hd S A hA F hF hsupp hL
        (show (0 : ℝ) ≤ 0 by norm_num) (show (1 : ℝ) < 2 by norm_num) B hlow hup0
      have hpow : (0 : ℝ) ^ (1 - (2 : ℝ)⁻¹) = 0 := by norm_num
      simpa only [hpow, mul_zero, zero_div, ENNReal.ofReal_zero] using h
    exact hzero.trans bot_le
  have hUone : 1 ≤ U := le_of_not_gt hU1
  have hcard := q8b_count_card_bound hd S A hL B hlow
  have hratio : (S.card : ℝ) / L ≤ U / L * (S.card : ℝ) := by
    have hdiv : (1 : ℝ) / L ≤ U / L := div_le_div_of_nonneg_right hUone hL.le
    have hmul := mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg S.card)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm,
      mul_left_comm, mul_assoc] using hmul
  by_cases hM0 : M = 0
  · subst M
    have hExp : Real.exp ((0 : ℝ) * Real.sqrt (2 * Real.log S.card)) = 1 := by simp
    by_cases hS0 : S.card = 0
    · have hzero : pinLaw d 10 B = 0 := by
        have h := hcard
        simp only [hS0, Nat.cast_zero, zero_div, ENNReal.ofReal_zero] at h
        exact le_zero_iff.mp h
      rw [hzero]
      exact bot_le
    have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS0
    have hzero := q8b_pinned_zero_energy_bound hd S A hA F hF hsupp
      hL (lt_of_lt_of_le zero_lt_one hUone) hSpos B hlow hup
    simpa only [hExp, min_eq_right (show (1 : ℝ) ≤ S.card by exact_mod_cast hSpos),
      mul_one] using hzero
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  let E := Real.exp (M * Real.sqrt (2 * Real.log S.card))
  by_cases hNE : (S.card : ℝ) ≤ E
  · calc
      pinLaw d 10 B ≤ ENNReal.ofReal ((S.card : ℝ) / L) := hcard
      _ ≤ ENNReal.ofReal (U / L * (S.card : ℝ)) := ENNReal.ofReal_le_ofReal hratio
      _ = ENNReal.ofReal (U / L * min (S.card : ℝ) E) := by rw [min_eq_left hNE]
  · have hEN : E < (S.card : ℝ) := lt_of_not_ge hNE
    have hNpos : 1 < (S.card : ℝ) := by
      have hEone : 1 ≤ E := by
        dsimp [E]
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hM (Real.sqrt_nonneg _))
      exact lt_of_le_of_lt hEone hEN
    let p : ℝ := 1 + Real.sqrt (2 * Real.log S.card) / M
    have hp : 1 < p := by
      dsimp [p]
      have hs : 0 < Real.sqrt (2 * Real.log S.card) :=
        Real.sqrt_pos.2 (by have := Real.log_pos hNpos; positivity)
      have := div_pos hs hMpos
      linarith
    have hholder := q8b_pinned_holder_bound hd S A hA F hF hsupp hL hU hp B hlow hup
    have hopt := q8b_holder_opt_real hMpos hUone hNpos hL
    have hbound : pinLaw d 10 B ≤ ENNReal.ofReal (U / L * E) :=
      hholder.trans (ENNReal.ofReal_le_ofReal (by simpa only [p, E] using hopt))
    change pinLaw d 10 B ≤ ENNReal.ofReal (U / L * min (S.card : ℝ) E)
    rw [min_eq_right hEN.le]
    exact hbound

end HigherDimLQGContinuity
