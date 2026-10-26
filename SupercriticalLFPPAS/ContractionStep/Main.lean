import SupercriticalLFPPAS.ContractionStep.Probability
import SupercriticalLFPPAS.ContractionStep.Deterministic
import SupercriticalLFPPAS.ContractionStep.Grid

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric (DistC addConst circleAvg)
open LQGMetric.Blueprint (fieldSigmaClosed0)
open SupercriticalLFPPAS.Core
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF LSCMetric)

namespace SupercriticalLFPPAS.ContractionStep

private theorem rpow_lt_of_exp_cutoff {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (hcut : x < Real.exp (Real.log u / v)) : x ^ v < u := by
  have hlog := Real.log_lt_log hx hcut
  rw [Real.log_exp] at hlog
  have hmul : v * Real.log x < Real.log u := by
    have h' := (lt_div_iff₀ hv).mp hlog
    nlinarith
  rw [Real.rpow_def_of_pos hx, ← Real.exp_log hu]
  exact Real.exp_lt_exp.mpr (by nlinarith [hmul])

private theorem selected_count_ge_two {ε s t : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hs : 0 < s) (hst : s < t) (hquarter : 4 * s ≤ t)
    (Sε : Finset ℤ) (hS : Sε ⊆ Iteration.radiusExponents ε s t)
    (hSCard : (Iteration.radiusExponents ε s t).card ≤ 3 * Sε.card)
    (hcut : ε < Real.exp (-(12 * Real.log (Iteration.annulusBase)) / t)) : 2 ≤ Sε.card := by
  have ht : 0 < t := by linarith
  have hlogB : 0 < Real.log (Iteration.annulusBase) :=
    Real.log_pos (by norm_num [Iteration.annulusBase])
  have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
  have hlogcut := Real.log_lt_log hε hcut
  rw [Real.log_exp] at hlogcut
  have hL : 12 * Real.log (Iteration.annulusBase) / t < -Real.log ε := by
    simpa [neg_div] using neg_lt_neg hlogcut
  have hfull := Iteration.radiusExponents_count_lower hε hε1 hs hst
  have hwidth : 3 * t / 4 ≤ t - s := by nlinarith [hquarter]
  have hlogpos : 0 < -Real.log ε := by linarith
  have hfull' : (Iteration.radiusExponents ε s t).card ≥
      (3 * t / 4) * (-Real.log ε) / Real.log (Iteration.annulusBase) - 1 := by
    have hmul := mul_le_mul_of_nonneg_right hwidth hlogpos.le
    have hdiv := (div_le_div_iff_of_pos_right hlogB).2 hmul
    linarith [hfull]
  have hselected : (3 * (Sε.card : ℝ)) ≥
      (3 * t / 4) * (-Real.log ε) / Real.log (Iteration.annulusBase) - 1 := by
    have hcard : ((Iteration.radiusExponents ε s t).card : ℝ) ≤ 3 * (Sε.card : ℝ) := by
      exact_mod_cast hSCard
    linarith [hfull']
  have hbig : (3 * t / 4) * (-Real.log ε) / Real.log (Iteration.annulusBase) > 9 := by
    calc
      (3 * t / 4) * (-Real.log ε) / Real.log (Iteration.annulusBase) >
          (3 * t / 4) * (12 * Real.log (Iteration.annulusBase) / t) /
            Real.log (Iteration.annulusBase) := by
        apply (div_lt_div_iff_of_pos_right hlogB).2
        exact mul_lt_mul_of_pos_left hL (by positivity)
      _ = 9 := by field_simp; ring
  have hlarge : (3 * (Sε.card : ℝ)) > 8 := by linarith
  have hreal : (2 : ℝ) ≤ (Sε.card : ℝ) := by nlinarith
  exact_mod_cast hreal

private theorem lattice_card_bound (R q : ℝ) (hR : 1 ≤ R) (hq : 0 < q) (hq1 : q ≤ 1) :
    let N : ℕ := ⌈(R + 1) / q⌉₊
    ((latticeIndices N).card : ℝ) ≤ ((2 * R + 5) / q) ^ 2 := by
  intro N
  have hceil : ((N : ℕ) : ℝ) < (R + 1) / q + 1 := Nat.ceil_lt_add_one (by positivity)
  have hside : (2 * (N : ℕ) + 1 : ℕ) ≤ (2 * R + 5) / q := by
    have hqinv : 1 ≤ q⁻¹ := by
      rw [← one_div, one_le_div₀ hq]
      exact hq1
    have hceil' : (N : ℝ) < (R + 1) * q⁻¹ + 1 := by simpa [div_eq_mul_inv] using hceil
    have hN' : 2 * (N : ℝ) + 1 < 2 * ((R + 1) * q⁻¹ + 1) + 1 := by nlinarith [hceil']
    have hbound' : 2 * ((R + 1) * q⁻¹ + 1) + 1 ≤ (2 * R + 5) * q⁻¹ := by
      nlinarith [hqinv, hR]
    have hbound : 2 * ((R + 1) / q + 1) + 1 ≤ (2 * R + 5) / q := by
      simpa [div_eq_mul_inv] using hbound'
    push_cast
    exact hN'.le.trans hbound
  rw [latticeIndices_card]
  have hsideR : (2 * (N : ℝ) + 1) ^ 2 ≤ ((2 * R + 5) / q) ^ 2 := by
    have hbase : (2 * (N : ℝ) + 1) ≤ (2 * R + 5) / q := by exact_mod_cast hside
    exact pow_le_pow_left₀ (by positivity) hbase 2
  push_cast
  exact hsideR

private theorem epsilon_power_lt_one {ε a : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) :
    ε ^ a < 1 := by
  rw [Real.rpow_def_of_pos hε]
  apply (Real.exp_lt_one_iff).2
  nlinarith [Real.log_neg hε hε1]

/-- A finite-grid estimate for one orientation of the contraction statement. -/
private theorem one_direction_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (d d' : Ω → LSCMetric) (κ : Set.Ioi (0 : ℝ) → ℝ)
    (R C ε s t told d₀ η A K cconc aconc : ℝ)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hε : 0 < ε) (hε1 : ε < 1)
    (h41 : Lemma41Stmt) (hs : 0 < s) (hst : s < t) (hquarter : 4 * s ≤ t)
    (ht : t < told) (htold : told < 1)
    (hd₀ : 0 < d₀) (hη : 0 < η) (hηsmall : 2 * Real.sqrt η < 1 / 10)
    (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hscaleCut : ε < Real.exp (Real.log (1 / 513) / s))
    (holdCut : ε < Real.exp (Real.log (η / 2052) / (told - t)))
    (Sε : Finset ℤ) (hS : Sε ⊆ Iteration.radiusExponents ε s t)
    (hSCard : (Iteration.radiusExponents ε s t).card ≤ 3 * Sε.card)
    (hκ : ∀ j ∈ Sε, κ (bandRad j) ≤ K)
    (E : ℝ → ℝ → ℂ → Set Ω)
    (hcconc : 0 < cconc) (haconc : 0 < aconc) (haconc1 : aconc < 1)
    (hEvent : ∀ r, ε ^ t ≤ r → r ≤ ε ^ s → ∀ z,
      MeasurableSet[fieldSigmaClosed0
        (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
        {x | r / 16 ≤ dist x z ∧ dist x z ≤ 32 * r}] (E ε r z) ∧
      ENNReal.ofReal aconc ≤ P (E ε r z))
    (hRoot : ∀ (r : ℝ) (hr : 0 < r) (z : ℂ),
      ∀ᵐ ω ∂P, ω ∈ E ε r z →
        GoodScale (d ω) (d' ω) z r hr η d₀ A (κ ⟨r, hr⟩))
    (hconc : ∀ (z : ℂ) (r : ℕ → ℝ) (E' : ℕ → Set Ω),
      (∀ k, 1 ≤ k → 0 < r k) →
      (∀ j k, 1 ≤ j → j ≤ k → r k ≤ r j) →
      (∀ k, 1 ≤ k → r (k + 1) / r k ≤ (1 / 4096 : ℝ)) →
      (∀ k, 1 ≤ k → MeasurableSet[
        fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) z))
          {x | r k / 16 ≤ dist x z ∧ dist x z ≤ 32 * r k}] (E' k)) →
      (∀ k, 1 ≤ k → ENNReal.ofReal aconc ≤ P (E' k)) →
      ∀ n : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E' n ω : ℝ) < (1 / 2) * n} ≤
        ENNReal.ofReal (cconc * Real.exp (-(16 * Real.log 4096 + 1) * n)))
    (hcountCut : ε < Real.exp (-(12 * Real.log (Iteration.annulusBase)) / t)) :
    P {ω | CompIn (d ω) (d' ω) (ball 0 (R + 2)) R C (513 * ε ^ told) ∧
      ¬ CompIn (d ω) (d' ω) (ball 0 (R + 2)) R
        (Iteration.contractionFactor C K (1 / (5 * A)) d₀) (513 * ε ^ s)} ≤
      ENNReal.ofReal ((cconc * Real.exp ((16 * Real.log 4096 + 1) / 3)) *
        (100 * (2 * R + 5)) ^ 2 * ε ^ (2 * t)) := by
  classical
  let q := ε ^ t / 100
  let N : ℕ := ⌈(R + 1) / q⌉₊
  let G := latticeIndices N
  let badCenter : ℂ → Set Ω := fun z => {ω | ∀ j ∈ Sε, ω ∉ E ε (bandRad j) z}
  let bad := ⋃ ij ∈ G, badCenter (latticePoint q ij)
  let ex : ℂ → Finset ℤ → Set Ω := fun z js => ⋃ j ∈ js,
    {ω | ω ∈ E ε (bandRad j) z ∧
      ¬ GoodScale (d ω) (d' ω) z (bandRad j) (bandRad j).property η d₀ A (κ (bandRad j))}
  let null := ⋃ ij ∈ G, ex (latticePoint q ij) Sε
  have htpos : 0 < t := by linarith
  have hpowpos : 0 < ε ^ t := Real.rpow_pos_of_pos hε t
  have hpowlt : ε ^ t < 1 := epsilon_power_lt_one hε hε1 htpos
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hN : (R + 1) / q ≤ (N : ℝ) := by
    dsimp [N]
    exact Nat.le_ceil _
  have hGridCard : (G.card : ℝ) ≤ ((2 * R + 5) / q) ^ 2 := by
    dsimp [G]
    exact lattice_card_bound R q hR hq hq1
  have hcount : 2 ≤ Sε.card :=
    selected_count_ge_two hε hε1 hs hst hquarter Sε hS hSCard hcountCut
  have hSsubset : Sε ⊆ Iteration.radiusExponents ε s t := hS
  have hnoGood : ∀ z, P (badCenter z) ≤ ENNReal.ofReal
      (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t)) := by
    intro z
    have hbase := noGoodSelected_probability P h hh
      (16 * Real.log 4096 + 1) (1 / 2) aconc cconc ε s t
      (by positivity) (by norm_num) (by norm_num) haconc haconc1 hcconc
      (by
        intro z' r E' hr hanti hratio hmeas hprob n
        exact hconc z' r E' hr hanti hratio hmeas hprob n)
      E (by
        intro r hlow hhigh z'
        exact hEvent r hlow hhigh z') hε hε1 hs hst Sε hS hcount z
    have hlogB : 0 < Real.log (Iteration.annulusBase) :=
      Real.log_pos (by norm_num [Iteration.annulusBase])
    have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
    have hlogcut := Real.log_lt_log hε hcountCut
    rw [Real.log_exp] at hlogcut
    have hL : 12 * Real.log (Iteration.annulusBase) / t < -Real.log ε := by
      simpa [neg_div] using neg_lt_neg hlogcut
    have hcountLower := Iteration.radiusExponents_count_lower hε hε1 hs hst
    have hwidth : 3 * t / 4 ≤ t - s := by nlinarith [hquarter]
    have hLpos : 0 < -Real.log ε := by linarith
    have hcnt : (Sε.card : ℝ) ≥ t / 4 * (-Real.log ε) / Real.log (Iteration.annulusBase) - 1 / 3 := by
      have hmul := mul_le_mul_of_nonneg_right hwidth hLpos.le
      have hdiv := (div_le_div_iff_of_pos_right hlogB).2 hmul
      have hselectCast : ((Iteration.radiusExponents ε s t).card : ℝ) ≤ 3 * (Sε.card : ℝ) := by
        exact_mod_cast hSCard
      have hfullge : (Iteration.radiusExponents ε s t).card ≥
          (3 * t / 4) * (-Real.log ε) / Real.log (Iteration.annulusBase) - 1 := by
        linarith [hdiv, hcountLower]
      have hfullhalf : 3 * (t / 4 * (-Real.log ε) / Real.log (Iteration.annulusBase)) - 1 ≤
          (Iteration.radiusExponents ε s t).card := by
        convert hfullge using 1 <;> ring
      nlinarith [hfullhalf]
    have ha : 0 < (16 * Real.log (Iteration.annulusBase) + 1 : ℝ) := by positivity
    have hrate : 4 * t * (-Real.log ε) - (16 * Real.log (Iteration.annulusBase) + 1) / 3 ≤
        (16 * Real.log (Iteration.annulusBase) + 1) * (Sε.card : ℝ) := by
      have hcoef : 4 ≤ (16 * Real.log (Iteration.annulusBase) + 1) /
          (4 * Real.log (Iteration.annulusBase)) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log (Iteration.annulusBase))).2
        nlinarith [hlogB]
      have hcntMul := mul_le_mul_of_nonneg_left hcnt ha.le
      have hsub : 4 * t * (-Real.log ε) ≤
          ((16 * Real.log (Iteration.annulusBase) + 1) /
            (4 * Real.log (Iteration.annulusBase))) * t * (-Real.log ε) := by
        have := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ t * (-Real.log ε) by positivity)
        nlinarith [hlogB]
      have hsub' : 4 * t * (-Real.log ε) ≤
          (16 * Real.log (Iteration.annulusBase) + 1) *
            (t / 4 * (-Real.log ε) / Real.log (Iteration.annulusBase)) := by
        calc
          4 * t * (-Real.log ε) ≤
              ((16 * Real.log (Iteration.annulusBase) + 1) /
                (4 * Real.log (Iteration.annulusBase))) * t * (-Real.log ε) := hsub
          _ = (16 * Real.log (Iteration.annulusBase) + 1) *
                (t / 4 * (-Real.log ε) / Real.log (Iteration.annulusBase)) := by ring
      nlinarith [hcntMul, hsub']
    have hexp : Real.exp (-((16 * Real.log (Iteration.annulusBase) + 1) * (Sε.card : ℝ))) ≤
        Real.exp ((16 * Real.log (Iteration.annulusBase) + 1) / 3) * ε ^ (4 * t) := by
      have hrpow : ε ^ (4 * t) = Real.exp (4 * t * Real.log ε) := by
        rw [Real.rpow_def_of_pos hε]
        ring_nf
      rw [hrpow, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hrate]
    have hval : cconc * Real.exp (-(16 * Real.log 4096 + 1) * Sε.card) ≤
        cconc * (Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hexp' : Real.exp (-(16 * Real.log 4096 + 1) * (Sε.card : ℝ)) ≤
          Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t) := by
        convert hexp using 1 <;> norm_num [Iteration.annulusBase] <;> ring
      exact hexp'
    exact hbase.trans (ENNReal.ofReal_le_ofReal (by
      have := hval
      simpa [mul_assoc] using this))
  have hbadBound : P bad ≤ ENNReal.ofReal
      ((G.card : ℝ) * (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t))) := by
    calc
      P bad ≤ ∑ ij ∈ G, P (badCenter (latticePoint q ij)) := by
        exact measure_biUnion_finset_le _ _
      _ ≤ ∑ ij ∈ G, ENNReal.ofReal
          (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t)) := by
        apply Finset.sum_le_sum
        intro ij hij
        exact hnoGood (latticePoint q ij)
      _ = ENNReal.ofReal
          ((G.card : ℝ) * (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * ε ^ (4 * t))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (show 0 ≤ (G.card : ℝ) by positivity)]
  have hbadBound' : P bad ≤ ENNReal.ofReal
      ((cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * (100 * (2 * R + 5)) ^ 2) *
        ε ^ (2 * t)) := by
    refine hbadBound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hgrid : (G.card : ℝ) ≤ (100 * (2 * R + 5)) ^ 2 / (ε ^ t) ^ 2 := by
      have := hGridCard
      dsimp [q] at this
      have hp : 0 < ε ^ t := hpowpos
      have hqeq : ((2 * R + 5) / (ε ^ t / 100)) ^ 2 =
          (100 * (2 * R + 5)) ^ 2 / (ε ^ t) ^ 2 := by field_simp
      simpa [hqeq] using this
    have hpow4 : ε ^ (4 * t) = (ε ^ t) ^ 4 := by
      rw [show 4 * t = t * 4 by ring, Real.rpow_mul (le_of_lt hε)]
      norm_num
    have hpow2 : ε ^ (2 * t) = (ε ^ t) ^ 2 := by
      rw [show 2 * t = t * 2 by ring, Real.rpow_mul (le_of_lt hε)]
      norm_num
    have hfac0 : 0 ≤ cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) := by positivity
    rw [hpow4, hpow2]
    have hfactor : 0 ≤ (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3)) * (ε ^ t) ^ 4 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hgrid hfactor
    calc
      (G.card : ℝ) * ((cconc * Real.exp ((16 * Real.log 4096 + 1) / 3)) * (ε ^ t) ^ 4) ≤
          ((100 * (2 * R + 5)) ^ 2 / (ε ^ t) ^ 2) *
            ((cconc * Real.exp ((16 * Real.log 4096 + 1) / 3)) * (ε ^ t) ^ 4) := hmul
      _ = (cconc * Real.exp ((16 * Real.log 4096 + 1) / 3)) *
            (100 * (2 * R + 5)) ^ 2 * (ε ^ t) ^ 2 := by
        field_simp [ne_of_gt hpowpos]
  have hnullEach : ∀ ij ∈ G, ∀ j ∈ Sε,
      P {ω | ω ∈ E ε (bandRad j) (latticePoint q ij) ∧
        ¬ GoodScale (d ω) (d' ω) (latticePoint q ij) (bandRad j) (bandRad j).property η d₀ A (κ (bandRad j))} = 0 := by
    intro ij hij j hj
    have hae := hRoot (bandRad j) (bandRad j).property (latticePoint q ij)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with ω hω
    intro hm
    exact hm.2 (hω hm.1)
  have hexNull : P null = 0 := by
    apply le_antisymm
    · calc
        P null ≤ ∑ ij ∈ G, P (ex (latticePoint q ij) Sε) := measure_biUnion_finset_le _ _
        _ ≤ ∑ ij ∈ G, ∑ j ∈ Sε,
            P {ω | ω ∈ E ε (bandRad j) (latticePoint q ij) ∧
              ¬ GoodScale (d ω) (d' ω) (latticePoint q ij) (bandRad j) (bandRad j).property η d₀ A (κ (bandRad j))} := by
          apply Finset.sum_le_sum
          intro ij hij
          exact measure_biUnion_finset_le _ _
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro ij hij
          apply Finset.sum_eq_zero
          intro j hj
          exact hnullEach ij hij j hj
    · exact bot_le
  have hfailSubset : {ω | CompIn (d ω) (d' ω) (ball 0 (R + 2)) R C (513 * ε ^ told) ∧
      ¬ CompIn (d ω) (d' ω) (ball 0 (R + 2)) R
        (Iteration.contractionFactor C K (1 / (5 * A)) d₀) (513 * ε ^ s)} ⊆ bad ∪ null := by
    intro ω hω
    by_contra hnot
    have hnot' : ω ∉ bad ∧ ω ∉ null := by simpa [Set.mem_union] using hnot
    have hωbad : ω ∉ bad := hnot'.1
    have hωnull : ω ∉ null := hnot'.2
    have hrmin : 0 < ε ^ t := hpowpos
    have hrange : ε ^ t ≤ ε ^ s := by
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (le_of_lt hst)
    have hscaleCut' := rpow_lt_of_exp_cutoff hε (by norm_num : 0 < (1 / 513 : ℝ)) hs hscaleCut
    have hscale : 513 * ε ^ s ≤ 1 := by nlinarith
    have holdPow := rpow_lt_of_exp_cutoff hε (div_pos hη (by norm_num))
      (sub_pos.mpr ht) holdCut
    have holdRel : 513 * ε ^ told < η * ε ^ t / 4 := by
      have hpowOld : ε ^ told = ε ^ t * ε ^ (told - t) := by
        calc
          ε ^ told = ε ^ (t + (told - t)) := by congr 1; ring
          _ = ε ^ t * ε ^ (told - t) := by rw [Real.rpow_add hε]
      have hmul := mul_lt_mul_of_pos_left holdPow (Real.rpow_pos_of_pos hε t)
      rw [hpowOld]
      nlinarith
    have hprior : CompIn (d ω) (d' ω) (ball 0 (R + 2)) R C (513 * ε ^ told) := hω.1
    have hGS : ∀ (Pcurve : ℝ → ℂ) (T : ℝ), IsGeodIn (d ω) Pcurve T R →
        ∀ u ∈ Icc 0 T,
          ∃ c r, ∃ hr : 0 < r, dist c (Pcurve u) < (ε ^ t) / 10 ∧
            r ∈ Icc (ε ^ t) (ε ^ s) ∧
              GoodScale (d ω) (d' ω) c r hr η d₀ A K := by
      intro Pcurve T hgeo u hu
      have huR := hgeo.2.2.2 u hu
      have hcover := lattice_cover q R hq hR N hN (Pcurve u) (by
        simpa [Metric.mem_ball, dist_eq_norm] using huR)
      obtain ⟨ij, hij, hclose⟩ := hcover
      let c : ℂ := latticePoint q ij
      have hnotcenter : ¬ ω ∈ badCenter c := by
        intro hb
        apply hωbad
        exact Set.mem_iUnion₂.mpr ⟨ij, hij, hb⟩
      obtain ⟨j, hj, hE⟩ : ∃ j ∈ Sε, ω ∈ E ε (bandRad j) c := by
        by_contra hn
        apply hnotcenter
        intro j hj
        exact fun hm => hn ⟨j, hj, hm⟩
      have hnotEx : ω ∉ {ω | ω ∈ E ε (bandRad j) c ∧
          ¬ GoodScale (d ω) (d' ω) c (bandRad j) (bandRad j).property η d₀ A (κ (bandRad j))} := by
        intro hm
        apply hωnull
        apply Set.mem_iUnion₂.mpr
        refine ⟨ij, hij, ?_⟩
        change ω ∈ ex c Sε
        change ω ∈ ⋃ j' ∈ Sε,
          {ω | ω ∈ E ε (bandRad j') c ∧
            ¬ GoodScale (d ω) (d' ω) c (bandRad j') (bandRad j').property η d₀ A (κ (bandRad j'))}
        exact Set.mem_iUnion₂.mpr ⟨j, hj, hm⟩
      have hgood0 : GoodScale (d ω) (d' ω) c (bandRad j) (bandRad j).property η d₀ A
          (κ (bandRad j)) := by
        by_contra hn
        exact hnotEx ⟨hE, hn⟩
      have hgood := goodScale_mono_K (bandRad j).property hd₀.le (hκ j hj) hgood0
      have hjfull := hS hj
      have hjcut := (Iteration.radiusExponents_mem_iff_cutoffs hε).1 hjfull
      have hrmem : (bandRad j : ℝ) ∈ Icc (ε ^ t) (ε ^ s) :=
        ⟨hjcut.1.le, hjcut.2.le⟩
      have hdist : dist c (Pcurve u) < (ε ^ t) / 10 := by
        rw [dist_comm]
        dsimp [c, q] at hclose ⊢
        nlinarith
      exact ⟨c, (bandRad j : ℝ), (bandRad j).property, hdist, hrmem, hgood⟩
    have hpriorGS := compIn_contract_of_goodScales h41
      (d ω) (d' ω) R C d₀ η A K (ε ^ t) (ε ^ s) (513 * ε ^ told)
      hC hη hηsmall hd₀.le hA hK hrmin hrange hscale
      (by positivity) holdRel hGS hprior
    exact hω.2 (by simpa [Iteration.contractionFactor] using hpriorGS)
  calc
    P {ω | CompIn (d ω) (d' ω) (ball 0 (R + 2)) R C (513 * ε ^ told) ∧
        ¬ CompIn (d ω) (d' ω) (ball 0 (R + 2)) R
          (Iteration.contractionFactor C K (1 / (5 * A)) d₀) (513 * ε ^ s)}
      ≤ P (bad ∪ null) := measure_mono hfailSubset
    _ ≤ P bad + P null := measure_union_le _ _
    _ ≤ ENNReal.ofReal
        ((cconc * Real.exp ((16 * Real.log 4096 + 1) / 3) * (100 * (2 * R + 5)) ^ 2) *
          ε ^ (2 * t)) := by
      rw [hexNull, add_zero]
      simpa [mul_assoc] using hbadBound'

theorem contraction_of (S : Setup) (hR : RootEventStmt S) (h41 : Lemma41Stmt) :
    ContractionStmt S := by
  let a₀ : ℝ := 16 * Real.log 4096 + 1
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  obtain ⟨p₀, cconc, hp₀, hp₀1, hcconc, hconc⟩ :=
    Concentration.paper_annulus_concentration a₀ (1 / 2) ha₀ (by norm_num) (by norm_num)
  obtain ⟨A, hA, hR₀⟩ := hR p₀ hp₀1
  have hlamPos : 0 < 1 / (5 * A) := by positivity
  have hlamLe : 1 / (5 * A) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 5 * A)]
    nlinarith [hA]
  refine ⟨1 / (5 * A), hlamPos, hlamLe, ?_⟩
  · intro d₀ hd₀ R hR1 s t told C hs hquarter ht htold hC
    obtain ⟨η, hη, hηsmall, hRband⟩ := hR₀ d₀ hd₀
    have hst : s < t := by nlinarith
    obtain ⟨εroot, hεroot, hRoot⟩ := hRband s t hs hst (lt_trans ht htold)
    let εcount := Real.exp (-(12 * Real.log (Iteration.annulusBase)) / t)
    let εscale := Real.exp (Real.log (1 / 513) / s)
    let εold := Real.exp (Real.log (η / 2052) / (told - t))
    let ε₁ := min εroot (min εcount (min εscale εold))
    let β := 2 * t
    let c₁ := cconc * Real.exp (a₀ / 3) * (100 * (2 * R + 5)) ^ 2
    have hcountPos : 0 < εcount := Real.exp_pos _
    have hscalePos : 0 < εscale := Real.exp_pos _
    have holdPos : 0 < εold := Real.exp_pos _
    have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
    have hβ : 0 < β := by dsimp [β]; linarith [hs, hquarter]
    have hc₁ : 0 < c₁ := by dsimp [c₁]; positivity
    refine ⟨β, c₁, ε₁, hβ, hc₁, hε₁, ?_⟩
    intro Ω _ P _ h hh ε hε hεsmall Sε hS hSCard K hKnonneg
    have hεroot' : ε < εroot := lt_of_lt_of_le hεsmall (by dsimp [ε₁]; exact min_le_left _ _)
    have hεsub : ε < min εcount (min εscale εold) :=
      lt_of_lt_of_le hεsmall (by dsimp [ε₁]; exact min_le_right _ _)
    have hεcount' : ε < εcount := lt_of_lt_of_le hεsub (min_le_left _ _)
    have hεsub2 : ε < min εscale εold := lt_of_lt_of_le hεsub (min_le_right _ _)
    have hεscale' : ε < εscale := lt_of_lt_of_le hεsub2 (min_le_left _ _)
    have hεold' : ε < εold := lt_of_lt_of_le hεsub2 (min_le_right _ _)
    have hε1 : ε < 1 := hε.2
    obtain ⟨E, hEvent, hRootAE⟩ := hRoot P h hh
    have hrootF : ∀ (r : ℝ) (hr : 0 < r) (z : ℂ),
        ∀ᵐ ω ∂P, ω ∈ E ε r z →
          GoodScale (S.D (h ω)) (locMetric S ε hε (h ω)) z r hr η d₀ A
            (kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩) := by
      intro r hr z
      have hpair := hRootAE ε hε r hr z
      filter_upwards [hpair] with ω hω
      intro hmem
      exact (hω hmem).1
    have hrootR : ∀ (r : ℝ) (hr : 0 < r) (z : ℂ),
        ∀ᵐ ω ∂P, ω ∈ E ε r z →
          GoodScale (locMetric S ε hε (h ω)) (S.D (h ω)) z r hr η d₀ A
            ((kappaS S ⟨ε, hε.1⟩ ⟨r, hr⟩)⁻¹) := by
      intro r hr z
      have hpair := hRootAE ε hε r hr z
      filter_upwards [hpair] with ω hω
      intro hmem
      exact (hω hmem).2
    have hconc' : ∀ (z : ℂ) (r : ℕ → ℝ) (E' : ℕ → Set Ω),
        (∀ k, 1 ≤ k → 0 < r k) →
        (∀ j k, 1 ≤ j → j ≤ k → r k ≤ r j) →
        (∀ k, 1 ≤ k → r (k + 1) / r k ≤ (1 / 4096 : ℝ)) →
        (∀ k, 1 ≤ k → MeasurableSet[
          fieldSigmaClosed0 (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) z))
            {x | r k / 16 ≤ dist x z ∧ dist x z ≤ 32 * r k}] (E' k)) →
        (∀ k, 1 ≤ k → ENNReal.ofReal p₀ ≤ P (E' k)) →
        ∀ n : ℕ, P {ω | (LQGMetric.Blueprint.countOcc E' n ω : ℝ) < (1 / 2) * n} ≤
          ENNReal.ofReal (cconc * Real.exp (-a₀ * n)) := by
      intro z r E' hr hanti hratio hmeas hprob n
      simpa [a₀] using hconc P h hh z r E' hr hanti hratio hmeas hprob n
    constructor
    · intro hκF
      have hκF' : ∀ j ∈ Sε,
          (fun r : Set.Ioi (0 : ℝ) => kappaS S ⟨ε, hε.1⟩ r) (bandRad j) ≤ K := hκF
      exact one_direction_bound P h hh (fun ω => S.D (h ω))
        (fun ω => locMetric S ε hε (h ω))
        (fun r : Set.Ioi (0 : ℝ) => kappaS S ⟨ε, hε.1⟩ r)
        R C ε s t told d₀ η A K cconc p₀ hR1 hC hε.1 hε1 h41 hs hst hquarter ht htold
        hd₀ hη hηsmall hA hKnonneg hεscale' hεold' Sε hS hSCard hκF' E hcconc hp₀ hp₀1
        (by
          intro r hlow hhigh z
          exact hEvent ε hε.1 hεroot' r hlow hhigh z)
        hrootF hconc' hεcount'
    · intro hκR
      have hκR' : ∀ j ∈ Sε,
          (fun r : Set.Ioi (0 : ℝ) => (kappaS S ⟨ε, hε.1⟩ r)⁻¹) (bandRad j) ≤ K := hκR
      exact one_direction_bound P h hh (fun ω => locMetric S ε hε (h ω))
        (fun ω => S.D (h ω))
        (fun r : Set.Ioi (0 : ℝ) => (kappaS S ⟨ε, hε.1⟩ r)⁻¹)
        R C ε s t told d₀ η A K cconc p₀ hR1 hC hε.1 hε1 h41 hs hst hquarter ht htold
        hd₀ hη hηsmall hA hKnonneg hεscale' hεold' Sε hS hSCard hκR' E hcconc hp₀ hp₀1
        (by
          intro r hlow hhigh z
          exact hEvent ε hε.1 hεroot' r hlow hhigh z)
        hrootR hconc' hεcount'

end SupercriticalLFPPAS.ContractionStep
