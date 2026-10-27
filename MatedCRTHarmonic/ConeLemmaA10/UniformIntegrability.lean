import MatedCRTHarmonic.LQGCoord.WPArea
import MatedCRTHarmonic.GMCFacts.BallMoment

/-!
# First moment preservation in the normalized whole-plane window

At normalization scale `δ = 1`, the factor relating `areaS` to `wMass` is one almost surely
for a normalized whole-plane GFF. The `WMassLimit` therefore identifies with the continuum
LQG integral, and its quantitative `L¹` rate preserves the exact finite-level first moment.

The existing `Win S 1` API requires `S ⊆ closedBall 0 (1 / 4)`. This file deliberately does
not claim the corresponding result for every test supported in the unit disk.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric
open LQGMetric.DGMC LQGMetric.DGMC.Neg3
open MatedCRTHarmonic.LQGCoord
open MatedCRTHarmonic.GMCFacts
open MatedCRTHarmonic.CellScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistC}
variable {S : Set ℂ} {f : ℂ → ℝ} {M : ℝ}

def unitApproxMomentQ (γ : ℝ) : ℝ := (1 + 4 / γ ^ 2) / 2

def unitApproxMomentP (γ : ℝ) : ℝ := (1 + unitApproxMomentQ γ) / 2

/-- A uniform moment strictly above one for an unrecentred unit-square approximation. This
uses the checked recentred square moment from `BallMoment` and Hölder with the remaining single
Gaussian circle-average factor. -/
theorem exists_unitSquare_approx_moment
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (z₀ : ℂ) :
    1 < unitApproxMomentP γ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℕ,
      ∫⁻ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
        (LQGMetric.DGMC.Neg3.sqQ z₀ 0) ^ unitApproxMomentP γ ∂P ≤ C := by
  let q : ℝ := unitApproxMomentQ γ
  let p : ℝ := unitApproxMomentP γ
  have hthreshold : 1 < 4 / γ ^ 2 := by
    rw [one_lt_div (sq_pos_of_pos hγ)]
    nlinarith
  have hq1 : 1 < q := by dsimp [q, unitApproxMomentQ]; linarith
  have hqT : q < 4 / γ ^ 2 := by dsimp [q, unitApproxMomentQ]; linarith
  have hp1 : 1 < p := by
    dsimp [p, unitApproxMomentP, unitApproxMomentQ]
    linarith
  have hpq : p < q := by
    dsimp [p, q, unitApproxMomentP, unitApproxMomentQ]
    linarith
  let a : ℝ := q / p
  let b : ℝ := q / (q - p)
  have hab : a.HolderConjugate b := by
    refine ⟨?_, ?_, ?_⟩
    · dsimp [a, b]
      rw [inv_div, inv_div, ← add_div, add_sub_cancel,
        div_self (by linarith : q ≠ 0), inv_one]
    · dsimp [a]
      exact div_pos (by linarith) (by linarith)
    · dsimp [b]
      exact div_pos (by linarith) (by linarith)
  let z : ℂ := z₀ + sqCentre
  have hcorner : sqCorner z (QuantumZipper.radius 0) = z₀ := by
    simp [z, sqCorner, sqCentre, QuantumZipper.radius]
  obtain ⟨Cs, hCs, hs⟩ := exists_lintegral_sq_rpow_le_pos hH hHm hγ hq1 hqT
  let R : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ENNReal.ofReal ((4 : ℝ)⁻¹ ^ 2) *
      ∫⁻ w in sqQ (sqCorner z (QuantumZipper.radius 0)) 0,
        nDens γ H z 4 (QuantumZipper.radius (0 + k)) w ω
  have hRm : ∀ k, Measurable (R k) := fun k => by
    have hr : 0 < QuantumZipper.radius (0 + k) := QuantumZipper.radius_pos _
    have hjm := measurable_uncurry_coord hH hHm hr
    have hd : Measurable fun p : ℂ × Ω =>
        nDens γ H z 4 (QuantumZipper.radius (0 + k)) p.1 p.2 :=
      ENNReal.measurable_ofReal.comp
        (((hjm.sub ((hHm 4 z).comp measurable_snd)).const_mul γ).exp.const_mul _)
    exact hd.lintegral_prod_left'.const_mul _
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (γ * H 4 z ω))
  have hGm : Measurable G :=
    ENNReal.measurable_ofReal.comp (((hHm 4 z).const_mul γ).exp)
  have hgauss : ∫⁻ ω, G ω ^ (p * b) ∂P < ⊤ := by
    have he : ∀ ω, G ω ^ (p * b) =
        ENNReal.ofReal (Real.exp ((p * b * γ) * H 4 z ω)) := fun ω => by
      simp only [G]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      ring
    simp_rw [he]
    rw [LQGMetric.DG.lintegral_exp_circleAvg hH (by norm_num : (0 : ℝ) < 4) z
      (p * b * γ)]
    exact ENNReal.ofReal_lt_top
  let K : ℝ≥0∞ := ENNReal.ofReal (4 ^ (2 + γ ^ 2 / 2))
  let C : ℝ≥0∞ := K ^ p *
    (Cs ^ (1 / a) * (∫⁻ ω, G ω ^ (p * b) ∂P) ^ (1 / b))
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by linarith : 0 ≤ p) ENNReal.ofReal_ne_top)
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / a) hCs.ne)
        (ENNReal.rpow_lt_top_of_nonneg (by positivity : 0 ≤ 1 / b) hgauss.ne))
  refine ⟨hp1, C, hC, fun k => ?_⟩
  have hsk : ∫⁻ ω, R k ω ^ q ∂P ≤ Cs := by
    apply hs z 4 0 k (by norm_num)
    · norm_num [QuantumZipper.radius]
    · norm_num [QuantumZipper.radius]
  have hfac : ∀ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) =
      K * G ω * R k ω := by
    intro ω
    rw [← hcorner]
    have hh := lqgApprox_sq_eq (H := H) γ z (by norm_num : (0 : ℝ) < 4) 0 k ω
    simp only [zero_add] at hh
    rw [hh]
    rw [ENNReal.ofReal_mul (by positivity)]
    simp only [K, G, R, zero_add]
  calc
    ∫⁻ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ p ∂P
        = K ^ p * ∫⁻ ω, (R k ω ^ p) * (G ω ^ p) ∂P := by
          have he : (fun ω =>
              MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) ^ p) =
              fun ω => K ^ p * (R k ω ^ p * G ω ^ p) := by
            funext ω
            rw [hfac, ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p),
              ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p)]
            ac_rfl
          rw [he, lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg
            (by linarith : 0 ≤ p) ENNReal.ofReal_ne_top)]
    _ ≤ K ^ p * ((∫⁻ ω, (R k ω ^ p) ^ a ∂P) ^ (1 / a) *
          (∫⁻ ω, (G ω ^ p) ^ b ∂P) ^ (1 / b)) := by
          gcongr
          exact ENNReal.lintegral_mul_le_Lp_mul_Lq P hab
            ((hRm k).pow_const p).aemeasurable (hGm.pow_const p).aemeasurable
    _ = K ^ p * ((∫⁻ ω, R k ω ^ q ∂P) ^ (1 / a) *
          (∫⁻ ω, G ω ^ (p * b) ∂P) ^ (1 / b)) := by
          congr 3 <;> apply lintegral_congr <;> intro ω
          · rw [← ENNReal.rpow_mul]
            congr 1
            dsimp [a]
            field_simp
          · rw [← ENNReal.rpow_mul]
    _ ≤ C := by
          dsimp [C]
          gcongr

/-- The four lower-left corners of unit squares covering the open unit disk. -/
def diskSquareCorners : Finset ℂ :=
  ((Finset.range 2) ×ˢ (Finset.range 2)).image fun a =>
    ⟨(a.1 : ℝ) - 1, (a.2 : ℝ) - 1⟩

lemma ball_one_subset_diskSquareCorners :
    ball (0 : ℂ) 1 ⊆ ⋃ z₀ ∈ diskSquareCorners, sqQ z₀ 0 := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  have hre : -1 < z.re ∧ z.re < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
    simpa [abs_lt] using h
  have him : -1 < z.im ∧ z.im < 1 := by
    have h := lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    simpa [abs_lt] using h
  let a : ℕ := if 0 ≤ z.re then 1 else 0
  let b : ℕ := if 0 ≤ z.im then 1 else 0
  have ha : a < 2 := by dsimp [a]; split <;> omega
  have hb : b < 2 := by dsimp [b]; split <;> omega
  refine mem_iUnion₂.2 ⟨⟨(a : ℝ) - 1, (b : ℝ) - 1⟩, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2
      ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb⟩, rfl⟩
  · have hr0 : QuantumZipper.radius 0 = 1 := by simp [QuantumZipper.radius]
    rw [sqQ, hr0, inv_one]
    simp only [Set.mem_setOf_eq, one_smul]
    change z - ⟨(a : ℝ) - 1, (b : ℝ) - 1⟩ ∈ cell0
    constructor
    · dsimp [a]
      split_ifs <;> norm_num <;> linarith [hre.1, hre.2]
    · constructor
      · dsimp [a]
        split_ifs <;> norm_num <;> linarith [hre.1, hre.2]
      · constructor
        · dsimp [b]
          split_ifs <;> norm_num <;> linarith [him.1, him.2]
        · dsimp [b]
          split_ifs <;> norm_num <;> linarith [him.1, him.2]

lemma finset_sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (g : ι → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ s, g i) ^ p ≤ (s.card : ℝ≥0∞) ^ p * ∑ i ∈ s, g i ^ p := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [ENNReal.zero_rpow_of_pos hp]
  obtain ⟨i₀, hi₀, hsup⟩ := Finset.exists_mem_eq_sup s hne g
  calc
    (∑ i ∈ s, g i) ^ p ≤ ((s.card : ℝ≥0∞) * s.sup g) ^ p := by
      apply ENNReal.rpow_le_rpow _ hp.le
      calc
        ∑ i ∈ s, g i ≤ ∑ _i ∈ s, s.sup g :=
          Finset.sum_le_sum fun i hi => Finset.le_sup hi
        _ = (s.card : ℝ≥0∞) * s.sup g := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s.card : ℝ≥0∞) ^ p * g i₀ ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, hsup]
    _ ≤ (s.card : ℝ≥0∞) ^ p * ∑ i ∈ s, g i ^ p := by
      gcongr
      exact Finset.single_le_sum (f := fun i => g i ^ p) (fun _ _ => zero_le) hi₀

lemma measurable_lqgApprox_set
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) (γ : ℝ) (k : ℕ)
    {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun ω => MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω A := by
  have hr : 0 < MatedCRTHarmonic.GMSLemma27.dyadicRadius k := by
    rw [dyadicRadius_eq_radius]
    exact QuantumZipper.radius_pos k
  have hj := measurable_uncurry_coord hH hHm hr
  have hm : Measurable fun p : ℂ × Ω => ENNReal.ofReal
      (MatedCRTHarmonic.GMSLemma27.dyadicRadius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * H (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp))
  simp only [MatedCRTHarmonic.GMSLemma27.lqgApprox, withDensity_apply _ hA]
  exact hm.lintegral_prod_left'

/-- Uniform `p > 1` moment of the dyadic approximation mass of the open unit disk. -/
theorem exists_unitDisk_approx_moment
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    1 < unitApproxMomentP γ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℕ,
      ∫⁻ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
        (ball (0 : ℂ) 1) ^ unitApproxMomentP γ ∂P ≤ C := by
  classical
  have hp : 1 < unitApproxMomentP γ :=
    (exists_unitSquare_approx_moment hH hHm hγ hγ2 0).1
  have hp0 : 0 < unitApproxMomentP γ := zero_lt_one.trans hp
  have hsquares : ∀ z₀ : ℂ, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ k : ℕ,
      ∫⁻ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
        (sqQ z₀ 0) ^ unitApproxMomentP γ ∂P ≤ C := fun z₀ =>
    (exists_unitSquare_approx_moment hH hHm hγ hγ2 z₀).2
  choose C hC hbound using hsquares
  let Ctot : ℝ≥0∞ := (diskSquareCorners.card : ℝ≥0∞) ^ unitApproxMomentP γ *
    ∑ z₀ ∈ diskSquareCorners, C z₀
  have hCtot : Ctot < ⊤ := by
    dsimp [Ctot]
    apply ENNReal.mul_lt_top
    · exact ENNReal.rpow_lt_top_of_nonneg hp0.le (ENNReal.natCast_ne_top _)
    · exact ENNReal.sum_lt_top.2 fun z₀ hz₀ => hC z₀
  refine ⟨hp, Ctot, hCtot, fun k => ?_⟩
  have hcover : ∀ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (ball 0 1) ≤
      ∑ z₀ ∈ diskSquareCorners,
        MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω (sqQ z₀ 0) := fun ω =>
    (measure_mono ball_one_subset_diskSquareCorners).trans (measure_biUnion_finset_le _ _)
  calc
    ∫⁻ ω, MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
        (ball (0 : ℂ) 1) ^ unitApproxMomentP γ ∂P
        ≤ ∫⁻ ω, (diskSquareCorners.card : ℝ≥0∞) ^ unitApproxMomentP γ *
            ∑ z₀ ∈ diskSquareCorners,
              MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
                (sqQ z₀ 0) ^ unitApproxMomentP γ ∂P := by
          apply lintegral_mono
          intro ω
          exact (ENNReal.rpow_le_rpow (hcover ω) hp0.le).trans
            (finset_sum_rpow_le_card_rpow_mul _ _ hp0)
    _ = (diskSquareCorners.card : ℝ≥0∞) ^ unitApproxMomentP γ *
          ∑ z₀ ∈ diskSquareCorners, ∫⁻ ω,
            MatedCRTHarmonic.GMSLemma27.lqgApprox γ H k ω
              (sqQ z₀ 0) ^ unitApproxMomentP γ ∂P := by
          rw [lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top _)),
            lintegral_finsetSum]
          intro z₀ hz₀
          exact ((measurable_lqgApprox_set hH hHm γ k (measurableSet_sqQ z₀ 0)).pow_const _)
    _ ≤ Ctot := by
          dsimp [Ctot]
          exact mul_le_mul le_rfl
            (Finset.sum_le_sum fun z₀ hz₀ => hbound z₀ k) zero_le zero_le

/-- At normalization scale one, every admissible finite-radius normalized mass has the
Lebesgue first moment of its test function. -/
lemma integral_wMass_one_eq (hY : IsNormalizedWPGFF Y P) (γ : ℝ)
    (hW : Win S 1) (hf : WinFun S f M) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1 / 2) :
    ∫ ω, wMass γ Y 1 f s ω ∂P = ∫ z, f z := by
  letI : IsProbabilityMeasure P := hY.1.gaussian.isProbabilityMeasure
  have hprod := integrable_fDens_prod hY.1 γ hW hf hs hs1
  calc
    ∫ ω, wMass γ Y 1 f s ω ∂P
        = ∫ ω, ∫ z in S, f z * wDens γ Y 1 s z ω ∂volume ∂P := by
            apply integral_congr_ae
            exact ae_of_all _ fun ω => wMass_eq_setIntegral hf γ 1 s ω
    _ = ∫ z in S, ∫ ω, f z * wDens γ Y 1 s z ω ∂P ∂volume :=
          integral_integral_swap hprod
    _ = ∫ z in S, f z ∂volume := by
          apply setIntegral_congr_fun hW.meas
          intro z hz
          change (∫ ω, f z * wDens γ Y 1 s z ω ∂P) = f z
          rw [integral_const_mul, (integral_wDens hY.1 γ hs (hW.norm_add_le hz hs1)).2]
          simp
    _ = ∫ z, f z ∂volume :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => hf.zero z hz

/-- Exact first moment for a continuous compactly supported test in the checked `δ = 1`
whole-plane window. -/
theorem integral_lqgArea_test_eq_volume (hY : IsNormalizedWPGFF Y P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : Win S 1) (hf : WinFun S f M) (hfc : Continuous f)
    (hfK : HasCompactSupport f) :
    ∫ ω, (∫ z, f z ∂lqgArea γ (Y ω)) ∂P = ∫ z, f z := by
  letI : IsProbabilityMeasure P := hY.1.gaussian.isProbabilityMeasure
  obtain ⟨L, hL⟩ := exists_wMass_limit hY.1 hγ hγ2 hW hf
  have hident : ∀ᵐ ω ∂P, L ω = ∫ z, f z ∂lqgArea γ (Y ω) := by
    filter_upwards [hL.tendsto, hY.2, ae_hasAreaLimitS_wp hY.1 hγ hγ2]
      with ω hLt hnorm harea
    have hscale : Tendsto (wRad 1) atTop (𝓝[>] (0 : ℝ)) := by
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
      rw [nhdsWithin]
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun k => ?_)⟩
      · convert ht using 1
        funext k
        simp [wRad]
      · exact wRad_pos one_pos k
    have harea' := (harea.2 f hfc hfK).comp hscale
    change Tendsto (fun k => ∫ z, f z ∂areaS γ (Y ω) (wRad 1 k)) atTop
      (𝓝 (∫ z, f z ∂lqgArea γ (Y ω))) at harea'
    have hseq : (fun k => ∫ z, f z ∂areaS γ (Y ω) (wRad 1 k)) =
        fun k => wMass γ Y 1 f (wRad 1 k) ω := by
      funext k
      rw [integral_areaS_eq_wMass γ 1 (wRad_pos one_pos k).le f ω, hnorm]
      simp
    rw [hseq] at harea'
    exact tendsto_nhds_unique hLt harea'
  have hrate : Tendsto
      (fun k => ∫⁻ ω, ‖wMass γ Y 1 f (wRad 1 k) ω - L ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    let b : ℕ → ℝ := fun k =>
      wConst γ * M * 1 ^ (2 + γ ^ 2 / 2) * wq γ ^ k / (1 - wq γ)
    have hbt : Tendsto (fun k => ENNReal.ofReal (b k)) atTop (𝓝 0) := by
      have ht : Tendsto (fun k : ℕ => wq γ ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (wq_pos γ).le (wq_lt_one hγ hγ2)
      have hb0 : Tendsto b atTop (𝓝 0) := by
        dsimp [b]
        convert (tendsto_const_nhds.mul ht).div_const (1 - wq γ) using 1 <;> simp
      convert ENNReal.tendsto_ofReal hb0 using 1 <;> simp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbt
    · exact Eventually.of_forall fun _ => bot_le
    · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hL.rate k hk⟩] with k hk
      simpa only [Real.enorm_eq_ofReal_abs, b] using hk
  have hint : Tendsto (fun k => ∫ ω, wMass γ Y 1 f (wRad 1 k) ω ∂P)
      atTop (𝓝 (∫ ω, L ω ∂P)) := by
    apply tendsto_integral_of_L1 L hL.aemeas.aestronglyMeasurable
    · filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
      exact integrable_wMass hY.1 γ hW hf (wRad_pos one_pos k) (wRad_le_half one_pos hk)
    · exact hrate
  have hconst : ∀ k, 1 ≤ k →
      ∫ ω, wMass γ Y 1 f (wRad 1 k) ω ∂P = ∫ z, f z := fun k hk =>
    integral_wMass_one_eq hY γ hW hf (wRad_pos one_pos k) (wRad_le_half one_pos hk)
  have hevent : ∀ᶠ k in atTop,
      ∫ ω, wMass γ Y 1 f (wRad 1 k) ω ∂P = ∫ z, f z :=
    eventually_atTop.2 ⟨1, fun k hk => hconst k hk⟩
  have hLint : ∫ ω, L ω ∂P = ∫ z, f z := by
    exact tendsto_nhds_unique hint
      (tendsto_const_nhds.congr' (hevent.mono fun _ hk => hk.symm))
  rw [← hLint]
  apply integral_congr_ae
  filter_upwards [hident] with ω hω
  exact hω.symm

end MatedCRTHarmonic.ConeLemmaA10

