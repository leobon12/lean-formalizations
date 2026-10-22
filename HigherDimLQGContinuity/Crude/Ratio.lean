import HigherDimLQGContinuity.Crude.Moment
import HigherDimLQGContinuity.Crude.Quantile
import HigherDimLFPP.Field.FiniteRange
import HigherDimLQGMetric.DGZ.Sec41Prob

/-!
# Crude quantile ratio from independent dyadic bands

This is Appendix A's CRUDE estimate. The product-law argument is the dimension-free
version of `LQGMetric.DG.dg_lemma25`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLQGMetric

/-- Continuous versions of disjoint bands are independent as continuous-map random elements. -/
private theorem crude_indep_contField {d : ℕ} {κ : Rd d → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {a b a' b' : ℝ}
    {F G : Rd d → Ω → ℝ} (hW : IsWhiteNoise P W)
    (hκ : IsLFPPKernel κ) (hF : IsBandVersion P W κ a b F)
    (hG : IsBandVersion P W κ a' b' G) (ha : 0 < a) (ha' : 0 < a')
    (h : b ≤ a') :
    IndepFun (contField F hF.continuous) (contField G hG.continuous) P := by
  have hi := IsBandVersion.indepFun_of_le hW hκ hF hG ha ha' h
  change Indep (MeasurableSpace.comap (contField F hF.continuous) inferInstance)
    (MeasurableSpace.comap (contField G hG.continuous) inferInstance) P
  rw [measurableSpace_continuousMap_eq_comap, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]
  exact hi

/-- The original one-space law inherits the product-law bad-ratio bound. -/
private theorem crude_bad_ratio_bands {d : ℕ} (hd : 0 < d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W) {a b a' b' : ℝ}
    {F G : Rd d → Ω → ℝ} (hF : IsBandVersion P W κ a b F)
    (hG : IsBandVersion P W κ a' b' G) (ha : 0 < a) (hab : a ≤ b)
    (ha' : 0 < a') (hba' : b ≤ a') (ξ C : ℝ) (hC : 0 < C) :
    P {ω | C * lfppDistance d ξ (fun z => G z ω) <
        lfppDistance d ξ (fun z => G z ω + F z ω)} ≤
      ENNReal.ofReal (Real.exp (Real.log (b / a) * ξ ^ 2 / 2) / C) := by
  let g : Ω → C(Rd d, ℝ) := contField G hG.continuous
  let f : Ω → C(Rd d, ℝ) := contField F hF.continuous
  let μ : Measure C(Rd d, ℝ) := P.map g
  let ν : Measure C(Rd d, ℝ) := P.map f
  have hgm : Measurable g := measurable_contField hG.continuous hG.measurable
  have hfm : Measurable f := measurable_contField hF.continuous hF.measurable
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  letI : IsProbabilityMeasure μ := by infer_instance
  letI : IsProbabilityMeasure ν := by infer_instance
  have hi : IndepFun g f P :=
    (crude_indep_contField hW hκ hF hG ha ha' hba').symm
  have hprod : P.map (fun ω => (g ω, f ω)) = μ.prod ν :=
    hi.map_prod_eq_prod_map_map hgm.aemeasurable hfm.aemeasurable
  let K := Real.exp (Real.log (b / a) * ξ ^ 2 / 2)
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hmom : ∀ z : Rd d, ∫⁻ u : C(Rd d, ℝ),
      ENNReal.ofReal (Real.exp (ξ * u z)) ∂ν ≤ ENNReal.ofReal K := by
    intro z
    exact (crude_band_exp_lintegral hF hW hκ ha hab ξ z).le
  have hbound := crude_product_bad_ratio (μ := μ) (ν := ν) hd ξ K C hK hC hmom
  have hXmeas : Measurable (fun p : C(Rd d, ℝ) × C(Rd d, ℝ) =>
      lfppDistance d ξ p.1) := (measurable_lfppDistance_continuousMap ξ).comp measurable_fst
  have hYmeas : Measurable (fun p : C(Rd d, ℝ) × C(Rd d, ℝ) =>
      lfppDistance d ξ (p.1 + p.2)) := by
    change Measurable (fun p : C(Rd d, ℝ) × C(Rd d, ℝ) =>
      lfppDistance d ξ (fun z => p.1 z + p.2 z))
    exact HigherDimLFPP.measurable_lfppDistance
      (fun p => p.1.continuous.add p.2.continuous)
      (fun z => ((continuous_eval_const z).measurable.comp measurable_fst).add
        ((continuous_eval_const z).measurable.comp measurable_snd)) ξ
  have hEvent : MeasurableSet {p : C(Rd d, ℝ) × C(Rd d, ℝ) |
      C * lfppDistance d ξ p.1 < lfppDistance d ξ (p.1 + p.2)} :=
    measurableSet_lt (hXmeas.const_mul C) hYmeas
  calc
    P {ω | C * lfppDistance d ξ (fun z => G z ω) <
        lfppDistance d ξ (fun z => G z ω + F z ω)}
        = P.map (fun ω => (g ω, f ω))
          {p : C(Rd d, ℝ) × C(Rd d, ℝ) |
            C * lfppDistance d ξ p.1 < lfppDistance d ξ (p.1 + p.2)} := by
            rw [Measure.map_apply (hgm.prodMk hfm) hEvent]
            rfl
    _ = (μ.prod ν) _ := by rw [hprod]
    _ ≤ _ := hbound

/-- The variance of the dyadic fine band is `m log 2`. -/
private theorem crude_dyadic_exp {n m : ℕ} (hmn : m ≤ n) (ξ : ℝ) :
    Real.exp (Real.log (((2 : ℝ)⁻¹ ^ (n - m)) / ((2 : ℝ)⁻¹ ^ n)) * ξ ^ 2 / 2) =
      (2 : ℝ) ^ (ξ ^ 2 * m / 2) := by
  have hratio : ((2 : ℝ)⁻¹ ^ (n - m)) / ((2 : ℝ)⁻¹ ^ n) = (2 : ℝ) ^ m := by
    have hpow : ((2 : ℝ)⁻¹) ^ n = ((2 : ℝ)⁻¹) ^ (n - m) * ((2 : ℝ)⁻¹) ^ m := by
      conv_lhs => rw [(Nat.sub_add_cancel hmn).symm, pow_add]
    rw [hpow]
    field_simp
    rw [← mul_pow]
    norm_num
  rw [hratio, Real.log_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Appendix A, CRUDE: a lower bound on quantile ratios with no subcriticality restriction. -/
theorem crudeLower {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) : CrudeLowerShape d κ := by
  intro ξ hξ q q' hq0 hqq' hq'1 Ω _ P W H hH n m hmn
  let k := n - m
  have hkn : k ≤ n := Nat.sub_le n m
  obtain ⟨F, hF, hDec⟩ := DGZ.exists_band_decomp hκ hH hkn
  have hb : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hkn
  have hgapFinite : q' - q ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_lt hq'1) tsub_le_self
  have hgapPos : 0 < (q' - q).toReal :=
    ENNReal.toReal_pos (tsub_pos_of_lt hqq').ne' hgapFinite
  let K : ℝ := (2 : ℝ) ^ (ξ ^ 2 * m / 2)
  let C : ℝ := (q' - q).toReal⁻¹ * K
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := mul_pos (inv_pos.2 hgapPos) hK
  have hquot : K / C = (q' - q).toReal := by
    dsimp [C]
    field_simp [ne_of_gt hgapPos, ne_of_gt hK]
  have hband : P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
      lfppDistance d ξ (fun z => H k z ω + F z ω)} ≤ q' - q := by
    have hbnd := crude_bad_ratio_bands (Nat.zero_lt_of_lt hd) hκ hH.whiteNoise hF
      (hH.band k) ha hab hb le_rfl ξ C hC
    rw [crude_dyadic_exp hmn ξ, ← show K = (2 : ℝ) ^ (ξ ^ 2 * m / 2) from rfl,
      hquot] at hbnd
    simpa only [ENNReal.ofReal_toReal hgapFinite] using hbnd
  have hbad : P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
      lfppDistance d ξ (fun z => H n z ω)} ≤ q' - q := by
    have heq : P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
        lfppDistance d ξ (fun z => H n z ω)} =
      P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
        lfppDistance d ξ (fun z => H k z ω + F z ω)} := by
      apply measure_congr
      filter_upwards [hDec] with ω hω
      have hfield : (fun z => H n z ω) = (fun z => H k z ω + F z ω) := funext (hω)
      rw [hfield]
    rwa [heq]
  have hq := crude_quantile_of_bad_ratio hH ξ n k hq0 hqq' hq'1 hC.le hbad
  simpa only [k, C, K] using hq

end HigherDimLQGContinuity
