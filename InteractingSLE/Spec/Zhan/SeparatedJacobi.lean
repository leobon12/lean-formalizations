/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsBeta
import InteractingSLE.WangWu.SeedJacobi

/-!
# The stationary Jacobi diffusion hits every interior level

Packet PROVE-ZHAN-B3. Astra, *Formalization proofs and dependency audit* (ruling R35), "Two-force transience,
including the seed case" (L1382–L1394): the angle of the two-seed law is a recurrent diffusion, so "every level is hit
almost surely". The transience transfer from the seed to separated pairs (L1416–L1419) only needs that a level is hit
with **positive** probability, which is proved here for every solution of the Jacobi martingale problem on `ℝ`
(`Sec2.Jacobi.IsJacobiMP`) with `κ, a, b > 0`, without scale functions or transition kernels:

* the law of `U_u` is the beta law `π = invLaw κ a b` at every time (`IsJacobiMP.map_eq_invLaw`: moment
  determinacy on `[0, 1]`), which charges every nonempty open subinterval of `(0, 1)`;
* the martingale-problem orthogonality extends from the polynomial weights `U_0^j` to the indicator
  `1{U_0 < α}` (`IsJacobiMP.integral_indicator_increment_eq_zero`: the two weighted laws of `U_0` have the same
  moments);
* if `U` never hits `α` after time `0` with positive probability, then `1{U_0 < α} = 1{U_v < α}` for all `v ≥ 0`
  almost surely, and the first-moment equation `d/dv E[1{U_0 < α} U_v] = a/2 P(U_0 < α) − (a+b)/2 E[1{U_0<α} U_v]`
  forces `E[U_0; U_0 < α] = (a/(a+b)) P(U_0 < α) = E[U_0] P(U_0 < α)`, which is false for a law charging both sides
  of `α` (`IsJacobiMP.measure_exists_eq_pos`).

## Main results

* `IsJacobiMP.map_eq_invLaw`: the one-time law of a Jacobi martingale-problem solution is `invLaw κ a b`.
* `IsJacobiMP.measure_exists_eq_pos`: for `α ∈ (0, 1)`, `0 < P(∃ u ≥ 0, U_u = α)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Sec2.Jacobi Sec2.JacobiExists

/-! ### The beta law charges open subintervals of `(0, 1)` -/

/-- The beta law charges every open subinterval `(s, t)` of `[0, 1]` with `s < t`. -/
theorem invLaw_Ioo_pos {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (ht : t ≤ 1) : 0 < invLaw κ a b (Ioo s t) := by
  set A := 2 * a / κ
  set B := 2 * b / κ
  have hA : 0 < A := by positivity
  have hB : 0 < B := by positivity
  rw [invLaw, betaMeasure, withDensity_apply _ measurableSet_Ioo]
  refine (setLIntegral_pos_iff (measurable_betaPDF' A B)).2 ?_
  have hsub : Ioo s t ⊆ Function.support (betaPDF A B) ∩ Ioo s t := fun x hx => by
    refine ⟨?_, hx⟩
    have hx0 : 0 < x := hs.trans_lt hx.1
    have hx1 : x < 1 := hx.2.trans_le ht
    simp only [Function.mem_support, betaPDF, ne_eq, ENNReal.ofReal_eq_zero, not_le, betaPDFReal,
      hx0, hx1, and_self, ↓reduceIte]
    have := beta_pos hA hB
    have h1 : 0 < x ^ (A - 1) := Real.rpow_pos_of_pos hx0 _
    have h2 : 0 < (1 - x) ^ (B - 1) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {κ a b : ℝ} {U : ℝ → Ω → ℝ}

/-! ### The one-time law -/

/-- **The one-time law of a Jacobi martingale-problem solution is the beta law** `invLaw κ a b`, at every time
(moment determinacy on `[0, 1]`). -/
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.map_eq_invLaw (hU : IsJacobiMP κ a b P U) (hκ : 0 < κ)
    (ha : 0 < a) (hb : 0 < b) (u : ℝ) : P.map (U u) = invLaw κ a b := by
  have := isProbabilityMeasure_invLaw hκ ha hb
  have hm : Measurable (U u) := hU.measurable u
  refine WangWu.JacobiLaw.eq_of_integral_pow_eq ?_ (ae_mem_Icc_invLaw κ a b) fun n => ?_
  · exact (ae_map_iff hm.aemeasurable measurableSet_Icc).mpr (ae_of_all _ fun ω => hU.mem_Icc u ω)
  · rw [integral_map hm.aemeasurable (continuous_pow n).aestronglyMeasurable,
      hU.moment_eq hκ.le (by linarith) n u, integral_pow_invLaw hκ ha hb]

/-- Integrals of bounded functions of `U_u` are integrals against the beta law. -/
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.integral_comp_eq (hU : IsJacobiMP κ a b P U) (hκ : 0 < κ)
    (ha : 0 < a) (hb : 0 < b) (u : ℝ) {g : ℝ → ℝ} (hg : AEStronglyMeasurable g (invLaw κ a b)) :
    ∫ ω, g (U u ω) ∂P = ∫ x, g x ∂(invLaw κ a b) := by
  rw [← hU.map_eq_invLaw hκ ha hb u] at hg ⊢
  rw [integral_map (hU.measurable u).aemeasurable hg]

/-! ### The first-moment increment, weighted by an event of `U_w` -/

omit [IsProbabilityMeasure P] in
/-- The generator on the identity: `L x = a/2 − ((a + b)/2) x`. -/
theorem gen_id_eq (x : ℝ) : gen κ a b (fun y => y ^ 1) x = a / 2 - (a + b) / 2 * x := by
  rw [gen_pow]; simp only [dcoef, ccoef]; ring

omit [IsProbabilityMeasure P] in
theorem gen_id_eq' (x : ℝ) : gen κ a b (fun y => y) x = a / 2 - (a + b) / 2 * x := by
  have h := gen_id_eq (κ := κ) (a := a) (b := b) x
  simp only [pow_one] at h
  exact h

/-- The first-moment martingale-problem increment `U_v − U_w − ∫_w^v (a/2 − ((a+b)/2) U_x) dx`. -/
def jacIncr (a b : ℝ) (U : ℝ → Ω → ℝ) (w v : ℝ) (ω : Ω) : ℝ :=
  U v ω - U w ω - ∫ x in w..v, (a / 2 - (a + b) / 2 * U x ω)

omit [IsProbabilityMeasure P] in
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.measurable_jacIncr (hU : IsJacobiMP κ a b P U) {w v : ℝ}
    (hwv : w ≤ v) : Measurable (jacIncr a b U w v) := by
  have h2 : Measurable fun p : Ω × ℝ => U p.2 p.1 := hU.measurable_uncurry
  have hf : StronglyMeasurable (Function.uncurry fun (ω : Ω) (x : ℝ) => a / 2 - (a + b) / 2 * U x ω) :=
    (measurable_const.sub (h2.const_mul _)).stronglyMeasurable
  have hI : Measurable fun ω => ∫ x in Ioc w v, (a / 2 - (a + b) / 2 * U x ω) :=
    (hf.integral_prod_right (ν := volume.restrict (Ioc w v))).measurable
  have e : (fun ω => ∫ x in w..v, (a / 2 - (a + b) / 2 * U x ω)) =
      fun ω => ∫ x in Ioc w v, (a / 2 - (a + b) / 2 * U x ω) :=
    funext fun ω => intervalIntegral.integral_of_le hwv
  unfold jacIncr
  exact ((hU.measurable v).sub (hU.measurable w)).sub (by rw [e]; exact hI)

omit [IsProbabilityMeasure P] in
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.abs_jacIncr_le (hU : IsJacobiMP κ a b P U) {w v : ℝ}
    (hwv : w ≤ v) (ω : Ω) : |jacIncr a b U w v ω| ≤ 1 + (|a / 2| + |(a + b) / 2|) * (v - w) := by
  have hv := hU.mem_Icc v ω
  have hw := hU.mem_Icc w ω
  have h1 : |U v ω - U w ω| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hv.2, hw.1], by linarith [hv.1, hw.2]⟩
  have h2 : ‖∫ x in w..v, (a / 2 - (a + b) / 2 * U x ω)‖ ≤ (|a / 2| + |(a + b) / 2|) * |v - w| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    have hx := hU.mem_Icc x ω
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le_one_of_mem_Icc hx)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hwv)] at h2
  unfold jacIncr
  exact (abs_sub _ _).trans (add_le_add h1 h2)

omit [IsProbabilityMeasure P] in
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.integrable_jacIncr [IsFiniteMeasure P]
    (hU : IsJacobiMP κ a b P U) {w v : ℝ} (hwv : w ≤ v) : Integrable (jacIncr a b U w v) P :=
  Integrable.of_bound (hU.measurable_jacIncr hwv).aestronglyMeasurable _
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hU.abs_jacIncr_le hwv ω)

omit [IsProbabilityMeasure P] in
/-- The martingale problem with the weights `U_w^j`. -/
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.integral_pow_mul_jacIncr (hU : IsJacobiMP κ a b P U)
    {w v : ℝ} (hwv : w ≤ v) (j : ℕ) : ∫ ω, U w ω ^ j * jacIncr a b U w v ω ∂P = 0 := by
  have h := hU.2.2.2 1 (fun _ => w) (fun _ => j) 1 w v (fun _ => le_rfl) hwv
  simp only [Fin.prod_univ_one, pow_one, gen_id_eq'] at h
  exact h

/-- **The martingale problem with an event of `U_w` as weight**: for a Borel set `S`,
`E[U_v − U_w − ∫_w^v L x (U_x) dx ; U_w ∈ S] = 0` (the two laws of `U_w` weighted by the positive and negative
parts of the increment have the same moments, hence agree). -/
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.setIntegral_jacIncr_eq_zero (hU : IsJacobiMP κ a b P U)
    {w v : ℝ} (hwv : w ≤ v) {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ ω in U w ⁻¹' S, jacIncr a b U w v ω ∂P = 0 := by
  set Z := jacIncr a b U w v with hZ
  have hZm : Measurable Z := hU.measurable_jacIncr hwv
  have hZi : Integrable Z P := hU.integrable_jacIncr hwv
  set fp : Ω → ℝ≥0 := fun ω => (Z ω).toNNReal with hfp
  set fn : Ω → ℝ≥0 := fun ω => (-Z ω).toNNReal with hfn
  have hfpm : Measurable fp := hZm.real_toNNReal
  have hfnm : Measurable fn := hZm.neg.real_toNNReal
  have hUm := hU.measurable w
  have : IsFiniteMeasure (P.withDensity fun ω => (fp ω : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hZi.2
  have : IsFiniteMeasure (P.withDensity fun ω => (fn ω : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hZi.neg.2
  have hIcc : ∀ (f : Ω → ℝ≥0), ∀ᵐ x ∂((P.withDensity fun ω => (f ω : ℝ≥0∞)).map (U w)),
      x ∈ Icc (0 : ℝ) 1 := fun f =>
    (ae_map_iff hUm.aemeasurable measurableSet_Icc).2 (ae_of_all _ fun ω => hU.mem_Icc w ω)
  have hmom : ∀ j : ℕ, ∫ x, x ^ j ∂((P.withDensity fun ω => (fp ω : ℝ≥0∞)).map (U w)) =
      ∫ x, x ^ j ∂((P.withDensity fun ω => (fn ω : ℝ≥0∞)).map (U w)) := by
    intro j
    rw [integral_map hUm.aemeasurable (continuous_pow j).aestronglyMeasurable,
      integral_map hUm.aemeasurable (continuous_pow j).aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hfpm, integral_withDensity_eq_integral_smul hfnm]
    have h0 := hU.integral_pow_mul_jacIncr hwv j
    have hpow : ∀ ω, |U w ω ^ j| ≤ 1 := fun ω => abs_le_one_of_mem_Icc (hU.pow_mem_Icc w ω j)
    have hip : Integrable (fun ω => fp ω • U w ω ^ j) P := by
      refine (hZi.pos_part.mul_bdd (c := 1) ((hUm.pow_const j).aestronglyMeasurable)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpow ω)).congr (ae_of_all _ fun ω => ?_)
      simp only [hfp, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
    have hin : Integrable (fun ω => fn ω • U w ω ^ j) P := by
      refine (hZi.neg.pos_part.mul_bdd (c := 1) ((hUm.pow_const j).aestronglyMeasurable)
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hpow ω)).congr (ae_of_all _ fun ω => ?_)
      simp only [hfn, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal', Pi.neg_apply]
    have e : (fun ω => U w ω ^ j * Z ω) = fun ω => fp ω • U w ω ^ j - fn ω • U w ω ^ j := by
      funext ω
      simp only [hfp, hfn, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal']
      rcases le_total 0 (Z ω) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [e, integral_sub hip hin, sub_eq_zero] at h0
    exact h0
  have heq := WangWu.JacobiLaw.eq_of_integral_pow_eq (hIcc fp) (hIcc fn) hmom
  have hS' := congrArg (fun μ : Measure ℝ => μ S) heq
  rw [Measure.map_apply hUm hS, Measure.map_apply hUm hS, withDensity_apply _ (hUm hS),
    withDensity_apply _ (hUm hS)] at hS'
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hZi.integrableOn]
  have e1 : ∫⁻ ω in U w ⁻¹' S, ENNReal.ofReal (Z ω) ∂P = ∫⁻ ω in U w ⁻¹' S, (fp ω : ℝ≥0∞) ∂P := rfl
  have e2 : ∫⁻ ω in U w ⁻¹' S, ENNReal.ofReal (-Z ω) ∂P = ∫⁻ ω in U w ⁻¹' S, (fn ω : ℝ≥0∞) ∂P := rfl
  rw [e1, e2, hS', sub_self]

/-! ### Hitting an interior level -/

omit [IsProbabilityMeasure P] in
theorem integrable_id_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ => x) (invLaw κ a b) := by
  have := isProbabilityMeasure_invLaw hκ ha hb
  refine Integrable.of_bound (C := 1) continuous_id.aestronglyMeasurable ?_
  filter_upwards [ae_mem_Icc_invLaw κ a b] with x hx
  rw [Real.norm_eq_abs]
  exact abs_le_one_of_mem_Icc hx

omit [IsProbabilityMeasure P] in
/-- The mean of the beta law is `a/(a+b)`. -/
theorem integral_id_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x, x ∂(invLaw κ a b) = a / (a + b) := by
  have h := integral_pow_invLaw hκ ha hb 1
  simp only [pow_one] at h
  rw [h]
  simp only [jacobiMoment, dcoef, ccoef, Nat.cast_one, zero_add, sub_self, mul_zero, one_mul]
  have hab : 0 < a + b := by linarith
  field_simp

omit [IsProbabilityMeasure P] in
/-- **The strict first-moment inequality below a level**: `E[X; X < α] < E[X] P(X < α)` for the beta law. -/
theorem setIntegral_Iio_lt_invLaw (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∫ x in Iio α, x ∂(invLaw κ a b) < a / (a + b) * (invLaw κ a b (Iio α)).toReal := by
  have := isProbabilityMeasure_invLaw hκ ha hb
  have hi := integrable_id_invLaw hκ ha hb
  rw [← measureReal_def]
  set p := (invLaw κ a b).real (Iio α) with hp
  set r := (invLaw κ a b).real (Ici α) with hr
  set c := ∫ x in Iio α, x ∂(invLaw κ a b) with hc
  set q := ∫ x in Ici α, x ∂(invLaw κ a b) with hq
  have hcq : c + q = a / (a + b) := by
    rw [hc, hq, ← compl_Iio, integral_add_compl measurableSet_Iio hi, integral_id_invLaw hκ ha hb]
  have hpq : p + r = 1 := by
    rw [hp, hr, ← compl_Iio, measureReal_add_measureReal_compl measurableSet_Iio, probReal_univ]
  have hp0 : 0 ≤ p := measureReal_nonneg
  -- `c < α p`
  have hαc : c < α * p := by
    have hpos : 0 < ∫ x in Iio α, (α - x) ∂(invLaw κ a b) := by
      refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ((integrable_const α).sub hi).integrableOn).2 ?_
      · exact (ae_restrict_iff' measurableSet_Iio).2 (ae_of_all _ fun x hx => sub_nonneg.2 (le_of_lt hx))
      · have hsub : Ioo 0 α ⊆ Function.support (fun x : ℝ => α - x) ∩ Iio α := fun x hx =>
          ⟨sub_ne_zero.2 (ne_of_gt hx.2), hx.2⟩
        exact (invLaw_Ioo_pos hκ ha hb le_rfl hα0 hα1.le).trans_le (measure_mono hsub)
    rw [integral_sub (integrable_const α).integrableOn hi.integrableOn, setIntegral_const, smul_eq_mul,
      mul_comm] at hpos
    linarith
  -- `α (1 − p) ≤ q`
  have hαq : α * r ≤ q := by
    have h := setIntegral_mono_on (integrable_const α).integrableOn hi.integrableOn measurableSet_Ici
      (fun x (hx : α ≤ x) => hx)
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h
    exact h
  have h1p : 0 < r := by
    rw [hr, measureReal_def]
    refine ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
    exact (invLaw_Ioo_pos hκ ha hb hα0.le hα1 le_rfl).trans_le (measure_mono fun x hx => le_of_lt hx.1)
  rw [← hcq]
  have hr' : r = 1 - p := by linarith
  rw [hr'] at hαq h1p
  nlinarith [mul_pos h1p (sub_pos.2 hαc), mul_nonneg hp0 (sub_nonneg.2 hαq)]

/-- **The stationary Jacobi diffusion hits every interior level with positive probability after time `0`.** For
a solution of the Jacobi martingale problem on `ℝ` with `κ, a, b > 0` and `α ∈ (0, 1)`,
`0 < P(∃ u ≥ 0, U_u = α)`. -/
theorem _root_.InteractingSLE.Sec2.Jacobi.IsJacobiMP.measure_exists_eq_pos (hU : IsJacobiMP κ a b P U)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < P {ω | ∃ u : ℝ, 0 ≤ u ∧ U u ω = α} := by
  by_contra hpos
  have h0 : P {ω | ∃ u : ℝ, 0 ≤ u ∧ U u ω = α} = 0 := le_antisymm (not_lt.1 hpos) bot_le
  have hnh : ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u → U u ω ≠ α := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) h0
    simp only [mem_ofPred_eq, not_forall, not_not] at hω ⊢
    obtain ⟨u, hu, h⟩ := hω
    exact ⟨u, hu, h⟩
  -- no crossing of `α` after time `0`
  have hside : ∀ᵐ ω ∂P, ∀ v : ℝ, 0 ≤ v → (U v ω < α ↔ U 0 ω < α) := by
    filter_upwards [hnh] with ω hω v hv
    have hc : ContinuousOn (fun u => U u ω) (Icc 0 v) := (hU.continuous ω).continuousOn
    constructor
    · intro hlt
      by_contra hge
      push Not at hge
      have hgt : α < U 0 ω := lt_of_le_of_ne hge (Ne.symm (hω 0 le_rfl))
      obtain ⟨u, hu, hue⟩ := intermediate_value_Icc' hv hc ⟨hlt.le, hgt.le⟩
      exact hω u hu.1 hue
    · intro hlt
      by_contra hge
      push Not at hge
      have hgt : α < U v ω := lt_of_le_of_ne hge (Ne.symm (hω v hv))
      obtain ⟨u, hu, hue⟩ := intermediate_value_Icc hv hc ⟨hlt.le, hgt.le⟩
      exact hω u hu.1 hue
  set S : Set ℝ := Iio α with hS
  have hSm : MeasurableSet S := measurableSet_Iio
  have := isProbabilityMeasure_invLaw hκ ha hb
  set p := (invLaw κ a b S).toReal with hp
  set c := ∫ x in S, x ∂(invLaw κ a b) with hc
  have hset : ∀ v : ℝ, 0 ≤ v → (U v ⁻¹' S : Set Ω) =ᵐ[P] (U 0 ⁻¹' S : Set Ω) := fun v hv => by
    filter_upwards [hside] with ω h
    exact propext (h v hv)
  have hF1 : ∀ x : ℝ, (P (U x ⁻¹' S)).toReal = p := fun x => by
    rw [hp, ← hU.map_eq_invLaw hκ ha hb x, Measure.map_apply (hU.measurable x) hSm]
  have hF2 : ∀ x : ℝ, ∫ ω in U x ⁻¹' S, U x ω ∂P = c := fun x => by
    rw [hc, ← hU.map_eq_invLaw hκ ha hb x, setIntegral_map hSm (f := fun y : ℝ => y)
      continuous_id.aestronglyMeasurable (hU.measurable x).aemeasurable]
  set A : Set Ω := U 0 ⁻¹' S with hA
  have hAm : MeasurableSet A := hU.measurable 0 hSm
  have hbdd : ∀ x ω, |U x ω| ≤ 1 := fun x ω => abs_le_one_of_mem_Icc (hU.mem_Icc x ω)
  have hintU : ∀ x, Integrable (U x) P := fun x =>
    Integrable.of_bound (hU.measurable x).aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hbdd x ω)
  -- Fubini for the time integral
  set f : Ω → ℝ → ℝ := fun ω x => a / 2 - (a + b) / 2 * U x ω with hf
  have hfm : Measurable (Function.uncurry f) :=
    measurable_const.sub (hU.measurable_uncurry.const_mul _)
  have hfb : ∀ ω x, |f ω x| ≤ |a / 2| + |(a + b) / 2| := fun ω x => by
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hbdd x ω)
  have hint : Integrable (Function.uncurry f) ((P.restrict A).prod (volume.restrict (Ioc 0 1))) :=
    Integrable.of_bound hfm.aestronglyMeasurable _ (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hfb z.1 z.2)
  have hswap := integral_integral_swap hint
  have hIint : IntegrableOn (fun ω => ∫ x in (0 : ℝ)..1, f ω x) A P := by
    have e : (fun ω => ∫ x in (0 : ℝ)..1, f ω x) = fun ω => ∫ x in Ioc 0 1, f ω x :=
      funext fun ω => intervalIntegral.integral_of_le zero_le_one
    rw [e]
    exact hint.integral_prod_left
  have hinner : ∀ x ∈ Ioc (0 : ℝ) 1, ∫ ω in A, f ω x ∂P = a / 2 * p - (a + b) / 2 * c := by
    intro x hx
    rw [setIntegral_congr_set (hset x hx.1.le).symm, hf]
    simp only
    rw [integral_sub (integrable_const _).integrableOn ((hintU x).const_mul _).integrableOn,
      setIntegral_const, smul_eq_mul, integral_const_mul, hF2 x, measureReal_def, hF1 x]
    ring
  have hI : ∫ ω in A, (∫ x in (0 : ℝ)..1, f ω x) ∂P = a / 2 * p - (a + b) / 2 * c := by
    have e : (fun ω => ∫ x in (0 : ℝ)..1, f ω x) = fun ω => ∫ x in Ioc 0 1, f ω x :=
      funext fun ω => intervalIntegral.integral_of_le zero_le_one
    rw [e, hswap, setIntegral_congr_fun measurableSet_Ioc hinner, setIntegral_const, smul_eq_mul,
      Real.volume_real_Ioc_of_le zero_le_one, sub_zero, one_mul]
  -- the martingale problem with weight `1{U_0 < α}`
  have hmp := hU.setIntegral_jacIncr_eq_zero (w := 0) (v := 1) zero_le_one hSm
  have hmp' : ∫ ω in A, ((U 1 ω - U 0 ω) - ∫ x in (0 : ℝ)..1, f ω x) ∂P = 0 := hmp
  have h10 : IntegrableOn (fun ω => U 1 ω - U 0 ω) A P := ((hintU 1).sub (hintU 0)).integrableOn
  rw [integral_sub (f := fun ω => U 1 ω - U 0 ω) (g := fun ω => ∫ x in (0 : ℝ)..1, f ω x) h10 hIint,
    integral_sub (hintU 1).integrableOn (hintU 0).integrableOn, hI,
    setIntegral_congr_set (hset 1 zero_le_one).symm, hF2 1, hF2 0] at hmp'
  have hab : 0 < a + b := by linarith
  have hceq : c = a / (a + b) * p := by
    field_simp
    linarith [hmp']
  exact absurd hceq (ne_of_lt (setIntegral_Iio_lt_invLaw hκ ha hb hα0 hα1))

end InteractingSLE.Zhan
