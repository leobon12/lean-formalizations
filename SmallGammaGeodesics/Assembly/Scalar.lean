import SmallGammaGeodesics.Assembly.Transfer
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Source §8: the scalar consequences (1.4)–(1.9) (packet P-L4)

Mathematics: planning audit GA4, Details (a), item A9 (§8 and the end of §5).

* `UpperBoundsXi P η`: the upper bounds (5.14)–(5.15) of source §5, at the scale `ξ = xiGamma γ`;
* `LowerBound71 P η`: Proposition 7.1 of source §7, for every `γ ∈ (0,2)`;
* `devConcl_of_bounds`: the two bounds give `DevConcl P η`, i.e. (1.4)–(1.9).

The proof follows A9:
* (1.4), (1.5): `0 ≤ ξ ≤ γ` for small `γ` (`dimension_input`, source (1.12));
* (1.6): Proposition 7.1 at `r = a γ^{2/3}`, with `Q γ · r^{3/2} = (2 + γ²/2) a^{3/2} ≤ 4 a^{3/2}`;
* (1.7), (1.9): Markov's inequality with (1.4), and (1.6);
* (1.8): the layer-cake formula with (1.6) (`Scalar.lintegral_ofReal_rpow_neg_le`).

The constants are those of A9: `C = max C₅ (4^{2/5} C₇)` and `γ₀ = min (min γ₅ γ_d) (min (r_*^{3/2}) 1)`,
where `γ_d` is the threshold of `dimension_input`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

/-- The upper bounds of source §5, (5.14)–(5.15), with `ξ = xiGamma γ`. -/
def UpperBoundsXi {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → C(unitInterval, ℂ)) :
    Prop :=
  ∃ C γ₁ : ℝ, 0 < γ₁ ∧
    (∀ γ ∈ Ioo (0 : ℝ) γ₁, ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂P ≤
      ENNReal.ofReal (C * LQGMetric.xiGamma γ ^ (2 / 3 : ℝ))) ∧
    (∀ A : ℝ, 1 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      P {ω | A * LQGMetric.xiGamma γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} ≤
        ENNReal.ofReal (C * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε))

/-- Proposition 7.1 (source §7), for every `γ ∈ (0,2)`. -/
def LowerBound71 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → C(unitInterval, ℂ)) :
    Prop :=
  ∃ C rs : ℝ, 0 < C ∧ 0 < rs ∧ ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ r ∈ Ioc (0 : ℝ) rs,
    P {ω | maxDev (η γ ω) ≤ r} ≤
      ENNReal.ofReal (C * (LQGMetric.Q γ * r ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ))

namespace Scalar

/-! ### Limits of real powers at `0⁺` -/

/-- `x ^ s → 0` as `x → 0⁺`, for `s > 0`. -/
theorem tendsto_rpow_nhdsGT_zero {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => x ^ s) (𝓝[>] 0) (𝓝 0) := by
  have h := Real.continuousAt_rpow_const 0 s (Or.inr hs.le)
  rw [ContinuousAt, Real.zero_rpow hs.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `ofReal (C x^s) → 0` as `x → 0⁺`, for `s > 0`. -/
theorem tendsto_ofReal_mul_rpow_nhdsGT_zero (C : ℝ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => ENNReal.ofReal (C * x ^ s)) (𝓝[>] 0) (𝓝 0) := by
  have h := ENNReal.tendsto_ofReal ((tendsto_rpow_nhdsGT_zero hs).const_mul C)
  rwa [mul_zero, ENNReal.ofReal_zero] at h

/-- A set of measure at most `C a^s` for every `a ∈ (0,1]` (with `s > 0`) is null. -/
theorem measure_eq_zero_of_le_mul_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {S : Set Ω} {C s : ℝ} (hs : 0 < s)
    (h : ∀ a ∈ Ioc (0 : ℝ) 1, P S ≤ ENNReal.ofReal (C * a ^ s)) : P S = 0 := by
  refine le_antisymm (ge_of_tendsto (tendsto_ofReal_mul_rpow_nhdsGT_zero C hs) ?_) zero_le
  filter_upwards [Ioo_mem_nhdsGT one_pos] with a ha
  exact h a ⟨ha.1, ha.2.le⟩

/-! ### Markov's inequality and the layer-cake formula -/

/-- **Markov's inequality** for a real random variable with a bound on `∫⁻ ofReal f`. -/
theorem measure_le_le_ofReal_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    (hf : AEMeasurable f P) {B t : ℝ} (ht : 0 < t)
    (hB : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal B) :
    P {ω | t ≤ f ω} ≤ ENNReal.ofReal (B / t) := by
  calc P {ω | t ≤ f ω} ≤ P {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (f ω)} :=
        measure_mono fun ω hω => ENNReal.ofReal_le_ofReal hω
    _ ≤ (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) / ENNReal.ofReal t :=
        meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp_aemeasurable hf)
          (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal B / ENNReal.ofReal t := ENNReal.div_le_div_right hB _
    _ = ENNReal.ofReal (B / t) := (ENNReal.ofReal_div_of_pos ht).symm

/-- `∫⁻_{(1,∞)} ofReal (C t^p) dt = ofReal (C · (-1/(p+1)))` for `C ≥ 0` and `p < -1`. -/
theorem lintegral_Ioi_one_ofReal_mul_rpow {C p : ℝ} (hC : 0 ≤ C) (hp : p < -1) :
    ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (C * t ^ p) = ENNReal.ofReal (C * (-1 / (p + 1))) := by
  have hint : IntegrableOn (fun t : ℝ => C * t ^ p) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hp one_pos).const_mul C
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => C * t ^ p :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
    integral_Ioi_rpow_of_lt hp one_pos, Real.one_rpow]

/-- **Negative moments from a small-ball bound (layer cake).** If `Y ≥ 0` and
`P[Y ≤ a] ≤ C a^s` for every `a ∈ (0,1]`, then `E[Y^{-r}] ≤ 1 + C r/(s - r)` for `0 < r < s`. The
negative power is taken in `ℝ≥0∞`, so `0^{-r} = ∞`; the bound shows in particular that `{Y = 0}` is
null. -/
theorem lintegral_ofReal_rpow_neg_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : AEMeasurable Y P) (hY0 : ∀ ω, 0 ≤ Y ω)
    {C s r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hrs : r < s)
    (hsmall : ∀ a ∈ Ioc (0 : ℝ) 1, P {ω | Y ω ≤ a} ≤ ENNReal.ofReal (C * a ^ s)) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ^ (-r) ∂P ≤ ENNReal.ofReal (1 + C * (r / (s - r))) := by
  have hs : 0 < s := hr.trans hrs
  -- `{Y ≤ 0}` is null, so `Y > 0` a.s.
  have h0 : P {ω | Y ω ≤ 0} = 0 := by
    refine measure_eq_zero_of_le_mul_rpow hs fun a ha => le_trans (measure_mono ?_) (hsmall a ha)
    intro ω hω
    exact (hω : Y ω ≤ 0).trans ha.1.le
  have hpos : ∀ᵐ ω ∂P, 0 < Y ω := ae_iff.2 (by simpa only [not_lt] using h0)
  -- the exponent of the tail bound
  have hr0 : -r ≠ 0 := neg_ne_zero.2 hr.ne'
  have hr' : (-r)⁻¹ < 0 := inv_lt_zero.2 (neg_lt_zero.2 hr)
  have he : (-r)⁻¹ * s = -(s / r) := by rw [inv_neg, neg_mul, inv_mul_eq_div]
  have he1 : -(s / r) < -1 := neg_lt_neg ((one_lt_div hr).2 hrs)
  -- the pieces `t ∈ (0,1]` and `t > 1` of the layer-cake integral
  have h1 : ∫⁻ t in Ioc (0 : ℝ) 1, P {ω | t < Y ω ^ (-r)} ≤ 1 := by
    calc ∫⁻ t in Ioc (0 : ℝ) 1, P {ω | t < Y ω ^ (-r)} ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, 1 :=
          lintegral_mono fun _ => prob_le_one
      _ = 1 := by rw [setLIntegral_one, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
  have h2 : ∫⁻ t in Ioi (1 : ℝ), P {ω | t < Y ω ^ (-r)} ≤
      ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (C * t ^ (-(s / r))) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := one_pos.trans ht1
    have ha : t ^ (-r)⁻¹ ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos ht0 _, Real.rpow_le_one_of_one_le_of_nonpos ht1.le hr'.le⟩
    calc P {ω | t < Y ω ^ (-r)} ≤ P {ω | Y ω ≤ t ^ (-r)⁻¹} := by
          refine measure_mono fun ω hω => ?_
          have hω' : t < Y ω ^ (-r) := hω
          rcases (hY0 ω).eq_or_lt with h | h
          · -- `Y ω = 0`: then `Y ω ^ (-r) = 0 < t`, impossible
            rw [← h, Real.zero_rpow hr0] at hω'
            exact absurd hω' (not_lt.2 ht0.le)
          · have hlt := Real.rpow_lt_rpow_of_neg ht0 hω' hr'
            rw [Real.rpow_rpow_inv h.le hr0] at hlt
            exact hlt.le
      _ ≤ ENNReal.ofReal (C * (t ^ (-r)⁻¹) ^ s) := hsmall _ ha
      _ = ENNReal.ofReal (C * t ^ (-(s / r))) := by rw [← Real.rpow_mul ht0.le, he]
  have h3 : ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (C * t ^ (-(s / r))) =
      ENNReal.ofReal (C * (r / (s - r))) := by
    rw [lintegral_Ioi_one_ofReal_mul_rpow hC he1]
    have hden : -(s / r) + 1 = -((s - r) / r) := by
      rw [sub_div, div_self hr.ne']
      ring
    rw [hden, div_neg, neg_div, neg_neg, one_div_div]
  calc ∫⁻ ω, ENNReal.ofReal (Y ω) ^ (-r) ∂P = ∫⁻ ω, ENNReal.ofReal (Y ω ^ (-r)) ∂P :=
        lintegral_congr_ae (hpos.mono fun ω hω => ENNReal.ofReal_rpow_of_pos hω)
    _ = ∫⁻ t in Ioi 0, P {ω | t < Y ω ^ (-r)} :=
        lintegral_eq_lintegral_meas_lt P (ae_of_all _ fun ω => Real.rpow_nonneg (hY0 ω) _)
          (hY.pow_const _)
    _ = (∫⁻ t in Ioc (0 : ℝ) 1, P {ω | t < Y ω ^ (-r)}) +
          ∫⁻ t in Ioi (1 : ℝ), P {ω | t < Y ω ^ (-r)} := by
        rw [← lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
          Ioc_union_Ioi_eq_Ioi zero_le_one]
    _ ≤ 1 + ENNReal.ofReal (C * (r / (s - r))) := add_le_add h1 (h2.trans h3.le)
    _ = ENNReal.ofReal (1 + C * (r / (s - r))) := by
        rw [ENNReal.ofReal_add zero_le_one
          (mul_nonneg hC (div_nonneg hr.le (sub_nonneg.2 hrs.le))), ENNReal.ofReal_one]

/-! ### The identity `Q γ · (a γ^{2/3})^{3/2} = (2 + γ²/2) a^{3/2}` -/

/-- `Q γ · (a γ^{2/3})^{3/2} = (2 + γ²/2) a^{3/2} ≤ 4 a^{3/2}` for `0 < γ < 2` and `a ≥ 0`. -/
theorem Q_mul_rpow_le {γ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (ha : 0 ≤ a) :
    LQGMetric.Q γ * (a * γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) ≤ 4 * a ^ (3 / 2 : ℝ) := by
  have hγ' : (γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = γ := by
    rw [← Real.rpow_mul hγ.le]
    norm_num
  rw [Real.mul_rpow ha (Real.rpow_nonneg hγ.le _), hγ']
  have hQ : LQGMetric.Q γ * γ = 2 + γ ^ 2 / 2 := by
    unfold LQGMetric.Q
    field_simp
  have ha' : 0 ≤ a ^ (3 / 2 : ℝ) := Real.rpow_nonneg ha _
  calc LQGMetric.Q γ * (a ^ (3 / 2 : ℝ) * γ) = (2 + γ ^ 2 / 2) * a ^ (3 / 2 : ℝ) := by
        rw [← hQ]
        ring
    _ ≤ 4 * a ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right (by nlinarith) ha'

/-- `(Q γ · (a γ^{2/3})^{3/2})^{2/5} ≤ 4^{2/5} a^{3/5}` for `0 < γ < 2` and `a ≥ 0`. -/
theorem Q_mul_rpow_rpow_le {γ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (ha : 0 ≤ a) :
    (LQGMetric.Q γ * (a * γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ) ≤
      4 ^ (2 / 5 : ℝ) * a ^ (3 / 5 : ℝ) := by
  have h0 : 0 ≤ LQGMetric.Q γ * (a * γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) :=
    mul_nonneg (LQGMetric.Q_pos hγ).le
      (Real.rpow_nonneg (mul_nonneg ha (Real.rpow_nonneg hγ.le _)) _)
  calc (LQGMetric.Q γ * (a * γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ)
      ≤ (4 * a ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ) :=
        Real.rpow_le_rpow h0 (Q_mul_rpow_le hγ hγ2 ha) (by norm_num)
    _ = 4 ^ (2 / 5 : ℝ) * a ^ (3 / 5 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg ha _), ← Real.rpow_mul ha]
        norm_num

end Scalar

open Scalar in
/-- **Source §8 (GA4 A9).** The upper bounds (5.14)–(5.15) and Proposition 7.1 give the
conclusion (1.4)–(1.9) of Theorem 1.1. -/
theorem devConcl_of_bounds {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {η : ℝ → Ω → C(unitInterval, ℂ)} (hη : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (η γ) P)
    (hU : UpperBoundsXi P η) (hL : LowerBound71 P η) : DevConcl P η := by
  obtain ⟨CU, γ₁, hγ₁, hU14, hU15⟩ := hU
  obtain ⟨C₇, rs, hC₇, hrs, hL71⟩ := hL
  obtain ⟨γd, Cd, hγd, hdim⟩ := dimension_input
  -- the constants of A9
  obtain ⟨C, hCU, hC6⟩ : ∃ C : ℝ, CU ≤ C ∧ 4 ^ (2 / 5 : ℝ) * C₇ ≤ C :=
    ⟨max CU (4 ^ (2 / 5 : ℝ) * C₇), le_max_left _ _, le_max_right _ _⟩
  have hC : 0 < C := (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC₇).trans_le hC6
  obtain ⟨γ₀, hγ₀, hγ₀₁, hγ₀d, hγ₀r, hγ₀1⟩ : ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ γ₁ ∧ γ₀ ≤ γd ∧
      γ₀ ≤ rs ^ (3 / 2 : ℝ) ∧ γ₀ ≤ 1 :=
    ⟨min (min γ₁ γd) (min (rs ^ (3 / 2 : ℝ)) 1),
      lt_min (lt_min hγ₁ hγd) (lt_min (Real.rpow_pos_of_pos hrs _) one_pos),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  -- `0 ≤ ξ ≤ γ` for small `γ` (source (1.12))
  have hξ : ∀ γ ∈ Ioo (0 : ℝ) γd, 0 ≤ LQGMetric.xiGamma γ ∧ LQGMetric.xiGamma γ ≤ γ := by
    intro γ hγ
    obtain ⟨-, h1, h2⟩ := hdim γ ⟨hγ.1, hγ.2.le⟩
    exact ⟨(div_nonneg hγ.1.le (by norm_num)).trans h1, h2⟩
  have hξ23 : ∀ γ ∈ Ioo (0 : ℝ) γd,
      LQGMetric.xiGamma γ ^ (2 / 3 : ℝ) ≤ γ ^ (2 / 3 : ℝ) := fun γ hγ =>
    Real.rpow_le_rpow (hξ γ hγ).1 (hξ γ hγ).2 (by norm_num)
  have hsmall : ∀ γ ∈ Ioo (0 : ℝ) γ₀, 0 < γ ∧ γ < 2 := fun γ hγ =>
    ⟨hγ.1, by linarith [hγ.2, hγ₀1]⟩
  have hM : ∀ γ, 0 < γ → γ < 2 → AEMeasurable (fun ω => maxDev (η γ ω)) P := fun γ h0 h2 =>
    lipschitzWith_maxDev.continuous.measurable.comp_aemeasurable (hη γ h0 h2)
  -- (1.4)
  have h14 : ∀ γ ∈ Ioo (0 : ℝ) γ₀,
      ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂P ≤ ENNReal.ofReal (C * γ ^ (2 / 3 : ℝ)) := by
    intro γ hγ
    have hγd' : γ ∈ Ioo (0 : ℝ) γd := ⟨hγ.1, hγ.2.trans_le hγ₀d⟩
    refine (hU14 γ ⟨hγ.1, hγ.2.trans_le hγ₀₁⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    calc CU * LQGMetric.xiGamma γ ^ (2 / 3 : ℝ) ≤ C * LQGMetric.xiGamma γ ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right hCU (Real.rpow_nonneg (hξ γ hγd').1 _)
      _ ≤ C * γ ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left (hξ23 γ hγd') hC.le
  -- (1.6)
  have h16 : ∀ γ ∈ Ioo (0 : ℝ) γ₀, ∀ a ∈ Ioc (0 : ℝ) 1,
      P {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} ≤ ENNReal.ofReal (C * a ^ (3 / 5 : ℝ)) := by
    intro γ hγ a ha
    obtain ⟨h0, h2⟩ := hsmall γ hγ
    have hg : 0 < γ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos h0 _
    have hgrs : γ ^ (2 / 3 : ℝ) ≤ rs := by
      calc γ ^ (2 / 3 : ℝ) ≤ (rs ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow h0.le (hγ.2.le.trans hγ₀r) (by norm_num)
        _ = rs := by
            rw [← Real.rpow_mul hrs.le]
            norm_num
    have hr : a * γ ^ (2 / 3 : ℝ) ∈ Ioc (0 : ℝ) rs :=
      ⟨mul_pos ha.1 hg, (mul_le_of_le_one_left hg.le ha.2).trans hgrs⟩
    refine (hL71 γ h0 h2 _ hr).trans (ENNReal.ofReal_le_ofReal ?_)
    calc C₇ * (LQGMetric.Q γ * (a * γ ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) ^ (2 / 5 : ℝ)
        ≤ C₇ * (4 ^ (2 / 5 : ℝ) * a ^ (3 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Q_mul_rpow_rpow_le h0 h2 ha.1.le) hC₇.le
      _ = 4 ^ (2 / 5 : ℝ) * C₇ * a ^ (3 / 5 : ℝ) := by ring
      _ ≤ C * a ^ (3 / 5 : ℝ) := mul_le_mul_of_nonneg_right hC6 (Real.rpow_nonneg ha.1.le _)
  refine ⟨C, γ₀, hγ₀, h14, ?_, h16, ?_, ?_, ?_⟩
  · -- (1.5)
    intro A hA ε hε
    filter_upwards [hU15 A hA ε hε, Ioo_mem_nhdsGT hγd] with γ hγ hγd'
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    have hAB : 0 ≤ A ^ (-3 : ℝ) + A ^ (-4 : ℝ) :=
      add_nonneg (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hA0 _)
    calc P {ω | A * γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)}
        ≤ P {ω | A * LQGMetric.xiGamma γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} := by
          refine measure_mono fun ω hω => ?_
          exact (mul_le_mul_of_nonneg_left (hξ23 γ hγd') hA0).trans_lt hω
      _ ≤ ENNReal.ofReal (CU * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε) := hγ
      _ ≤ ENNReal.ofReal (C * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε) :=
          ENNReal.ofReal_le_ofReal (add_le_add (mul_le_mul_of_nonneg_right hCU hAB) le_rfl)
  · -- (1.7)
    intro ε hε
    have hεC : 0 < ε / (2 * C) := div_pos hε (by positivity)
    obtain ⟨a, ha0, ha1, haε⟩ : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a ≤ (ε / (2 * C)) ^ (5 / 3 : ℝ) :=
      ⟨min 1 ((ε / (2 * C)) ^ (5 / 3 : ℝ)), lt_min one_pos (Real.rpow_pos_of_pos hεC _),
        min_le_left _ _, min_le_right _ _⟩
    have hCa : C * a ^ (3 / 5 : ℝ) ≤ ε / 2 := by
      have h : a ^ (3 / 5 : ℝ) ≤ ε / (2 * C) := by
        calc a ^ (3 / 5 : ℝ) ≤ ((ε / (2 * C)) ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) :=
              Real.rpow_le_rpow ha0.le haε (by norm_num)
          _ = ε / (2 * C) := by
              rw [← Real.rpow_mul hεC.le]
              norm_num
      calc C * a ^ (3 / 5 : ℝ) ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left h hC.le
        _ = ε / 2 := by
            field_simp
    refine ⟨a, 2 * C / ε, ha0, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hγ₀] with γ hγ
    obtain ⟨h0, h2⟩ := hsmall γ hγ
    have hg : 0 < γ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos h0 _
    have hAg : 0 < 2 * C / ε * γ ^ (2 / 3 : ℝ) := by positivity
    calc P {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
          maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ 2 * C / ε)}
        ≤ P ({ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} ∪
            {ω | 2 * C / ε * γ ^ (2 / 3 : ℝ) ≤ maxDev (η γ ω)}) := by
          refine measure_mono fun ω hω => ?_
          rcases not_and_or.1 hω with h | h
          · exact Or.inl ((div_lt_iff₀ hg).1 (not_le.1 h)).le
          · exact Or.inr ((lt_div_iff₀ hg).1 (not_le.1 h)).le
      _ ≤ P {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} +
            P {ω | 2 * C / ε * γ ^ (2 / 3 : ℝ) ≤ maxDev (η γ ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          gcongr
          · exact (h16 γ hγ a ⟨ha0, ha1⟩).trans (ENNReal.ofReal_le_ofReal hCa)
          · refine (measure_le_le_ofReal_div (hM γ h0 h2) hAg (h14 γ hγ)).trans (le_of_eq ?_)
            congr 1
            field_simp
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
  · -- (1.8)
    intro r hr
    refine ⟨1 + C * (r / (3 / 5 - r)), fun γ hγ => ?_⟩
    obtain ⟨h0, h2⟩ := hsmall γ hγ
    have hg : 0 < γ ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos h0 _
    refine lintegral_ofReal_rpow_neg_le (Y := fun ω => maxDev (η γ ω) / γ ^ (2 / 3 : ℝ))
      ((hM γ h0 h2).div_const _) (fun ω => div_nonneg (maxDev_nonneg _) hg.le) hC.le hr.1 hr.2
      fun a ha => le_trans (measure_mono fun ω hω => ?_) (h16 γ hγ a ha)
    exact (div_le_iff₀ hg).1 hω
  · -- (1.9)
    intro ε hε
    have hlim : Tendsto (fun γ : ℝ => ENNReal.ofReal (C * γ ^ (ε * (3 / 5 : ℝ))) +
        ENNReal.ofReal (C * γ ^ ε)) (𝓝[>] 0) (𝓝 0) := by
      simpa only [add_zero] using (tendsto_ofReal_mul_rpow_nhdsGT_zero C
        (by positivity : 0 < ε * (3 / 5 : ℝ))).add (tendsto_ofReal_mul_rpow_nhdsGT_zero C hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsGT hγ₀] with γ hγ
    obtain ⟨h0, h2⟩ := hsmall γ hγ
    have hγε : γ ^ ε ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos h0 _, Real.rpow_le_one h0.le (hγ.2.le.trans hγ₀1) hε.le⟩
    have ht : 0 < γ ^ (2 / 3 - ε) := Real.rpow_pos_of_pos h0 _
    calc P {ω | ¬ (γ ^ (2 / 3 + ε) ≤ maxDev (η γ ω) ∧ maxDev (η γ ω) ≤ γ ^ (2 / 3 - ε))}
        ≤ P ({ω | maxDev (η γ ω) ≤ γ ^ ε * γ ^ (2 / 3 : ℝ)} ∪
            {ω | γ ^ (2 / 3 - ε) ≤ maxDev (η γ ω)}) := by
          refine measure_mono fun ω hω => ?_
          rcases not_and_or.1 hω with h | h
          · have h' := not_le.1 h
            rw [Real.rpow_add h0] at h'
            exact Or.inl (h'.le.trans_eq (mul_comm _ _))
          · exact Or.inr (not_le.1 h).le
      _ ≤ P {ω | maxDev (η γ ω) ≤ γ ^ ε * γ ^ (2 / 3 : ℝ)} +
            P {ω | γ ^ (2 / 3 - ε) ≤ maxDev (η γ ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (C * γ ^ (ε * (3 / 5 : ℝ))) + ENNReal.ofReal (C * γ ^ ε) := by
          gcongr
          · refine (h16 γ hγ _ hγε).trans (le_of_eq ?_)
            rw [← Real.rpow_mul h0.le]
          · refine (measure_le_le_ofReal_div (hM γ h0 h2) ht (h14 γ hγ)).trans (le_of_eq ?_)
            rw [mul_div_assoc, ← Real.rpow_sub h0, sub_sub_cancel]

end SmallGammaGeodesics
