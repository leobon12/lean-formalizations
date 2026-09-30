import QuantumZipper.Proofs.Thm18.R18G3TFid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: the Palm mass of scheme `C` is positive and finite (F3-C)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 and p. 28. The Palm mass of scheme `C`
is `g3pZ = E ν_C[−δ, 0]` (`g3pZ_eq_honest`), and `ν_C = |t|^β ν_Z` on `ℝ ∖ {0}` with
`β = −(γ − 2/γ)γ/2 = 1 − γ²/2 > −1` (`ae_g3pField_good`), `ν_Z` the boundary measure of the free
field normalized on the unit semicircle.

* `lintegral_qBoundaryMeasure_zField_one_Icc_le`: the mean measure of `ν_Z` is at most Lebesgue
  on `(−1, 1)`: `E ν_Z[u, v] ≤ b − a` for `−1 < a < u ≤ v < b < 1` (the Fatou argument of
  `G3HonestFin2.lintegral_qBoundaryMeasure_zField_one_Icc_lt_top`, with an Urysohn function
  `≤ 1` supported in `(a, b)`, so that `∫ f ≤ b − a`);
* `g3pZ_lt_top`: dyadic decomposition of `[−δ, 0)` into `[−x_n, −x_n/2]`, `x_n = δ 2^{−n}`, on
  which `|t|^β ≤ ((1/2)^β + 1) x_n^β`; the sum `∑ x_n^{β+1}` is geometric since `β + 1 > 0`;
* `g3pZ_pos`: `|t|^β` is bounded below on `(−δ, −δ/2)` and the free field's boundary measure has
  positive first moment there (as `G3FidHonest.lintegral_qBoundaryMeasure_normField_Icc_pos`).

Own elementary bookkeeping on top of the cited lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Mean measure of `ν_Z` at most Lebesgue** (on windows inside `(−1, 1)`). -/
theorem lintegral_qBoundaryMeasure_zField_one_Icc_le (hX : IsFreeGFFModConstH X P)
    [IsProbabilityMeasure P] {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a u v b : ℝ}
    (ha : -1 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b) (hb : b < 1) :
    ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ∂P ≤ ENNReal.ofReal (b - a) := by
  have hdisj : Disjoint (Icc u v) (Ioo a b)ᶜ :=
    disjoint_compl_right_iff_subset.2 fun t ht => ⟨hau.trans_le ht.1, ht.2.trans_lt hvb⟩
  obtain ⟨F, hF1, hF0, hFcs, hF01⟩ := exists_continuous_one_zero_of_isCompact isCompact_Icc
    isOpen_Ioo.isClosed_compl hdisj
  set f : ℝ → ℝ := ⇑F with hfdef
  have hfc : Continuous f := F.continuous
  have hf0 : ∀ t, 0 ≤ f t := fun t => (hF01 t).1
  have hfcs : HasCompactSupport f := hFcs
  have hsupp : Function.support f ⊆ Ioo a b := fun t ht => by
    by_contra h
    exact ht (hF0 (show t ∈ (Ioo a b)ᶜ from h))
  have htsupp : tsupport f ⊆ Icc a b :=
    closure_minimal (hsupp.trans Ioo_subset_Icc_self) isClosed_Icc
  set m0 : ℝ := max |a| |b| with hm0
  have hm01 : m0 < 1 := max_lt (abs_lt.2 ⟨by linarith, by linarith⟩)
    (abs_lt.2 ⟨by linarith, hb⟩)
  have habs : ∀ t ∈ Icc a b, |t| ≤ m0 := fun t ht => by
    rw [abs_le]
    constructor
    · have h1 : |a| ≤ m0 := le_max_left _ _
      have h2 : -|a| ≤ a := neg_abs_le a
      linarith [ht.1]
    · have h1 : |b| ≤ m0 := le_max_right _ _
      have h2 : b ≤ |b| := le_abs_self b
      linarith [ht.2]
  have hr : Tendsto radius atTop (𝓝 (0 : ℝ)) :=
    RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ k in atTop, ∀ t ∈ tsupport f, |t| + radius k ≤ 1 := by
    filter_upwards [hr.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 - m0 by linarith))] with k hk t ht
    have := habs t (htsupp ht)
    linarith
  set Z : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (BdryExist.zField X 1 ω) k) with hZdef
  have hZeq : ∀ k, Z k = fun ω => ∫⁻ (t : ℝ), ENNReal.ofReal (f t) *
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
        Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ))) ∂volume := by
    intro k
    funext ω
    rw [hZdef]
    simp only
    rw [bdryApprox, lintegral_withDensity_eq_lintegral_mul₀
      (measurable_bdryDens_zField_one (X := X) hX k ω).aemeasurable
      (hfc.measurable.ennreal_ofReal.aemeasurable)]
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply]
    exact mul_comm _ _
  have hZmeas : ∀ k, Measurable (Z k) := by
    intro k
    rw [hZeq k]
    have hjoint : Measurable (Function.uncurry fun (ω : Ω) (t : ℝ) =>
        ENNReal.ofReal (f t) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
          Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))) :=
      (hfc.measurable.ennreal_ofReal.comp measurable_snd).mul
        (measurable_bdryDens_zField_one_pair (X := X) hX k)
    exact Measurable.lintegral_prod_right (ν := volume)
      (f := fun (ω : Ω) (t : ℝ) => ENNReal.ofReal (f t) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) *
        Real.exp (γ / 2 * avgReg (BdryExist.zField X 1 ω) k (t : ℂ)))) hjoint
  have hae : ∀ᵐ ω ∂P, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ≤
      liminf (fun k => Z k ω) atTop := by
    filter_upwards [BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField (P := P) hX hγ hγ2 1,
      FirstMoment.ae_qBoundaryMeasure_Icc_lt_top_zField (P := P) hX hγ hγ2 1] with ω hv hfin
    have hint : Integrable f (qBoundaryMeasure γ (BdryExist.zField X 1 ω)) :=
      GoodSample.integrable_of_tsupport (U := Icc (-1) 1)
        (fun K hK hKU => (measure_mono hKU).trans_lt (by simpa using hfin (-1) 1))
        hfc hfcs (fun t ht => by
          have := habs t (htsupp ht)
          rw [abs_le] at this
          exact ⟨by linarith, by linarith⟩)
    refine (le_trans ?_ (lintegral_le_liminf_of_isVagueLimitR hv hfc hfcs hf0 hint))
    rw [← lintegral_indicator_one measurableSet_Icc]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ Icc u v
    · rw [indicator_of_mem ht, Pi.one_apply, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_of_eq (hF1 ht).symm)
    · rw [indicator_of_notMem ht]
      exact zero_le
  have hevconst : ∀ᶠ k in atTop, ∫⁻ ω, Z k ω ∂P = ENNReal.ofReal (∫ t, f t) := by
    filter_upwards [hev] with k hk
    exact lintegral_bdryApprox_zField_one (P := P) hX hfc hf0 hfcs hk
  have hliminfconst : liminf (fun k => ∫⁻ ω, Z k ω ∂P) atTop = ENNReal.ofReal (∫ t, f t) :=
    Filter.Tendsto.liminf_eq
      (Filter.Tendsto.congr' (hevconst.mono fun k hk => hk.symm) tendsto_const_nhds)
  have hfint : ∫ t, f t ≤ b - a := by
    have hle : ∀ t, f t ≤ (Ioo a b).indicator (fun _ => (1 : ℝ)) t := fun t => by
      by_cases ht : t ∈ Ioo a b
      · rw [indicator_of_mem ht]; exact (hF01 t).2
      · rw [indicator_of_notMem ht]
        exact le_of_eq (by_contra fun h => ht (hsupp h))
    calc ∫ t, f t ≤ ∫ t, (Ioo a b).indicator (fun _ => (1 : ℝ)) t :=
          integral_mono (hfc.integrable_of_hasCompactSupport hfcs)
            ((integrableOn_const (μ := volume) (s := Ioo a b) (C := (1 : ℝ))
              (by simp)).integrable_indicator measurableSet_Ioo) hle
      _ = b - a := by
          rw [integral_indicator_const _ measurableSet_Ioo, smul_eq_mul, mul_one,
            Real.volume_real_Ioo_of_le (by linarith)]
  calc ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X 1 ω) (Icc u v) ∂P
      ≤ ∫⁻ ω, liminf (fun k => Z k ω) atTop ∂P := lintegral_mono_ae hae
    _ ≤ liminf (fun k => ∫⁻ ω, Z k ω ∂P) atTop := lintegral_liminf_le hZmeas
    _ = ENNReal.ofReal (∫ t, f t) := hliminfconst
    _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal hfint

/-! ## The density `|t|^β` on dyadic pieces -/

theorem rpow_le_of_half {β x s : ℝ} (hx : 0 < x) (hs1 : x / 2 ≤ s) (hs2 : s ≤ x) :
    s ^ β ≤ ((1 / 2 : ℝ) ^ β + 1) * x ^ β := by
  have hy0 : 0 < s / x := div_pos (by linarith) hx
  have hy1 : s / x ≤ 1 := (div_le_one hx).2 hs2
  have hyh : 1 / 2 ≤ s / x := by rw [le_div_iff₀ hx]; linarith
  have e : s = x * (s / x) := by field_simp
  have hyb : (s / x) ^ β ≤ (1 / 2 : ℝ) ^ β + 1 := by
    rcases le_total 0 β with hβ | hβ
    · have := Real.rpow_le_one hy0.le hy1 hβ
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) β
      linarith
    · have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hyh hβ
      linarith
  rw [e, Real.mul_rpow hx.le hy0.le, mul_comm]
  exact mul_le_mul_of_nonneg_right hyb (Real.rpow_nonneg hx.le _)

theorem rpow_ge_of_half {β x s : ℝ} (hx : 0 < x) (hs1 : x / 2 ≤ s) (hs2 : s ≤ x) :
    min ((1 / 2 : ℝ) ^ β) 1 * x ^ β ≤ s ^ β := by
  have hy0 : 0 < s / x := div_pos (by linarith) hx
  have hy1 : s / x ≤ 1 := (div_le_one hx).2 hs2
  have hyh : 1 / 2 ≤ s / x := by rw [le_div_iff₀ hx]; linarith
  have e : s = x * (s / x) := by field_simp
  have hyb : min ((1 / 2 : ℝ) ^ β) 1 ≤ (s / x) ^ β := by
    rcases le_total 0 β with hβ | hβ
    · exact (min_le_left _ _).trans (Real.rpow_le_rpow (by norm_num) hyh hβ)
    · exact (min_le_right _ _).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 hβ)
  rw [e, Real.mul_rpow hx.le hy0.le, mul_comm (x ^ β)]
  exact mul_le_mul_of_nonneg_right hyb (Real.rpow_nonneg hx.le _)

/-- The dyadic scales `x_n = δ 2^{−n}`. -/
abbrev dyX (δ : ℝ) (n : ℕ) : ℝ := δ * (1 / 2) ^ n

theorem dyX_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : 0 < dyX δ n := by unfold dyX; positivity

theorem dyX_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : dyX δ n ≤ δ := by
  unfold dyX
  exact mul_le_of_le_one_right hδ.le (pow_le_one₀ (by norm_num) (by norm_num))

theorem mem_dyadic_cover {δ t : ℝ} (_hδ : 0 < δ) (ht : t ∈ Icc (-δ) 0) (ht0 : t ≠ 0) :
    ∃ n : ℕ, t ∈ Icc (-dyX δ n) (-(dyX δ n / 2)) := by
  have htn : 0 < -t := by
    have := ht.2; rcases this.lt_or_eq with h | h
    · linarith
    · exact absurd h ht0
  have hx : 1 ≤ δ / -t := by rw [le_div_iff₀ htn]; linarith [ht.1]
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  rw [le_div_iff₀ htn] at h1
  rw [div_lt_iff₀ htn] at h2
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e : dyX δ n = δ / 2 ^ n := by unfold dyX; rw [one_div_pow, mul_one_div]
  refine ⟨n, ?_, ?_⟩
  · rw [e, neg_le, le_div_iff₀ hp]; linarith
  · rw [e, le_neg, div_div, div_le_iff₀ (by positivity)]
    rw [pow_succ] at h2; linarith

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

theorem aemeasurable_zField_Icc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℝ} :
    AEMeasurable (fun ω => qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc u v)) gffBase.P :=
  (Measure.measurable_coe measurableSet_Icc).comp_aemeasurable
    (LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (X := BdryExist.zField X₀ 1)
      (fun μ => (measurable_pi_apply μ).comp (BdryExist.measurable_zField gffBase.gff 1))
      (BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField gffBase.gff hγ hγ2 1))

/-- A.s. dyadic bound of `ν_C[−δ, 0]` by `ν_Z`. -/
theorem ae_g3pField_Icc_le_tsum {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂gffBase.P, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Icc (-δ) 0) ≤
      ∑' n, ENNReal.ofReal (((1 / 2 : ℝ) ^ (-(αC γ * γ / 2)) + 1) *
          dyX δ n ^ (-(αC γ * γ / 2))) *
        qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-dyX δ n) (-(dyX δ n / 2))) := by
  filter_upwards [ae_g3pField_good hγ hγ2] with ω hω
  obtain ⟨-, -, hat, hform⟩ := hω
  set νC := qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)
  set νZ := qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω)
  set β : ℝ := -(αC γ * γ / 2)
  have hcov : Icc (-δ) 0 ⊆ {0} ∪ ⋃ n, Icc (-dyX δ n) (-(dyX δ n / 2)) := fun t ht => by
    by_cases h0 : t = 0
    · exact Or.inl h0
    · exact Or.inr (mem_iUnion.2 (mem_dyadic_cover hδ ht h0))
  have hpiece : ∀ n, νC (Icc (-dyX δ n) (-(dyX δ n / 2))) ≤
      ENNReal.ofReal (((1 / 2 : ℝ) ^ β + 1) * dyX δ n ^ β) *
        νZ (Icc (-dyX δ n) (-(dyX δ n / 2))) := fun n => by
    have hx := dyX_pos hδ n
    rw [hform, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ t in Icc (-dyX δ n) (-(dyX δ n / 2)), ENNReal.ofReal (|t - 0| ^ β) ∂(νZ.restrict {0}ᶜ)
        ≤ ∫⁻ t in Icc (-dyX δ n) (-(dyX δ n / 2)),
            ENNReal.ofReal (((1 / 2 : ℝ) ^ β + 1) * dyX δ n ^ β) ∂(νZ.restrict {0}ᶜ) :=
          setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal (by
            rw [sub_zero, abs_of_nonpos (by linarith [ht.2])]
            exact rpow_le_of_half hx (by linarith [ht.2]) (by linarith [ht.1]))
      _ = ENNReal.ofReal (((1 / 2 : ℝ) ^ β + 1) * dyX δ n ^ β) *
            (νZ.restrict {0}ᶜ) (Icc (-dyX δ n) (-(dyX δ n / 2))) := setLIntegral_const _ _
      _ ≤ _ := by gcongr; exact Measure.restrict_le_self
  calc νC (Icc (-δ) 0) ≤ νC ({0} ∪ ⋃ n, Icc (-dyX δ n) (-(dyX δ n / 2))) := measure_mono hcov
    _ ≤ νC {0} + νC (⋃ n, Icc (-dyX δ n) (-(dyX δ n / 2))) := measure_union_le _ _
    _ = νC (⋃ n, Icc (-dyX δ n) (-(dyX δ n / 2))) := by rw [hat 0, zero_add]
    _ ≤ ∑' n, νC (Icc (-dyX δ n) (-(dyX δ n / 2))) := measure_iUnion_le _
    _ ≤ _ := ENNReal.tsum_le_tsum hpiece

theorem one_add_β_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < -(αC γ * γ / 2) + 1 := by
  have e : αC γ * γ = γ ^ 2 - 2 := by unfold αC; field_simp
  rw [e]
  nlinarith

/-- **F3-C, finiteness.** -/
theorem g3pZ_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    g3pZ γ (g3wProf γ) i < ⊤ := by
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  have hδ4 := i.hδ
  set β : ℝ := -(αC γ * γ / 2) with hβ
  set K : ℝ := (1 / 2 : ℝ) ^ β + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hβ1 := one_add_β_pos hγ hγ2
  set r : ℝ := (1 / 2 : ℝ) ^ (β + 1) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ1
  have hterm : ∀ n, K * dyX i.δ n ^ β * (3 / 2 * dyX i.δ n) =
      (3 / 2 * K * i.δ ^ (β + 1)) * r ^ n := fun n => by
    have hx := dyX_pos hδ n
    have e1 : dyX i.δ n ^ β * dyX i.δ n = dyX i.δ n ^ (β + 1) := (Real.rpow_add_one hx.ne' β).symm
    have e2 : dyX i.δ n ^ (β + 1) = i.δ ^ (β + 1) * r ^ n := by
      rw [dyX, Real.mul_rpow hδ.le (by positivity), hr,
        Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc K * dyX i.δ n ^ β * (3 / 2 * dyX i.δ n) = 3 / 2 * K * (dyX i.δ n ^ β * dyX i.δ n) := by
          ring
      _ = _ := by rw [e1, e2]; ring
  have hsum : Summable fun n => K * dyX i.δ n ^ β * (3 / 2 * dyX i.δ n) := by
    simp_rw [hterm]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hnn : ∀ n, 0 ≤ K * dyX i.δ n ^ β * (3 / 2 * dyX i.δ n) := fun n => by
    have hx := dyX_pos hδ n
    positivity
  rw [g3pZ_eq_honest hγ hγ2 i]
  calc ∫⁻ ω, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Icc (-i.δ) 0) ∂gffBase.P
      ≤ ∫⁻ ω, ∑' n, ENNReal.ofReal (K * dyX i.δ n ^ β) *
          qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-dyX i.δ n) (-(dyX i.δ n / 2)))
          ∂gffBase.P := lintegral_mono_ae (ae_g3pField_Icc_le_tsum hγ hγ2 hδ)
    _ = ∑' n, ENNReal.ofReal (K * dyX i.δ n ^ β) * ∫⁻ ω,
          qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-dyX i.δ n) (-(dyX i.δ n / 2)))
          ∂gffBase.P := by
        rw [lintegral_tsum fun n => (aemeasurable_zField_Icc hγ hγ2).const_mul _]
        exact tsum_congr fun n => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ∑' n, ENNReal.ofReal (K * dyX i.δ n ^ β) * ENNReal.ofReal (3 / 2 * dyX i.δ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        gcongr
        have hx := dyX_pos hδ n
        have hxl := dyX_le hδ n
        have := lintegral_qBoundaryMeasure_zField_one_Icc_le (P := gffBase.P) gffBase.gff hγ hγ2
          (a := -(3 / 2 * dyX i.δ n)) (u := -dyX i.δ n) (v := -(dyX i.δ n / 2)) (b := 0)
          (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
        rwa [zero_sub, neg_neg] at this
    _ = ENNReal.ofReal (∑' n, K * dyX i.δ n ^ β * (3 / 2 * dyX i.δ n)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
        refine tsum_congr fun n => ?_
        have hx := dyX_pos hδ n
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ K * dyX i.δ n ^ β)]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A.s. lower bound of `ν_C[−δ, 0]` by `ν_Z` on `(−δ, −δ/2)`. -/
theorem ae_g3pField_Icc_ge {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂gffBase.P, ENNReal.ofReal (min ((1 / 2 : ℝ) ^ (-(αC γ * γ / 2))) 1 *
        δ ^ (-(αC γ * γ / 2))) *
        qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Ioo (-δ) (-(δ / 2))) ≤
      qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Icc (-δ) 0) := by
  filter_upwards [ae_g3pField_good hγ hγ2] with ω hω
  obtain ⟨-, -, -, hform⟩ := hω
  set νZ := qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω)
  set β : ℝ := -(αC γ * γ / 2)
  set c : ℝ := min ((1 / 2 : ℝ) ^ β) 1 * δ ^ β
  have hsub : Ioo (-δ) (-(δ / 2)) ⊆ Icc (-δ) 0 := fun t ht =>
    ⟨ht.1.le, (ht.2.trans (by linarith)).le⟩
  have hmem : Ioo (-δ) (-(δ / 2)) ⊆ ({0} : Set ℝ)ᶜ := fun t ht => by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.2]
  have hρ : Measurable fun t : ℝ => ENNReal.ofReal (|t - 0| ^ β) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_id.sub continuous_const).abs.measurable.pow_const β)
  rw [hform, withDensity_apply _ measurableSet_Icc]
  calc ENNReal.ofReal c * νZ (Ioo (-δ) (-(δ / 2)))
      = ENNReal.ofReal c * (νZ.restrict {0}ᶜ) (Ioo (-δ) (-(δ / 2))) := by
        rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 hmem]
    _ = ∫⁻ t in Ioo (-δ) (-(δ / 2)), ENNReal.ofReal c ∂(νZ.restrict {0}ᶜ) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Ioo (-δ) (-(δ / 2)), ENNReal.ofReal (|t - 0| ^ β) ∂(νZ.restrict {0}ᶜ) :=
        setLIntegral_mono hρ fun t ht => ENNReal.ofReal_le_ofReal (by
          rw [sub_zero, abs_of_nonpos (by linarith [ht.2])]
          exact rpow_ge_of_half hδ (by linarith [ht.2]) (by linarith [ht.1]))
    _ ≤ _ := lintegral_mono_set hsub

/-- **F3-C, positivity.** -/
theorem g3pZ_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    0 < g3pZ γ (g3wProf γ) i := by
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  set δ := i.δ with hδdef
  have huv : -δ < -(δ / 2) := by linarith
  have hXpos : 0 < ∫⁻ ω, qBoundaryMeasure γ (X₀ ω) (Ioo (-δ) (-(δ / 2))) ∂gffBase.P :=
    FirstMoment.lintegral_qBoundaryMeasure_Ioo_pos_X gffBase.gff hγ hγ2 huv
  have hsm := Positivity.ae_qBoundaryMeasure_eq_smul_zField (X := X₀) gffBase.gff hγ hγ2 1
  set b : Ω₀ → ℝ≥0∞ :=
    fun ω => qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Ioo (-δ) (-(δ / 2))) with hbdef
  set a : Ω₀ → ℝ≥0∞ :=
    fun ω => ENNReal.ofReal (Real.exp (γ / 2 * X₀ ω (foldedCircle 0 1))) with hadef
  have ha : Measurable a :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((gffBase.gff.measurable_coord (foldedCircle 0 1)).const_mul (γ / 2)))
  have hb : AEMeasurable b gffBase.P :=
    (Measure.measurable_coe measurableSet_Ioo).comp_aemeasurable
      (LQGMeasAE.aemeasurable_qBoundaryMeasure_of_ae (X := BdryExist.zField X₀ 1)
        (fun μ => (measurable_pi_apply μ).comp (BdryExist.measurable_zField gffBase.gff 1))
        (BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField gffBase.gff hγ hγ2 1))
  have hkey : ∫⁻ ω, qBoundaryMeasure γ (X₀ ω) (Ioo (-δ) (-(δ / 2))) ∂gffBase.P =
      ∫⁻ ω, a ω * b ω ∂gffBase.P :=
    lintegral_congr_ae (by
      filter_upwards [hsm] with ω hω
      simp only [hω, Measure.smul_apply, smul_eq_mul, hbdef, hadef])
  have hpos : 0 < ∫⁻ ω, a ω * b ω ∂gffBase.P := hkey ▸ hXpos
  have hbpos : 0 < ∫⁻ ω, b ω ∂gffBase.P := by
    refine pos_iff_ne_zero.2 fun h0 => absurd hpos (not_lt.2 ?_)
    have hbae : b =ᵐ[gffBase.P] 0 := (lintegral_eq_zero_iff' hb).1 h0
    have hmul : AEMeasurable (fun ω => a ω * b ω) gffBase.P := ha.aemeasurable.mul hb
    rw [show (∫⁻ ω, a ω * b ω ∂gffBase.P) = 0 from by
      rw [lintegral_eq_zero_iff' hmul]
      filter_upwards [hbae] with ω hω
      simp [hω]]
  set c : ℝ := min ((1 / 2 : ℝ) ^ (-(αC γ * γ / 2))) 1 * δ ^ (-(αC γ * γ / 2)) with hc
  have hc0 : 0 < c := mul_pos (lt_min (by positivity) one_pos) (by positivity)
  have hmono : ∫⁻ ω, ENNReal.ofReal c * b ω ∂gffBase.P ≤
      ∫⁻ ω, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Icc (-δ) 0) ∂gffBase.P :=
    lintegral_mono_ae (ae_g3pField_Icc_ge hγ hγ2 hδ)
  have hfac : ∫⁻ ω, ENNReal.ofReal c * b ω ∂gffBase.P =
      ENNReal.ofReal c * ∫⁻ ω, b ω ∂gffBase.P :=
    lintegral_const_mul' _ b ENNReal.ofReal_ne_top
  rw [g3pZ_eq_honest hγ hγ2 i]
  exact lt_of_lt_of_le (hfac ▸ ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc0).ne' hbpos.ne') hmono

/-- **F3-C.** The Palm mass of scheme `C` is positive and finite. -/
theorem g3pZ_pos_lt_top {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    0 < g3pZ γ (g3wProf γ) i ∧ g3pZ γ (g3wProf γ) i < ⊤ :=
  ⟨g3pZ_pos hγ hγ2 i, g3pZ_lt_top hγ hγ2 i⟩

end R18
end QuantumZipper
