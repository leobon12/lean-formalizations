import QuantumZipper.Proofs.Thm18.G3PalmRTightBasic
import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.LQG.AreaOffsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-PALMRTIGHT, part 2: uniform-in-root bounds for the log-singular measure

For `m^x = |t − x|^{−γ²/2} ν_Z|_{\{x\}ᶜ}` (`palmM`, `Z = zField X 5`):

* `palmM_Icc_ge`: `m^x[¼, ½] ≥ ν_Z[¼, ½]` for `x ∈ [−½, 0]` (the density is `≥ 1` there);
* `palmM_le_tsum`: `m^x(A) ≤ S_x := Σ_n 2^{(n+1)γ²/2} ν_Z(x + 2^{−n}[−1, 1])` for `A` within
  distance `1` of `x` (dyadic annuli around the root);
* `palm_moment_bound`: `E S_x^p ≤ B` for some `p ∈ (0, 1]`, uniformly in `|x| ≤ 1`, from the
  fractional moment bound `FracMom.fracMoment_dyadic` (whose constant is uniform in the centre)
  and `p < (Q − γ)/γ` (the standard `α < Q` log-singularity argument, as in
  `LogSing.ae_summable_tail`; Duplantier–Sheffield, arXiv:0808.1560);
* `palm_tight_upper` (Markov) and `palm_tight_lower` (`ν_Z[¼, ½] > 0` a.s.,
  `Positivity.ae_forall_pos_qBoundaryMeasure`).

The uniformity in the root is exactly what the paper's "translation invariance" gives; here it
comes from the centre-uniform constant of `fracMoment_dyadic`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem ofReal_rpow_le_tsum_annuli {γ x t : ℝ} (hγ : 0 < γ) (ht0 : t ≠ x) (ht1 : |t - x| ≤ 1) :
    ENNReal.ofReal (|t - x| ^ (-(γ * γ / 2))) ≤
      ∑' n, LogSing.annW γ γ n * (LogSing.annI x n).indicator 1 t := by
  classical
  have hpos : 0 < |t - x| := abs_pos.2 (sub_ne_zero.2 ht0)
  have hex : ∃ n, radius (n + 1) ≤ |t - x| := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, (AreaExist.aradius_anti (Nat.le_succ n)).trans hn.le⟩
  set n := Nat.find hex with hn
  have hn1 : radius (n + 1) ≤ |t - x| := Nat.find_spec hex
  have hdn : |t - x| ≤ radius n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos'
    · rw [h0, LogSing.radius_zero']; exact ht1
    · have := Nat.find_min hex (show n - 1 < n by omega)
      rw [Nat.sub_add_cancel hpos'] at this
      exact (not_le.1 this).le
  refine le_trans ?_ (ENNReal.le_tsum n)
  rw [indicator_of_mem (LogSing.mem_annI hdn), Pi.one_apply, mul_one]
  unfold LogSing.annW
  exact ENNReal.ofReal_le_ofReal (LogSing.rpow_neg_le_of_le hγ (radius_pos _) hn1 ht1)

/-- The dyadic-annuli majorant `S_x`. -/
def palmS (γ x R : ℝ) (X : Ω → FieldSample) (ω : Ω) : ℝ≥0∞ :=
  ∑' n, LogSing.annW γ γ n * qBoundaryMeasure γ (BdryExist.zField X R ω) (LogSing.annI x n)

theorem palmM_le_palmS {γ x : ℝ} (hγ : 0 < γ) (R : ℝ) (ω : Ω) {A : Set ℝ}
    (hA : MeasurableSet A) (hA1 : ∀ t ∈ A, |t - x| ≤ 1) :
    palmM γ x R X ω A ≤ palmS γ x R X ω := by
  set ν := qBoundaryMeasure γ (BdryExist.zField X R ω)
  have hmi : ∀ n, Measurable fun t => LogSing.annW γ γ n * (LogSing.annI x n).indicator 1 t :=
    fun n => (measurable_const.indicator measurableSet_Icc).const_mul _
  rw [palmM, withDensity_apply _ hA, Measure.restrict_restrict hA]
  calc ∫⁻ t in A ∩ {x}ᶜ, ENNReal.ofReal (|t - x| ^ (-(γ * γ / 2))) ∂ν
      ≤ ∫⁻ t in A ∩ {x}ᶜ, ∑' n, LogSing.annW γ γ n * (LogSing.annI x n).indicator 1 t ∂ν :=
        setLIntegral_mono' (hA.inter (measurableSet_singleton x).compl) fun t ht =>
          ofReal_rpow_le_tsum_annuli hγ ht.2 (hA1 t ht.1)
    _ ≤ ∫⁻ t, ∑' n, LogSing.annW γ γ n * (LogSing.annI x n).indicator 1 t ∂ν :=
        setLIntegral_le_lintegral _ _
    _ = palmS γ x R X ω := by
        rw [lintegral_tsum fun n => (hmi n).aemeasurable]
        unfold palmS
        congr 1
        funext n
        have hm : MeasurableSet (LogSing.annI x n) := measurableSet_Icc
        rw [lintegral_const_mul _ (measurable_one.indicator hm), lintegral_indicator_one hm]

theorem palmM_Icc_ge {γ x : ℝ} (hx0 : x ≤ 0) (hx1 : -(1 / 2) ≤ x) (R : ℝ) (ω : Ω) :
    qBoundaryMeasure γ (BdryExist.zField X R ω) (Icc (1 / 4) (1 / 2)) ≤
      palmM γ x R X ω (Icc (1 / 4) (1 / 2)) := by
  have hsub : Icc (1 / 4 : ℝ) (1 / 2) ∩ {x}ᶜ = Icc (1 / 4) (1 / 2) := by
    refine inter_eq_left.2 fun t ht => ?_
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h; linarith [ht.1]
  rw [palmM, withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    hsub, ← setLIntegral_one]
  refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
  have h1 : 0 < |t - x| := abs_pos.2 (by linarith [ht.1])
  have h2 : |t - x| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ENNReal.one_le_ofReal.2
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h1 h2 (by nlinarith [sq_nonneg γ]))

theorem isFreeGFFModConstH_zField (hX : IsFreeGFFModConstH X P) (R : ℝ) :
    IsFreeGFFModConstH (BdryExist.zField X R) P :=
  S5.FieldLaw.Raw.isFreeGFFModConstH_addConst hX (c := fun ω => -X ω (foldedCircle 0 R))
    (hX.measurable_coord _).neg

open Classical in
theorem aemeasurable_zField_bdry [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    AEMeasurable (fun ω => qBoundaryMeasure γ (BdryExist.zField X R ω) S) P := by
  refine ⟨fun ω => (if IsLQGGood γ (BdryExist.zField X R ω) then
      qBoundaryMeasure γ (BdryExist.zField X R ω) else 0) S, ?_, ?_⟩
  · exact (Measure.measurable_coe hS).comp
      ((GoodMeas.measurable_qBoundaryMeasure_global γ).comp (BdryExist.measurable_zField hX R))
  · filter_upwards [AreaOffsets.ae_isLQGGood (isFreeGFFModConstH_zField hX R) hγ hγ2] with ω hω
    simp [hω]

theorem aemeasurable_palmS [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x R : ℝ) :
    AEMeasurable (palmS γ x R X) P :=
  AEMeasurable.ennreal_tsum fun _ =>
    (aemeasurable_zField_bdry hX hγ hγ2 R measurableSet_Icc).const_mul _

/-- **Uniform fractional moment of `S_x`.** -/
theorem palm_moment_bound [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x : ℝ, |x| ≤ 1 →
      ∫⁻ ω, palmS γ x 5 X ω ^ p ∂P ≤ B := by
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
  have hαQ : γ < Qc γ := gamma_lt_Qc_g3prt hγ hγ2
  set p := min 1 ((Qc γ - γ) / γ) with hpdef
  have hp0 : 0 < p := lt_min one_pos (div_pos (by linarith) hγ)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpγ : γ * p ≤ Qc γ - γ := by
    have := min_le_right 1 ((Qc γ - γ) / γ)
    rw [le_div_iff₀ hγ] at this; linarith
  set e := γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4) with he
  have hneg : LogSing.expB γ γ * p + e < 0 := by
    have hin : γ * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4 < 0 := by
      have h1 : γ * (γ * p) ≤ γ * (Qc γ - γ) := mul_le_mul_of_nonneg_left hpγ hγ.le
      have h2 : γ * (γ - Qc γ) < 0 := mul_neg_of_pos_of_neg hγ (by linarith)
      nlinarith
    have : LogSing.expB γ γ * p + e = p * (γ * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4) := by
      rw [he]; unfold LogSing.expB; rw [max_eq_left hγ.le]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hp0 hin
  obtain ⟨C, hC0, hC⟩ := FracMom.fracMoment_dyadic hX hγ hγ2 (R := 5) (by norm_num) hp0 hp1
  set u : ℕ → ℝ := fun n => (radius (n + 1) ^ (-LogSing.expB γ γ)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e)
    with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _) (by positivity)
  have husum : Summable u := LogSing.summable_annuli hp0.le hneg
  refine ⟨p, hp0, hp1, ENNReal.ofReal C * ENNReal.ofReal (∑' n, u n),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun x hx => ?_⟩
  have hterm : ∀ n, ∫⁻ ω, (LogSing.annW γ γ n *
      qBoundaryMeasure γ (BdryExist.zField X 5 ω) (LogSing.annI x n)) ^ p ∂P ≤
      ENNReal.ofReal C * ENNReal.ofReal (u n) := by
    intro n
    have hw : LogSing.annW γ γ n ^ p =
        ENNReal.ofReal ((radius (n + 1) ^ (-LogSing.expB γ γ)) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (radius_pos _).le _) hp0.le
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hcond : |x| + 4 * radius n ≤ 5 := by linarith [BdryExist.radius_le_one n]
    have hsub : LogSing.annI x n ⊆ Ioo (x - 4 * radius n / 2) (x + 4 * radius n / 2) := by
      intro t ht
      have := radius_pos n
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc ENNReal.ofReal ((radius (n + 1) ^ (-LogSing.expB γ γ)) ^ p) *
          ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X 5 ω) (LogSing.annI x n) ^ p ∂P
        ≤ ENNReal.ofReal ((radius (n + 1) ^ (-LogSing.expB γ γ)) ^ p) *
          ENNReal.ofReal (C * 2 ^ (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))) := by
          gcongr
          refine le_trans (lintegral_mono fun ω => ?_) (hC n x hcond).2
          exact ENNReal.rpow_le_rpow (measure_mono hsub) hp0.le
      _ = ENNReal.ofReal C * ENNReal.ofReal (u n) := by
          rw [show (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4)) = (n : ℝ) * e by
            rw [he]; ring, ENNReal.ofReal_mul hC0, hu,
            ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _)]
          ring
  calc ∫⁻ ω, palmS γ x 5 X ω ^ p ∂P
      ≤ ∫⁻ ω, ∑' n, (LogSing.annW γ γ n *
          qBoundaryMeasure γ (BdryExist.zField X 5 ω) (LogSing.annI x n)) ^ p ∂P :=
        lintegral_mono fun ω => FracMom.rpow_tsum_le_tsum_rpow _ hp0 hp1
    _ = ∑' n, ∫⁻ ω, (LogSing.annW γ γ n *
          qBoundaryMeasure γ (BdryExist.zField X 5 ω) (LogSing.annI x n)) ^ p ∂P :=
        lintegral_tsum fun n =>
          ((aemeasurable_zField_bdry hX hγ hγ2 5 measurableSet_Icc).const_mul _).pow_const p
    _ ≤ ∑' n, ENNReal.ofReal C * ENNReal.ofReal (u n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal C * ENNReal.ofReal (∑' n, u n) := by
        rw [ENNReal.tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hu0 husum]

/-- **Upper tightness of `S_x`, uniformly in `|x| ≤ 1`** (Markov). -/
theorem palm_tight_upper [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, |x| ≤ 1 →
      P {ω | ENNReal.ofReal K ≤ palmS γ x 5 X ω} ≤ ENNReal.ofReal ε := by
  obtain ⟨p, hp0, hp1, B, hB, hbd⟩ := palm_moment_bound hX hγ hγ2
  set b := B.toReal
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  set y := (b + 1) / ε with hy
  have hy0 : 0 < y := div_pos (by linarith) hε
  refine ⟨y ^ p⁻¹, Real.rpow_pos_of_pos hy0 _, fun x hx => ?_⟩
  have hKp : ENNReal.ofReal (y ^ p⁻¹) ^ p = ENNReal.ofReal y := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hy0.le _) hp0.le,
      Real.rpow_inv_rpow hy0.le hp0.ne']
  calc P {ω | ENNReal.ofReal (y ^ p⁻¹) ≤ palmS γ x 5 X ω}
      ≤ P {ω | ENNReal.ofReal (y ^ p⁻¹) ^ p ≤ palmS γ x 5 X ω ^ p} :=
        measure_mono fun ω hω => ENNReal.rpow_le_rpow hω hp0.le
    _ ≤ (∫⁻ ω, palmS γ x 5 X ω ^ p ∂P) / ENNReal.ofReal (y ^ p⁻¹) ^ p :=
        meas_ge_le_lintegral_div ((aemeasurable_palmS hX hγ hγ2 x 5).pow_const p)
          (by rw [hKp]; exact (ENNReal.ofReal_pos.2 hy0).ne') (by rw [hKp]; exact ENNReal.ofReal_ne_top)
    _ ≤ B / ENNReal.ofReal y := by rw [hKp]; gcongr; exact hbd x hx
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.div_le_of_le_mul ?_
        rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hε.le, hy,
          mul_div_cancel₀ _ hε.ne']
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Lower tightness of `ν_Z[¼, ½]`** (`ν_Z[¼, ½] > 0` a.s.). -/
theorem palm_tight_lower [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ P {ω | qBoundaryMeasure γ (BdryExist.zField X 5 ω) (Icc (1 / 4) (1 / 2)) <
      (n : ℝ≥0∞)⁻¹} ≤ ENNReal.ofReal ε := by
  have hg := aemeasurable_zField_bdry hX hγ hγ2 5 (measurableSet_Icc (a := (1 / 4 : ℝ)) (b := 1 / 2))
  set g' := hg.mk _
  have hpos : ∀ᵐ ω ∂P, 0 < g' ω := by
    filter_upwards [Positivity.ae_forall_pos_qBoundaryMeasure (isFreeGFFModConstH_zField hX 5)
      hγ hγ2, hg.ae_eq_mk] with ω hω he
    exact lt_of_lt_of_eq (hω _ (by rw [interior_Icc]; exact nonempty_Ioo.2 (by norm_num))) he
  set E : ℕ → Set Ω := fun n => {ω | g' ω < (n : ℝ≥0∞)⁻¹}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_lt hg.measurable_mk measurable_const
  have hanti : Antitone E := fun m n hmn ω hω =>
    lt_of_lt_of_le hω (ENNReal.inv_le_inv.2 (by exact_mod_cast hmn))
  have hI : P (⋂ n, E n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    simp only [mem_iInter, E, mem_setOf_eq] at hω
    simp only [mem_setOf_eq, not_lt, nonpos_iff_eq_zero]
    by_contra h0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h0
    exact (hω n).not_gt hn
  have ht := tendsto_measure_iInter_atTop (fun n => (hEm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  rw [hI] at ht
  obtain ⟨N, hN⟩ := (ht.eventually (eventually_le_nhds (ENNReal.ofReal_pos.2 hε))).exists_forall_of_atTop
  refine ⟨N + 1, Nat.succ_pos _, le_trans (measure_mono_ae ?_) (hN (N + 1) (Nat.le_succ N))⟩
  filter_upwards [hg.ae_eq_mk] with ω he hω
  exact lt_of_eq_of_lt he.symm hω

end Thm18Asm
end QuantumZipper
