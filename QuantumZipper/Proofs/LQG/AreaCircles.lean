import QuantumZipper.Proofs.LQG.PalmArea
import QuantumZipper.Proofs.LQG.Atomless
import QuantumZipper.Proofs.LQG.AreaOffsets
import QuantumZipper.Proofs.LQG.MeasurabilityAE
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# M4-A4, part 1: the area measure charges no circle centred at `0`

Blueprint `M4_BLUEPRINT.md`, node M4-A4. Almost surely `μ_X(∂B(0,a) ∩ ℍ) = 0` for **every**
`a` (`ae_sphere_null`).

Route (the blueprint's): the area Palm formula `PalmArea.palm_formula_area_free` applied to
`φ(Y, z) = min(1, ∫_{∂B(0,|z|)} χ dμ_Y)` (written as a measurable function `phiC` of the folded-
circle coordinates `muJ j` of `Y` and of `z`). The right side vanishes because the field with a
`γ`-log singularity at `z` has no atom at `z` (M4-P4, area version, taken as the hypothesis
`AreaLogSingNoAtom`: `AtomlessUncond.lean` is not built) and, away from `z`, is absolutely
continuous with respect to `μ_Z`, which does not charge the fixed circle `∂B(0,|z|)`
(first moment, `ae_sphere_null_fixed`). Hence `E ∫ w(z) min(1, μ(∂B_{|z|}) ...) μ(dz) = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace AreaCircles

open VagueH
open AreaExist (aZ)

/-! ## 1. Tents around circles -/

/-- `max(0, 1 − (n+1) |‖w‖ − r|)`, decreasing in `n` to the indicator of `∂B(0,r)`. -/
def tentR (n : ℕ) (r : ℝ) (w : ℂ) : ℝ := max 0 (1 - ((n : ℝ) + 1) * |‖w‖ - r|)

theorem continuous_tentR (n : ℕ) : Continuous (fun p : ℝ × ℂ => tentR n p.1 p.2) := by
  unfold tentR; fun_prop

theorem continuous_tentR' (n : ℕ) (r : ℝ) : Continuous (tentR n r) := by
  unfold tentR; fun_prop

theorem tentR_nonneg (n : ℕ) (r : ℝ) (w : ℂ) : 0 ≤ tentR n r w := le_max_left _ _

theorem tentR_le_one (n : ℕ) (r : ℝ) (w : ℂ) : tentR n r w ≤ 1 := by
  unfold tentR
  have h1 : 0 ≤ ((n : ℝ) + 1) * |‖w‖ - r| := by positivity
  exact max_le zero_le_one (by linarith)

theorem tentR_of_norm {n : ℕ} {r : ℝ} {w : ℂ} (h : ‖w‖ = r) : tentR n r w = 1 := by
  simp [tentR, h]

theorem tentR_anti (r : ℝ) (w : ℂ) : Antitone fun n : ℕ => tentR n r w := by
  intro n n' h
  unfold tentR
  have h' : (n : ℝ) ≤ n' := by exact_mod_cast h
  have : ((n : ℝ) + 1) * |‖w‖ - r| ≤ ((n' : ℝ) + 1) * |‖w‖ - r| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  exact max_le_max le_rfl (by linarith)

theorem exists_tentR_eq_zero {r : ℝ} {w : ℂ} (h : ‖w‖ ≠ r) :
    ∃ N : ℕ, tentR N r w = 0 := by
  have hd : 0 < |‖w‖ - r| := abs_pos.2 (sub_ne_zero.2 h)
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / |‖w‖ - r|)
  refine ⟨N, ?_⟩
  unfold tentR
  refine max_eq_left ?_
  have : 1 ≤ (N : ℝ) * |‖w‖ - r| := by rwa [div_le_iff₀ hd] at hN
  nlinarith

theorem tentR_mul_le {χ : ℂ → ℝ} (hχ : ∀ w, 0 ≤ χ w) (n : ℕ) (r : ℝ) (w : ℂ) :
    tentR n r w * χ w ≤ χ w := by
  have := tentR_le_one n r w
  have := hχ w
  nlinarith [tentR_nonneg n r w]

theorem iInf_ofReal_tentR {χ : ℂ → ℝ} (r : ℝ) (w : ℂ) :
    ⨅ n : ℕ, ENNReal.ofReal (tentR n r w * χ w) =
      (Metric.sphere (0 : ℂ) r).indicator (fun w => ENNReal.ofReal (χ w)) w := by
  by_cases h : ‖w‖ = r
  · have hm : w ∈ Metric.sphere (0 : ℂ) r := by rw [mem_sphere_zero_iff_norm]; exact h
    rw [indicator_of_mem hm]
    simp only [tentR_of_norm h, one_mul, ciInf_const]
  · have hm : w ∉ Metric.sphere (0 : ℂ) r := by rw [mem_sphere_zero_iff_norm]; exact h
    rw [indicator_of_notMem hm]
    obtain ⟨N, hN⟩ := exists_tentR_eq_zero h
    refine le_antisymm ((iInf_le _ N).trans ?_) bot_le
    rw [hN, zero_mul, ENNReal.ofReal_zero]

/-! ## 2. The measurable functional `∫_{∂B(0,r)} χ dμ` -/

theorem measurable_integral_areaApprox_param (γ : ℝ) (k : ℕ) {g : ℝ × ℂ → ℝ}
    (hg : Measurable g) :
    Measurable fun p : FieldSample × ℝ => ∫ w, g (p.2, w) ∂areaApprox γ p.1 k := by
  let D : FieldSample × ℂ → ℝ := fun p =>
    radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg p.1 k p.2)
  have hDm : Measurable D :=
    (Real.measurable_exp.comp ((measurable_avgReg k).const_mul γ)).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ p : FieldSample × ℝ,
      ∫ w, g (p.2, w) ∂areaApprox γ p.1 k = ∫ w, D (p.1, w) * g (p.2, w) ∂(volume.restrict H) :=
    fun p => GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (hDm.comp (measurable_const.prodMk measurable_id)) (fun z => hD0 _) _
  simp_rw [heq]
  have hm : Measurable (fun q : (FieldSample × ℝ) × ℂ => D (q.1.1, q.2) * g (q.1.2, q.2)) :=
    (hDm.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hg.comp (measurable_fst.snd.prodMk measurable_snd))
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict H)
    hm.stronglyMeasurable).measurable

/-- `∫_{∂B(0,r)} χ dμ`, read off the approximations. -/
def circF (γ : ℝ) (χ : ℂ → ℝ) (x : FieldSample) (r : ℝ) : ℝ≥0∞ :=
  ⨅ n : ℕ, ENNReal.ofReal (liminf (fun k => ∫ w, tentR n r w * χ w ∂areaApprox γ x k) atTop)

theorem measurable_circF (γ : ℝ) {χ : ℂ → ℝ} (hχ : Measurable χ) :
    Measurable fun p : FieldSample × ℝ => circF γ χ p.1 p.2 := by
  unfold circF
  refine Measurable.iInf fun n => ENNReal.measurable_ofReal.comp ?_
  exact Measurable.liminf fun k => measurable_integral_areaApprox_param γ k
    (g := fun q : ℝ × ℂ => tentR n q.1 q.2 * χ q.2)
    ((continuous_tentR n).measurable.mul (hχ.comp measurable_snd))

theorem circF_eq {γ : ℝ} {χ : ℂ → ℝ} (hχ : IsTestH χ) (hχ0 : ∀ w, 0 ≤ χ w) {x : FieldSample}
    {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x) μ) (r : ℝ) :
    circF γ χ x r = ∫⁻ w in Metric.sphere (0 : ℂ) r, ENNReal.ofReal (χ w) ∂μ := by
  have hfin : μ (tsupport χ) < ⊤ := hμ.2.1 _ hχ.2.1 hχ.2.2
  have htest : ∀ n : ℕ, IsTestH (fun w => tentR n r w * χ w) := fun n =>
    ⟨(continuous_tentR' n r).mul hχ.1, hχ.2.1.mul_left,
      (tsupport_mul_subset_right).trans hχ.2.2⟩
  have hn : ∀ n : ℕ, ENNReal.ofReal (liminf (fun k => ∫ w, tentR n r w * χ w
      ∂areaApprox γ x k) atTop) = ∫⁻ w, ENNReal.ofReal (tentR n r w * χ w) ∂μ := by
    intro n
    have ht := hμ.2.2 _ (htest n).1 (htest n).2.1 (htest n).2.2
    rw [ht.liminf_eq, ofReal_integral_eq_lintegral_ofReal
      ((htest n).integrable ((measure_mono (tsupport_mul_subset_right)).trans_lt hfin))
      (ae_of_all _ fun w => mul_nonneg (tentR_nonneg n r w) (hχ0 w))]
  unfold circF
  simp_rw [hn]
  rw [← lintegral_iInf]
  · simp_rw [iInf_ofReal_tentR r]
    rw [lintegral_indicator Metric.isClosed_sphere.measurableSet]
  · exact fun n => ENNReal.measurable_ofReal.comp
      ((continuous_tentR' n r).mul hχ.1).measurable
  · exact fun n n' h w => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (tentR_anti r w h) (hχ0 w))
  · refine ne_top_of_le_ne_top (ne_top_of_lt ((htest 0).integrable
      ((measure_mono (tsupport_mul_subset_right)).trans_lt hfin)).lintegral_lt_top) ?_
    refine lintegral_mono fun w => ?_
    first
      | exact le_rfl
      | (rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))

/-- The Palm test functional `φ(y, z) = min(1, ∫_{∂B(0,‖z‖)} χ dμ_{rec y})`. -/
def phiC (γ : ℝ) (χ : ℂ → ℝ) (y : ℕ → ℝ) (z : ℂ) : ℝ :=
  min 1 (circF γ χ (Atomless.recJ y) ‖z‖).toReal

theorem measurable_phiC (γ : ℝ) {χ : ℂ → ℝ} (hχ : Measurable χ) :
    Measurable (Function.uncurry (phiC γ χ)) := by
  have h1 : Measurable (fun p : (ℕ → ℝ) × ℂ => (Atomless.recJ p.1, ‖p.2‖)) :=
    (Atomless.measurable_recJ.comp measurable_fst).prodMk measurable_snd.norm
  have h := Measurable.comp (g := fun q : FieldSample × ℝ => circF γ χ q.1 q.2)
    (f := fun p : (ℕ → ℝ) × ℂ => (Atomless.recJ p.1, ‖p.2‖)) (measurable_circF γ hχ) h1
  exact measurable_const.min (ENNReal.measurable_toReal.comp h)

theorem phiC_nonneg (γ : ℝ) (χ : ℂ → ℝ) (y : ℕ → ℝ) (z : ℂ) : 0 ≤ phiC γ χ y z :=
  le_min zero_le_one ENNReal.toReal_nonneg

theorem abs_phiC_le (γ : ℝ) (χ : ℂ → ℝ) (y : ℕ → ℝ) (z : ℂ) : |phiC γ χ y z| ≤ 1 := by
  rw [abs_of_nonneg (phiC_nonneg γ χ y z)]; exact min_le_left _ _

theorem areaApprox_recJ (γ : ℝ) (x : FieldSample) (k : ℕ) :
    areaApprox γ (Atomless.recJ (fun j => x (Atomless.muJ j))) k = areaApprox γ x k := by
  unfold areaApprox
  refine withDensity_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  dsimp only
  rw [Atomless.avgReg_recJ x k (H_subset_Hbar hz)]

theorem phiC_coords {γ : ℝ} {χ : ℂ → ℝ} (hχ : IsTestH χ) (hχ0 : ∀ w, 0 ≤ χ w)
    {x : FieldSample} {μ : Measure ℂ} (hμ : IsVagueLimitOn H (areaApprox γ x) μ) (z : ℂ) :
    phiC γ χ (fun j => x (Atomless.muJ j)) z =
      min 1 (∫⁻ w in Metric.sphere (0 : ℂ) ‖z‖, ENNReal.ofReal (χ w) ∂μ).toReal := by
  have e : circF γ χ (Atomless.recJ (fun j => x (Atomless.muJ j))) ‖z‖ = circF γ χ x ‖z‖ := by
    unfold circF; simp_rw [areaApprox_recJ]
  unfold phiC
  rw [e, circF_eq hχ hχ0 hμ]

/-! ## 3. A fixed circle is not charged (first moment) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem ofFun_zero_add' (y : FieldSample) : ofFun (fun _ => (0 : ℝ)) + y = y :=
  Atomless.ofFun_zero_add y

theorem aemeasurable_qAreaMeasure_aZ [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    AEMeasurable (fun ω => qAreaMeasure γ (aZ X R ω)) P := by
  have h := PalmArea.aemeasurable_qAreaMeasure_free (m := fun _ => (0 : ℝ)) hX hγ hγ2 R
    continuous_const
  simp only [ofFun_zero_add'] at h
  exact h

/-- **A fixed circle `∂B(0,r)` is a.s. not charged** by `μ_Z`, `Z = aZ X R`, `r + 3 ≤ R`. -/
theorem ae_sphere_null_fixed [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {R r : ℝ} (hr : r + 3 ≤ R) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (aZ X R ω) (Metric.sphere 0 r ∩ H) = 0 := by
  rcases lt_or_ge r 0 with hr0 | hr0
  · refine ae_of_all _ fun ω => ?_
    rw [Metric.sphere_eq_empty_of_neg hr0, empty_inter, measure_empty]
  have hR0 : 0 < R := by linarith
  set Kn : ℕ → Set ℂ := fun n =>
    Metric.sphere 0 r ∩ {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.im} with hKn
  have hU : Metric.sphere (0 : ℂ) r ∩ H = ⋃ n, Kn n := by
    ext z
    simp only [mem_inter_iff, mem_iUnion, hKn, mem_setOf_eq]
    constructor
    · rintro ⟨hs, hz⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < z.im from hz)
      exact ⟨n, hs, hn.le⟩
    · rintro ⟨n, hs, hn⟩
      exact ⟨hs, show 0 < z.im from lt_of_lt_of_le (by positivity) hn⟩
  have hmeasZ := aemeasurable_qAreaMeasure_aZ hX hγ hγ2 R (P := P)
  have key : ∀ n, ∀ᵐ ω ∂P, qAreaMeasure γ (aZ X R ω) (Kn n) = 0 := by
    intro n
    set K := Kn n with hK
    have hKc : IsCompact K := (isCompact_sphere 0 r).inter_right
      (isClosed_le continuous_const Complex.continuous_im)
    have hKH : K ⊆ H := fun z hz =>
      show 0 < z.im from lt_of_lt_of_le (by positivity) hz.2
    have hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R - 1 := fun z hz => by
      rw [mem_sphere_zero_iff_norm.1 hz.1]; linarith
    obtain ⟨χ, hχ, hχR, hχ1, hχ0⟩ := PalmArea.exists_testBump hKc hKH hKR
    set w : ℕ → ℂ → ℝ := fun j z => tentR j r z * χ z with hw
    have hwtest : ∀ j, IsTestH (w j) := fun j =>
      ⟨(continuous_tentR' j r).mul hχ.1, hχ.2.1.mul_left,
        (tsupport_mul_subset_right).trans hχ.2.2⟩
    have hw0 : ∀ j z, 0 ≤ w j z := fun j z => mul_nonneg (tentR_nonneg j r z) (hχ0 z)
    have hwR1 : ∀ j, ∀ z ∈ tsupport (w j), ‖z‖ + 1 ≤ R := fun j z hz => by
      have := hχR z (tsupport_mul_subset_right hz); linarith
    have hwR2 : ∀ j, ∀ z ∈ tsupport (w j), ‖z‖ + 2 ≤ R := fun j z hz => by
      have := hχR z (tsupport_mul_subset_right hz); linarith
    set ρ : ℂ → ℝ := fun z => Real.exp (γ ^ 2 * (2 * Real.log R - Real.log ‖z - conj z‖) / 2)
      with hρ
    have H' : ∀ j, ∫ ω, ∫ z, w j z ∂qAreaMeasure γ (aZ X R ω) ∂P = ∫ z, w j z * ρ z := by
      intro j
      have H := PalmArea.palm_formula_area_free (m := fun _ => (0 : ℝ)) (μ := Atomless.muJ)
        (φ := fun _ _ => (1 : ℝ)) (P := P) hX hγ hγ2 hR0 continuous_const Atomless.adm_muJ
        (hwtest j).1 (hwtest j).2.1 (hw0 j) (hwtest j).2.2 (hwR2 j) measurable_const
        (Cφ := 1) (fun _ _ => by simp)
      simpa only [mul_one, ofFun_zero_add', integral_const, probReal_univ, smul_eq_mul,
        one_mul, mul_zero, zero_add] using H
    have hint : ∀ j, Integrable (fun ω => ∫ z, w j z ∂qAreaMeasure γ (aZ X R ω)) P := fun j =>
      (PalmArea.integrable_and_tendsto_areaTest hX hγ hγ2 (hwtest j) (hwR1 j)).1
    have hbound : ∀ j, ∀ᵐ ω ∂P, qAreaMeasure γ (aZ X R ω) K ≤
        ENNReal.ofReal (∫ z, w j z ∂qAreaMeasure γ (aZ X R ω)) := by
      intro j
      filter_upwards [AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hv
      have hi : Integrable (w j) (qAreaMeasure γ (aZ X R ω)) := (hwtest j).integrable
        ((measure_mono tsupport_mul_subset_right).trans_lt (hv.2.1 _ hχ.2.1 hχ.2.2))
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hw0 j)),
        ← lintegral_indicator_one hKc.measurableSet]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz, Pi.one_apply, hw]
        simp only
        rw [tentR_of_norm (mem_sphere_zero_iff_norm.1 hz.1), hχ1 hz, Pi.one_apply, mul_one,
          ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]; exact bot_le
    have hle : ∀ j, ∫⁻ ω, qAreaMeasure γ (aZ X R ω) K ∂P ≤
        ENNReal.ofReal (∫ z, w j z * ρ z) := by
      intro j
      calc ∫⁻ ω, qAreaMeasure γ (aZ X R ω) K ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal (∫ z, w j z ∂qAreaMeasure γ (aZ X R ω)) ∂P :=
            lintegral_mono_ae (hbound j)
        _ = ENNReal.ofReal (∫ ω, ∫ z, w j z ∂qAreaMeasure γ (aZ X R ω) ∂P) :=
            (ofReal_integral_eq_lintegral_ofReal (hint j)
              (ae_of_all _ fun ω => integral_nonneg (hw0 j))).symm
        _ = _ := by rw [H' j]
    -- the right side tends to `0`
    have hρm : Measurable ρ := by
      have h1 : Measurable (fun z : ℂ => Real.log ‖z - conj z‖) :=
        Real.measurable_log.comp (continuous_id.sub Complex.continuous_conj).norm.measurable
      have h2 : Measurable (fun z : ℂ => γ ^ 2 * (2 * Real.log R - Real.log ‖z - conj z‖) / 2) :=
        ((measurable_const.sub h1).const_mul _).div_const _
      exact Real.measurable_exp.comp h2
    have hρ0 : ∀ z, 0 ≤ ρ z := fun z => (Real.exp_pos _).le
    have hρc : ContinuousOn ρ (tsupport χ) := by
      refine Real.continuous_exp.comp_continuousOn (ContinuousOn.div_const
        (continuousOn_const.mul (continuousOn_const.sub ?_)) _)
      refine ((continuous_id.sub Complex.continuous_conj).norm.continuousOn).log fun z hz => ?_
      show ‖z - (starRingEnd ℂ) z‖ ≠ 0
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have h1 : z.im = -z.im := by
        conv_lhs => rw [h]
        rw [Complex.conj_im]
      have := hχ.2.2 hz
      have h2 : 0 < z.im := this
      linarith
    obtain ⟨D, hD⟩ := hχ.2.1.isCompact.exists_bound_of_continuousOn hρc
    obtain ⟨C, hC⟩ := hχ.1.bounded_above_of_compact_support hχ.2.1
    have hgint : Integrable (fun z => χ z * ρ z) := by
      have hi : Integrable ((tsupport χ).indicator fun _ => C * D) :=
        (integrable_indicator_iff (isClosed_tsupport χ).measurableSet).2
          (integrableOn_const hχ.2.1.isCompact.measure_lt_top.ne)
      refine hi.mono' (hχ.1.measurable.mul hρm).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ tsupport χ
      · rw [indicator_of_mem hz, norm_mul]
        exact mul_le_mul (hC z) (hD z hz) (norm_nonneg _)
          ((norm_nonneg _).trans (hC z))
      · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero]
    have hlim : Tendsto (fun j => ∫ z, w j z * ρ z) atTop (𝓝 0) := by
      have hnull : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ Metric.sphere (0 : ℂ) r :=
        measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume 0 r)
      have h := tendsto_integral_of_dominated_convergence (fun z => χ z * ρ z)
        (F := fun j z => w j z * ρ z) (f := fun _ => (0 : ℝ))
        (fun j => (((continuous_tentR' j r).mul hχ.1).measurable.mul hρm).aestronglyMeasurable)
        hgint (fun j => ae_of_all _ fun z => by
          rw [Real.norm_of_nonneg (mul_nonneg (hw0 j z) (hρ0 z))]
          exact mul_le_mul_of_nonneg_right (tentR_mul_le hχ0 j r z) (hρ0 z))
        (hnull.mono fun z hz => by
          have hne : ‖z‖ ≠ r := fun h => hz (mem_sphere_zero_iff_norm.2 h)
          obtain ⟨N, hN⟩ := exists_tentR_eq_zero hne
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop N] with j hj
          have h0 : tentR j r z = 0 :=
            le_antisymm ((tentR_anti r z hj).trans hN.le) (tentR_nonneg j r z)
          simp only [hw, h0, zero_mul])
      simpa using h
    have hlim' : Tendsto (fun j => ENNReal.ofReal (∫ z, w j z * ρ z)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hlim
    have h0 : ∫⁻ ω, qAreaMeasure γ (aZ X R ω) K ∂P = 0 :=
      le_antisymm (ge_of_tendsto' hlim' hle) bot_le
    exact (lintegral_eq_zero_iff'
      ((Measure.measurable_coe hKc.measurableSet).comp_aemeasurable hmeasZ)).1 h0
  filter_upwards [ae_all_iff.2 key] with ω h
  rw [hU]
  exact measure_iUnion_null h

/-! ## 4. The Palm argument on a window -/

/-- **Hypothesis standing in for the interior (area) version of M4-P4**: for the normalized free
field `Z = aZ X R`, every `z ∈ ℍ` and every `g` continuous on `Hbar`, almost surely
`W = Z + γ(−log‖· − z‖) + g` has a vague area limit on `ℍ` and `μ_W({z}) = 0`. This is
`AtomlessUncond.ae_logSingularity_area` (not built) plus the continuous shift `g`. -/
def AreaLogSingNoAtom (X : Ω → FieldSample) (P : Measure Ω) (γ : ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ z : ℂ, z ∈ H → ‖z‖ + 1 ≤ R → ∀ g : ℂ → ℝ, ContinuousOn g Hbar →
    ∀ᵐ ω ∂P,
      IsVagueLimitOn H (areaApprox γ (aZ X R ω + ofFun (fun v => γ * -Real.log ‖v - z‖ + g v)))
        (qAreaMeasure γ (aZ X R ω + ofFun (fun v => γ * -Real.log ‖v - z‖ + g v))) ∧
      qAreaMeasure γ (aZ X R ω + ofFun (fun v => γ * -Real.log ‖v - z‖ + g v)) {z} = 0

theorem isVagueLimitOn_restrict' {U U' : Set ℂ} (hU' : IsOpen U') (hUU : U' ⊆ U)
    {νs : ℕ → Measure ℂ} {μ : Measure ℂ} (h : IsVagueLimitOn U νs μ) :
    IsVagueLimitOn U' νs (μ.restrict U') := by
  obtain ⟨h0, hK, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply' hU'.measurableSet]; simp, fun K hKc hKU =>
    (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKU.trans hUU)), fun f hf hfc hfU => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
    image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
  exact ht f hf hfc (hfU.trans hUU)

/-! ## 5. The Palm argument on a window (continued) -/

/-- First moment of `μ_Z(K)`, `Z = aZ X R`, for a compact `K ⊆ ℍ` well inside `B(0,R)`. -/
theorem lintegral_qAreaMeasure_aZ_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R) :
    ∫⁻ ω, qAreaMeasure γ (aZ X R ω) K ∂P < ∞ := by
  have h1 := PalmArea.lintegral_qAreaMeasure_zG_lt_top (m := fun _ => (0 : ℝ)) (P := P)
    hX hγ hγ2 hK hKH hKR continuous_const
  refine lt_of_eq_of_lt (lintegral_congr fun ω => ?_) h1
  have e : qAreaMeasure γ (ofFun (fun _ => (0 : ℝ)) + PalmFree.zG X R ω) =
      qAreaMeasure γ (BdryExist.zField X R ω) := by
    rw [PalmArea.qAreaMeasure_congr_Hbar (PalmFree.zG_add_fc' R _ ω), ofFun_zero_add']
  exact (congrArg (fun m : Measure ℂ => m K) e).symm

/-- Integrability of `ω ↦ ∫ G(ω,·) dν_ω` for a bounded jointly measurable `G` vanishing off a
measurable `K` with `E ν(K) < ∞`. -/
theorem integrable_integral_of_bdd {ν : Ω → Measure ℂ} (hν : AEMeasurable ν P) {K : Set ℂ}
    (hKm : MeasurableSet K) (hfin : ∫⁻ ω, ν ω K ∂P < ∞) {G : Ω × ℂ → ℝ} (hGm : Measurable G)
    {C : ℝ} (hGb : ∀ q, ‖G q‖ ≤ C) (hGvan : ∀ ω, ∀ z ∉ K, G (ω, z) = 0) :
    Integrable (fun ω => ∫ z, G (ω, z) ∂ν ω) P := by
  have hmeasK : AEMeasurable (fun ω => ν ω K) P :=
    (Measure.measurable_coe hKm).comp_aemeasurable hν
  have hIres : ∀ ω, ∫ z, G (ω, z) ∂ν ω = ∫ z in K, G (ω, z) ∂ν ω := fun ω =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hGvan ω)).symm
  set κ := PalmArea.kerIC hν hKm with hκ
  have hsm : StronglyMeasurable fun ω => ∫ z, G (ω, z) ∂κ ω :=
    hGm.stronglyMeasurable.integral_kernel_prod_right'
  have hIeq : (fun ω => ∫ z, G (ω, z) ∂ν ω) =ᵐ[P] fun ω => ∫ z, G (ω, z) ∂κ ω := by
    filter_upwards [PalmArea.nuModC_ae_eq hν hKm hfin] with ω hω
    rw [hκ, PalmArea.kerIC_apply, hω]
    exact hIres ω
  have hIbd : ∀ᵐ ω ∂P, ‖∫ z, G (ω, z) ∂ν ω‖ ≤ C * (ν ω K).toReal := by
    filter_upwards [ae_lt_top' hmeasK hfin.ne] with ω hω
    have : IsFiniteMeasure ((ν ω).restrict K) := isFiniteMeasure_restrict.2 hω.ne
    rw [hIres ω]
    have h := norm_integral_le_of_norm_le_const (μ := (ν ω).restrict K) (C := C)
      (ae_of_all _ fun z => hGb (ω, z))
    rw [measureReal_def, Measure.restrict_apply_univ] at h
    linarith
  exact ((integrable_toReal_of_lintegral_ne_top hmeasK hfin.ne).const_mul C).mono'
    (hsm.aestronglyMeasurable.congr hIeq.symm) hIbd

/-- The right side of the Palm identity vanishes pointwise: for `z ∈ ℍ`, a.s. the field with a
`γ`-log singularity at `z` does not charge `∂B(0,‖z‖)`. -/
theorem ae_phiC_logSing_eq_zero [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hP4 : AreaLogSingNoAtom X P γ) {R : ℝ} (hR0 : 0 < R) {z : ℂ}
    (hzH : z ∈ H) (hzR : ‖z‖ + 3 ≤ R) {χ : ℂ → ℝ} (hχ : IsTestH χ) (hχ0 : ∀ w, 0 ≤ χ w) :
    ∀ᵐ ω ∂P, phiC γ χ (fun j => (aZ X R ω +
      ofFun (fun u => γ * PalmArea.freeKernelC R z u)) (Atomless.muJ j)) z = 0 := by
  set g : ℂ → ℝ := fun v => γ * (-Real.log ‖v - (starRingEnd ℂ) z‖) -
    γ * KernelId.fcPot R 0 v with hg
  have hgc : ContinuousOn g Hbar := PalmArea.continuousOn_freeKernelC_rem γ hR0 hzH
  have heq : ∀ ω, aZ X R ω + ofFun (fun u => γ * PalmArea.freeKernelC R z u) =
      aZ X R ω + ofFun (fun v => γ * -Real.log ‖v - z‖ + g v) := by
    intro ω
    congr 2
    funext u
    rw [PalmArea.mul_freeKernelC_eq]
  set U : Set ℂ := H \ {z} with hUdef
  have hU : IsOpen U := isOpen_H.sdiff isClosed_singleton
  have hφc : ContinuousOn (fun v => γ * -Real.log ‖v - z‖ + g v) ({v | v ≠ z} ∩ Hbar) := by
    refine ContinuousOn.add (continuousOn_const.mul (ContinuousOn.neg ?_))
      (hgc.mono inter_subset_right)
    refine ((continuous_id.sub continuous_const).norm.continuousOn).log fun u hu => ?_
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hu.1)
  filter_upwards [hP4 R hR0 z hzH (by linarith) g hgc,
    PalmFree.ae_isRegularSample_zField hX R,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R,
    ae_sphere_null_fixed hX hγ hγ2 (r := ‖z‖) hzR] with ω hω hreg hvZ hnull
  obtain ⟨hv, hat⟩ := hω
  rw [heq ω, phiC_coords hχ hχ0 hv]
  set μW := qAreaMeasure γ (aZ X R ω + ofFun (fun v => γ * -Real.log ‖v - z‖ + g v))
  set μZ := qAreaMeasure γ (aZ X R ω)
  have hA := isVagueLimitOn_restrict' hU diff_subset hv
  have hB := LocalRule.isVagueLimitOn_add_ofFun hreg hU diff_subset
    (isVagueLimitOn_restrict' hU diff_subset hvZ) (W := {v | v ≠ z}) isOpen_ne
    (fun v hv => hv.2) hφc
  have hAB := isVagueLimitOn_unique hU hA hB
  set S := Metric.sphere (0 : ℂ) ‖z‖
  have hSm : MeasurableSet S := Metric.isClosed_sphere.measurableSet
  have h1 : μW (S ∩ U) = 0 := by
    rw [← Measure.restrict_apply hSm, hAB]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply hSm]
    exact measure_mono_null (inter_subset_inter_right _ diff_subset) hnull
  have h2 : μW S = 0 := by
    have hsub : S ⊆ (S ∩ U) ∪ {z} ∪ Hᶜ := by
      intro v hv
      by_cases hvH : v ∈ H
      · by_cases hvz : v = z
        · exact Or.inl (Or.inr hvz)
        · exact Or.inl (Or.inl ⟨hv, hvH, hvz⟩)
      · exact Or.inr hvH
    exact measure_mono_null hsub (measure_union_null (measure_union_null h1 hat) hv.1)
  rw [setLIntegral_measure_zero _ _ h2]
  simp

theorem measurable_phiC_comp {α : Type*} [MeasurableSpace α] (γ : ℝ) {χ : ℂ → ℝ}
    (hχ : Measurable χ) {f : α → ℕ → ℝ} {g : α → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => phiC γ χ (f a) (g a) := by
  have h1 : Measurable fun a => (Atomless.recJ (f a), ‖g a‖) :=
    (Atomless.measurable_recJ.comp hf).prodMk hg.norm
  have h := (measurable_circF γ hχ).comp h1
  simp only [Function.comp_def] at h
  unfold phiC
  exact measurable_const.min (ENNReal.measurable_toReal.comp h)

/-- Pathwise conclusion: if `∫ w(z) min(1, ∫_{∂B(0,‖z‖)} χ dν) ν(dz) = 0` with `χ = 1` on
`tsupport w`, then `ν` charges no `∂B(0,r) ∩ {w > 0}`. -/
theorem sphere_null_of_integral_eq_zero {γ : ℝ} {y : FieldSample} {ν : Measure ℂ}
    (hv : IsVagueLimitOn H (areaApprox γ y) ν) {w χ : ℂ → ℝ} (hw : IsTestH w)
    (hw0 : ∀ z, 0 ≤ w z) (hχ : IsTestH χ) (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : EqOn χ 1 (tsupport w))
    (hI : ∫ z, w z * phiC γ χ (fun j => y (Atomless.muJ j)) z ∂ν = 0) (r : ℝ) :
    ν (Metric.sphere 0 r ∩ {z | 0 < w z}) = 0 := by
  set K := tsupport w with hKdef
  have hfinK : ν K < ⊤ := hv.2.1 K hw.2.1 hw.2.2
  obtain ⟨Cw, hCw⟩ := hw.1.bounded_above_of_compact_support hw.2.1
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℝ, g = fun z => w z * phiC γ χ (fun j => y (Atomless.muJ j)) z :=
    ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact hw.1.measurable.mul
      (measurable_phiC_comp γ hχ.1.measurable measurable_const measurable_id)
  have hg0 : ∀ z, 0 ≤ g z := fun z => by
    rw [hg]; exact mul_nonneg (hw0 _) (phiC_nonneg γ χ _ _)
  have hgb : ∀ z, ‖g z‖ ≤ Cw := fun z => by
    rw [Real.norm_of_nonneg (hg0 z), hg]
    have h1 : phiC γ χ (fun j => y (Atomless.muJ j)) z ≤ 1 := min_le_left _ _
    calc w z * phiC γ χ (fun j => y (Atomless.muJ j)) z ≤ w z * 1 := mul_le_mul_of_nonneg_left h1 (hw0 _)
      _ = w z := mul_one _
      _ ≤ Cw := by have := hCw z; rw [Real.norm_of_nonneg (hw0 _)] at this; exact this
  have hgvan : ∀ z ∉ K, g z = 0 := fun z hz => by
    simp only [hg, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hIK : ∫ z in K, g z ∂ν = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hgvan, hg]; exact hI
  have : IsFiniteMeasure (ν.restrict K) := isFiniteMeasure_restrict.2 hfinK.ne
  have hint : Integrable g (ν.restrict K) :=
    Integrable.of_bound hgm.aestronglyMeasurable Cw (ae_of_all _ hgb)
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hint).1 hIK
  by_contra hne
  set A := Metric.sphere (0 : ℂ) r ∩ {z | 0 < w z} with hA
  have hAm : MeasurableSet A := Metric.isClosed_sphere.measurableSet.inter
    (isOpen_lt continuous_const hw.1).measurableSet
  have hAK : A ⊆ K := fun z hz => subset_tsupport w (ne_of_gt hz.2)
  have hcirc_pos : 0 < ∫⁻ v in Metric.sphere (0 : ℂ) r, ENNReal.ofReal (χ v) ∂ν := by
    have e1 : ν A = ∫⁻ v in A, ENNReal.ofReal (χ v) ∂ν := by
      rw [← setLIntegral_one]
      refine setLIntegral_congr_fun hAm fun v hv => ?_
      rw [hχ1 (hAK hv), Pi.one_apply, ENNReal.ofReal_one]
    have hpos : 0 < ν A := pos_iff_ne_zero.2 hne
    rw [e1] at hpos
    exact hpos.trans_le (lintegral_mono_set inter_subset_left)
  have hcirc_fin : ∫⁻ v in Metric.sphere (0 : ℂ) r, ENNReal.ofReal (χ v) ∂ν ≠ ⊤ := by
    have hi : Integrable χ ν := hχ.integrable (hv.2.1 _ hχ.2.1 hχ.2.2)
    refine ne_top_of_le_ne_top (ne_of_lt ?_) (setLIntegral_le_lintegral _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hχ0)]
    exact ENNReal.ofReal_lt_top
  have hgpos : ∀ z ∈ A, g z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ = r := mem_sphere_zero_iff_norm.1 hz.1
    simp only [hg]
    rw [phiC_coords hχ hχ0 hv, hz']
    exact (mul_pos hz.2 (lt_min one_pos (ENNReal.toReal_pos hcirc_pos.ne' hcirc_fin))).ne'
  have hnull : ν.restrict K {z | g z ≠ 0} = 0 := ae_iff.1 hae
  have h0 : ν.restrict K A = 0 := measure_mono_null hgpos hnull
  rw [Measure.restrict_apply hAm, inter_eq_self_of_subset_left hAK] at h0
  exact hne h0

/-- **The Palm argument on a window.** -/
theorem ae_sphere_null_window [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hP4 : AreaLogSingNoAtom X P γ) {R : ℝ} {w : ℂ → ℝ}
    (hw : IsTestH w) (hw0 : ∀ z, 0 ≤ w z) (hwR : ∀ z ∈ tsupport w, ‖z‖ + 3 ≤ R) :
    ∀ᵐ ω ∂P, ∀ r : ℝ,
      qAreaMeasure γ (aZ X R ω) (Metric.sphere 0 r ∩ {z | 0 < w z}) = 0 := by
  by_cases hne : (tsupport w).Nonempty
  swap
  · refine ae_of_all _ fun ω r => ?_
    have : {z | 0 < w z} = ∅ := by
      ext z
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      rw [image_eq_zero_of_notMem_tsupport (fun h => hne ⟨z, h⟩)]
    rw [this, inter_empty, measure_empty]
  obtain ⟨z₀, hz₀⟩ := hne
  have hR0 : 0 < R := by linarith [hwR z₀ hz₀, norm_nonneg z₀]
  set K := tsupport w with hKdef
  have hK : IsCompact K := hw.2.1
  have hKH : K ⊆ H := hw.2.2
  have hKR : ∀ z ∈ K, ‖z‖ + 2 ≤ R := fun z hz => by linarith [hwR z hz]
  obtain ⟨χ, hχ, hχR, hχ1, hχ0⟩ := PalmArea.exists_testBump hK hKH hKR
  have hPalm := PalmArea.palm_formula_area_free (m := fun _ => (0 : ℝ)) (μ := Atomless.muJ)
    (φ := phiC γ χ) (P := P) hX hγ hγ2 hR0 continuous_const Atomless.adm_muJ hw.1 hw.2.1 hw0
    hw.2.2 hKR (measurable_phiC γ hχ.1.measurable) (Cφ := 1) (abs_phiC_le γ χ)
  simp only [ofFun_zero_add'] at hPalm
  have hRHS : ∫ z, w z * Real.exp (γ * 0 + γ ^ 2 * (2 * Real.log R -
      Real.log ‖z - (starRingEnd ℂ) z‖) / 2) *
      ∫ ω, phiC γ χ (fun j => (aZ X R ω +
        ofFun (fun u => γ * PalmArea.freeKernelC R z u)) (Atomless.muJ j)) z ∂P = 0 := by
    refine integral_eq_zero_of_ae (ae_of_all _ fun z => ?_)
    simp only [Pi.zero_apply]
    by_cases hz : z ∈ K
    · rw [integral_eq_zero_of_ae (ae_phiC_logSing_eq_zero hX hγ hγ2 hP4 hR0 (hKH hz)
        (hwR z hz) hχ hχ0), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]
  obtain ⟨ν, hνdef⟩ : ∃ ν : Ω → Measure ℂ, ν = fun ω => qAreaMeasure γ (aZ X R ω) := ⟨_, rfl⟩
  have hν : AEMeasurable ν P := by rw [hνdef]; exact aemeasurable_qAreaMeasure_aZ hX hγ hγ2 R
  have hcoord : Measurable fun ω => fun j => aZ X R ω (Atomless.muJ j) :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply _).comp (AreaExist.measurable_aZ hX R)
  have hfin : ∫⁻ ω, ν ω K ∂P < ∞ := by
    rw [hνdef]; exact lintegral_qAreaMeasure_aZ_lt_top hX hγ hγ2 hK hKH hKR
  obtain ⟨Cw, hCw⟩ := hw.1.bounded_above_of_compact_support hw.2.1
  obtain ⟨G, hG⟩ : ∃ G : Ω × ℂ → ℝ,
      G = fun q => w q.2 * phiC γ χ (fun j => aZ X R q.1 (Atomless.muJ j)) q.2 := ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hG]
    exact (hw.1.measurable.comp measurable_snd).mul
      (measurable_phiC_comp γ hχ.1.measurable (hcoord.comp measurable_fst) measurable_snd)
  have hG0 : ∀ q, 0 ≤ G q := fun q => by
    rw [hG]; exact mul_nonneg (hw0 _) (phiC_nonneg γ χ _ _)
  have hGb : ∀ q, ‖G q‖ ≤ Cw := fun q => by
    rw [Real.norm_of_nonneg (hG0 q), hG]
    have h1 : phiC γ χ (fun j => aZ X R q.1 (Atomless.muJ j)) q.2 ≤ 1 := min_le_left _ _
    calc w q.2 * phiC γ χ (fun j => aZ X R q.1 (Atomless.muJ j)) q.2 ≤ w q.2 * 1 := mul_le_mul_of_nonneg_left h1 (hw0 _)
      _ = w q.2 := mul_one _
      _ ≤ Cw := by have := hCw q.2; rw [Real.norm_of_nonneg (hw0 _)] at this; exact this
  have hGvan : ∀ ω, ∀ z ∉ K, G (ω, z) = 0 := fun ω z hz => by
    simp only [hG, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hInt : Integrable (fun ω => ∫ z, G (ω, z) ∂ν ω) P :=
    integrable_integral_of_bdd hν hK.measurableSet hfin hGm hGb hGvan
  have hPalm' : ∫ ω, ∫ z, G (ω, z) ∂ν ω ∂P = 0 := by
    rw [hG, hνdef]; exact hPalm.trans hRHS
  have hI0 : (fun ω => ∫ z, G (ω, z) ∂ν ω) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => integral_nonneg fun z => hG0 _) hInt).1 hPalm'
  filter_upwards [hI0, AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hI hv r
  have hI' : ∫ z, w z * phiC γ χ (fun j => aZ X R ω (Atomless.muJ j)) z
      ∂qAreaMeasure γ (aZ X R ω) = 0 := by
    have := hI; rw [hG, hνdef] at this; exact this
  exact sphere_null_of_integral_eq_zero hv hw hw0 hχ hχ0 hχ1 hI' r

/-! ## 6. All circles, for the free field -/

/-- **M4-A4 (circles).** For the free field, almost surely `μ_X(∂B(0,a) ∩ ℍ) = 0` for every
`a`, under the area log-singularity hypothesis (M4-P4, area). -/
theorem ae_sphere_null [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hP4 : AreaLogSingNoAtom X P γ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, qAreaMeasure γ (X ω) (Metric.sphere 0 a ∩ H) = 0 := by
  have hbump : ∀ N : ℕ, ∃ w : ℂ → ℝ, IsTestH w ∧ (∀ z, 0 ≤ w z) ∧
      (∀ z ∈ tsupport w, ‖z‖ + 3 ≤ (N : ℝ) + 4) ∧ LQGMeas.hExh N ⊆ {z | 0 < w z} := by
    intro N
    obtain ⟨g, hgc, hgcs, hgU, hg1, hg0⟩ := GoodSample.exists_bump (LQGMeas.isCompact_hExhK N)
      (isOpen_H.inter (isOpen_lt continuous_norm continuous_const))
      (fun z hz => ⟨LQGMeas.hExhK_subset_H N hz,
        show ‖z‖ < (N : ℝ) + 1 by linarith [mem_closedBall_zero_iff.1 hz.1]⟩)
    refine ⟨g, ⟨hgc, hgcs, hgU.trans inter_subset_left⟩, hg0, fun z hz => ?_, fun z hz => ?_⟩
    · have : ‖z‖ < (N : ℝ) + 1 := (hgU hz).2
      linarith
    · show 0 < g z
      rw [hg1 (LQGMeas.hExh_subset_compact N hz), Pi.one_apply]; exact one_pos
  choose w hw hw0 hwR hwsub using hbump
  have h1 : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ r : ℝ, qAreaMeasure γ (aZ X ((N : ℝ) + 4) ω)
      (Metric.sphere 0 r ∩ {z | 0 < w N z}) = 0 :=
    ae_all_iff.2 fun N => ae_sphere_null_window hX hγ hγ2 hP4 (hw N) (hw0 N) (hwR N)
  have h2 : ∀ᵐ ω ∂P, ∀ N : ℕ, qAreaMeasure γ (BdryExist.zField X ((N : ℝ) + 4) ω) =
      ENNReal.ofReal (Real.exp (-(γ * X ω (foldedCircle 0 ((N : ℝ) + 4))))) •
        qAreaMeasure γ (X ω) :=
    ae_all_iff.2 fun N => AreaOffsets.ae_qAreaMeasure_zField_eq hX hγ hγ2 _
  filter_upwards [h1, h2] with ω h1 h2 a
  have hsub : Metric.sphere (0 : ℂ) a ∩ H ⊆
      ⋃ N : ℕ, Metric.sphere 0 a ∩ {z | 0 < w N z} := by
    intro z hz
    obtain ⟨N, hN⟩ := mem_iUnion.1 (LQGMeas.H_subset_iUnion_hExh hz.2)
    exact mem_iUnion.2 ⟨N, hz.1, hwsub N hN⟩
  refine measure_mono_null hsub (measure_iUnion_null fun N => ?_)
  have h := h1 N a
  have e : aZ X ((N : ℝ) + 4) ω = BdryExist.zField X ((N : ℝ) + 4) ω := rfl
  rw [e, h2 N, Measure.smul_apply, smul_eq_mul] at h
  rcases mul_eq_zero.1 h with h' | h'
  · exact absurd h' (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  · exact h'

end AreaCircles
end QuantumZipper
