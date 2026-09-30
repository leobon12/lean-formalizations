import QuantumZipper.Proofs.LQG.LogSingularity

/-!
# Good samples with a boundary log singularity at `0`: the deterministic part

For a regular sample `x` and `L = α(−log‖·‖)` (`Lf α`):

* exact densities at every radius `r > 0`: `bdryDens (x + L) r t = max(r,|t|)^{−αγ/2} bdryDens x r t`
  and `areaDens (x + L) r z = max(r,‖z‖)^{−αγ} areaDens x r z` (mean value property of `log`);
* area (`hasAreaLimit_add_Lf`): the area test functions are supported in `ℍ`, away from `0`, so
  the area limit of `x + L` is `‖z‖^{−αγ} μ_x`, deterministically;
* boundary (`hasBdryLimit_add_Lf`): given uniform smallness near `0` along `goodFilter`, the
  boundary limit of `x + L` is `|t|^{−αγ/2} ν_x` restricted to `ℝ \ {0}`;
* uniform smallness near `0` along all offsets (`tight_offsets`) from a summable tail of
  `annW n · annTo n`, where `annTo x n` is the supremum of `ν_r(x)([−2^{−n}, 2^{−n}])` over all
  (rational) radii `0 < r ≤ 2^{−n}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LogSingGood

open GoodSample LogSing CircleFubini

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {γ : ℝ}

/-- The log singularity `α(−log‖·‖)` at `0`. -/
def Lf (α : ℝ) (v : ℂ) : ℝ := α * -Real.log ‖v‖

theorem Lf_eq (α : ℝ) : (fun v : ℂ => α * -Real.log ‖v - ((0 : ℝ) : ℂ)‖) = Lf α := by
  funext v; simp [Lf]

theorem regular_add_Lf (hF : IsRegularWith x F) (α : ℝ) :
    IsRegularWith (x + ofFun (Lf α)) (fun q => F q + α * (CircleCont.circPot q.2 q.1 0 / 2)) := by
  have h := hF.add_ofFun_log' α 0
  rw [Lf_eq] at h
  simpa using h

theorem evalReg_add_Lf_fc (hF : IsRegularWith x F) (α : ℝ) {z : ℂ} (hz : z ∈ Hbar) {r : ℝ}
    (hr : 0 < r) :
    evalReg (x + ofFun (Lf α)) (foldedCircle z r) =
      evalReg x (foldedCircle z r) + α * -Real.log (max r ‖z‖) := by
  rw [(regular_add_Lf hF α).evalReg_fc_of_mem hz hr, hF.evalReg_fc_of_mem hz hr]
  simp only [CircleCont.circPot, map_zero, sub_zero]
  ring

theorem exp_mul_neg_log {M : ℝ} (hM : 0 < M) (c : ℝ) :
    Real.exp (c * -Real.log M) = M ^ (-c) := by
  rw [Real.rpow_def_of_pos hM]; congr 1; ring

theorem bdryDens_add_Lf (hF : IsRegularWith x F) (γ α : ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    bdryDens γ (x + ofFun (Lf α)) r t = max r |t| ^ (-(α * γ / 2)) * bdryDens γ x r t := by
  have ht : ((t : ℂ)) ∈ Hbar := GaussTK.ofReal_mem_Hbar t
  have hm0 : 0 < max r |t| := lt_max_of_lt_left hr
  unfold bdryDens
  rw [evalReg_add_Lf_fc hF α ht hr, Complex.norm_real, Real.norm_eq_abs, mul_add,
    Real.exp_add]
  have e1 : Real.exp (γ / 2 * (α * -Real.log (max r |t|))) = max r |t| ^ (-(α * γ / 2)) := by
    rw [← exp_mul_neg_log hm0]; congr 1; ring
  rw [e1]; ring

theorem areaDens_add_Lf (hF : IsRegularWith x F) (γ α : ℝ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ Hbar) :
    areaDens γ (x + ofFun (Lf α)) r z = max r ‖z‖ ^ (-(α * γ)) * areaDens γ x r z := by
  have hm0 : 0 < max r ‖z‖ := lt_max_of_lt_left hr
  unfold areaDens
  rw [evalReg_add_Lf_fc hF α hz hr, mul_add, Real.exp_add]
  have e1 : Real.exp (γ * (α * -Real.log (max r ‖z‖))) = max r ‖z‖ ^ (-(α * γ)) := by
    rw [← exp_mul_neg_log hm0]; congr 1; ring
  rw [e1]; ring

theorem integral_bdryR_add_Lf (hF : IsRegularWith x F) (γ α : ℝ) {r : ℝ} (hr : 0 < r)
    (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryR γ (x + ofFun (Lf α)) r =
      ∫ t, max r |t| ^ (-(α * γ / 2)) * f t ∂bdryR γ x r := by
  unfold bdryR
  rw [integral_withDensity_ofReal (continuous_bdryDens γ (regular_add_Lf hF α) hr).measurable
      (bdryDens_nonneg γ _ hr),
    integral_withDensity_ofReal (continuous_bdryDens γ hF hr).measurable (bdryDens_nonneg γ _ hr)]
  congr 1; funext t
  rw [bdryDens_add_Lf hF γ α hr t]; ring

theorem integral_areaR_add_Lf (hF : IsRegularWith x F) (γ α : ℝ) {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℝ) :
    ∫ z, f z ∂areaR γ (x + ofFun (Lf α)) r =
      ∫ z, max r ‖z‖ ^ (-(α * γ)) * f z ∂areaR γ x r := by
  unfold areaR
  rw [integral_withDensity_ofReal (continuous_areaDens γ (regular_add_Lf hF α) hr).measurable
      (areaDens_nonneg γ _ hr),
    integral_withDensity_ofReal (continuous_areaDens γ hF hr).measurable (areaDens_nonneg γ _ hr)]
  refine integral_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  have hz' : z ∈ Hbar := show (0 : ℝ) ≤ z.im from le_of_lt hz
  show areaDens γ (x + ofFun (Lf α)) r z * f z = areaDens γ x r z * (max r ‖z‖ ^ (-(α * γ)) * f z)
  rw [areaDens_add_Lf hF γ α hr hz']; ring

/-! ## Continuity of products with functions continuous off a closed set -/

theorem continuous_mul_of_tsupport' {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsOpen U)
    {φ g : X → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ U) (hg : ContinuousOn g U) :
    Continuous fun z => g z * φ z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ U
  · exact (hg.continuousAt (hU.mem_nhds hz)).mul hφ.continuousAt
  · have h0 : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hz (hs h))
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

/-! ## The area limit -/

theorem hasAreaLimit_add_Lf (hF : IsRegularWith x F) {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ)
    (α : ℝ) :
    HasAreaLimit γ (x + ofFun (Lf α))
      (μ.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(α * γ)))) := by
  have hgc : ContinuousOn (fun z : ℂ => ‖z‖ ^ (-(α * γ))) H :=
    continuous_norm.continuousOn.rpow_const fun z hz => Or.inl (norm_ne_zero_iff.2 fun h => by
      have : (0 : ℝ) < z.im := hz
      rw [h] at this; simp at this)
  have hwm : Measurable fun z : ℂ => ‖z‖ ^ (-(α * γ)) := measurable_norm.pow_const _
  refine ⟨withDensity_absolutelyContinuous _ _ hμ.1,
    fun K hK hKH => withDensity_lt_top hK (hμ.2.1 K hK hKH) (hgc.mono hKH),
    fun f hf hfc hfU => ?_⟩
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ z ∈ tsupport f, δ ≤ ‖z‖ := by
    by_cases hne : (tsupport f).Nonempty
    · obtain ⟨z0, hz0, hmin⟩ := hfc.isCompact.exists_isMinOn hne continuous_norm.continuousOn
      refine ⟨‖z0‖, norm_pos_iff.2 fun h => ?_, fun z hz => hmin hz⟩
      have : (0 : ℝ) < z0.im := hfU hz0
      rw [h] at this; simp at this
    · exact ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hne⟩
  have hgcont : Continuous fun z => ‖z‖ ^ (-(α * γ)) * f z :=
    continuous_mul_of_tsupport' isOpen_H hf hfU hgc
  have hlim := hμ.2.2 _ hgcont (hfc.mul_left) ((tsupport_mul_subset_right).trans hfU)
  rw [integral_withDensity_ofReal hwm fun z => Real.rpow_nonneg (norm_nonneg z) _]
  refine hlim.congr' ?_
  filter_upwards [tendsto_goodRad.eventually (Ioo_mem_nhdsGT hδ)] with i hi
  rw [integral_areaR_add_Lf hF γ α hi.1 f]
  congr 1; funext z
  by_cases hz : z ∈ tsupport f
  · rw [max_eq_right ((hi.2.le).trans (hδK z hz))]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

/-! ## The boundary limit, given uniform smallness near `0` -/

/-- The boundary weight `|t|^{−αγ/2}`. -/
def wB (γ α : ℝ) (t : ℝ) : ℝ := |t| ^ (-(α * γ / 2))

theorem continuousOn_wB (γ α : ℝ) : ContinuousOn (wB γ α) {0}ᶜ :=
  continuous_abs.continuousOn.rpow_const fun _ ht => Or.inl (abs_ne_zero.2 ht)

theorem measurable_wB (γ α : ℝ) : Measurable (wB γ α) := continuous_abs.measurable.pow_const _

theorem wB_nonneg (γ α t : ℝ) : 0 ≤ wB γ α t := Real.rpow_nonneg (abs_nonneg t) _

theorem tsupport_subset_of_vanish {g : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hg0 : ∀ t, |t| < η → g t = 0) : tsupport g ⊆ {0}ᶜ := by
  intro t ht h0
  rw [mem_singleton_iff] at h0
  subst h0
  have : g =ᶠ[𝓝 (0 : ℝ)] 0 := by
    filter_upwards [Ioo_mem_nhds (by linarith : -η < 0) hη] with u hu
    exact hg0 u (abs_lt.2 hu)
  exact (notMem_tsupport_iff_eventuallyEq.2 this) ht

theorem continuous_wB_mul (γ α : ℝ) {g : ℝ → ℝ} (hg : Continuous g) {η : ℝ} (hη : 0 < η)
    (hg0 : ∀ t, |t| < η → g t = 0) : Continuous fun t => wB γ α t * g t :=
  continuous_mul_of_tsupport' isOpen_compl_singleton hg (tsupport_subset_of_vanish hη hg0)
    (continuousOn_wB γ α)

instance goodFilter_neBot : goodFilter.NeBot :=
  Filter.prod_neBot.2 ⟨atTop_neBot, principal_neBot_iff.2 (nonempty_Icc.2 (by norm_num))⟩

section Bdry

variable {α : ℝ}

/-- Test functions vanishing near `0`: the limit is `∫ |t|^{−αγ/2} g dν`. -/
theorem tendsto_far (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : HasBdryLimit γ x ν)
    {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) {η : ℝ} (hη : 0 < η)
    (hg0 : ∀ t, |t| < η → g t = 0) :
    Tendsto (fun i => ∫ t, g t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i)) goodFilter
      (𝓝 (∫ t, wB γ α t * g t ∂ν)) := by
  have hlim := hν.2 _ (continuous_wB_mul γ α hg hη hg0) hgc.mul_left
  refine hlim.congr' ?_
  filter_upwards [tendsto_goodRad.eventually (Ioo_mem_nhdsGT hη)] with i hi
  rw [integral_bdryR_add_Lf hF γ α hi.1 g]
  congr 1; funext t
  by_cases ht : |t| < η
  · rw [hg0 t ht, mul_zero, mul_zero]
  · rw [max_eq_right (hi.2.le.trans (not_lt.1 ht))]; rfl

theorem integral_nu' {ν : Measure ℝ} {g : ℝ → ℝ} (hg0 : g 0 = 0) :
    ∫ t, g t ∂((ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t)) =
      ∫ t, wB γ α t * g t ∂ν := by
  rw [integral_withDensity_ofReal (measurable_wB γ α) (wB_nonneg γ α)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
  have : t = 0 := by simpa using ht
  rw [this, hg0, mul_zero]

theorem abs_integral_le_of_indicator {μ : Measure ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hμS : μ S < ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ t, |g t| ≤ C * S.indicator 1 t) {ε : ℝ} (hε : 0 ≤ ε) (hle : μ S ≤ ENNReal.ofReal ε) :
    |∫ t, g t ∂μ| ≤ C * ε := by
  have hi1 : Integrable (S.indicator (1 : ℝ → ℝ)) μ :=
    (integrable_indicator_iff hS).2 ((integrableOn_const_iff).2 (Or.inr hμS))
  have hi : Integrable (fun t => C * S.indicator (1 : ℝ → ℝ) t) μ := hi1.const_mul C
  calc |∫ t, g t ∂μ| = ‖∫ t, g t ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, C * S.indicator (1 : ℝ → ℝ) t ∂μ :=
        norm_integral_le_of_norm_le hi (ae_of_all _ fun t => by rw [Real.norm_eq_abs]; exact hg t)
    _ = C * μ.real S := by rw [integral_const_mul, integral_indicator_one hS]
    _ ≤ C * ε := mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hε hle) hC

theorem trapS_le_one' (δ t : ℝ) : trapS 0 δ t ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- Smallness of the limit near `0`. -/
theorem nu'_small (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : HasBdryLimit γ x ν) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hev : ∀ᶠ i in goodFilter, bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ) ≤
      ENNReal.ofReal ε) :
    ((ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t)) (Ioo (-(δ / 2)) (δ / 2)) ≤
      ENNReal.ofReal ε := by
  set ν' := (ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t) with hν'
  have := hν.1
  have hFL := regular_add_Lf hF α
  have hν0 : ν' {0} = 0 := withDensity_absolutelyContinuous _ _ (by
    rw [Measure.restrict_apply (measurableSet_singleton 0)]; simp)
  set S : ℕ → Set ℝ := fun j => Ioo (-(δ / 2)) (δ / 2) ∩ {t | 2 / ((j : ℝ) + 1) ≤ |t|} with hSdef
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)
  have hS : ∀ j, ν' (S j) ≤ ENNReal.ofReal ε := by
    intro j
    set φ : ℝ → ℝ := fun t => cutS 0 j t * trapS 0 δ t with hφdef
    have hφc : Continuous φ := continuous_cutS.mul (continuous_trapS 0 δ)
    have hφcs : HasCompactSupport φ := (hasCompactSupport_trapS hδ).mul_left
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hφ0 : ∀ t, |t| < 1 / ((j : ℝ) + 1) → φ t = 0 := fun t ht => by
      simp only [hφdef]
      rw [cutS_eq_zero (by simpa using ht.le), zero_mul]
    have hφnn : ∀ t, 0 ≤ φ t := fun t => mul_nonneg cutS_nonneg trapS_nonneg
    have hφS : ∀ t ∈ S j, φ t = 1 := by
      intro t ht
      simp only [hφdef]
      rw [cutS_eq_one (by simpa using ht.2), trapS_eq_one hδ (by
        have := ht.1; simpa using (abs_lt.2 ⟨this.1, this.2⟩).le), one_mul]
    have hφle : ∀ t, φ t ≤ (Ioo (-δ) δ).indicator 1 t := by
      intro t
      by_cases ht : t ∈ Ioo (-δ) δ
      · rw [indicator_of_mem ht, Pi.one_apply]
        exact mul_le_one₀ cutS_le_one trapS_nonneg (trapS_le_one' δ t)
      · rw [indicator_of_notMem ht]
        have hδt : δ ≤ |t - 0| := by
          rw [sub_zero]
          by_contra h
          push_neg at h
          exact ht (abs_lt.1 h)
        simp only [hφdef]
        rw [trapS_eq_zero hδ hδt, mul_zero]
    have hlim := tendsto_far (α := α) hF hν hφc hφcs hj hφ0
    have hle : ∀ᶠ i in goodFilter, ∫ t, φ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) ≤ ε := by
      filter_upwards [hev, eventually_goodRad_pos] with i hi hpos
      have hfin : bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ) < ⊤ :=
        hi.trans_lt ENNReal.ofReal_lt_top
      have := abs_integral_le_of_indicator (g := φ) measurableSet_Ioo hfin zero_le_one
        (fun t => by rw [abs_of_nonneg (hφnn t), one_mul]; exact hφle t) hε hi
      rw [one_mul] at this
      exact (le_abs_self _).trans this
    have hlimle : ∫ t, wB γ α t * φ t ∂ν ≤ ε := le_of_tendsto hlim hle
    have hwφc := continuous_wB_mul γ α hφc hj hφ0
    have hint : Integrable (fun t => wB γ α t * φ t) ν :=
      hwφc.integrable_of_hasCompactSupport hφcs.mul_left
    calc ν' (S j) = ∫⁻ t, (S j).indicator 1 t ∂ν' := (lintegral_indicator_one (hSm j)).symm
      _ ≤ ∫⁻ t, ENNReal.ofReal (φ t) ∂ν' := lintegral_mono fun t => by
          by_cases ht : t ∈ S j
          · rw [indicator_of_mem ht, hφS t ht]; simp
          · rw [indicator_of_notMem ht]; exact zero_le
      _ = ∫⁻ t, ENNReal.ofReal (wB γ α t) * ENNReal.ofReal (φ t) ∂(ν.restrict {0}ᶜ) := by
          rw [hν', lintegral_withDensity_eq_lintegral_mul _ (measurable_wB γ α).ennreal_ofReal
            hφc.measurable.ennreal_ofReal]
          rfl
      _ ≤ ∫⁻ t, ENNReal.ofReal (wB γ α t) * ENNReal.ofReal (φ t) ∂ν :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ t, ENNReal.ofReal (wB γ α t * φ t) ∂ν := by
          simp_rw [← ENNReal.ofReal_mul (wB_nonneg γ α _)]
      _ = ENNReal.ofReal (∫ t, wB γ α t * φ t ∂ν) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (ae_of_all _ fun t => mul_nonneg (wB_nonneg γ α t) (hφnn t))).symm
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hlimle
  have hmono : Monotone S := by
    intro i j hij t ht
    refine ⟨ht.1, ?_⟩
    have h2 : 2 / ((i : ℝ) + 1) ≤ |t| := ht.2
    show 2 / ((j : ℝ) + 1) ≤ |t|
    refine le_trans ?_ h2
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have hU : Ioo (-(δ / 2)) (δ / 2) ⊆ (⋃ j, S j) ∪ {0} := by
    intro t ht
    by_cases h0 : t = 0
    · right; exact h0
    · left
      have hpos : 0 < |t| := abs_pos.2 h0
      obtain ⟨j, hj⟩ := exists_nat_gt (2 / |t|)
      refine mem_iUnion.2 ⟨j, ht, ?_⟩
      show 2 / ((j : ℝ) + 1) ≤ |t|
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hj
      nlinarith
  calc ν' (Ioo (-(δ / 2)) (δ / 2)) ≤ ν' ((⋃ j, S j) ∪ {0}) := measure_mono hU
    _ ≤ ν' (⋃ j, S j) + ν' {0} := measure_union_le _ _
    _ = ⨆ j, ν' (S j) := by rw [hν0, add_zero, hmono.measure_iUnion]
    _ ≤ ENNReal.ofReal ε := iSup_le hS

theorem isFiniteMeasureOnCompacts_nu' {ν : Measure ℝ} (hν : HasBdryLimit γ x ν)
    (hsmall : ∃ δ > 0, ((ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t))
      (Ioo (-δ) δ) < ⊤) :
    IsFiniteMeasureOnCompacts ((ν.restrict {0}ᶜ).withDensity
      fun t => ENNReal.ofReal (wB γ α t)) := by
  obtain ⟨δ, hδ, hfin⟩ := hsmall
  have := hν.1
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K \ Ioo (-δ) δ) := hK.diff isOpen_Ioo
  have hsub : K ⊆ Ioo (-δ) δ ∪ (K \ Ioo (-δ) δ) := fun t ht => by
    by_cases h : t ∈ Ioo (-δ) δ
    · exact Or.inl h
    · exact Or.inr ⟨ht, h⟩
  refine (measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.2 ⟨hfin, ?_⟩))
  have hm : MeasurableSet (K \ Ioo (-δ) δ) := hK'.isClosed.measurableSet
  have hne : K \ Ioo (-δ) δ ⊆ {0}ᶜ := fun t ht h0 => by
    rw [mem_singleton_iff] at h0
    exact ht.2 (by rw [h0]; exact ⟨by linarith, hδ⟩)
  calc ((ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t)) (K \ Ioo (-δ) δ)
      ≤ (ν.withDensity fun t => ENNReal.ofReal (wB γ α t)) (K \ Ioo (-δ) δ) := by
        rw [withDensity_apply _ hm, withDensity_apply _ hm]
        exact lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) le_rfl
    _ < ⊤ := withDensity_lt_top hK' hK'.measure_lt_top ((continuousOn_wB γ α).mono hne)

/-- **Boundary limit of `x + α(−log‖·‖)`**, given uniform smallness of the approximations near
`0` along `goodFilter`. -/
theorem hasBdryLimit_add_Lf (hF : IsRegularWith x F) {ν : Measure ℝ} (hν : HasBdryLimit γ x ν)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ i in goodFilter,
      bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ) ≤ ENNReal.ofReal ε) :
    HasBdryLimit γ (x + ofFun (Lf α))
      ((ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t)) := by
  set ν' := (ν.restrict {0}ᶜ).withDensity fun t => ENNReal.ofReal (wB γ α t) with hν'
  have hFL := regular_add_Lf hF α
  have hfinC : IsFiniteMeasureOnCompacts ν' := by
    obtain ⟨δ, hδ, hev⟩ := htight 1 one_pos
    exact isFiniteMeasureOnCompacts_nu' hν ⟨δ / 2, by positivity,
      (nu'_small hF hν hδ zero_le_one hev).trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' := ε / (4 * (C + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hev⟩ := htight ε' hε'0
  have hsm := nu'_small hF hν hδ hε'0.le hev
  set χ := trapS 0 (δ / 2) with hχ
  have hδ2 : 0 < δ / 2 := by positivity
  have hχc : Continuous χ := continuous_trapS 0 (δ / 2)
  set f₁ : ℝ → ℝ := fun t => f t * (1 - χ t) with hf₁
  set f₂ : ℝ → ℝ := fun t => f t * χ t with hf₂
  have hf₁c : Continuous f₁ := hf.mul (continuous_const.sub hχc)
  have hf₂c : Continuous f₂ := hf.mul hχc
  have hf₁cs : HasCompactSupport f₁ := hfc.mul_right
  have hf₂cs : HasCompactSupport f₂ := hfc.mul_right
  have hf₁0 : ∀ t, |t| < δ / 4 → f₁ t = 0 := fun t ht => by
    simp only [hf₁, hχ]
    rw [trapS_eq_one hδ2 (by rw [sub_zero]; linarith), sub_self, mul_zero]
  have hf₂b : ∀ t, |f₂ t| ≤ C * (Ioo (-(δ / 2)) (δ / 2)).indicator 1 t := by
    intro t
    by_cases ht : t ∈ Ioo (-(δ / 2)) (δ / 2)
    · rw [indicator_of_mem ht, Pi.one_apply, mul_one, hf₂, abs_mul,
        abs_of_nonneg (trapS_nonneg (s := 0) (t := t) (δ := δ / 2))]
      have h1 : |f t| ≤ C := by simpa [Real.norm_eq_abs] using hC t
      calc |f t| * χ t ≤ C * 1 :=
            mul_le_mul h1 (trapS_le_one' _ t) trapS_nonneg hC0
        _ = C := mul_one C
    · rw [indicator_of_notMem ht, mul_zero]
      have hδt : δ / 2 ≤ |t - 0| := by
        rw [sub_zero]
        by_contra h
        push_neg at h
        exact ht (abs_lt.1 h)
      simp only [hf₂, hχ]
      rw [trapS_eq_zero hδ2 hδt, mul_zero, abs_zero]
  have hf₂b' : ∀ t, |f₂ t| ≤ C * (Ioo (-δ) δ).indicator 1 t := by
    intro t
    refine (hf₂b t).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    exact indicator_le_indicator_of_subset (Ioo_subset_Ioo (by linarith) (by linarith))
      (fun _ => zero_le_one) t
  have hlim := tendsto_far (α := α) hF hν hf₁c hf₁cs (by positivity : (0 : ℝ) < δ / 4) hf₁0
  rw [← integral_nu' (hf₁0 0 (by rw [abs_zero]; linarith))] at hlim
  filter_upwards [Metric.tendsto_nhds.1 hlim (ε / 2) (by positivity), hev,
    eventually_goodRad_pos] with i h1 h2 hpos
  haveI : IsFiniteMeasureOnCompacts (bdryR γ (x + ofFun (Lf α)) (goodRad i)) :=
    ⟨fun K hK => bdryR_lt_top γ hFL hpos hK⟩
  have e1 : ∫ t, f t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) =
      ∫ t, f₁ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) +
        ∫ t, f₂ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) := by
    rw [← integral_add (hf₁c.integrable_of_hasCompactSupport hf₁cs)
      (hf₂c.integrable_of_hasCompactSupport hf₂cs)]
    congr 1; funext t; simp only [hf₁, hf₂, Pi.add_apply]; ring
  have e2 : ∫ t, f t ∂ν' = ∫ t, f₁ t ∂ν' + ∫ t, f₂ t ∂ν' := by
    rw [← integral_add (hf₁c.integrable_of_hasCompactSupport hf₁cs)
      (hf₂c.integrable_of_hasCompactSupport hf₂cs)]
    congr 1; funext t; simp only [hf₁, hf₂, Pi.add_apply]; ring
  have b1 : |∫ t, f₂ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i)| ≤ C * ε' :=
    abs_integral_le_of_indicator measurableSet_Ioo (h2.trans_lt ENNReal.ofReal_lt_top) hC0
      hf₂b' hε'0.le h2
  have b2 : |∫ t, f₂ t ∂ν'| ≤ C * ε' :=
    abs_integral_le_of_indicator measurableSet_Ioo (hsm.trans_lt ENNReal.ofReal_lt_top) hC0
      hf₂b hε'0.le hsm
  rw [Real.dist_eq] at h1 ⊢
  rw [e1, e2]
  have hCε : 2 * (C * ε') ≤ ε / 2 := by
    rw [hε']
    have : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    calc 2 * (C * (ε / (4 * (C + 1)))) = ε / 2 * (C / (C + 1)) := by field_simp; ring
      _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε / 2 := mul_one _
  calc |∫ t, f₁ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) +
          ∫ t, f₂ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) -
        (∫ t, f₁ t ∂ν' + ∫ t, f₂ t ∂ν')|
      ≤ |∫ t, f₁ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) - ∫ t, f₁ t ∂ν'| +
          |∫ t, f₂ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i)| + |∫ t, f₂ t ∂ν'| := by
        have := abs_add_three (∫ t, f₁ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i) -
          ∫ t, f₁ t ∂ν') (∫ t, f₂ t ∂bdryR γ (x + ofFun (Lf α)) (goodRad i))
          (-∫ t, f₂ t ∂ν')
        rw [abs_neg] at this
        refine le_trans (le_of_eq ?_) this
        congr 1; ring
    _ < ε / 2 + C * ε' + C * ε' := by linarith
    _ ≤ ε := by linarith

end Bdry

/-! ## Uniform smallness near `0` along all offsets, from the annuli -/

/-- `sup_{0 < r ≤ 2^{−n}, r ∈ ℚ} ν_r(x)([−2^{−n}, 2^{−n}])`. -/
def annTo (γ : ℝ) (x : FieldSample) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 < (q : ℝ) ∧ (q : ℝ) ≤ radius n), bdryR γ x q (annI 0 n)

theorem le_annTo (hF : IsRegularWith x F) {n : ℕ} {r : ℝ} (hr : 0 < r) (hrn : r ≤ radius n) :
    bdryR γ x r (annI 0 n) ≤ annTo γ x n := by
  have hq : ∀ j : ℕ, ∃ q : ℚ, r - r / ((j : ℝ) + 2) < q ∧ (q : ℝ) < r := fun j =>
    exists_rat_btwn (by have : 0 < r / ((j : ℝ) + 2) := by positivity
                        linarith)
  choose q hq1 hq2 using hq
  have hqpos : ∀ j, 0 < (q j : ℝ) := by
    intro j
    have : r / ((j : ℝ) + 2) ≤ r / 2 :=
      div_le_div_of_nonneg_left hr.le (by norm_num) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    linarith [hq1 j]
  have hqt : Tendsto (fun j => (q j : ℝ)) atTop (𝓝 r) := by
    have hlow : Tendsto (fun j : ℕ => r - r / ((j : ℝ) + 2)) atTop (𝓝 r) := by
      have : Tendsto (fun j : ℕ => r / ((j : ℝ) + 2)) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul r
        rw [mul_zero] at h
        refine squeeze_zero (fun j => div_nonneg hr.le (by positivity)) (fun j => ?_) h
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left hr.le (by positivity) (by linarith)
      simpa using tendsto_const_nhds.sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun j => (hq1 j).le) (fun j => (hq2 j).le)
  have hdens : ∀ t, Tendsto (fun j => ENNReal.ofReal (bdryDens γ x (q j) t)) atTop
      (𝓝 (ENNReal.ofReal (bdryDens γ x r t))) := by
    intro t
    have ht : ((t : ℂ)) ∈ Hbar := GaussTK.ofReal_mem_Hbar t
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    have hFt : Tendsto (fun j => F ((t : ℂ), (q j : ℝ))) atTop (𝓝 (F ((t : ℂ), r))) :=
      (hF.1 ((t : ℂ), r) ⟨ht, hr⟩).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨tendsto_const_nhds.prodMk_nhds hqt, Eventually.of_forall fun j => ⟨ht, hqpos j⟩⟩)
    have e : ∀ ρ, 0 < ρ → bdryDens γ x ρ t = ρ ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * F ((t : ℂ), ρ)) :=
      fun ρ hρ => by rw [bdryDens, hF.evalReg_fc_of_mem ht hρ]
    rw [e r hr]
    have e' : (fun j => bdryDens γ x (q j) t) =
        fun j => (q j : ℝ) ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * F ((t : ℂ), (q j : ℝ))) :=
      funext fun j => e _ (hqpos j)
    rw [e']
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')).tendsto.comp hqt).mul
      ((Real.continuous_exp.tendsto _).comp (hFt.const_mul _))
  calc bdryR γ x r (annI 0 n) = ∫⁻ t in annI 0 n, ENNReal.ofReal (bdryDens γ x r t) :=
        withDensity_apply _ measurableSet_Icc
    _ = ∫⁻ t in annI 0 n, liminf (fun j => ENNReal.ofReal (bdryDens γ x (q j) t)) atTop := by
        congr 1; funext t; exact ((hdens t).liminf_eq).symm
    _ ≤ liminf (fun j => ∫⁻ t in annI 0 n, ENNReal.ofReal (bdryDens γ x (q j) t)) atTop :=
        lintegral_liminf_le fun j => (continuous_bdryDens γ hF (hqpos j)).measurable.ennreal_ofReal
    _ ≤ ⨆ j, ∫⁻ t in annI 0 n, ENNReal.ofReal (bdryDens γ x (q j) t) :=
        le_trans Filter.liminf_le_limsup Filter.limsup_le_iSup
    _ ≤ annTo γ x n := iSup_le fun j => by
        refine le_trans (le_of_eq (withDensity_apply (μ := volume)
          (fun t => ENNReal.ofReal (bdryDens γ x (q j) t))
          (measurableSet_Icc : MeasurableSet (annI 0 n))).symm) ?_
        exact le_iSup₂ (f := fun (q' : ℚ) (_ : 0 < (q' : ℝ) ∧ (q' : ℝ) ≤ radius n) =>
          bdryR γ x q' (annI 0 n)) (q j) ⟨hqpos j, (hq2 j).le.trans hrn⟩

theorem weight_le_sum (hγ : 0 < γ) (α : ℝ) {m k : ℕ} {r : ℝ} (hr : 0 < r) (hrm : r ≤ radius m)
    (hk1 : radius (k + 1) < r) (hkr : r ≤ radius k) {t : ℝ} (ht : |t| < radius m) :
    ENNReal.ofReal (max r |t| ^ (-(α * γ / 2))) ≤
      ∑ n ∈ Finset.Ico m (k + 1), annW γ α n * (annI 0 n).indicator 1 t := by
  classical
  have hmk : m ≤ k := by
    by_contra h
    push_neg at h
    have := AreaExist.aradius_anti (show k + 1 ≤ m by omega)
    linarith
  have hm1 : radius m ≤ 1 := BdryExist.radius_le_one m
  by_cases hd : |t| ≤ radius k
  · refine le_trans ?_ (Finset.single_le_sum (f := fun i => annW γ α i * (annI 0 i).indicator 1 t)
      (fun i _ => zero_le) (Finset.mem_Ico.2 ⟨hmk, Nat.lt_succ_self k⟩))
    rw [indicator_of_mem (mem_annI (by simpa using hd)), Pi.one_apply, mul_one]
    unfold annW
    refine ENNReal.ofReal_le_ofReal (rpow_neg_le_of_le hγ (radius_pos _)
      (hk1.le.trans (le_max_left _ _)) ?_)
    exact max_le (hrm.trans hm1) (ht.le.trans hm1)
  · push_neg at hd
    have hex : ∃ n, radius (n + 1) ≤ |t| := ⟨k, (AreaExist.aradius_anti (Nat.le_succ k)).trans hd.le⟩
    set n := Nat.find hex with hn
    have hn1 : radius (n + 1) ≤ |t| := Nat.find_spec hex
    have hnk : n ≤ k := Nat.find_min' hex ((AreaExist.aradius_anti (Nat.le_succ k)).trans hd.le)
    have hmn : m ≤ n := by
      by_contra h
      push_neg at h
      have := AreaExist.aradius_anti (show n + 1 ≤ m by omega)
      linarith
    have hdn : |t| ≤ radius n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, radius_zero']; linarith
      · have := Nat.find_min hex (show n - 1 < n by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact (not_le.1 this).le
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => annW γ α i * (annI 0 i).indicator 1 t)
      (fun i _ => zero_le) (Finset.mem_Ico.2 ⟨hmn, Nat.lt_succ_of_le hnk⟩))
    rw [indicator_of_mem (mem_annI (by simpa using hdn)), Pi.one_apply, mul_one]
    unfold annW
    rw [max_eq_right (hkr.trans hd.le)]
    exact ENNReal.ofReal_le_ofReal (rpow_neg_le_of_le hγ (radius_pos _) hn1 (ht.le.trans hm1))

/-- **Uniform smallness near `0` along all offsets.** -/
theorem tight_offsets (hγ : 0 < γ) (hF : IsRegularWith x F) (α : ℝ) {N : ℕ}
    (hsum : ∑' n, annW γ α (n + N) * annTo γ x (n + N) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ i in goodFilter,
      bdryR γ (x + ofFun (Lf α)) (goodRad i) (Ioo (-δ) δ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  set a : ℕ → ℝ≥0∞ := fun n => annW γ α n * annTo γ x n with ha
  set tail : ℕ → ℝ≥0∞ := fun i => ∑' j, a (j + i + N) with htail
  have hF1 : Tendsto tail atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun n => a (n + N)) hsum
    simpa only [htail, add_assoc] using this
  have hF3 : ∀ i k, ∑ n ∈ Finset.Ico (i + N) k, a n ≤ tail i := fun i k => by
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (k - (i + N))))
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha]
    congr 2 <;> omega
  obtain ⟨i0, hi0⟩ := (hF1.eventually (eventually_le_nhds (ENNReal.ofReal_pos.2 hε))).exists
  set m := i0 + N with hm
  refine ⟨radius m, radius_pos m, ?_⟩
  filter_upwards [tendsto_goodRad.eventually (Ioo_mem_nhdsGT (radius_pos m))] with i hi
  obtain ⟨hr0, hrm⟩ := hi
  set r := goodRad i with hr
  have hex : ∃ k, radius (k + 1) < r := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr0 (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, (AreaExist.aradius_anti (Nat.le_succ n)).trans_lt hn⟩
  set k := Nat.find hex with hk
  have hk1 : radius (k + 1) < r := Nat.find_spec hex
  have hkr : r ≤ radius k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, radius_zero']; linarith [BdryExist.radius_le_one m]
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this
      exact not_lt.1 this
  have hdm : Measurable fun t => ENNReal.ofReal (bdryDens γ x r t) :=
    (continuous_bdryDens γ hF hr0).measurable.ennreal_ofReal
  have hmeas : ∀ n, MeasurableSet (annI 0 n) := fun n => measurableSet_Icc
  calc bdryR γ (x + ofFun (Lf α)) r (Ioo (-radius m) (radius m))
      = ∫⁻ t in Ioo (-radius m) (radius m),
          ENNReal.ofReal (max r |t| ^ (-(α * γ / 2))) * ENNReal.ofReal (bdryDens γ x r t) := by
        rw [bdryR, withDensity_apply _ measurableSet_Ioo]
        congr 1; funext t
        rw [bdryDens_add_Lf hF γ α hr0 t,
          ENNReal.ofReal_mul (Real.rpow_nonneg (le_max_of_le_left hr0.le) _)]
    _ ≤ ∫⁻ t in Ioo (-radius m) (radius m),
          (∑ n ∈ Finset.Ico m (k + 1), annW γ α n * (annI 0 n).indicator 1 t) *
            ENNReal.ofReal (bdryDens γ x r t) := by
        refine setLIntegral_mono ((Finset.measurable_sum _ fun n _ =>
          (measurable_one.indicator (hmeas n)).const_mul _).mul hdm) fun t ht => ?_
        gcongr
        exact (weight_le_sum hγ α hr0 hrm.le hk1 hkr
          (abs_lt.2 ⟨by linarith [ht.1], ht.2⟩))
    _ ≤ ∫⁻ t, (∑ n ∈ Finset.Ico m (k + 1), annW γ α n * (annI 0 n).indicator 1 t) *
            ENNReal.ofReal (bdryDens γ x r t) := setLIntegral_le_lintegral _ _
    _ = ∑ n ∈ Finset.Ico m (k + 1), annW γ α n * bdryR γ x r (annI 0 n) := by
        simp_rw [Finset.sum_mul]
        rw [lintegral_finsetSum]
        swap
        · intro n _
          exact ((measurable_one.indicator (hmeas n)).const_mul _).mul hdm
        refine Finset.sum_congr rfl fun n _ => ?_
        simp_rw [mul_assoc]
        rw [lintegral_const_mul]
        swap
        · exact (measurable_one.indicator (hmeas n)).mul hdm
        congr 1
        rw [bdryR, withDensity_apply _ (hmeas n), ← lintegral_indicator (hmeas n)]
        congr 1; funext t
        by_cases ht : t ∈ annI 0 n
        · simp [ht]
        · simp [ht]
    _ ≤ ∑ n ∈ Finset.Ico m (k + 1), a n := Finset.sum_le_sum fun n hn => by
        simp only [ha]
        gcongr
        exact le_annTo hF hr0 (hkr.trans (AreaExist.aradius_anti
          (Nat.lt_succ_iff.1 (Finset.mem_Ico.1 hn).2)))
    _ ≤ tail i0 := hF3 i0 (k + 1)
    _ ≤ ENNReal.ofReal ε := hi0

end LogSingGood
end QuantumZipper
