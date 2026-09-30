import QuantumZipper.Proofs.LQG.Positivity
import QuantumZipper.Proofs.LQG.AreaExistenceAS

/-!
# M4-P2: positivity of the area LQG measure

Blueprint `M4_BLUEPRINT.md`, node M4-P2 (area part).

For the free field `X` and `γ ∈ (0,2)`, almost surely `qAreaMeasure γ (X ω)` charges every
nonempty open subset of `ℍ` (`ae_forall_pos_qAreaMeasure`).

Same template as `Positivity.lean`: for an open box `B = (a₁,b₁) × (a₂,b₂)` with `a₂ > 0` and
`Z = aZ X R`, the event `{μ_Z(B) = 0}` is read on the dyadic circle coordinates through a tent
`g` supported on `B`; it is invariant under continuous shifts (on regular samples the densities
change by `exp(γ ∫ φ dfc)`, bounded uniformly in `k` on `supp g`); P1 gives probability `0`
or `1`; and `1` is excluded because `E ∫ g dμ_k ≥ ∫ g > 0` for large `k` while
`E|∫ g dμ_k − ∫ g dμ_Z| → 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace PositivityArea

open Factorization GaussTK GoodSample AreaExist Positivity

/-! ### Congruence and pathwise comparison -/

theorem areaApprox_congr_pcirc {x x' : FieldSample}
    (h : ∀ i : PIdx, x (pcirc i.1) = x' (pcirc i.1)) (γ : ℝ) :
    areaApprox γ x = areaApprox γ x' := by
  funext k
  unfold areaApprox
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem isOpen_H.measurableSet] with z hz
  rw [avgReg_congr_pcirc h k (H_subset_Hbar hz)]

theorem avgReg_add_ofFun_H {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {φ : ℂ → ℝ} (hφ : Continuous φ) (k : ℕ) {z : ℂ} (hz : z ∈ Hbar) :
    avgReg (x + ofFun φ) k z = avgReg x k z + ∫ v, φ v ∂foldedCircle z (radius k) := by
  rw [(gs_add_ofFun hF hφ.continuousOn).avgReg_eq k hz, hF.avgReg_eq k hz]

theorem abs_smooth_le_H {φ : ℂ → ℝ} {M T : ℝ}
    (hM : ∀ u ∈ CircleFubini.ballH (T + 1), |φ u| ≤ M) (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ T) :
    |∫ v, φ v ∂foldedCircle z (radius k)| ≤ M := by
  have hsupp := CircleFubini.foldedCircle_support (radius_pos k).le (z := z) (R := T + 1)
    (by have := BdryExist.radius_le_one k; linarith)
  have hae : ∀ᵐ u ∂foldedCircle z (radius k), ‖φ u‖ ≤ M :=
    (ae_iff.2 hsupp).mono fun u hu => by rw [Real.norm_eq_abs]; exact hM u hu
  have := MeasureTheory.norm_integral_le_of_norm_le_const hae
  simpa [Real.norm_eq_abs] using this

theorem lintegral_areaApprox_add_ofFun_le {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℂ → ℝ}
    (hg : Measurable g) {T : ℝ} (hgT : ∀ z, g z ≠ 0 → ‖z‖ ≤ T ∧ z ∈ Hbar) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ (x + ofFun φ) k ≤
      C * ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k := by
  obtain ⟨M, hM⟩ :=
    (CircleFubini.isCompact_ballH (T + 1)).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨ENNReal.ofReal (Real.exp (|γ| * M)), ENNReal.ofReal_ne_top, fun k => ?_⟩
  have hm : ∀ y : FieldSample, Measurable fun z : ℂ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg y k z)) := fun y =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((RegClosure.measurable_avgReg_slice y k).const_mul _).exp)
  unfold areaApprox
  rw [lintegral_withDensity_eq_lintegral_mul _ (hm _) hg.ennreal_ofReal,
    lintegral_withDensity_eq_lintegral_mul _ (hm _) hg.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun z => ?_
  simp only [Pi.mul_apply]
  by_cases h0 : g z = 0
  · simp [h0]
  obtain ⟨hzT, hzH⟩ := hgT z h0
  set s := ∫ v, φ v ∂foldedCircle z (radius k) with hs_def
  have hs : |s| ≤ M :=
    abs_smooth_le_H (fun u hu => by simpa [Real.norm_eq_abs] using hM u hu) k hzT
  rw [avgReg_add_ofFun_H hF hφ k hzH, ← hs_def]
  have hle : γ * s ≤ |γ| * M := by
    calc γ * s ≤ |γ * s| := le_abs_self _
      _ = |γ| * |s| := abs_mul _ _
      _ ≤ |γ| * M := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
  set A := avgReg x k z
  have hr : 0 ≤ radius k ^ (γ ^ 2 / 2) := Real.rpow_nonneg (radius_pos k).le _
  have hd : ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * (A + s))) ≤
      ENNReal.ofReal (Real.exp (|γ| * M)) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * A)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    calc radius k ^ (γ ^ 2 / 2) * Real.exp (γ * (A + s))
        = (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * A)) * Real.exp (γ * s) := by
          rw [mul_add, Real.exp_add]; ring
      _ ≤ (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * A)) * Real.exp (|γ| * M) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by positivity)
      _ = Real.exp (|γ| * M) * (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * A)) :=
          mul_comm _ _
  calc ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * (A + s))) *
        ENNReal.ofReal (g z)
      ≤ (ENNReal.ofReal (Real.exp (|γ| * M)) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * A))) *
          ENNReal.ofReal (g z) := by gcongr
    _ = _ := mul_assoc _ _ _

theorem limsup_area_add_ofFun_eq_zero {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℂ → ℝ}
    (hg : Measurable g) {T : ℝ} (hgT : ∀ z, g z ≠ 0 → ‖z‖ ≤ T ∧ z ∈ Hbar)
    (h0 : limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k) atTop = 0) :
    limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ (x + ofFun φ) k) atTop = 0 := by
  obtain ⟨C, hC, hle⟩ := lintegral_areaApprox_add_ofFun_le hF γ hφ hg hgT
  refine le_antisymm ?_ zero_le
  calc limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ (x + ofFun φ) k) atTop
      ≤ limsup (fun k => C * ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k) atTop :=
        limsup_le_limsup (Eventually.of_forall hle)
    _ = C * limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k) atTop :=
        ENNReal.limsup_const_mul_of_ne_top hC
    _ = 0 := by rw [h0, mul_zero]

theorem limsup_area_eq_zero_iff_add_ofFun {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (γ : ℝ) {φ : ℂ → ℝ} (hφ : Continuous φ) {g : ℂ → ℝ}
    (hg : Measurable g) {T : ℝ} (hgT : ∀ z, g z ≠ 0 → ‖z‖ ≤ T ∧ z ∈ Hbar) :
    limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k) atTop = 0 ↔
      limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ (x + ofFun φ) k) atTop = 0 := by
  refine ⟨limsup_area_add_ofFun_eq_zero hF γ hφ hg hgT, fun h => ?_⟩
  have hF' := gs_add_ofFun hF hφ.continuousOn
  have e : x + ofFun φ + ofFun (-φ) = x := by
    funext μ; simp only [Pi.add_apply, Pi.neg_apply, ofFun, integral_neg]; ring
  have := limsup_area_add_ofFun_eq_zero hF' γ hφ.neg hg hgT h
  rwa [e] at this

theorem limsup_lintegral_area_eq_ofReal {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) {γ : ℝ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ x) μ) {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgH : tsupport g ⊆ H) (hg0 : ∀ z, 0 ≤ g z) :
    limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k) atTop =
      ENNReal.ofReal (∫ z, g z ∂μ) := by
  have e : ∀ k, ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ x k =
      ENNReal.ofReal (∫ z, g z ∂areaApprox γ x k) := by
    intro k
    have : IsFiniteMeasureOnCompacts (areaApprox γ x k) := ⟨fun K hK => by
      rw [← areaR_radius γ hF k]
      exact areaR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK⟩
    rw [ofReal_integral_eq_lintegral_ofReal (hg.integrable_of_hasCompactSupport hgc)
      (ae_of_all _ hg0)]
  simp_rw [e]
  exact ((ENNReal.continuous_ofReal.tendsto _).comp (hμ.2.2 g hg hgc hgH)).limsup_eq

/-! ### Boxes and tents -/

/-- Closed box `[a₁,b₁] × [a₂,b₂]`. -/
def cbox (a₁ b₁ a₂ b₂ : ℝ) : Set ℂ := Complex.re ⁻¹' Icc a₁ b₁ ∩ Complex.im ⁻¹' Icc a₂ b₂

/-- Open box `(a₁,b₁) × (a₂,b₂)`. -/
def obox (a₁ b₁ a₂ b₂ : ℝ) : Set ℂ := Complex.re ⁻¹' Ioo a₁ b₁ ∩ Complex.im ⁻¹' Ioo a₂ b₂

/-- Tent on the box, positive exactly on the open box. -/
def tent2 (a₁ b₁ a₂ b₂ : ℝ) (z : ℂ) : ℝ := tent a₁ b₁ z.re * tent a₂ b₂ z.im

section Box

variable {a₁ b₁ a₂ b₂ : ℝ}

theorem continuous_tent2 : Continuous (tent2 a₁ b₁ a₂ b₂) :=
  ((continuous_tent a₁ b₁).comp Complex.continuous_re).mul
    ((continuous_tent a₂ b₂).comp Complex.continuous_im)

theorem tent2_nonneg (z : ℂ) : 0 ≤ tent2 a₁ b₁ a₂ b₂ z :=
  mul_nonneg (tent_nonneg _ _ _) (tent_nonneg _ _ _)

theorem tent2_pos_iff {z : ℂ} : 0 < tent2 a₁ b₁ a₂ b₂ z ↔ z ∈ obox a₁ b₁ a₂ b₂ := by
  unfold tent2 obox
  simp only [mem_inter_iff, mem_preimage, mem_Ioo]
  have h1 := tent_nonneg a₁ b₁ z.re
  have h2 := tent_nonneg a₂ b₂ z.im
  constructor
  · intro h
    refine ⟨tent_pos_iff.1 (lt_of_le_of_ne h1 fun e => ?_),
      tent_pos_iff.1 (lt_of_le_of_ne h2 fun e => ?_)⟩
    · rw [← e, zero_mul] at h; exact lt_irrefl _ h
    · rw [← e, mul_zero] at h; exact lt_irrefl _ h
  · rintro ⟨ha, hb⟩
    exact mul_pos (tent_pos_iff.2 ha) (tent_pos_iff.2 hb)

theorem tent2_ne_zero_iff {z : ℂ} : tent2 a₁ b₁ a₂ b₂ z ≠ 0 ↔ z ∈ obox a₁ b₁ a₂ b₂ := by
  rw [← tent2_pos_iff]
  exact ⟨fun h => lt_of_le_of_ne (tent2_nonneg z) (Ne.symm h), fun h => h.ne'⟩

theorem obox_subset_cbox : obox a₁ b₁ a₂ b₂ ⊆ cbox a₁ b₁ a₂ b₂ := fun z hz =>
  ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩

theorem tent2_eq_zero_of_notMem {z : ℂ} (hz : z ∉ cbox a₁ b₁ a₂ b₂) :
    tent2 a₁ b₁ a₂ b₂ z = 0 := by
  by_contra h
  exact hz (obox_subset_cbox (tent2_ne_zero_iff.1 h))

theorem norm_le_of_mem_cbox {z : ℂ} (hz : z ∈ cbox a₁ b₁ a₂ b₂) :
    ‖z‖ ≤ |a₁| + |b₁| + (|a₂| + |b₂|) := by
  have hre : |z.re| ≤ |a₁| + |b₁| := abs_le.2 ⟨by linarith [hz.1.1, neg_abs_le a₁, abs_nonneg b₁],
    by linarith [hz.1.2, le_abs_self b₁, abs_nonneg a₁]⟩
  have him : |z.im| ≤ |a₂| + |b₂| := abs_le.2 ⟨by linarith [hz.2.1, neg_abs_le a₂, abs_nonneg b₂],
    by linarith [hz.2.2, le_abs_self b₂, abs_nonneg a₂]⟩
  linarith [Complex.norm_le_abs_re_add_abs_im z]

theorem isCompact_cbox : IsCompact (cbox a₁ b₁ a₂ b₂) := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im))
    ((Metric.isBounded_closedBall (x := (0 : ℂ))
      (r := |a₁| + |b₁| + (|a₂| + |b₂|))).subset fun z hz => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_cbox hz

theorem isOpen_obox : IsOpen (obox a₁ b₁ a₂ b₂) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem cbox_subset_H (ha : 0 < a₂) : cbox a₁ b₁ a₂ b₂ ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le ha hz.2.1

theorem hasCompactSupport_tent2 : HasCompactSupport (tent2 a₁ b₁ a₂ b₂) :=
  HasCompactSupport.intro isCompact_cbox fun _ hz => tent2_eq_zero_of_notMem hz

theorem tsupport_tent2_subset : tsupport (tent2 a₁ b₁ a₂ b₂) ⊆ cbox a₁ b₁ a₂ b₂ :=
  closure_minimal (fun z hz => obox_subset_cbox (tent2_ne_zero_iff.1 hz))
    isCompact_cbox.isClosed

theorem ofReal_integral_tent2_eq_zero_iff {μ : Measure ℂ} (hK : μ (cbox a₁ b₁ a₂ b₂) < ⊤) :
    ENNReal.ofReal (∫ z, tent2 a₁ b₁ a₂ b₂ z ∂μ) = 0 ↔ μ (obox a₁ b₁ a₂ b₂) = 0 := by
  have hi : Integrable (tent2 a₁ b₁ a₂ b₂) μ :=
    (continuous_tent2.continuousOn.integrableOn_of_subset_isCompact isCompact_cbox
      isCompact_cbox.measurableSet subset_rfl hK.ne).integrable_of_forall_notMem_eq_zero
      fun _ hz => tent2_eq_zero_of_notMem hz
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ tent2_nonneg),
    lintegral_eq_zero_iff continuous_tent2.measurable.ennreal_ofReal,
    Filter.EventuallyEq, ae_iff]
  have : {z | ¬ENNReal.ofReal (tent2 a₁ b₁ a₂ b₂ z) = (0 : ℂ → ℝ≥0∞) z} = obox a₁ b₁ a₂ b₂ := by
    ext z
    simp only [mem_setOf_eq, Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    exact tent2_pos_iff
  rw [this]

end Box

/-! ### Positivity for one box -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem pY_eq_aZ (R : ℝ) (i : PIdx) (ω : Ω) : pY X R i ω = aZ X R ω (pcirc i.1) :=
  (addConst_fc_eq_fcPairVal (X := X) R _ _ ω).symm

/-- The mean density is at least `1` on the box, for small radii. -/
theorem one_le_aDens_mean {γ R : ℝ} {z : ℂ} {k : ℕ} (hR1 : 1 ≤ R) (hrz : radius k ≤ z.im)
    (hzR : ‖z‖ + 1 ≤ R) :
    1 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (aV R k z * γ ^ 2 / 2) := by
  have hr := radius_pos k
  have hz0 : 0 < z.im := hr.trans_le hrz
  have hcov := fcPairCov_Zself_int (z := z) (R := R) hr hrz (by linarith [BdryExist.radius_le_one k])
  have hV : 2 * Real.log R - Real.log (radius k) - Real.log ‖z - conj z‖ ≤ (aV R k z : ℝ) := by
    simp only [aV]; rw [← hcov]; exact Real.le_coe_toNNReal _
  have hpos : 0 < ‖z - conj z‖ := by linarith [two_im_le_norm_sub_conj z]
  have hle : ‖z - conj z‖ ≤ R ^ 2 := by
    have h1 : ‖z - conj z‖ ≤ ‖z‖ + ‖conj z‖ := norm_sub_le _ _
    rw [Complex.norm_conj] at h1
    nlinarith [norm_nonneg z]
  have hlog : Real.log ‖z - conj z‖ ≤ 2 * Real.log R := by
    have := Real.log_le_log hpos hle
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  apply Real.one_le_exp
  nlinarith [mul_le_mul_of_nonneg_right hV (sq_nonneg γ), mul_nonneg (sub_nonneg.2 hlog)
    (sq_nonneg γ)]

/-- **M4-P2 for one box, normalized field.** -/
theorem ae_pos_qAreaMeasure_aZ [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a₁ b₁ a₂ b₂ : ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂)
    (ha : 0 < a₂) :
    ∀ᵐ ω ∂P, 0 < qAreaMeasure γ (aZ X (|a₁| + |b₁| + (|a₂| + |b₂|) + 1) ω)
      (obox a₁ b₁ a₂ b₂) := by
  set R := |a₁| + |b₁| + (|a₂| + |b₂|) + 1 with hRdef
  set g := tent2 a₁ b₁ a₂ b₂ with hgdef
  set K := cbox a₁ b₁ a₂ b₂ with hKdef
  have hR1 : 1 ≤ R := by
    linarith [abs_nonneg a₁, abs_nonneg b₁, abs_nonneg a₂, abs_nonneg b₂]
  have hR : 0 < R := by linarith
  have hKH : K ⊆ H := cbox_subset_H ha
  have hKR : ∀ z ∈ K, ‖z‖ + 1 ≤ R := fun z hz => by linarith [norm_le_of_mem_cbox hz]
  have hgT : ∀ z, g z ≠ 0 → ‖z‖ ≤ |a₁| + |b₁| + (|a₂| + |b₂|) ∧ z ∈ Hbar := fun z h => by
    have hz := obox_subset_cbox (tent2_ne_zero_iff.1 h)
    exact ⟨norm_le_of_mem_cbox hz, H_subset_Hbar (hKH hz)⟩
  have hgH : tsupport g ⊆ H := tsupport_tent2_subset.trans hKH
  -- the event
  set Φ : (PIdx → ℝ) → ℝ≥0∞ := fun y =>
    limsup (fun k => ∫⁻ z, ENNReal.ofReal (g z) ∂areaApprox γ (recP y) k) atTop with hΦdef
  have hΦ : Measurable Φ := Measurable.limsup fun k =>
    (Measure.measurable_lintegral continuous_tent2.measurable.ennreal_ofReal).comp
      ((measurable_areaApprox γ k).comp measurable_recP)
  set A : Set (PIdx → ℝ) := Φ ⁻¹' {0} with hAdef
  have hA : MeasurableSet A := hΦ (measurableSet_singleton 0)
  set Yv : Ω → PIdx → ℝ := fun ω j => pY X R j ω with hYvdef
  have hYv : Measurable Yv := measurable_pi_iff.2 fun j => measurable_fcPairVal hX _
  have hrec : ∀ ω, areaApprox γ (recP (Yv ω)) = areaApprox γ (aZ X R ω) := fun ω =>
    areaApprox_congr_pcirc (recP_apply (fun i => pY_eq_aZ R i ω)) γ
  have hgood : ∀ᵐ ω ∂P, IsRegularSample (aZ X R ω) ∧
      IsVagueLimitOn H (areaApprox γ (aZ X R ω)) (qAreaMeasure γ (aZ X R ω)) := by
    filter_upwards [RegSample.ae_isRegularSample hX,
      ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω h1 h2
    exact ⟨h1.addConst' _, h2⟩
  have hiff : ∀ᵐ ω ∂P, (Yv ω ∈ A ↔ qAreaMeasure γ (aZ X R ω) (obox a₁ b₁ a₂ b₂) = 0) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨⟨F, hF⟩, hμ⟩ := hω
    show Φ (Yv ω) = 0 ↔ _
    rw [hΦdef]
    simp only [hrec ω]
    rw [limsup_lintegral_area_eq_ofReal hF hμ continuous_tent2 hasCompactSupport_tent2 hgH
      tent2_nonneg, ofReal_integral_tent2_eq_zero_iff (hμ.2.1 K isCompact_cbox hKH)]
  -- invariance under the rational covariance shifts
  have hinv : ∀ (i : PIdx) (q : ℚ), (fun y : PIdx → ℝ ↦ y + (q : ℝ) • fun j ↦
      CameronMartin.covK (pY X R) P j i) ⁻¹' A =ᵐ[P.map fun ω j ↦ pY X R j ω] A := by
    intro i q
    set s := fun y : PIdx → ℝ ↦ y + (q : ℝ) • fun j ↦ CameronMartin.covK (pY X R) P j i
      with hsdef
    have hs : Measurable s := ZeroOneCM.zo_measurable_add _
    have hpt : ∀ ω, IsRegularSample (aZ X R ω) → (Yv ω ∈ s ⁻¹' A ↔ Yv ω ∈ A) := by
      rintro ω ⟨F, hF⟩
      have hφ : Continuous fun u => (q : ℝ) * psiP R i u :=
        continuous_const.mul (continuous_psiP hR i)
      have hsh : areaApprox γ (recP (s (Yv ω))) =
          areaApprox γ (aZ X R ω + ofFun fun u => (q : ℝ) * psiP R i u) := by
        refine areaApprox_congr_pcirc (recP_apply fun j => ?_) γ
        simp only [hsdef, hYvdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofFun]
        rw [covK_pY hX hR j i, pY_eq_aZ, integral_const_mul]
      show Φ (s (Yv ω)) = 0 ↔ Φ (Yv ω) = 0
      rw [hΦdef]
      simp only [hsh, hrec ω]
      exact (limsup_area_eq_zero_iff_add_ofFun hF γ hφ continuous_tent2.measurable hgT).symm
    have hnull : P {ω | ¬ IsRegularSample (aZ X R ω)} = 0 :=
      ae_iff.1 (hgood.mono fun ω h => h.1)
    rw [ae_eq_set]
    constructor
    · rw [Measure.map_apply hYv ((hs hA).diff hA)]
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro hreg
      exact hω.2 ((hpt ω hreg).1 hω.1)
    · rw [Measure.map_apply hYv (hA.diff (hs hA))]
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro hreg
      exact hω.2 ((hpt ω hreg).2 hω.1)
  have h01 := ZeroOneCM.measure_preimage_eq_zero_or_one_of_ratShift
    (isGaussianProcess_pY hX hR) (fun j => measurable_fcPairVal hX _)
    (fun j => integral_fcPairVal hX (pidx_good hR j)) hA hinv
  rcases h01 with h0 | h1
  · have hn : ∀ᵐ ω ∂P, ω ∉ Yv ⁻¹' A := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [hn, hiff] with ω h hi
    exact pos_iff_ne_zero.2 fun h' => h (hi.2 h')
  · exfalso
    have hae : ∀ᵐ ω ∂P, ω ∈ Yv ⁻¹' A := mem_ae_iff.2 ((prob_compl_eq_zero_iff (hYv hA)).2 h1)
    have hz : ∀ᵐ ω ∂P, ∫ z, g z ∂qAreaMeasure γ (aZ X R ω) = 0 := by
      filter_upwards [hae, hiff] with ω h hi
      have hμ0 := hi.1 h
      refine integral_eq_zero_of_ae ?_
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun z hz => ?_) hμ0
      exact tent2_ne_zero_iff.1 hz
    -- L¹ rate to the limit, and the limit vanishes
    have hgtest : VagueH.IsTestH g := ⟨continuous_tent2, hasCompactSupport_tent2, hgH⟩
    obtain ⟨C, -, k₀, hC⟩ := areaApprox_L1_rate_limit hX hγ hγ2 hgtest
      (fun z hz => hKR z (tsupport_tent2_subset hz))
    -- the first-moment lower bound
    obtain ⟨d, hd0, hd1, hdK⟩ := exists_im_lower_bound isCompact_cbox hKH
    obtain ⟨k₁, hk₁⟩ : ∃ k₁ : ℕ, radius k₁ ≤ d := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd0 (by norm_num : (2 : ℝ)⁻¹ < 1)
      exact ⟨n, hn.le⟩
    have hKm : MeasurableSet K := isCompact_cbox.measurableSet
    have hKf : volume K < ∞ := isCompact_cbox.measure_lt_top
    obtain ⟨M, hM⟩ := continuous_tent2.bounded_above_of_compact_support
      (hasCompactSupport_tent2 (a₁ := a₁) (b₁ := b₁) (a₂ := a₂) (b₂ := b₂))
    have hM' : ∀ z, |g z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
    have hlow : ∀ k : ℕ, radius k ≤ d → ∫ z in K, g z ≤
        ∫ ω, ∫ z, g z ∂areaApprox γ (aZ X R ω) k ∂P := by
      intro k hk
      simp_rw [integral_areaApprox_aZ (X := X) (f := g) γ R k hKH
        (fun z hz => tent2_eq_zero_of_notMem hz)]
      have hint := integrable_fDensA hX hKm hKf hd1 hKR hdK γ continuous_tent2.measurable hM' hk
      rw [integral_integral_swap (f := fun ω z => g z * aDens γ X R k z ω) hint]
      refine setIntegral_mono_on
        (continuous_tent2.continuousOn.integrableOn_compact isCompact_cbox)
        hint.integral_prod_right hKm fun z hzK => ?_
      have hmean : ∫ ω, aDens γ X R k z ω ∂P =
          radius k ^ (γ ^ 2 / 2) * Real.exp (aV R k z * γ ^ 2 / 2) := by
        simp only [aDens]
        rw [integral_const_mul, integral_exp_aU hX hd1 hKR hdK hk hzK]
      rw [integral_const_mul, hmean]
      calc g z = g z * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
            (one_le_aDens_mean hR1 (hk.trans (hdK z hzK)) (hKR z hzK)) (tent2_nonneg z)
    have hsupp : Function.support g = obox a₁ b₁ a₂ b₂ := by
      ext z; exact tent2_ne_zero_iff
    have hpos : 0 < ∫ z in K, g z := by
      rw [integral_pos_iff_support_of_nonneg tent2_nonneg
        (continuous_tent2.continuousOn.integrableOn_compact isCompact_cbox), hsupp,
        Measure.restrict_apply isOpen_obox.measurableSet,
        Set.inter_eq_left.2 obox_subset_cbox]
      refine isOpen_obox.measure_pos volume ⟨⟨(a₁ + b₁) / 2, (a₂ + b₂) / 2⟩, ?_, ?_⟩
      · show (a₁ + b₁) / 2 ∈ Ioo a₁ b₁; constructor <;> linarith
      · show (a₂ + b₂) / 2 ∈ Ioo a₂ b₂; constructor <;> linarith
    -- the expectations are bounded below but tend to zero
    have hsmall : Tendsto (fun k : ℕ => C * Real.exp (-areaRate γ * (k * Real.log 2))) atTop
        (𝓝 0) := by
      have hq1 : Real.exp (-areaRate γ * Real.log 2) < 1 := by
        rw [← Real.exp_zero]
        have := areaRate_pos hγ hγ2
        have := Real.log_pos one_lt_two
        exact Real.exp_lt_exp.2 (by nlinarith)
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le hq1).const_mul C
      rw [mul_zero] at this
      refine this.congr fun k => ?_
      rw [← Real.exp_nat_mul]; congr 2; ring
    have hev : ∀ᶠ k : ℕ in atTop, ∫ z in K, g z ≤
        C * Real.exp (-areaRate γ * (k * Real.log 2)) := by
      filter_upwards [eventually_ge_atTop (max k₀ k₁)] with k hk
      have hk0 : k₀ ≤ k := (le_max_left _ _).trans hk
      have hk1 : radius k ≤ d := (aradius_anti ((le_max_right _ _).trans hk)).trans hk₁
      calc ∫ z in K, g z ≤ ∫ ω, ∫ z, g z ∂areaApprox γ (aZ X R ω) k ∂P := hlow k hk1
        _ ≤ |∫ ω, ∫ z, g z ∂areaApprox γ (aZ X R ω) k ∂P| := le_abs_self _
        _ ≤ ∫ ω, |∫ z, g z ∂areaApprox γ (aZ X R ω) k| ∂P := abs_integral_le_integral_abs
        _ = ∫ ω, |∫ z, g z ∂areaApprox γ (aZ X R ω) k -
              ∫ z, g z ∂qAreaMeasure γ (aZ X R ω)| ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hz] with ω hω
            rw [hω, sub_zero]
        _ ≤ _ := hC k hk0
    have := ge_of_tendsto hsmall hev
    linarith

/-- A.s. `μ_Z = e^{-γ X(fc(0,R))} μ_X`. -/
theorem ae_qAreaMeasure_aZ_eq_smul [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, qAreaMeasure γ (aZ X R ω) =
      ENNReal.ofReal (Real.exp (-(γ * X ω (foldedCircle 0 R)))) • qAreaMeasure γ (X ω) := by
  filter_upwards [ae_isVagueLimitOn_qAreaMeasure hX hγ hγ2,
    ae_areaApprox_aZ_eq (P := P) hX γ R] with ω hμX hsc
  obtain ⟨h0, hK, ht⟩ := hμX
  set c := ENNReal.ofReal (Real.exp (-(γ * X ω (foldedCircle 0 R)))) with hc
  have hμ : IsVagueLimitOn H (areaApprox γ (aZ X R ω)) (c • qAreaMeasure γ (X ω)) := by
    refine ⟨by rw [Measure.smul_apply, h0, smul_zero], fun K hKc hKH => ?_,
      fun f hf hfc hfH => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hK K hKc hKH)
    · simp_rw [hsc, integral_smul_measure]
      exact (ht f hf hfc hfH).const_smul _
  exact qAreaMeasure_eq hμ

/-- **M4-P2 (area), rational boxes.** -/
theorem ae_forall_pos_qAreaMeasure_obox [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ a₁ b₁ a₂ b₂ : ℚ, (a₁ : ℝ) < b₁ → (a₂ : ℝ) < b₂ → (0 : ℝ) < a₂ →
      0 < qAreaMeasure γ (X ω) (obox a₁ b₁ a₂ b₂) := by
  refine ae_all_iff.2 fun a₁ => ae_all_iff.2 fun b₁ => ae_all_iff.2 fun a₂ =>
    ae_all_iff.2 fun b₂ => ?_
  by_cases h : (a₁ : ℝ) < b₁ ∧ (a₂ : ℝ) < b₂ ∧ (0 : ℝ) < a₂
  · obtain ⟨h₁, h₂, ha⟩ := h
    filter_upwards [ae_pos_qAreaMeasure_aZ hX hγ hγ2 h₁ h₂ ha,
      ae_qAreaMeasure_aZ_eq_smul hX hγ hγ2
        (|(a₁ : ℝ)| + |(b₁ : ℝ)| + (|(a₂ : ℝ)| + |(b₂ : ℝ)|) + 1)] with ω hpos heq _ _ _
    rw [heq, Measure.smul_apply, smul_eq_mul] at hpos
    exact pos_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  · exact Eventually.of_forall fun ω h₁ h₂ ha => absurd ⟨h₁, h₂, ha⟩ h

/-- **M4-P2 (area).** For the free field and `γ ∈ (0,2)`, almost surely the area LQG measure
charges every nonempty open subset of `ℍ`. -/
theorem ae_forall_pos_qAreaMeasure [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ (X ω) V := by
  filter_upwards [ae_forall_pos_qAreaMeasure_obox hX hγ hγ2] with ω h V hV hVH hne
  obtain ⟨z, hz⟩ := hne
  have him : 0 < z.im := hVH hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV z hz
  set δ := min (ε / 2) (z.im / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδi : δ ≤ z.im / 2 := min_le_right _ _
  obtain ⟨a₁, ha₁, ha₁'⟩ := exists_rat_btwn (show z.re - δ < z.re by linarith)
  obtain ⟨b₁, hb₁, hb₁'⟩ := exists_rat_btwn (show z.re < z.re + δ by linarith)
  obtain ⟨a₂, ha₂, ha₂'⟩ := exists_rat_btwn (show z.im - δ < z.im by linarith)
  obtain ⟨b₂, hb₂, hb₂'⟩ := exists_rat_btwn (show z.im < z.im + δ by linarith)
  have hsub : obox a₁ b₁ a₂ b₂ ⊆ V := by
    intro w hw
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : |(w - z).re| < δ := by
      rw [Complex.sub_re, abs_lt]; constructor <;> linarith [hw.1.1, hw.1.2]
    have h2 : |(w - z).im| < δ := by
      rw [Complex.sub_im, abs_lt]; constructor <;> linarith [hw.2.1, hw.2.2]
    linarith [Complex.norm_le_abs_re_add_abs_im (w - z)]
  exact (h a₁ b₁ a₂ b₂ (by linarith) (by linarith) (by linarith)).trans_le (measure_mono hsub)

end Main

end PositivityArea
end QuantumZipper
