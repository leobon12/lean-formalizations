import QuantumZipper.Proofs.LQG.WedgeInfTotalFree
import QuantumZipper.Proofs.LQG.WedgeInfGrowth

/-!
# WEDGE-INF-2: the quantum wedge has infinite total area

* `ae_lateral_weighted_eq_top`: for the free field `X` on `ℍ` modulo constants, `γ ∈ (0,2)` and
  `a < Q = Qc γ`, almost surely
  `∫_{‖z‖ ≥ 1, z ∈ ℍ} ‖z‖^{−γa} e^{−γ h_{‖z‖}(0)} dμ_X(z) = ∞`.
* `wedgeInfiniteTotal`: `WedgeCan4.WedgeInfiniteTotal γ α` for `γ ∈ (0,2)`, `α < Q`.

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6, p. 21, which
asserts without proof that the wedge measure has "an infinite amount [of mass] in each
neighborhood of ∞". The proof is an own argument (see `WedgeInfTotalFree.lean` for the free-field
part): exact dyadic scaling of the lateral mass (law invariance of the full normalized
coordinates), positivity, and `P(total < K) ≤ P(c_n Φ(X) < K) → 0` with `c_n → ∞`. The reduction
uses the density rule `WedgeCan4.ae_qAreaMeasure_wedgeField_eq` and the linear growth
`WedgeInf.ae_wedgeProcess_neg_ge` of the wedge radial process at `−∞`: on `‖z‖ ≥ 1`,
`e^{γ g(z)} ≥ e^{−γC} ‖z‖^{−γ(α+ε)} e^{−γ h_{‖z‖}(0)}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeInf

open Factorization CoordsFull InfMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem tendsto_cst {γ a : ℝ} (hγ : 0 < γ) (ha : a < Qc γ) : Tendsto (cst γ a) atTop atTop := by
  have hc : 0 < γ * (Qc γ - a) * Real.log 2 := by
    have := Real.log_pos one_lt_two
    have : 0 < Qc γ - a := by linarith
    positivity
  have ht : Tendsto (fun n : ℕ => γ * (Qc γ - a) * Real.log 2 * n + -(γ * a * Real.log 2))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  exact (Real.tendsto_exp_atTop.comp ht).congr fun n => (cst_eq γ a n).symm

theorem monotone_cst {γ a : ℝ} (hγ : 0 < γ) (ha : a < Qc γ) : Monotone (cst γ a) := by
  intro n m h
  rw [cst_eq, cst_eq]
  refine Real.exp_le_exp.2 ?_
  have hc : 0 < γ * (Qc γ - a) * Real.log 2 := by
    have := Real.log_pos one_lt_two
    have : 0 < Qc γ - a := by linarith
    positivity
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  nlinarith

theorem ae_latW_eq_top_of_nonneg [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < Qc γ) :
    ∀ᵐ ω ∂P, latW γ a (X ω) = ⊤ := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hXm : Measurable X := WedgeTK.measurable_X_pi hX
  have hgood := AreaOffsets.ae_isLQGGood hX (P := P) hγ hγ2
  have hN0m : Measurable fun ω => normCF (X ω) :=
    measurable_pi_iff.2 fun i => (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hNm : ∀ n : ℕ, Measurable fun ω => normCF (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)) := by
    intro n
    have : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    refine measurable_pi_iff.2 fun i => ?_
    exact ((measurable_coordChange_apply (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ)
      (fcF i)).comp hXm).sub ((measurable_coordChange_apply
        (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ) fc01).comp hXm)
  set V : Ω → ℝ≥0∞ := fun ω => PsiF γ (normCF (X ω)) with hV
  have hVm : Measurable V := (measurable_PsiF γ).comp hN0m
  have hVpos : ∀ᵐ ω ∂P, 0 < V ω := by
    filter_upwards [hgood, hG.ae_good, PositivityArea.ae_forall_pos_qAreaMeasure hX hγ hγ2]
      with ω hω hr hp
    show 0 < PsiF γ (normCF (X ω))
    rw [PsiF_normCF hω (GoodRad.radLim hr)]
    unfold Phi
    rw [if_pos hω]
    have hne : R0.Nonempty := by
      refine ⟨((3 / 2 : ℝ) : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
      · show 1 < ‖((3 / 2 : ℝ) : ℂ) * Complex.I‖
        rw [norm_mul, Complex.norm_I, Complex.norm_real]; norm_num
      · show ‖((3 / 2 : ℝ) : ℂ) * Complex.I‖ < 2
        rw [norm_mul, Complex.norm_I, Complex.norm_real]; norm_num
      · show 0 < (((3 / 2 : ℝ) : ℂ) * Complex.I).im
        simp
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (hp R0 isOpen_R0 inter_subset_right hne).ne'
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂P, ENNReal.ofReal (cst γ a n) *
      PsiF γ (normCF (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n))) ≤ latW γ a (X ω) := by
    intro n
    filter_upwards [hgood, hG.ae_good] with ω hω hr
    have hb : (0 : ℝ) < 2 ^ n := by positivity
    rw [PsiF_normCF (hω.rescale hγ hb) (radLim_rescale hr.1 (Qc γ) hb)]
    exact latW_ge hγ ha0 hω hr n
  have hlaw : ∀ n : ℕ, ∀ S : Set (ℕ → ℝ), MeasurableSet S →
      P ((fun ω => normCF (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n))) ⁻¹' S) =
        P ((fun ω => normCF (X ω)) ⁻¹' S) := by
    intro n S hS
    rw [← Measure.map_apply (hNm n) hS, ← Measure.map_apply hN0m hS,
      map_normCF_rescale hX hG (Qc γ) (by positivity)]
  have hK : ∀ K : ℕ, ∀ᵐ ω ∂P, (K : ℝ≥0∞) ≤ latW γ a (X ω) := by
    intro K
    set E : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (cst γ a n) * V ω < K} with hE
    have hEm : ∀ n, MeasurableSet (E n) := fun n =>
      measurableSet_lt (measurable_const.mul hVm) measurable_const
    have hEanti : Antitone E := fun n m hnm ω hω =>
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (monotone_cst hγ ha hnm)) (by positivity)) hω
    have hEnull : P (⋂ n, E n) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hVpos)
      intro ω hω
      simp only [mem_iInter, hE, mem_setOf_eq] at hω
      show ¬ 0 < V ω
      intro hpos
      by_cases htop : V ω = ⊤
      · have h0 := hω 0
        rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (cst_pos γ a 0)).ne'] at h0
        exact absurd h0 (not_lt.2 le_top)
      · have hv : 0 < (V ω).toReal := ENNReal.toReal_pos hpos.ne' htop
        obtain ⟨n, hn'⟩ := ((tendsto_cst hγ ha).eventually_ge_atTop
          ((K : ℝ) / (V ω).toReal)).exists
        have h1 := hω n
        rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (cst_pos γ a n).le] at h1
        have h2 : (K : ℝ) ≤ cst γ a n * (V ω).toReal := by rwa [div_le_iff₀ hv] at hn'
        have h3 : (K : ℝ≥0∞) ≤ ENNReal.ofReal (cst γ a n * (V ω).toReal) := by
          rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal h2
        exact absurd h1 (not_lt.2 h3)
    have htend := tendsto_measure_iInter_atTop (fun n => (hEm n).nullMeasurableSet) hEanti
      ⟨0, measure_ne_top P _⟩
    rw [hEnull] at htend
    have hle : ∀ n, P {ω | ¬ (K : ℝ≥0∞) ≤ latW γ a (X ω)} ≤ P (E n) := by
      intro n
      have hS : MeasurableSet {c : ℕ → ℝ | ENNReal.ofReal (cst γ a n) * PsiF γ c < K} :=
        measurableSet_lt (measurable_const.mul (measurable_PsiF γ)) measurable_const
      rw [show E n = (fun ω => normCF (X ω)) ⁻¹'
        {c : ℕ → ℝ | ENNReal.ofReal (cst γ a n) * PsiF γ c < K} from rfl, ← hlaw n _ hS]
      refine measure_mono_ae ?_
      filter_upwards [hbound n] with ω hω hlt
      exact lt_of_le_of_lt hω (not_le.1 hlt)
    rw [ae_iff]
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto' htend hle)
  filter_upwards [ae_all_iff.2 hK] with ω hω
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  calc (r : ℝ≥0∞) ≤ ((⌈r⌉₊ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 (Nat.le_ceil r)
    _ = (⌈r⌉₊ : ℝ≥0∞) := ENNReal.coe_natCast _
    _ ≤ _ := hω _

/-- **Infinite weighted lateral area of the free field near `∞`.** -/
theorem ae_lateral_weighted_eq_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {a : ℝ} (ha : a < Qc γ) :
    ∀ᵐ ω ∂P, ∫⁻ z in {z : ℂ | 1 ≤ ‖z‖} ∩ H, ENNReal.ofReal (‖z‖ ^ (-(γ * a)) *
      Real.exp (-(γ * radAvgReg (X ω) ‖z‖))) ∂qAreaMeasure γ (X ω) = ⊤ := by
  have hQ : 0 < Qc γ := by unfold Qc; positivity
  filter_upwards [ae_latW_eq_top_of_nonneg hX hγ hγ2 (le_max_right a 0)
    (max_lt ha hQ)] with ω hω
  exact top_unique (hω.symm.le.trans (latW_anti hγ.le (le_max_left a 0) (X ω)))

/-- **WEDGE-INF: the quantum wedge has infinite total area** (Sheffield §1.6, p. 21). -/
theorem wedgeInfiniteTotal {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    WedgeCan4.WedgeInfiniteTotal γ α := by
  intro Ω' _ P' X A hP hX hA _
  set ε : ℝ := (Qc γ - α) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  filter_upwards [WedgeCan4.ae_qAreaMeasure_wedgeField_eq hX hγ hγ2 (Q := Qc γ)
      (WedgeCan4.ae_continuous_wedgeProcess hA), ae_wedgeProcess_neg_ge hA,
      ae_lateral_weighted_eq_top hX hγ hγ2 (a := α + ε) (by rw [hε_def]; linarith)]
    with ω hW hgrow hlat
  obtain ⟨C, hC⟩ := hgrow ε hε
  rw [hW.1, withDensity_apply _ isOpen_H.measurableSet]
  set S : Set ℂ := {z : ℂ | 1 ≤ ‖z‖} ∩ H with hS
  have hSm : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_norm).inter isOpen_H.measurableSet
  have hc : ENNReal.ofReal (Real.exp (-(γ * C))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(γ * C))) * ∫⁻ z in S,
        ENNReal.ofReal (‖z‖ ^ (-(γ * (α + ε))) * Real.exp (-(γ * radAvgReg (X ω) ‖z‖)))
          ∂qAreaMeasure γ (X ω) := by rw [hlat, ENNReal.mul_top hc]
    _ = ∫⁻ z in S, ENNReal.ofReal (Real.exp (-(γ * C))) *
        ENNReal.ofReal (‖z‖ ^ (-(γ * (α + ε))) * Real.exp (-(γ * radAvgReg (X ω) ‖z‖)))
          ∂qAreaMeasure γ (X ω) := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (Real.exp (γ * WedgeCan.wedgeProfile (X ω)
          (fun t => A t ω) (Qc γ) z)) ∂qAreaMeasure γ (X ω) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hSm] with z hz
        have hz1 : 1 ≤ ‖z‖ := hz.1
        have hzpos : 0 < ‖z‖ := by linarith
        set L := Real.log ‖z‖ with hL
        have hL0 : 0 ≤ L := Real.log_nonneg hz1
        have hAz := hC L hL0
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.rpow_def_of_pos hzpos, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        unfold WedgeCan.wedgeProfile
        rw [← hL]
        have : (Qc γ - α - ε) * L - C ≤ A (-L) ω := hAz
        have hQ : Qc γ = α + 2 * ε := by rw [hε_def]; ring
        rw [hQ] at this ⊢
        nlinarith
    _ ≤ _ := lintegral_mono_set inter_subset_right

end WedgeInf

end QuantumZipper
