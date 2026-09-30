import QuantumZipper.Proofs.GFF.Existence

/-!
# DOM-a by annulus features (D34), nodes AN2/AN3: test vectors for the free field

The free Hilbert space is `HkE = L²(hkM)`, `hkM = dt|_{(0,∞)} ⊗ γ`, and `v̂_ρ` is the heat-kernel
feature `q ↦ (2t)^{-1/2} (hkA ρ q − ρ(ℂ) hkA ρ₀ q)` (`GFFExist.freeVec`). This file supplies a dense
set of test vectors against which the pairing with any free vector is an integral of a *bounded
continuous function* against the measure:

* `anTest`: the vectors of `L²(hkM)` vanishing outside a slab `[1/(n+1), n+1] × ℂ`;
  `anTest_dense`: their span is dense (its orthogonal complement is `0`).
* `anPhi g x = ∫ (2t)^{-1/2} g(q) h_x(q) dhkM(q)` is bounded and continuous (`continuous_anPhi`,
  `abs_anPhi_le`), and `inner_freeVec_anTest`:
  `⟪v̂_ρ, g⟫ = ∫ anPhi g dρ − ρ(ℂ) ∫ anPhi g dρ₀`.

This plays the role of the test functions `∇f` of the mixed proof (`K3.pair_rieszVec`,
`MixedM5Rep.lean`). Own elementary argument (Fubini on `hkM ⊗ ρ`; cost rule).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open GFFExist LQGDimension.Coupling LQGDimension.HeatKernel

/-- The slab `[1/(n+1), n+1] × ℂ`. -/
def anSlab (n : ℕ) : Set (ℝ × ℂ) := Icc ((n : ℝ) + 1)⁻¹ ((n : ℝ) + 1) ×ˢ univ

theorem measurableSet_anSlab (n : ℕ) : MeasurableSet (anSlab n) :=
  measurableSet_Icc.prod MeasurableSet.univ

theorem hkM_anSlab_lt_top (n : ℕ) : hkM (anSlab n) < ⊤ := by
  rw [anSlab, hkM, Measure.prod_prod, measure_univ, mul_one]
  exact (Measure.restrict_apply_le _ _).trans_lt measure_Icc_lt_top

/-- The test vectors: `L²(hkM)` vectors vanishing outside a slab. -/
def anTest : Set HkE := {g | ∃ n : ℕ, ∀ᵐ q ∂hkM, q ∉ anSlab n → g q = 0}

theorem hkM_ae_pos : ∀ᵐ q ∂hkM, 0 < q.1 := by
  rw [ae_iff]
  have e : {q : ℝ × ℂ | ¬ 0 < q.1} = Iic 0 ×ˢ univ := by ext q; simp
  rw [e, hkM, Measure.prod_prod, Measure.restrict_apply measurableSet_Iic,
    show Iic (0 : ℝ) ∩ Ioi 0 = ∅ from
      Set.eq_empty_of_forall_notMem fun x hx => (not_lt.2 (mem_Iic.1 hx.1)) (mem_Ioi.1 hx.2),
    measure_empty, zero_mul]

theorem exists_mem_anSlab {q : ℝ × ℂ} (hq : 0 < q.1) : ∃ n : ℕ, q ∈ anSlab n := by
  refine ⟨⌈max q.1 q.1⁻¹⌉₊, ⟨?_, ?_⟩, mem_univ _⟩
  · have h := (le_max_right q.1 q.1⁻¹).trans (Nat.le_ceil (max q.1 q.1⁻¹))
    rw [inv_le_comm₀ (by positivity) hq]
    linarith
  · have h := (le_max_left q.1 q.1⁻¹).trans (Nat.le_ceil (max q.1 q.1⁻¹))
    show q.1 ≤ _
    linarith

/-- **Density of the test vectors.** -/
theorem anTest_dense : (Submodule.span ℝ anTest).topologicalClosure = ⊤ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  suffices h : (Submodule.span ℝ anTest)ᗮ = ⊥ by rw [h, Submodule.bot_orthogonal_eq_top]
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hwL := Lp.memLp w
  have hslab : ∀ n : ℕ, ∀ᵐ q ∂hkM, q ∈ anSlab n → w q = 0 := by
    intro n
    have hI := hwL.indicator (measurableSet_anSlab n)
    have hgT : hI.toLp _ ∈ anTest := ⟨n, by
      filter_upwards [hI.coeFn_toLp] with q hq hqn
      rw [hq, indicator_of_notMem hqn]⟩
    have h0 : ⟪hI.toLp _, w⟫ = 0 :=
      (Submodule.mem_orthogonal _ _).1 hw _ (Submodule.subset_span hgT)
    rw [L2.inner_def] at h0
    have e : ∀ᵐ q ∂hkM, ⟪(hI.toLp _ : HkE) q, w q⟫ =
        (anSlab n).indicator (fun q => w q ^ 2) q := by
      filter_upwards [hI.coeFn_toLp] with q hq
      rw [hq]
      by_cases hqn : q ∈ anSlab n
      · simp [indicator_of_mem hqn, sq]
      · simp [indicator_of_notMem hqn]
    rw [integral_congr_ae e, integral_indicator (measurableSet_anSlab n)] at h0
    have hint : IntegrableOn (fun q => w q ^ 2) (anSlab n) hkM :=
      (hwL.integrable_sq).integrableOn
    have h1 := (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun q => sq_nonneg (w q)) hint).1 h0
    rw [EventuallyEq, ae_restrict_iff' (measurableSet_anSlab n)] at h1
    filter_upwards [h1] with q hq hqn
    exact pow_eq_zero_iff two_ne_zero |>.1 (hq hqn)
  have hall : ∀ᵐ q ∂hkM, ∀ n : ℕ, q ∈ anSlab n → w q = 0 := ae_all_iff.2 hslab
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hall, hkM_ae_pos] with q hq hpos
  obtain ⟨n, hn⟩ := exists_mem_anSlab hpos
  exact hq n hn

/-- The weight `(2t)^{-1/2}`. -/
def anC (q : ℝ × ℂ) : ℝ := (Real.sqrt (2 * q.1))⁻¹

theorem measurable_anC : Measurable anC := by unfold anC; fun_prop

theorem anC_le_of_mem {n : ℕ} {q : ℝ × ℂ} (hq : q ∈ anSlab n) : ‖anC q‖ ≤ (n : ℝ) + 1 := by
  obtain ⟨⟨h1, -⟩, -⟩ := hq
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  have hq0 : 0 < q.1 := (inv_pos.2 hn).trans_le h1
  have hs : ((n : ℝ) + 1)⁻¹ ≤ Real.sqrt (2 * q.1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [inv_pos.2 hn]
  rw [anC, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  calc (Real.sqrt (2 * q.1))⁻¹ ≤ (((n : ℝ) + 1)⁻¹)⁻¹ := inv_anti₀ (by positivity) hs
    _ = (n : ℝ) + 1 := inv_inv _

/-- `(2t)^{-1/2} g` is integrable for a test vector `g`. -/
theorem integrable_anC_mul {g : HkE} (hg : g ∈ anTest) :
    Integrable (fun q => anC q * g q) hkM := by
  obtain ⟨n, hn⟩ := hg
  have : IsFiniteMeasure (hkM.restrict (anSlab n)) :=
    isFiniteMeasure_restrict.2 (hkM_anSlab_lt_top n).ne
  have hf : MemLp ((anSlab n).indicator anC) 2 hkM := by
    rw [memLp_indicator_iff_restrict (measurableSet_anSlab n)]
    refine MemLp.of_bound measurable_anC.aestronglyMeasurable ((n : ℝ) + 1) ?_
    exact (ae_restrict_iff' (measurableSet_anSlab n)).2 (ae_of_all _ fun q hq => anC_le_of_mem hq)
  have h := hf.integrable_mul (Lp.memLp g) (p := 2) (q := 2)
  refine h.congr ?_
  filter_upwards [hn] with q hq
  by_cases hqn : q ∈ anSlab n
  · simp [indicator_of_mem hqn]
  · simp [indicator_of_notMem hqn, hq hqn]

/-- The test potential `anPhi g x = ∫ (2t)^{-1/2} g(q) h_x(q) dhkM(q)`. -/
def anPhi (g : HkE) (x : ℂ) : ℝ := ∫ q, anC q * g q * hkH 1 q.1 q.2 x ∂hkM

theorem norm_hkH_one_le (t : ℝ) (ξ x : ℂ) : ‖hkH 1 t ξ x‖ ≤ 4 := by
  rw [Real.norm_eq_abs]
  have := abs_hkH_le 1 t ξ x
  norm_num at this
  linarith

theorem continuous_anPhi {g : HkE} (hg : g ∈ anTest) : Continuous (anPhi g) := by
  have hi := integrable_anC_mul hg
  refine continuous_of_dominated (bound := fun q => 4 * ‖anC q * g q‖) (fun x => ?_)
    (fun x => ae_of_all _ fun q => ?_) (hi.norm.const_mul 4) (ae_of_all _ fun q => ?_)
  · exact hi.aestronglyMeasurable.mul
      ((measurable_hkH 1).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_hkH_one_le _ _ _) (norm_nonneg _)
  · unfold hkH hkG cF sF
    fun_prop

theorem abs_anPhi_le {g : HkE} (hg : g ∈ anTest) (x : ℂ) :
    |anPhi g x| ≤ ∫ q, 4 * ‖anC q * g q‖ ∂hkM := by
  rw [← Real.norm_eq_abs, anPhi]
  refine norm_integral_le_of_norm_le ((integrable_anC_mul hg).norm.const_mul 4)
    (ae_of_all _ fun q => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_hkH_one_le _ _ _) (norm_nonneg _)

/-- Fubini: `∫ (2t)^{-1/2} g hkA_ν dhkM = ∫ anPhi g dν`. -/
theorem integral_anC_mul_hkA {g : HkE} (hg : g ∈ anTest) (ν : Measure ℂ) [IsFiniteMeasure ν] :
    Integrable (fun q => anC q * g q * hkA 1 q.1 ν q.2) hkM ∧
      ∫ q, anC q * g q * hkA 1 q.1 ν q.2 ∂hkM = ∫ x, anPhi g x ∂ν := by
  have hi := integrable_anC_mul hg
  refine ⟨?_, ?_⟩
  · refine (hi.norm.const_mul (4 * ν.real univ)).mono'
      (hi.aestronglyMeasurable.mul (measurable_hkA 1 ν).aestronglyMeasurable)
      (ae_of_all _ fun q => ?_)
    rw [norm_mul, mul_comm (4 * ν.real univ), Real.norm_eq_abs (hkA _ _ _ _)]
    refine mul_le_mul_of_nonneg_left ((abs_hkA_le 1 q.1 ν q.2).trans (le_of_eq ?_))
      (norm_nonneg _)
    norm_num
  · have hF : Integrable (Function.uncurry fun (q : ℝ × ℂ) (x : ℂ) =>
        anC q * g q * hkH 1 q.1 q.2 x) (hkM.prod ν) := by
      have hb : Integrable (fun p : (ℝ × ℂ) × ℂ => 4 * ‖anC p.1 * g p.1‖ * (1 : ℝ))
          (hkM.prod ν) := (hi.norm.const_mul 4).mul_prod (integrable_const (1 : ℝ))
      refine hb.mono' ((hi.aestronglyMeasurable.comp_fst).mul
        (measurable_hkH 1).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
      simp only [Function.uncurry, mul_one]
      rw [norm_mul, mul_comm (4 : ℝ)]
      exact mul_le_mul_of_nonneg_left (norm_hkH_one_le _ _ _) (norm_nonneg _)
    calc ∫ q, anC q * g q * hkA 1 q.1 ν q.2 ∂hkM
        = ∫ q, ∫ x, anC q * g q * hkH 1 q.1 q.2 x ∂ν ∂hkM := by
          refine integral_congr_ae (ae_of_all _ fun q => ?_)
          simp only [hkA]
          rw [integral_const_mul]
      _ = ∫ x, anPhi g x ∂ν := integral_integral_swap hF

/-- **Pairing with a test vector.** `⟪v̂_ρ, g⟫ = ∫ anPhi g dρ − ρ(ℂ) ∫ anPhi g dρ₀`. -/
theorem inner_freeVec_anTest (ρ : AdmT) {g : HkE} (hg : g ∈ anTest) :
    ⟪freeVec ρ, g⟫ = ∫ x, anPhi g x ∂ρ.1 - ρ.1.real univ * ∫ x, anPhi g x ∂gffExRef := by
  have := ρ.2.1
  obtain ⟨hA, eA⟩ := integral_anC_mul_hkA hg ρ.1
  obtain ⟨hB, eB⟩ := integral_anC_mul_hkA hg gffExRef
  have e0 : ⟪freeVec ρ, g⟫ = ⟪freeVec ρ, (Lp.memLp g).toLp g⟫ := by rw [Lp.toLp_coeFn]
  rw [e0, freeVec, hk_inner_toLp, ← eA, ← eB, ← integral_const_mul, ← integral_sub hA
    (hB.const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [hkFeat, freeRef, hkA_smul, anC, measureReal_def]
  ring

end Prop16Asm

end QuantumZipper
