import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.LQG.BoundaryVague
import QuantumZipper.Statements.CouplingFields

/-!
# M4-P6(a): infinite mass of half-lines

* `ae_zero_or_top_of_scaling` (abstract lemma): if `M ∈ [0,∞]`, `M'_n =_d M`,
  `M'_n = e^{Y_n} M` a.s. and `Y_n → −∞` in probability, then `M ∈ {0, ∞}` a.s.
* `ae_qBoundaryMeasure_Ici_eq_top`: for the free field and `γ ∈ (0,2)`, almost surely
  `ν_X[x,∞) = ν_X(−∞,x] = ∞` for every `x`.
* `ae_qBoundaryMeasureOn_gamma0_eq_top`: the same for `Γ⁰ = ofFun (h0rev κ) + X`, `γ = √κ`, on
  each open half-line (whose local measure is `|t| ν_X`).

Route for the free field: `M = e^{-γ X(fc(0,1))/2} ν_X(U)` for a cone `U ∈ {(0,∞), (−∞,0)}` is a
measurable function `Φ` of the normalized coordinates `x(fc_i) − x(fc(0,1))`. Exact dyadic
scaling: the normalized coordinates of `rescale X Q 2^n` have the law of those of `X`
(kernel invariance, `WedgeTK.map_gaussFam_eq`, `kernelCov2_map_mul`), and deterministically
`ν_{rescale x Q 2^n} = (·/2^n)_* ν_x` along the dyadic radii (using `γQ/2 − γ²/4 = 1`).
Hence `M'_n = e^{Y_n} M` with `Y_n = −(γ/2)(X(fc(0,2^n)) − X(fc(0,1)) + Q n log 2)`, whose
Gaussian part has variance `2 n log 2` (Chebyshev). Positivity (M4-P2) excludes `M = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper

namespace InfMass

open Factorization LQGMeas

/-! ## 1. The abstract lemma -/

theorem ae_zero_or_top_of_scaling {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {M : Ω → ℝ≥0∞} {M' : ℕ → Ω → ℝ≥0∞} {Y : ℕ → Ω → ℝ}
    (hM : AEMeasurable M P) (hM' : ∀ n, AEMeasurable (M' n) P)
    (hlaw : ∀ n, P.map (M' n) = P.map M)
    (hrel : ∀ n, ∀ᵐ ω ∂P, M' n ω = ENNReal.ofReal (Real.exp (Y n ω)) * M ω)
    (hY : ∀ L : ℝ, Tendsto (fun n => P {ω | L ≤ Y n ω}) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, M ω = 0 ∨ M ω = ⊤ := by
  -- Step 1: no mass in `[1/(m+1), m+1]`
  have hstep : ∀ m : ℕ, P (M ⁻¹' Icc ((m + 1 : ℝ≥0∞)⁻¹) (m + 1)) = 0 := by
    intro m
    set I : Set ℝ≥0∞ := Icc ((m + 1 : ℝ≥0∞)⁻¹) (m + 1) with hI
    have hPI : ∀ n, P (M ⁻¹' I) = P (M' n ⁻¹' I) := fun n => by
      rw [← Measure.map_apply_of_aemeasurable hM measurableSet_Icc,
        ← Measure.map_apply_of_aemeasurable (hM' n) measurableSet_Icc, hlaw n]
    set A : ℕ → Set Ω := fun K => {ω | ((K + 1 : ℕ) : ℝ≥0∞) < M ω ∧ M ω < ⊤} with hA
    have hbound : ∀ K n : ℕ, P (M ⁻¹' I) ≤ P (A K) +
        P {ω | Real.log (1 / (((m : ℝ) + 1) * ((K : ℝ) + 1))) ≤ Y n ω} := by
      intro K n
      rw [hPI n]
      refine (measure_mono_ae ?_).trans (measure_union_le _ _)
      filter_upwards [hrel n] with ω hω hmem
      simp only [mem_preimage, hI, mem_Icc] at hmem
      rw [hω] at hmem
      have hK0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      by_cases htop : M ω = ⊤
      · exfalso
        rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'] at hmem
        exact absurd hmem.2 (by simp)
      by_cases hlt : ((K + 1 : ℕ) : ℝ≥0∞) < M ω
      · exact Or.inl ⟨hlt, lt_top_iff_ne_top.2 htop⟩
      · right
        push_neg at hlt
        have h1 : ((m + 1 : ℝ≥0∞))⁻¹ ≤ ENNReal.ofReal (Real.exp (Y n ω)) * ((K + 1 : ℕ) : ℝ≥0∞) :=
          hmem.1.trans (by gcongr)
        have e1 : ENNReal.ofReal (1 / ((m : ℝ) + 1)) = ((m + 1 : ℝ≥0∞))⁻¹ := by
          rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_add (Nat.cast_nonneg _)
            zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
        have e2 : ENNReal.ofReal ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast]; norm_num
        rw [← e1, ← e2, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
        show Real.log (1 / (((m : ℝ) + 1) * ((K : ℝ) + 1))) ≤ Y n ω
        rw [Real.log_le_iff_le_exp (by positivity)]
        rw [div_le_iff₀ hm0] at h1
        rw [div_le_iff₀ (by positivity)]
        linarith [h1, show Real.exp (Y n ω) * ((K : ℝ) + 1) * ((m : ℝ) + 1) =
          Real.exp (Y n ω) * (((m : ℝ) + 1) * ((K : ℝ) + 1)) by ring]
    have hK : ∀ K : ℕ, P (M ⁻¹' I) ≤ P (A K) := by
      intro K
      have ht := (hY (Real.log (1 / (((m : ℝ) + 1) * ((K : ℝ) + 1))))).const_add (P (A K))
      rw [add_zero] at ht
      exact ge_of_tendsto ht (Eventually.of_forall fun n => hbound K n)
    have hA0 : Tendsto (fun K => P (A K)) atTop (𝓝 0) := by
      have hanti : Antitone A := by
        intro K K' hKK' ω hω
        refine ⟨lt_of_le_of_lt ?_ hω.1, hω.2⟩
        exact_mod_cast Nat.add_le_add_right hKK' 1
      have hnull : ∀ K, NullMeasurableSet (A K) P := fun K =>
        hM.nullMeasurable (measurableSet_Ioo (a := ((K + 1 : ℕ) : ℝ≥0∞)) (b := ⊤))
      have hemp : (⋂ K, A K) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
        rw [mem_iInter] at hω
        obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt (hω 0).2.ne
        have h1 := (hω K).1
        have h2 : (K : ℝ≥0∞) ≤ ((K + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ K
        exact absurd (hK.trans (h2.trans_lt h1)) (lt_irrefl _)
      have := tendsto_measure_iInter_atTop hnull hanti ⟨0, measure_ne_top _ _⟩
      rwa [hemp, measure_empty] at this
    exact le_antisymm (ge_of_tendsto hA0 (Eventually.of_forall hK)) zero_le
  -- Step 2
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hstep)
  simp only [mem_ofPred_eq, not_or] at hω
  obtain ⟨h0, htop⟩ := hω
  obtain ⟨a, ha⟩ := ENNReal.exists_nat_gt htop
  obtain ⟨b, hb⟩ := ENNReal.exists_inv_nat_lt h0
  refine mem_iUnion.2 ⟨a + b, ?_, ?_⟩
  · have : (b : ℝ≥0∞) ≤ ((a + b : ℕ) : ℝ≥0∞) + 1 := by
      exact_mod_cast (show b ≤ a + b + 1 by omega)
    exact (ENNReal.inv_le_inv.2 this).trans hb.le
  · have : (a : ℝ≥0∞) ≤ ((a + b : ℕ) : ℝ≥0∞) + 1 := by
      exact_mod_cast (show a ≤ a + b + 1 by omega)
    exact ha.le.trans this

/-! ## 2. Deterministic part -/

/-- The measurable functional `ν(U)`, computed from `bdryFun` (liminf of approximating
integrals) against cut-offs of the bounded open pieces `U ∩ (−N, N)`. -/
def Psi (γ : ℝ) (U : Set ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ m : ℕ, ENNReal.ofReal (bdryFun γ (openBump (U ∩ Ioo (-(N : ℝ)) N) m) y)

theorem measurable_Psi (γ : ℝ) (U : Set ℝ) : Measurable (Psi γ U) :=
  Measurable.iSup fun _ => Measurable.iSup fun _ => ENNReal.measurable_ofReal.comp
    (measurable_bdryFun γ (continuous_openBump _ _).measurable)

theorem Psi_congr {γ : ℝ} {U : Set ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    Psi γ U x = Psi γ U x' := by
  unfold Psi bdryFun; rw [bdryApprox_congr h]

theorem Psi_eq {γ : ℝ} {U : Set ℝ} (hU : IsOpen U) {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) : Psi γ U y = ν U := by
  have := hν.1
  have hN : ∀ N : ℕ, ν (U ∩ Ioo (-(N : ℝ)) N) =
      ⨆ m : ℕ, ENNReal.ofReal (bdryFun γ (openBump (U ∩ Ioo (-(N : ℝ)) N) m) y) := by
    intro N
    have hV : IsOpen (U ∩ Ioo (-(N : ℝ)) N) := hU.inter isOpen_Ioo
    have hVb : Bornology.IsBounded (U ∩ Ioo (-(N : ℝ)) N) :=
      (Metric.isBounded_Ioo _ _).subset inter_subset_right
    have hVc : (U ∩ Ioo (-(N : ℝ)) N)ᶜ.Nonempty := ⟨N, fun h => lt_irrefl _ h.2.2⟩
    rw [measure_open_eq_iSup ν hV hVc]
    congr 1; funext m
    have hc := continuous_openBump (U ∩ Ioo (-(N : ℝ)) N) m
    have hcs := hasCompactSupport_openBump hVb m
    rw [show bdryFun γ (openBump (U ∩ Ioo (-(N : ℝ)) N) m) y =
        ∫ t, openBump (U ∩ Ioo (-(N : ℝ)) N) m t ∂ν from (hν.2 _ hc hcs).liminf_eq,
      ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
        (ae_of_all _ fun t => openBump_nonneg _ m t)]
  have hU' : U = ⋃ N : ℕ, U ∩ Ioo (-(N : ℝ)) N := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, mem_Ioo]
    constructor
    · intro ht
      obtain ⟨N, hN⟩ := exists_nat_gt |t|
      exact ⟨N, ht, (abs_lt.1 hN).1, (abs_lt.1 hN).2⟩
    · rintro ⟨N, ht, -⟩; exact ht
  have hmono : Monotone fun N : ℕ => U ∩ Ioo (-(N : ℝ)) N := by
    intro N N' h
    have h' : (N : ℝ) ≤ N' := by exact_mod_cast h
    exact inter_subset_inter_right _ (Ioo_subset_Ioo (by linarith) h')
  unfold Psi
  simp_rw [← hN]
  conv_rhs => rw [hU']
  rw [hmono.measure_iUnion]

open Classical in
theorem reconstruct_coords_add_apply (x : FieldSample) (c : ℝ) (i : ℕ) :
    reconstruct (fun j => coords x j + c)
        (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) =
      x (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) + c := by
  have h : ∃ j, foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) =
      foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) := ⟨i, rfl⟩
  unfold reconstruct
  rw [dif_pos h]
  exact congrArg (· + c) (congrArg x (Nat.find_spec h))

theorem avgReg_reconstruct_add (x : FieldSample) (c : ℝ) :
    avgReg (reconstruct (fun j => coords x j + c)) = avgReg (addConst x c) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have := reconstruct_coords_add_apply x c i
  rw [hi] at this
  refine this.trans ?_
  simp [addConst, measure_univ]

theorem Psi_addConst {γ : ℝ} {U : Set ℝ} (hU : IsOpen U) {x : FieldSample}
    (hx : IsRegularSample x) {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) (c : ℝ) :
    Psi γ U (addConst x c) = ENNReal.ofReal (Real.exp (γ * c / 2)) * ν U := by
  have h2 : IsVagueLimitR (bdryApprox γ (addConst x c))
      (ENNReal.ofReal (Real.exp (γ * c / 2)) • ν) := by
    have := BdryVague.IsVagueLimitR.const_smul hν (c := ENNReal.ofReal (Real.exp (γ * c / 2)))
      ENNReal.ofReal_ne_top
    convert this using 1
    funext k
    exact LocalRule.bdryApprox_addConst hx.rawConverges γ c k
  rw [Psi_eq hU h2, Measure.smul_apply, smul_eq_mul]

/-! ### Dyadic rescaling of the approximating measures -/

theorem two_pow_mul_radius {n k : ℕ} (h : n ≤ k) : (2 : ℝ) ^ n * radius k = radius (k - n) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [radius, Nat.add_sub_cancel_left, pow_add]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]

theorem avgReg_rescale_of {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    (Q : ℝ) {b : ℝ} (hb : 0 < b) {k j : ℕ} (hbk : b * radius k = radius j) (t : ℝ) :
    avgReg (rescale x Q b) k (t : ℂ) = avgReg x j ((b * t : ℝ) : ℂ) + Q * Real.log b := by
  rw [(h.rescale' Q hb).avgReg_eq k (GaussTK.ofReal_mem_Hbar t)]
  rw [h.avgReg_eq j (GaussTK.ofReal_mem_Hbar _), hbk, Complex.ofReal_mul]

theorem integral_bdryApprox_rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    {γ : ℝ} (hγ : γ ≠ 0) {b : ℝ} (hb : 0 < b) {k j : ℕ} (hbk : b * radius k = radius j)
    (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryApprox γ (rescale x (Qc γ) b) k = ∫ s, f (s * b⁻¹) ∂bdryApprox γ x j := by
  have hm1 : Measurable fun t : ℝ => avgReg (rescale x (Qc γ) b) k (t : ℂ) :=
    (RegClosure.measurable_avgReg_slice _ k).comp Complex.measurable_ofReal
  have hm2 : Measurable fun t : ℝ => avgReg x j (t : ℂ) :=
    (RegClosure.measurable_avgReg_slice _ _).comp Complex.measurable_ofReal
  rw [bdryApprox, bdryApprox,
    GoodSample.integral_withDensity_ofReal (d := fun t : ℝ => radius k ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg (rescale x (Qc γ) b) k (t : ℂ)))
      ((Real.measurable_exp.comp (hm1.const_mul _)).const_mul _)
      (fun t => mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le) f,
    GoodSample.integral_withDensity_ofReal (d := fun t : ℝ => radius j ^ (γ ^ 2 / 4) *
      Real.exp (γ / 2 * avgReg x j (t : ℂ)))
      ((Real.measurable_exp.comp (hm2.const_mul _)).const_mul _)
      (fun t => mul_nonneg (Real.rpow_nonneg (radius_pos _).le _) (Real.exp_pos _).le) _]
  have hcv := MeasureTheory.Measure.integral_comp_mul_left (fun s =>
    radius j ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x j (s : ℂ)) * f (s * b⁻¹)) b
  simp only [abs_inv, abs_of_pos hb, smul_eq_mul] at hcv
  have e : ∀ t : ℝ, b * t * b⁻¹ = t := fun t => by field_simp
  simp only [e] at hcv
  rw [← mul_right_inj' hb.ne', ← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hcv
  rw [← hcv, ← integral_const_mul]
  congr 1
  funext t
  rw [avgReg_rescale_of h (Qc γ) hb hbk t]
  have hr : radius k = radius j * b⁻¹ := by
    rw [← hbk]; field_simp
  have hpos := radius_pos j
  rw [hr, Real.mul_rpow hpos.le (inv_nonneg.2 hb.le), Real.rpow_def_of_pos hpos,
    Real.rpow_def_of_pos (inv_pos.2 hb), Real.log_inv, mul_add, Real.exp_add]
  have hQ : γ / 2 * (Qc γ * Real.log b) = Real.log b + γ ^ 2 / 4 * Real.log b := by
    unfold Qc; field_simp; ring
  rw [hQ, Real.exp_add, Real.exp_log hb]
  have hc : Real.exp (-Real.log b * (γ ^ 2 / 4)) * Real.exp (γ ^ 2 / 4 * Real.log b) = 1 := by
    rw [← Real.exp_add, show -Real.log b * (γ ^ 2 / 4) + γ ^ 2 / 4 * Real.log b = 0 by ring,
      Real.exp_zero]
  linear_combination (Real.exp (Real.log (radius j) * (γ ^ 2 / 4)) *
    Real.exp (γ / 2 * avgReg x j ((b * t : ℝ) : ℂ)) * b * f t) * hc

theorem isVagueLimitR_rescale {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    {γ : ℝ} (hγ : γ ≠ 0) {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) (n : ℕ) :
    IsVagueLimitR (bdryApprox γ (rescale x (Qc γ) ((2 : ℝ) ^ n)))
      (ν.map fun s => s * ((2 : ℝ) ^ n)⁻¹) := by
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹ with hcdef
  have hc : c ≠ 0 := by positivity
  have hmeas : Measurable fun s : ℝ => s * c := measurable_id.mul_const c
  have := hν.1
  refine ⟨?_, fun f hf hfc => ?_⟩
  · have : IsFiniteMeasureOnCompacts (ν.map fun s => s * c) := ⟨fun K hK => by
      rw [Measure.map_apply hmeas hK.measurableSet]
      exact ((Homeomorph.mulRight₀ c hc).isCompact_preimage.2 hK).measure_lt_top⟩
    infer_instance
  · have hf' : Continuous fun s => f (s * c) := hf.comp (continuous_id.mul continuous_const)
    have hfc' : HasCompactSupport fun s => f (s * c) :=
      hfc.comp_homeomorph (Homeomorph.mulRight₀ c hc)
    have ht := (hν.2 _ hf' hfc').comp (tendsto_sub_atTop_nat n)
    rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    exact (integral_bdryApprox_rescale h hγ (by positivity) (two_pow_mul_radius hk) f).symm

/-! ## 3. The free field -/

/-- The unit semicircle at `0`. -/
def fc01 : Measure ℂ := foldedCircle 0 1

/-- The `i`-th recorded circle. -/
def fcI (i : ℕ) : Measure ℂ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

/-- Normalized coordinates `x(fc_i) − x(fc(0,1))`. -/
def normC (x : FieldSample) : ℕ → ℝ := fun i => x (fcI i) - x fc01

theorem normC_eq (x : FieldSample) : normC x = fun j => coords x j + -(x fc01) := by
  funext j; simp only [normC, coords, fcI, sub_eq_add_neg]

theorem Psi_normC (γ : ℝ) (U : Set ℝ) (x : FieldSample) :
    Psi γ U (reconstruct (normC x)) = Psi γ U (addConst x (-(x fc01))) := by
  rw [normC_eq]; exact Psi_congr (avgReg_reconstruct_add x _)

theorem fcI_admissible (i : ℕ) : IsAdmissibleH (fcI i) := by
  rw [fcI, ← WedgeTK.fc_foldH_eq]
  exact isAdmissibleH_foldedCircle (CircleFubini.foldH_mem_Hbar' _) (radius_pos _)

theorem fc01_admissible : IsAdmissibleH fc01 :=
  isAdmissibleH_foldedCircle GaussTK.zero_mem_Hbar one_pos

theorem fcI_univ (i : ℕ) : fcI i Set.univ = fc01 Set.univ := by
  simp only [fcI, fc01, measure_univ]

/-- The balanced pairs `(fc_i, fc(0,1))`. -/
def pN (i : ℕ) : WedgeTK.BPair := ⟨(fcI i, fc01), fcI_admissible i, fc01_admissible, fcI_univ i⟩

/-- Their images under `z ↦ b z`. -/
def qN {b : ℝ} (hb : 0 < b) (i : ℕ) : WedgeTK.BPair :=
  ⟨((fcI i).map fun u => (b : ℂ) * u, fc01.map fun u => (b : ℂ) * u),
    WedgeTK.isAdmissibleH_map_mul hb (fcI_admissible i),
    WedgeTK.isAdmissibleH_map_mul hb fc01_admissible,
    by rw [WedgeTK.map_univ_mul, WedgeTK.map_univ_mul, fcI_univ]⟩

section FreeField

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem rescale_fc_apply (x : FieldSample) (Q : ℝ) {b : ℝ} (hb : 0 < b) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] :
    rescale x Q b μ = evalReg x (μ.map fun u => (b : ℂ) * u) + Q * Real.log b := by
  show evalReg x (μ.map fun u => (b : ℂ) * u) + Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (b : ℂ) * z) z‖ ∂μ = _
  rw [RegClosure.integral_log_deriv_mul hb]

theorem ae_evalReg_map_fc {G : Ω → ℂ × ℝ → ℝ} (hG : WedgeTK.IsRegVersion X P G) {b : ℝ}
    (hb : 0 < b) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, evalReg (X ω) ((foldedCircle d r).map fun u => (b : ℂ) * u) =
      X ω ((foldedCircle d r).map fun u => (b : ℂ) * u) := by
  rw [WedgeTK.fc_map_mul _ _ hb]
  exact WedgeTK.ae_evalReg_fc hG _ (mul_pos hb hr)

theorem map_normC_rescale (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : WedgeTK.IsRegVersion X P G) (Q : ℝ) {b : ℝ} (hb : 0 < b) :
    P.map (fun ω => normC (rescale (X ω) Q b)) = P.map (fun ω => normC (X ω)) := by
  have h1 : (fun ω => normC (X ω)) = fun ω i => WedgeTK.gaussFam X pN i ω := rfl
  have h01 := ae_evalReg_map_fc hG hb 0 one_pos
  have hI : ∀ᵐ ω ∂P, ∀ i, evalReg (X ω) ((fcI i).map fun u => (b : ℂ) * u) =
      X ω ((fcI i).map fun u => (b : ℂ) * u) :=
    ae_all_iff.2 fun i => ae_evalReg_map_fc hG hb _ (radius_pos _)
  have h2 : (fun ω => normC (rescale (X ω) Q b)) =ᵐ[P]
      fun ω i => WedgeTK.gaussFam X (qN hb) i ω := by
    filter_upwards [h01, hI] with ω h01 hI
    funext i
    simp only [normC, WedgeTK.gaussFam, qN]
    have : IsProbabilityMeasure (fcI i) := by unfold fcI; infer_instance
    have : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    rw [rescale_fc_apply _ _ hb (fcI i), rescale_fc_apply _ _ hb fc01, hI i]
    rw [show fc01 = foldedCircle 0 1 from rfl]
    rw [h01]
    ring
  rw [Measure.map_congr h2, h1]
  exact WedgeTK.map_gaussFam_eq hX _ _ fun i j => WedgeTK.kernelCov2_map_mul hb (pN i) (pN j)

/-- The dilation pair `(fc(0,1) ∘ (b·)⁻¹, fc(0,1))`. -/
def dPair {b : ℝ} (hb : 0 < b) : Unit → WedgeTK.BPair := fun _ =>
  ⟨(fc01.map fun u => (b : ℂ) * u, fc01), WedgeTK.isAdmissibleH_map_mul hb fc01_admissible,
    fc01_admissible, by rw [WedgeTK.map_univ_mul]⟩

theorem kernelCov2_dPair {b : ℝ} (hb : 1 ≤ b) :
    kernelCov2 neumannH (dPair (by linarith : (0 : ℝ) < b) ()).1
      (dPair (by linarith : (0 : ℝ) < b) ()).1 = 2 * Real.log b := by
  have hb0 : (0 : ℝ) < b := by linarith
  simp only [dPair, kernelCov2, fc01]
  rw [WedgeTK.fc_map_mul _ _ hb0, mul_zero, mul_one, WedgeTK.kernelCov_fc0 hb0 hb0,
    WedgeTK.kernelCov_fc0 hb0 one_pos, WedgeTK.kernelCov_fc0 one_pos hb0,
    WedgeTK.kernelCov_fc0 one_pos one_pos, max_self, max_self, max_eq_left hb, max_eq_right hb,
    Real.log_one]
  ring

theorem tendsto_prob_Y (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : WedgeTK.IsRegVersion X P G) {γ : ℝ} (hγ : 0 < γ) (L : ℝ) :
    Tendsto (fun n : ℕ => P {ω | L ≤ γ / 2 * (X ω fc01 -
      rescale (X ω) (Qc γ) ((2 : ℝ) ^ n) fc01)}) atTop (𝓝 0) := by
  set a : ℝ := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos one_lt_two
  have hQ : 0 < Qc γ := by unfold Qc; positivity
  set d : ℝ := 2 * L / γ with hd
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|d| / (Qc γ * a))
  have hcpos : ∀ n : ℕ, N0 ≤ n → 0 < Qc γ * (n * a) + d := by
    intro n hn
    have h1 : |d| / (Qc γ * a) < n := hN0.trans_le (by exact_mod_cast hn)
    rw [div_lt_iff₀ (by positivity)] at h1
    have := neg_abs_le d
    nlinarith
  have hbound : ∀ n : ℕ, N0 ≤ n → P {ω | L ≤ γ / 2 * (X ω fc01 -
      rescale (X ω) (Qc γ) ((2 : ℝ) ^ n) fc01)} ≤
      ENNReal.ofReal (2 * (n * a) / (Qc γ * (n * a) + d) ^ 2) := by
    intro n hn
    have hb0 : (0 : ℝ) < 2 ^ n := by positivity
    have hb1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
    set D : Ω → ℝ := WedgeTK.gaussFam X (dPair hb0) () with hD
    have hmem := WedgeTK.memLp_gaussFam hX (dPair hb0) ()
    have hmean : ∫ ω, D ω ∂P = 0 := WedgeTK.integral_gaussFam hX (dPair hb0) ()
    have hvar : variance D P = 2 * (n * a) := by
      rw [← covariance_self hmem.aemeasurable, WedgeTK.cov_gaussFam hX,
        kernelCov2_dPair hb1, ha, Real.log_pow]
    have hc := hcpos n hn
    have hcheb := meas_ge_le_variance_div_sq hmem hc
    rw [hmean, hvar] at hcheb
    refine le_trans (measure_mono_ae ?_) hcheb
    have h01 : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    filter_upwards [ae_evalReg_map_fc hG hb0 0 one_pos] with ω hω hmemω
    rw [rescale_fc_apply _ _ hb0 fc01, show fc01 = foldedCircle 0 1 from rfl, hω, Real.log_pow, ← ha] at hmemω
    have hDω : D ω = X ω ((foldedCircle 0 1).map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) -
        X ω (foldedCircle 0 1) := rfl
    rw [sub_zero, show WedgeTK.gaussFam X (dPair hb0) () ω = D ω from rfl, hDω]
    have : X ω ((foldedCircle 0 1).map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) - X ω (foldedCircle 0 1)
        ≤ -(Qc γ * (n * a) + d) := by
      rw [hd]
      have h2 : L * 2 / γ ≤ X ω (foldedCircle 0 1) -
          (X ω ((foldedCircle 0 1).map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) + Qc γ * (n * a)) := by
        rw [div_le_iff₀ hγ]; linarith
      have : 2 * L / γ = L * 2 / γ := by ring
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hreal : Tendsto (fun n : ℕ => 2 * (n * a) / (Qc γ * (n * a) + d) ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have ht : Tendsto (fun n : ℕ => 2 * a * (1 / (n : ℝ)) / (Qc γ * a + d * (1 / (n : ℝ))) ^ 2)
        atTop (𝓝 (2 * a * 0 / (Qc γ * a + d * 0) ^ 2)) :=
      ((tendsto_const_nhds.mul hinv).div ((tendsto_const_nhds.add
        (tendsto_const_nhds.mul hinv)).pow 2) (by rw [mul_zero, add_zero]; exact pow_ne_zero _ (mul_pos hQ ha0).ne'))
    simp only [mul_zero, zero_div] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop (max N0 1)] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
    have hc := hcpos n ((le_max_left _ _).trans hn)
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hc0 : Qc γ * (n * a) + d ≠ 0 := hc.ne'
    have e1 : Qc γ * a + d * (1 / (n : ℝ)) = (Qc γ * (n * a) + d) / n := by field_simp
    rw [e1, div_pow]
    field_simp
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * (n * a) / (Qc γ * (n * a) + d) ^ 2))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨N0, hbound⟩)

/-! ## 4. `Γ⁰` -/

theorem isVagueLimitOnR_restrict {νs : ℕ → Measure ℝ} {ν : Measure ℝ} (h : IsVagueLimitR νs ν)
    {U : Set ℝ} (hU : IsOpen U) : IsVagueLimitOnR U νs (ν.restrict U) := by
  have := h.1
  refine ⟨?_, fun K hK _ => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top,
    fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply hU.measurableSet.compl, compl_inter_self, measure_empty]
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h' => ht (hfU h')]
    exact h.2 f hf hfc

theorem exp_h0rev {κ : ℝ} (hκ : 0 < κ) {t : ℝ} (ht : t ≠ 0) :
    Real.exp (Real.sqrt κ / 2 * h0rev κ (t : ℂ)) = |t| := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [h0rev, Complex.norm_real, Real.norm_eq_abs,
    show Real.sqrt κ / 2 * (2 / Real.sqrt κ * Real.log |t|) = Real.log |t| by field_simp,
    Real.exp_log (abs_pos.2 ht)]

end FreeField

end InfMass

end QuantumZipper
