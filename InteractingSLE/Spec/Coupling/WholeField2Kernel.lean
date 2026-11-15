import InteractingSLE.Spec.Coupling.WholeField2Hull
import InteractingSLE.Spec.Coupling.WholeFieldMean
import InteractingSLE.Spec.Coupling.SafeEnergy
import InteractingSLE.Spec.Coupling.Assembly11Safe
import InteractingSLE.Spec.Coupling.Assembly11Path

/-!
# The frozen kernel with the hull germ retained: (PK1) of Aux. lemma 48 and (GB2) of Aux. lemma 47

Packet PROVE-WHOLEFIELD2 (ruling R36), item (2). Specification Aux. lemma 18, last paragraph (`source/spec/
p097-144.md#aux-18-proof`, pp. 97–98), Aux. lemma 47 (GB2) and Aux. lemma 48 (PK1) (`p193-240.md#aux-47`,
`#aux-48`, pp. 227–230).

For a coupling satisfying the frozen `IsOptionalHullCoupling`, a stopping time `τ < ζ` of the frozen driving
filtration and a hitting-measurable version `A` of `K_τ`, the conditional law of the centred field `h⁰ = h − 𝔥₀`
given the **hull germ together with the stopped history**, `germSigma A h⁰ ⊔ 𝓕_τ`, is the frozen kernel off the hull:
almost surely on `{supp φ ∩ K_τ = ∅}`,

`E[(h⁰, φ) | 𝒜 ∨ 𝓕_τ] = (𝔥_τ − 𝔥₀, φ)`,  `E[e^{i(h⁰, φ)} | 𝒜 ∨ 𝓕_τ] = e^{i(𝔥_τ − 𝔥₀, φ)} e^{−‖φ‖²_{H⁻¹(ℍ∖K_τ)}/2}`.

This is `WholeField.ae_condExp_germSigma_history_eq` (`WholeFieldMean`) fed with
* the history marking of `K_τ` (`isHistoryAvoidanceLocal_hull`, `WholeField2Hull`);
* the frozen kernel at all frequencies `c` (test `c • φ`; the mean is linear and the Green energy quadratic), with
  the frozen energy `E_τ(φ)` identified with the dual Dirichlet norm on `ℍ ∖ K_τ` (`Coupling.
  loewnerGreenEnergy_eq_zeroGFFTestCov`, through the driver frozen after a time before `ζ`);
* an event of `𝓕_τ` almost surely equal to `{supp φ ∩ K_τ = ∅}` (`exists_measurableSet_ae_iff_disjoint`): the
  safe stops `ρ_n` of the compact `supp φ` below an announcing sequence (`Coupling.exists_safeSeq_of_adapted`) give
  `⋃ₙ {τ ≤ ρ_n}`;
* a `𝓕_τ`-measurable version of the mean (`meanOfCharFun`): on that event the conditional characteristic function
  at frequency `1/(n + 1)` is `e^{i m/(n+1)} e^{−v/(2(n+1)²)}`, so `m = lim (n + 1) arg(·)`.

## Main results

* `isZeroBoundaryGFF_centredField`: `h − 𝔥₀` is a zero-boundary GFF;
* `exists_measurableSet_ae_iff_disjoint`: `{supp φ ∩ K_τ = ∅}` is an event of `𝓕_τ` up to a null set;
* `meanOfCharFun_eq`, `measurable_meanOfCharFun`;
* **`ae_condExp_germSigma_hull_eq`** ((PK1)/(GB2)): the frozen kernel holds given the hull germ and the history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling

/-! ### Elementary facts -/

/-- A test function scaled by `c` has its support inside that of the test function. -/
theorem tsupport_smul_testOn_subset (c : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    tsupport ⇑(c • φ) ⊆ tsupport ⇑φ := by
  rw [FunLike.coe_smul]
  exact tsupport_smul_subset_right (fun _ : ℂ => c) ⇑φ

/-- The Loewner Green energy is quadratic. -/
theorem loewnerGreenEnergy_smul (w : ℝ → ℝ) (t c : ℝ) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t (c • φ) = c ^ 2 * loewnerGreenEnergy w t φ := by
  unfold loewnerGreenEnergy
  rw [sq, mul_assoc, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext y
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The pairing of a function with a scaled test function. -/
theorem integral_mul_smul (f : ℂ → ℝ) (c : ℝ) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, f z * (c • φ) z = c * ∫ z, f z * φ z := by
  rw [← integral_const_mul]
  congr 1
  funext z
  rw [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The frozen energy is the dual Dirichlet norm off the hull** for a driver continuous before the lifetime with
`w 0 = 0`, at a time `t < ζ`. -/
theorem loewnerGreenEnergy_rpath_eq_zeroGFFTestCov {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (ψ : TestOn upperHalfPlaneOpens) (hψ : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => w s.toNNReal) t)) :
    loewnerGreenEnergy (fun s : ℝ => w s.toNNReal) t ψ =
      zeroGFFTestCov (H \ fwdHull (fun s : ℝ => w s.toNNReal) t) ψ ψ := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hc := Ito.continuous_clampDrv (W := Ito.rpath w) t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have heq : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull (Ito.clampDrv (Ito.rpath w) t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr =>
      (Ito.clampDrv_eqOn (W := Ito.rpath w) (T := (t₂ : ℝ)) hr).symm
  have h0 : Ito.clampDrv (Ito.rpath w) t₂ 0 = 0 := by
    rw [Ito.clampDrv_eqOn ⟨le_rfl, t₂.coe_nonneg⟩]
    simp [Ito.rpath, hw0]
  rw [heq] at hψ ⊢
  have e := loewnerGreenEnergy_clampDrv_of_le (W := Ito.rpath w) htt₂'.le ψ
  refine e.symm.trans ?_
  exact loewnerGreenEnergy_eq_zeroGFFTestCov hc h0 t.coe_nonneg ψ hψ

/-! ### Recovering the mean from the conditional characteristic functions -/

section MeanRecovery

variable {Ω : Type*}

/-- `arg (e^{iθ} r) = θ` for `θ ∈ (−π, π]` and `r = e^x > 0`. -/
theorem arg_exp_mul_real_exp {θ : ℝ} (hθ : θ ∈ Ioc (-Real.pi) Real.pi) (x : ℝ) :
    Complex.arg (Complex.exp (Complex.I * (θ : ℂ)) * ((Real.exp x : ℝ) : ℂ)) = θ := by
  rw [Complex.arg_mul_real (Real.exp_pos x), mul_comm, Complex.arg_exp_mul_I, toIocMod_eq_self]
  rw [Set.mem_Ioc] at hθ ⊢
  constructor <;> linarith [hθ.1, hθ.2]

/-- The mean read off the conditional characteristic functions at the frequencies `1/(n + 1)`:
`lim (n + 1) arg ψₙ`. -/
def meanOfCharFun (ψ : ℕ → Ω → ℂ) (ω : Ω) : ℝ :=
  limUnder atTop fun n : ℕ => ((n : ℝ) + 1) * Complex.arg (ψ n ω)

/-- If `ψₙ(ω) = e^{i m/(n+1)} e^{−v/(2(n+1)²)}` for every `n`, the recovered mean is `m`. -/
theorem meanOfCharFun_eq {ψ : ℕ → Ω → ℂ} {ω : Ω} {m v : ℝ}
    (h : ∀ n : ℕ, ψ n ω = Complex.exp (Complex.I * ((1 / ((n : ℝ) + 1) * m : ℝ) : ℂ)) *
      ((Real.exp (-(1 / 2) * ((1 / ((n : ℝ) + 1)) ^ 2 * v)) : ℝ) : ℂ)) :
    meanOfCharFun ψ ω = m := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt (|m| / Real.pi)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hθ : 1 / ((n : ℝ) + 1) * m ∈ Ioc (-Real.pi) Real.pi := by
    have hlt : |m| / ((n : ℝ) + 1) < Real.pi := by
      rw [div_lt_iff₀ hn1]
      have h1 : |m| < Real.pi * N := by
        rw [div_lt_iff₀ Real.pi_pos] at hN; linarith
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
    have habs : |1 / ((n : ℝ) + 1) * m| < Real.pi := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)), one_div_mul_eq_div]
      exact hlt
    rw [abs_lt] at habs
    exact ⟨habs.1, habs.2.le⟩
  rw [h n, arg_exp_mul_real_exp hθ]
  field_simp

/-- The recovered mean of a family measurable for `ℋ` is measurable for `ℋ`. -/
theorem measurable_meanOfCharFun {ℋ : MeasurableSpace Ω} {ψ : ℕ → Ω → ℂ}
    (hψ : ∀ n, StronglyMeasurable[ℋ] (ψ n)) : Measurable[ℋ] (meanOfCharFun ψ) :=
  (StronglyMeasurable.limUnder fun n =>
    ((Complex.measurable_arg.comp (hψ n).measurable).const_mul _).stronglyMeasurable).measurable

end MeanRecovery

/-! ### The frozen coupling -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- `h − 𝔥₀` is a zero-boundary GFF on `ℍ`. -/
theorem isZeroBoundaryGFF_centredField (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P := by
  refine ⟨measurable_centredField hC.2.1 u₀, ?_⟩
  have e : (fun φ ω => centredField h u₀ ω φ) = fun φ ω => h ω φ - ∫ z, u₀ z * φ z := by
    funext φ ω
    exact centredField_apply h hu₀.1 ω φ
  rw [e]
  exact hC.2.2.1 u₀ hu₀

omit [IsProbabilityMeasure P] in
/-- **`{C ∩ K_τ = ∅}` is an event of `𝓕_τ` up to a null set**, for a compact `C ⊆ ℍ`: with the safe stops `ρₙ` of `C`
below an announcing sequence of the lifetime, it is almost surely `⋃ₙ {τ ≤ ρₙ}`. -/
theorem exists_measurableSet_ae_iff_disjoint
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {σ : ℕ → Ω → ℝ≥0} (hσ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    ∃ G : Set Ω, MeasurableSet[hτ.measurableSpace] G ∧
      ∀ᵐ ω ∂P, (ω ∈ G ↔ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) := by
  obtain ⟨m, hm, hCm⟩ := exists_pos_le_im_of_isCompact hC hCH
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨ρ, hρst, -, -, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := killedDrivingFiltration hX)
    (adaptedBefore_killedDriving_W hX) hpath hC hCH hm hCm hσ.1 hσ.2.1 hσ.2.2.1
  refine ⟨⋃ n, {ω | τ ω ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0)},
    MeasurableSet.iUnion fun n => hτ.measurableSet_le_stopping_time (hρst n), ?_⟩
  filter_upwards [hτζ, ae_all_iff.2 hρsafe, hρex, hσ.2.2.2, hE.2.2.2.2] with ω hτω hsafe hex hann hp
  have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at hτω; exact absurd hτω (not_lt.2 le_top)
  set s : ℝ≥0 := (τ ω).untopD 0 with hs_def
  have hτs : τ ω = (s : WithTop ℝ≥0) := (coe_untopD_of_ne_top hτtop).symm
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [← coe_untopD_of_ne_top hτtop] at hτω; exact hτω
  constructor
  · rintro hω
    obtain ⟨n, hn⟩ := mem_iUnion.1 hω
    have hsn : s ≤ ρ n ω := by
      have : (s : WithTop ℝ≥0) ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) := by rw [← hτs]; exact hn
      exact_mod_cast this
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hS := hsafe n
    have hz' : z ∉ fwdHull (Ito.rpath fun t => W t ω) (ρ n ω) :=
      notMem_fwdHull_of_alive hp.2.2.2.1 hS.1 (hCH hz) (hS.2.2.2 z hz).1
    exact hz' ((QuantumZipper.fwdHull_mono).1 (by exact_mod_cast hsn) hzK)
  · intro hdis
    have halive : ∀ z ∈ C, ∃ u, IsForwardSol (Ito.rpath fun t => W t ω) z s u := fun z hz =>
      Ito.exists_isForwardSol_of_mem s.coe_nonneg ⟨hCH hz, fun h' => hdis.ne_of_mem hz h' rfl⟩
    obtain ⟨j, hj⟩ := hann s hsζ
    obtain ⟨n, hn⟩ := (hex j s hj halive).exists
    refine mem_iUnion.2 ⟨n, ?_⟩
    show τ ω ≤ ((ρ n ω : ℝ≥0) : WithTop ℝ≥0)
    rw [hτs]
    exact_mod_cast hn

/-- **The frozen kernel with the hull germ retained** ((PK1) of Aux. lemma 48, (GB2) of Aux. lemma 47; Aux. lemma 18,
last paragraph). For a coupling satisfying `IsOptionalHullCoupling` with `κ > 0`, a stopping time `τ < ζ` of the
frozen driving filtration, a hitting-measurable version `A` of `K_τ`, bounded harmonic extensions `u₀` of the
time-zero data and `u ω` of the data at `τ`, and a test function `φ`: almost surely on `{supp φ ∩ K_τ = ∅}`, the
centred field `h⁰ = h − 𝔥₀` has, given the germ σ-algebra of `A` together with `𝓕_τ`, the conditional mean
`(𝔥_τ − 𝔥₀, φ)` and the conditional characteristic function `e^{i(𝔥_τ − 𝔥₀, φ)} e^{−‖φ‖²_{H⁻¹(ℍ∖K_τ)}/2}`. -/
theorem ae_condExp_germSigma_hull_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    (∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => centredField h u₀ ω' φ | germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]) ω =
        (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) -
          ∫ z, u₀ z * φ z) ∧
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
          germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * (((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) - ∫ z, u₀ z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
  classical
  set h0 := centredField h u₀ with hh0_def
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens h0 P := isZeroBoundaryGFF_centredField hC hu₀
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ hτζ hA hAK
  obtain ⟨hE, hhm, -, hX', hker⟩ := hC
  have hker' := hker τ hτ hτζ
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hker'.1.2.1, hAK] with ω h1 h2
    rw [h2]
    exact h1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hτζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h⟩ := hF.exists
    exact h
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B) (κ := κ)
    (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  -- the event `{supp φ ∩ K_τ = ∅}` of `𝓕_τ`
  obtain ⟨G, hGm, hGiff⟩ := exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ
    φ.hasCompactSupport.isCompact φ.tsupport_subset
  -- the mean and the variance
  set M : Ω → ℝ := fun ω => ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z *
    φ z with hM_def
  set a : ℝ := ∫ z, u₀ z * φ z with ha_def
  -- the frozen kernel at every frequency
  have hfreq : ∀ c : ℝ, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c * (M ω - a) : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    have hk := hker'.2 u hu (c • φ)
    have hsm := condExp_smul (μ := P) (Complex.exp (-(Complex.I * ((c * a : ℝ) : ℂ))))
      (fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ))) hτ.measurableSpace
    have e1 : (fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((c * a : ℝ) : ℂ))) •
          fun ω' => Complex.exp (Complex.I * (h ω' (c • φ) : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hh0_def, centredField_apply h hu₀.1, map_smul,
        smul_eq_mul]
      congr 1
      push_cast
      ring
    filter_upwards [hk, hsm, hAK, hE.2.2.2.2, hτζ] with ω hkω hsmω hAω hp hτω hdis
    have hdisK : Disjoint (tsupport φ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) := hAω ▸ hdis
    have hdisc := hdisK.mono_left (tsupport_smul_testOn_subset c φ)
    have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at hτω; exact absurd hτω (not_lt.2 le_top)
    have hsζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [← coe_untopD_of_ne_top hτtop] at hτω; exact hτω
    have hen := loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hp.2.2.2.1 hp.1 hsζ φ hdisK
    rw [e1, hsmω, Pi.smul_apply, smul_eq_mul, hkω hdisc, integral_mul_smul, FunLike.coe_smul,
      loewnerGreenEnergy_smul, hen, ← hAω, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- an `𝓕_τ`-measurable version of the mean
  set ψ : ℕ → Ω → ℂ := fun n =>
    P[fun ω' => Complex.exp (Complex.I * ((1 / ((n : ℝ) + 1) * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace] with hψ_def
  have hψm : ∀ n, StronglyMeasurable[hτ.measurableSpace] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[hτ.measurableSpace] (meanOfCharFun ψ) := measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) → meanOfCharFun ψ ω = M ω - a := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hfreq (1 / ((n : ℝ) + 1))] with ω hω hdis
    exact meanOfCharFun_eq fun n => hω n hdis
  -- the kernel hypothesis of the history-marked law, on the event of `𝓕_τ`
  have hkern : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ G →
      (P[fun ω' => Complex.exp (Complex.I * ((c * h0 ω' φ : ℝ) : ℂ)) | hτ.measurableSpace]) ω =
        Complex.exp (Complex.I * ((c * meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (c ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro c
    filter_upwards [hfreq c, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hωG
    have hdis : Disjoint (tsupport φ) (A ω) := by rw [h4]; exact h3.1 hωG
    rw [h2 hdis]
    exact h1 hdis
  obtain ⟨k1, k2⟩ := ae_condExp_germSigma_history_eq hh0 hA hℋ hloc hAc φ hGm hmm hkern
  refine ⟨?_, ?_⟩
  · filter_upwards [k1, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hdis
    have hωG : ω ∈ G := h3.2 (h4 ▸ hdis)
    rw [h1 hωG, h2 hdis]
  · filter_upwards [k2, hmeq, hGiff, hAK] with ω h1 h2 h3 h4 hdis
    have hωG : ω ∈ G := h3.2 (h4 ▸ hdis)
    rw [h1 hωG, h2 hdis]

end Coupling

end WholeField

end InteractingSLE
