/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefRecoveryDense
import InteractingSLE.Spec.Ito.Measurability

/-!
# The ambient recovery, probabilistic part: interior chart coordinates converge to every ambient pairing

Packet PROVE-LEMMA725REF5. Specification §7.4, Aux. lemma 125's proof (`source/spec/p385-432.md` L197–L250, p. 398);
Astra's shortcut note, Proposition 2.1 step 3 (`source/external/AstraIG1/ig1_shortcuts_audited.txt` L276–L285): "The
Gaussian isometry recovers each ambient test pairing from these interior coordinates as an `L²` limit. Countable
determining tests and the measurable subsequence construction on p. 398 give a Borel recovery map."

Let `X` be, conditionally on `𝓦`, a zero-boundary GFF on a random open `U_ω ⊆ ℍ` (`IsCondZeroBoundaryGFF P 𝓦 U X`),
and let `c` be a `𝓦`-measurable random conformal chart with `U_ω ⊆ dom c_ω` on a `𝓦`-event `A`. For a test function
`φ` on `ℍ`:

* the error tests `T_k(ω) = φ − pushTest_ω g_k` (on `A`; `0` off `A`) are `𝓦`-measurable random test functions, and
  `X(T_k)` is conditionally centred Gaussian with variance `Cov_{U_ω}(T_k(ω), T_k(ω))`
  (`RandomTest.condExp_cexp_apply_ae_eq`);
* a `𝓦`-measurable version `condVarVer` of this variance is read off the conditional characteristic function;
* a `𝓦`-measurable selection `J_n(ω)` (`Nat.find`) picks a generator with variance `< 16⁻ⁿ`, which exists by the
  density lemma `exists_genTest_pushTest_cov_lt`;
* `E[X(T_{J_n})²] ≤ 4 · 16⁻ⁿ` (`LocalExt.lintegral_sq_le_of_condCharFun`) and Borel–Cantelli give
  **`exists_ae_tendsto_pushTest`**: almost surely on `A`, `X(pushTest_ω g_{J_n(ω)}) → X(φ)`.

Conditional helper; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped ENNReal
open QuantumZipper (H isOpen_H zeroGFFTestCov)
open QuantumZipper.Thm11Asm (covVec)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Sec7.Lemma725RefRecovery

open LocalSets LocalExt Chart

/-! ### The countable family indexed by `ℕ` -/

/-- The generators of `𝒟'(ℍ)`, indexed by `ℕ` through `Nat.unpair`. -/
abbrev genIdx (k : ℕ) : TestOn upperHalfPlaneOpens := genTest (Nat.unpair k)

theorem exists_genIdx_pushTest_cov_lt {c : Chart} (hc : c.IsConformal) {U : Set ℂ} (hUo : IsOpen U)
    (hUd : U ⊆ c.dom) (φ : TestOn upperHalfPlaneOpens) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, zeroGFFTestCov U ⇑(φ - pushTest hc (genIdx k)) ⇑(φ - pushTest hc (genIdx k)) < ε := by
  obtain ⟨j, hj⟩ := exists_genTest_pushTest_cov_lt hc hUo hUd φ hε
  refine ⟨Nat.pair j.1 j.2, ?_⟩
  simp only [genIdx, Nat.unpair_pair]
  exact hj

theorem zeroGFFTestCov_zero_zero {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) :
    zeroGFFTestCov V ⇑(0 : TestOn upperHalfPlaneOpens) ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := by
  have h0 : covVec V ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := by
    have := covVec_sub hV hVH (0 : TestOn upperHalfPlaneOpens) 0
    rw [sub_self, sub_self] at this
    exact this
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, h0, inner_zero_left]

/-! ### Borel–Cantelli for summable second moments -/

section BorelCantelli

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **Summable second moments give almost sure convergence**: if `E[D_n²] ≤ 4 · 16⁻ⁿ`, then `D_n → 0` almost surely
(`Σ 4ⁿ D_n²` has finite integral). -/
theorem ae_tendsto_zero_of_lintegral_sq_le {D : ℕ → Ω → ℝ} (hD : ∀ n, Measurable (D n))
    (hb : ∀ n, ∫⁻ ω, ENNReal.ofReal (D n ω ^ 2) ∂P ≤ ENNReal.ofReal (4 * (1 / 16 : ℝ) ^ n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => D n ω) atTop (𝓝 0) := by
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((4 : ℝ) ^ n * D n ω ^ 2) with hf
  have hfm : ∀ n, Measurable (f n) := fun n => ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((hD n).pow_const 2))
  have hfi : ∀ n, ∫⁻ ω, f n ω ∂P ≤ ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) := fun n => by
    have e : ∀ ω, f n ω = ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (D n ω ^ 2) := fun ω => by
      show ENNReal.ofReal ((4 : ℝ) ^ n * D n ω ^ 2) = _
      rw [ENNReal.ofReal_mul (by positivity)]
    have hm : Measurable fun ω => ENNReal.ofReal (D n ω ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hD n).pow_const 2)
    simp_rw [e]
    rw [lintegral_const_mul _ hm]
    calc ENNReal.ofReal ((4 : ℝ) ^ n) * ∫⁻ ω, ENNReal.ofReal (D n ω ^ 2) ∂P
        ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (4 * (1 / 16 : ℝ) ^ n) := by gcongr; exact hb n
      _ = ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (1 / 16 : ℝ) = (1 / 4) * (1 / 4) by norm_num, mul_pow,
            show (1 / 4 : ℝ) ^ n = ((4 : ℝ) ^ n)⁻¹ by rw [one_div, inv_pow]]
          field_simp
  have hsum : ∑' n, ENNReal.ofReal (4 * (1 / 4 : ℝ) ^ n) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4)]
    exact ENNReal.ofReal_ne_top
  have hint : ∫⁻ ω, ∑' n, f n ω ∂P ≠ ∞ := by
    rw [lintegral_tsum fun n => (hfm n).aemeasurable]
    exact ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum hfi)
  filter_upwards [ae_lt_top (Measurable.tsum hfm) hint] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun n => (4 : ℝ) ^ n * D n ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simp only [ENNReal.toReal_zero] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply, hf]
    exact ENNReal.toReal_ofReal (by positivity)
  have h3 : Tendsto (fun n => Real.sqrt ((4 : ℝ) ^ n * D n ω ^ 2)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    rwa [Real.sqrt_zero] at this
  refine squeeze_zero_norm (fun n => ?_) h3
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  have h4 : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
  nlinarith [sq_nonneg (D n ω)]

end BorelCantelli

/-! ### Random error tests and the conditional variance -/

section Defs

variable {Ω : Type*}

/-- **A `𝓦`-measurable version of the conditional variance** `Cov_{U_ω}(T(ω), T(ω))`, read off the conditional
characteristic function. -/
def condVarVer (𝓦 : MeasurableSpace Ω) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (T : Ω → TestOn upperHalfPlaneOpens) (ω : Ω) : ℝ :=
  -2 * Real.log ((P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝓦] ω).re)

end Defs


section Core

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The random error test** `φ − pushTest_ω g_k` on `A`, `0` off `A`. -/
def errTest (A : Set Ω) (c : Ω → Chart) (hc : ∀ ω, (c ω).IsConformal) (φ : TestOn upperHalfPlaneOpens) (k : ℕ)
    (ω : Ω) : TestOn upperHalfPlaneOpens :=
  A.indicator (fun ω => φ - pushTest (hc ω) (genIdx k)) ω

omit mΩ in
theorem errTest_of_mem {A : Set Ω} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (φ : TestOn upperHalfPlaneOpens) (k : ℕ) {ω : Ω} (hω : ω ∈ A) :
    errTest A c hc φ k ω = φ - pushTest (hc ω) (genIdx k) := indicator_of_mem hω _

omit mΩ in
theorem errTest_of_notMem {A : Set Ω} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (φ : TestOn upperHalfPlaneOpens) (k : ℕ) {ω : Ω} (hω : ω ∉ A) : errTest A c hc φ k ω = 0 :=
  indicator_of_notMem hω _

omit mΩ in
theorem measurable_errTest_apply {A : Set Ω} (hA : MeasurableSet[𝓦] A) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (φ : TestOn upperHalfPlaneOpens) (k : ℕ) (z : ℂ) : Measurable[𝓦] fun ω => errTest A c hc φ k ω z := by
  have e : (fun ω => errTest A c hc φ k ω z) =
      A.indicator (fun ω => φ z - pushTest (hc ω) (genIdx k) z) := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [errTest_of_mem hc φ k hω, indicator_of_mem hω]; rfl
    · rw [errTest_of_notMem hc φ k hω, indicator_of_notMem hω]; rfl
  rw [e]
  exact (measurable_const.sub (@measurable_pushTest_apply Ω 𝓦 c hc hdom hfwd (genIdx k) z)).indicator hA

/-- **The conditional characteristic function at a `𝓦`-measurable random test function** of a conditional
zero-boundary GFF on `U_ω` (`RandomTest.condExp_cexp_apply_ae_eq` with the zero-boundary laws `exists_zbExtLaw`). -/
theorem condExp_cexp_apply_random [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H)
    (hcond : IsCondZeroBoundaryGFF P 𝓦 U X) {T : Ω → TestOn upperHalfPlaneOpens}
    (hT : ∀ z, Measurable[𝓦] fun ω => T ω z) :
    P[fun ω => Complex.exp (Complex.I * (X ω (T ω) : ℂ)) | 𝓦] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) (T ω) (T ω)) : ℝ) : ℂ) :=
  RandomTest.condExp_cexp_apply_ae_eq h𝓦 hX
    (Ψ := fun ω φ => ((Real.exp (-(1 / 2) * zeroGFFTestCov (U ω) φ φ) : ℝ) : ℂ))
    (fun ω => RandomTest.exists_zbExtLaw (U := ⟨U ω, hUo ω⟩) (hUH ω)) hcond hT

theorem measurable_condVarVer (X : Ω → DistOn upperHalfPlaneOpens) (T : Ω → TestOn upperHalfPlaneOpens) :
    Measurable[𝓦] (condVarVer 𝓦 P X T) :=
  (Real.measurable_log.comp (Complex.measurable_re.comp stronglyMeasurable_condExp.measurable)).const_mul _

theorem condVarVer_ae_eq [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H)
    (hcond : IsCondZeroBoundaryGFF P 𝓦 U X) {T : Ω → TestOn upperHalfPlaneOpens}
    (hT : ∀ z, Measurable[𝓦] fun ω => T ω z) :
    condVarVer 𝓦 P X T =ᵐ[P] fun ω => zeroGFFTestCov (U ω) (T ω) (T ω) := by
  filter_upwards [condExp_cexp_apply_random h𝓦 hX hUo hUH hcond hT] with ω hω
  rw [condVarVer, hω, Complex.ofReal_re, Real.log_exp]
  ring

end Core

/-! ### The `𝓦`-measurable selection -/

section Select

variable {Ω : Type*}

/-- The selection predicate: `V_k(ω) < ε`, or no index qualifies. -/
def SelPred (V : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) (k : ℕ) : Prop := V k ω < ε ∨ ∀ i, ε ≤ V i ω

theorem exists_selPred (V : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) : ∃ k, SelPred V ε ω k := by
  by_cases h : ∃ i, V i ω < ε
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, Or.inl hi⟩
  · push Not at h
    exact ⟨0, Or.inr h⟩

open Classical in
/-- **The selected index**: the least `k` with `V_k(ω) < ε` (or `0` if there is none). -/
def selIdx (V : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℕ := Nat.find (exists_selPred V ε ω)

open Classical in
theorem measurable_selIdx {𝓦 : MeasurableSpace Ω} {V : ℕ → Ω → ℝ} (hV : ∀ k, Measurable[𝓦] (V k)) (ε : ℝ) :
    Measurable[𝓦] (selIdx V ε) := by
  refine @measurable_find Ω 𝓦 (SelPred V ε) _ (exists_selPred V ε) fun k => ?_
  have e : {ω | SelPred V ε ω k} = {ω | V k ω < ε} ∪ ⋂ i, {ω | ε ≤ V i ω} := by
    ext ω
    simp only [SelPred, mem_ofPred_eq, mem_union, mem_iInter]
  rw [e]
  exact (measurableSet_lt (hV k) measurable_const).union
    (MeasurableSet.iInter fun i => measurableSet_le measurable_const (hV i))

theorem selIdx_spec {V : ℕ → Ω → ℝ} {ε : ℝ} {ω : Ω} (h : ∃ i, V i ω < ε) : V (selIdx V ε ω) ω < ε := by
  classical
  have hs : SelPred V ε ω (selIdx V ε ω) := by
    unfold selIdx
    convert Nat.find_spec (exists_selPred V ε ω)
  rcases hs with h1 | h2
  · exact h1
  · obtain ⟨i, hi⟩ := h
    exact absurd (h2 i) (not_le.2 hi)

end Select

/-! ### Interior chart coordinates converge to every ambient pairing -/

section Converge

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The ambient recovery's convergence** (p. 398, Astra's Proposition 2.1 step 3). Let `X` be, conditionally on
`𝓦`, a zero-boundary GFF on the random open `U_ω ⊆ ℍ`, and `c` a `𝓦`-measurable random conformal chart with
`U_ω ⊆ dom c_ω` on the `𝓦`-event `A`. For every test function `φ` on `ℍ` there are `𝓦`-measurable indices `J_n` such
that almost surely on `A`, `X(pushTest_ω g_{J_n(ω)}) → X(φ)`. -/
theorem exists_ae_tendsto_pushTest [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) {U : Ω → Set ℂ} (hUo : ∀ ω, IsOpen (U ω))
    (hUH : ∀ ω, U ω ⊆ H) (hUA : ∀ ω ∈ A, U ω ⊆ (c ω).dom) (hcond : IsCondZeroBoundaryGFF P 𝓦 U X)
    (φ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℕ → Ω → ℕ, (∀ n, Measurable[𝓦] (J n)) ∧
      ∀ᵐ ω ∂P, ω ∈ A → Tendsto (fun n => X ω (pushTest (hc ω) (genIdx (J n ω)))) atTop (𝓝 (X ω φ)) := by
  set T : ℕ → Ω → TestOn upperHalfPlaneOpens := fun k => errTest A c hc φ k with hTdef
  have hT : ∀ k z, Measurable[𝓦] fun ω => T k ω z := fun k z => measurable_errTest_apply hA hc hdom hfwd φ k z
  set V : ℕ → Ω → ℝ := fun k => condVarVer 𝓦 P X (T k) with hVdef
  have hVm : ∀ k, Measurable[𝓦] (V k) := fun k => measurable_condVarVer X (T k)
  have hVe : ∀ᵐ ω ∂P, ∀ k, V k ω = zeroGFFTestCov (U ω) (T k ω) (T k ω) :=
    ae_all_iff.2 fun k => condVarVer_ae_eq h𝓦 hX hUo hUH hcond (hT k)
  have hex : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ k, V k ω < (1 / 16 : ℝ) ^ n := by
    filter_upwards [hVe] with ω hω n
    by_cases hωA : ω ∈ A
    · obtain ⟨k, hk⟩ := exists_genIdx_pushTest_cov_lt (hc ω) (hUo ω) (hUA ω hωA) φ (ε := (1 / 16 : ℝ) ^ n)
        (by positivity)
      refine ⟨k, ?_⟩
      rw [hω k, hTdef]
      simp only
      rw [errTest_of_mem hc φ k hωA]
      exact hk
    · refine ⟨0, ?_⟩
      rw [hω 0, hTdef]
      simp only
      rw [errTest_of_notMem hc φ 0 hωA, zeroGFFTestCov_zero_zero (hUo ω) (hUH ω)]
      positivity
  set J : ℕ → Ω → ℕ := fun n => selIdx V ((1 / 16 : ℝ) ^ n) with hJdef
  have hJm : ∀ n, Measurable[𝓦] (J n) := fun n => measurable_selIdx hVm _
  have hJ : ∀ᵐ ω ∂P, ∀ n, V (J n ω) ω < (1 / 16 : ℝ) ^ n := by
    filter_upwards [hex] with ω hω n
    exact selIdx_spec (hω n)
  -- the selected error tests
  set S : ℕ → Ω → TestOn upperHalfPlaneOpens := fun n ω => T (J n ω) ω with hSdef
  have hS : ∀ n z, Measurable[𝓦] fun ω => S n ω z := fun n z =>
    @Ito.measurable_comp_index Ω ℝ 𝓦 _ (fun ω k => T k ω z) (fun k => hT k z) (J n) (hJm n)
  set D : ℕ → Ω → ℝ := fun n ω => X ω (S n ω) with hDdef
  have hDm : ∀ n, Measurable (D n) := fun n =>
    RandomTest.measurable_apply_of_forall_measurable hX fun z => (hS n z).mono h𝓦 le_rfl
  set W : ℕ → Ω → ℝ := fun n ω => V (J n ω) ω with hWdef
  have hWm : ∀ n, Measurable (W n) := fun n =>
    (@Ito.measurable_comp_index Ω ℝ 𝓦 _ (fun ω k => V k ω) (fun k => hVm k) (J n) (hJm n)).mono h𝓦 le_rfl
  have hWe : ∀ n, ∀ᵐ ω ∂P, W n ω = zeroGFFTestCov (U ω) (S n ω) (S n ω) := fun n => by
    filter_upwards [hVe] with ω hω
    exact hω (J n ω)
  have hD2 : ∀ n, ∫⁻ ω, ENNReal.ofReal (D n ω ^ 2) ∂P ≤ ENNReal.ofReal (4 * (1 / 16 : ℝ) ^ n) := by
    intro n
    refine lintegral_sq_le_of_condCharFun h𝓦 (hDm n) (hWm n) ?_ (fun t => ?_) (by positivity) ?_
    · filter_upwards [hWe n] with ω hω
      rw [hω]
      exact zeroGFFTestCov_self_nonneg (hUo ω) (hUH ω) _
    · have hTt : ∀ z, Measurable[𝓦] fun ω => (t • S n ω) z := fun z => by
        simpa only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul] using (hS n z).const_mul t
      have key := condExp_cexp_apply_random h𝓦 hX hUo hUH hcond hTt
      have e1 : (fun ω => Complex.exp (Complex.I * ((t * D n ω : ℝ) : ℂ))) =
          fun ω => Complex.exp (Complex.I * (X ω (t • S n ω) : ℂ)) := by
        funext ω
        rw [map_smul, smul_eq_mul]
      rw [e1]
      refine key.trans ?_
      filter_upwards [hWe n] with ω hω
      rw [zeroGFFTestCov_smul_left (hUo ω) (hUH ω), zeroGFFTestCov_smul_right (hUo ω) (hUH ω), ← hω]
      congr 3
      ring
    · filter_upwards [hJ] with ω hω
      exact (hω n).le
  have hlim := ae_tendsto_zero_of_lintegral_sq_le hDm hD2
  refine ⟨J, hJm, ?_⟩
  filter_upwards [hlim] with ω hω hωA
  have e : ∀ n, X ω (pushTest (hc ω) (genIdx (J n ω))) = X ω φ - D n ω := fun n => by
    simp only [hDdef, hSdef, hTdef]
    rw [errTest_of_mem hc φ _ hωA, map_sub]
    ring
  simp_rw [e]
  simpa using (tendsto_const_nhds (x := X ω φ)).sub hω

end Converge

end InteractingSLE.Sec7.Lemma725RefRecovery
