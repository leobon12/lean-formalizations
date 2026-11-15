import InteractingSLE.GFF.LocalSets.PointVariance

/-!
# Boundary vanishing of the harmonic projection (specification Proposition 3.3)

Source: `source/ig1-specification.pdf`, §3.1, Proposition 3.3 and its proof (pp. 44–45;
transcription `source/spec/p001-048.md#prop-3.3`, `#prop-3.3-proof`): for a simply connected
domain `D ≠ ℂ`, a deterministic relatively closed `K ⊆ D`, and the harmonic function `h₁` on
`D ∖ K` representing the projection of the zero-boundary GFF `h` onto `H^⊥(D ∖ K)`, almost surely
`h₁(z) → 0` as `z → z₀` for every `z₀ ∈ ∂D ∖ cl K`.

Here `U = D ∖ K` is an open subset of `D`, and the projection is the harmonic part `h − h_U` of
any Markov decomposition `IsMarkovDecomposition U D h h_U P` (Proposition 3.1).

## Route (the source's, with two simplifications)

1. Pointwise exponential moments `E e^{λ h₁(y)} ≤ e^{2 λ² t(y)}` with `t(y) → 0` as
   `dist(y, ∂D) → 0` at fixed distance from `K` (`PointVariance.lean`; replaces the
   killed-Brownian-motion identity and the Gaussian `p`-th moments of the source).
2. Instead of Whitney squares, the dyadic layers `Aₙ = {2^{-n-1} ≤ dist(·, ∂D) ≤ 2^{-n}}` of a
   patch:
   by Jensen's inequality and the mean value property against a radial bump of radius
   `εₙ = 2^{-n-2}`, `sup_{Aₙ} e^{±λ h₁} ≤ C 4ⁿ ∫_{Nₙ} e^{±λ h₁}` for a slightly larger layer `Nₙ`
   (`ofReal_exp_mul_le_lintegral_of_harmonic`); Tonelli (for a jointly measurable version,
   `exists_measurable_harmonic_version`) and Markov's inequality with `λₙ = n log 8 / η` give
   `P(sup_{Aₙ} |h₁| ≥ η) ≤ C 2^{-n}`; Borel–Cantelli.
3. A countable cover of `∂D ∖ cl K` by patches.

## Main results

* `exp_mul_le_setIntegral_of_harmonic`: Jensen's inequality for `e^{λ g}`, `g` harmonic;
* `exists_measurable_harmonic_version`: a jointly measurable version of the harmonic part;
* `lintegral_exp_version_le`: its exponential moments;
* `ae_eventually_abs_lt`: Borel–Cantelli on the dyadic layers of a patch;
* `ae_tendsto_markov_sub_frontier`: **Proposition 3.3** (for any Markov decomposition);
* `ae_tendsto_harmonic_frontier`: Proposition 3.3 in the source's form (`K = D ∖ U`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric TopologicalSpace MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace InteractingSLE
namespace GFF

/-- A function continuous on an open neighbourhood of `B̄(w, δ)`, times the bump at `w`, is
continuous on `ℂ`. -/
lemma continuous_mul_bumpFun {V : Set ℂ} (hV : IsOpen V) {F : ℂ → ℝ} (hF : ContinuousOn F V)
    {w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hB : closedBall w δ ⊆ V) :
    Continuous fun y => F y * bumpFun w δ y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ closedBall w δ
  · exact ((hF y (hB hy)).continuousAt (hV.mem_nhds (hB hy))).mul
      (contDiff_bumpFun w δ).continuous.continuousAt
  · have hev : (fun y => F y * bumpFun w δ y) =ᶠ[𝓝 y] fun _ => 0 := by
      have : (closedBall w δ)ᶜ ∈ 𝓝 y := isClosed_closedBall.isOpen_compl.mem_nhds hy
      filter_upwards [this] with z hz
      rw [mem_compl_iff, mem_closedBall, not_le] at hz
      rw [bumpFun_eq_zero hδ hz.le, mul_zero]
    exact (continuousAt_congr hev).2 continuousAt_const

/-- **Jensen's inequality for the exponential of a harmonic function** (mean value property against
the radial bump): `e^{λ g(w)} δ² ∫ e(1 − |y|²) ≤ e(1) ∫_{B̄(w, δ)} e^{λ g}`. -/
theorem exp_mul_le_setIntegral_of_harmonic {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V) {w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall w δ ⊆ V) (lam : ℝ) :
    Real.exp (lam * g w) * (δ ^ 2 * bumpMass) ≤
      expNegInvGlue 1 * ∫ y in closedBall w δ, Real.exp (lam * g y) := by
  have hgc : ContinuousOn g V := fun y hy => (hg y hy).1.continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun y => Real.exp (lam * g y)) V :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgc))
  set b := bumpFun w δ with hb
  have hbc : Continuous b := (contDiff_bumpFun w δ).continuous
  have hbs : HasCompactSupport b := hasCompactSupport_bumpFun hδ
  have hbi : Integrable b := hbc.integrable_of_hasCompactSupport hbs
  have hgbi : Integrable fun y => g y * b y :=
    (continuous_mul_bumpFun hV hgc hδ hB).integrable_of_hasCompactSupport
      (hbs.mul_left)
  have hEbi : Integrable fun y => Real.exp (lam * g y) * b y :=
    (continuous_mul_bumpFun hV hEc hδ hB).integrable_of_hasCompactSupport (hbs.mul_left)
  have hmv := integral_mul_bumpFun_of_harmonic hV hg hδ hB
  have hI := integral_bumpFun (x := w) hδ
  set m := g w
  set E := Real.exp (lam * m)
  -- tangent line
  have htan : ∀ y, E * ((1 - lam * m) * b y + lam * (g y * b y)) ≤
      Real.exp (lam * g y) * b y := by
    intro y
    have h1 : lam * (g y - m) + 1 ≤ Real.exp (lam * (g y - m)) := Real.add_one_le_exp _
    have h2 : Real.exp (lam * g y) = E * Real.exp (lam * (g y - m)) := by
      rw [← Real.exp_add]; ring_nf
    rw [h2]
    have hb0 := bumpFun_nonneg w δ y
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc E * ((1 - lam * m) * b y + lam * (g y * b y)) = E * ((lam * (g y - m) + 1) * b y) := by
          ring
      _ ≤ E * (Real.exp (lam * (g y - m)) * b y) := by gcongr
      _ = E * Real.exp (lam * (g y - m)) * b y := by ring
  have hlow : E * (δ ^ 2 * bumpMass) ≤ ∫ y, Real.exp (lam * g y) * b y := by
    have hint : ∫ y, E * ((1 - lam * m) * b y + lam * (g y * b y)) =
        E * (δ ^ 2 * bumpMass) := by
      rw [integral_const_mul, integral_add (hbi.const_mul _) (hgbi.const_mul _),
        integral_const_mul, integral_const_mul, hI, hmv]
      ring
    rw [← hint]
    exact integral_mono ((hbi.const_mul _).add (hgbi.const_mul _) |>.const_mul _) hEbi htan
  have hup : ∫ y, Real.exp (lam * g y) * b y ≤
      expNegInvGlue 1 * ∫ y in closedBall w δ, Real.exp (lam * g y) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall w δ) (fun y hy => by
      rw [mem_closedBall, not_le] at hy
      rw [hb, bumpFun_eq_zero hδ hy.le, mul_zero]), ← integral_const_mul]
    have hEi : IntegrableOn (fun y => Real.exp (lam * g y)) (closedBall w δ) :=
      (hEc.mono hB).integrableOn_compact (isCompact_closedBall w δ)
    refine setIntegral_mono_on hEbi.integrableOn (hEi.const_mul _) measurableSet_closedBall
      fun y _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (bumpFun_le w δ y) (Real.exp_pos _).le
  exact hlow.trans hup

/-- The `ℝ≥0∞` form over any measurable `N ⊇ B̄(w, δ)`. -/
theorem ofReal_exp_mul_le_lintegral_of_harmonic {V : Set ℂ} (hV : IsOpen V) {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V) {w : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall w δ ⊆ V) (lam : ℝ) {N : Set ℂ} (hBN : closedBall w δ ⊆ N) :
    ENNReal.ofReal (Real.exp (lam * g w) * (δ ^ 2 * bumpMass)) ≤
      ENNReal.ofReal (expNegInvGlue 1) * ∫⁻ y in N, ENNReal.ofReal (Real.exp (lam * g y)) := by
  have hgc : ContinuousOn g V := fun y hy => (hg y hy).1.continuousAt.continuousWithinAt
  have hEc : ContinuousOn (fun y => Real.exp (lam * g y)) V :=
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hgc))
  have hEi : IntegrableOn (fun y => Real.exp (lam * g y)) (closedBall w δ) :=
    (hEc.mono hB).integrableOn_compact (isCompact_closedBall w δ)
  refine (ENNReal.ofReal_le_ofReal (exp_mul_le_setIntegral_of_harmonic hV hg hδ hB lam)).trans ?_
  rw [ENNReal.ofReal_mul (expNegInvGlue.nonneg _),
    ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall fun y => (Real.exp_pos _).le)]
  gcongr


open LQGMetric (TestOn DistOn IsZeroBoundaryGFF measurable_distOn_apply)

/-- `g` is a harmonic representative of the distribution `T` on `U`. -/
def IsHarmRep (U : Opens ℂ) (T : DistOn U) (g : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd g U ∧ ∀ φ : TestOn U, T φ = ∫ x, g x * φ x

lemma testIncl_bumpTest {U D : Opens ℂ} (hUD : U ≤ D) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall x δ ⊆ U) :
    testIncl U D (bumpTest x hδ hB) = bumpTest x hδ (hB.trans hUD) := by
  apply DFunLike.coe_injective
  rw [coe_testIncl hUD]; rfl

/-- Pairing a distribution with a harmonic representative against a bump gives the point value. -/
lemma apply_bumpTest_of_isHarmRep {U D : Opens ℂ} (hUD : U ≤ D) {Y : DistOn D} {g : ℂ → ℝ}
    (hg : IsHarmRep U (restrictDist U Y) g) {x : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hB : closedBall x δ ⊆ U) :
    Y (bumpTest x hδ (hB.trans hUD)) = g x * (δ ^ 2 * bumpMass) := by
  rw [← testIncl_bumpTest hUD x hδ hB, ← restrictDist_apply, hg.2, coe_bumpTest]
  exact integral_mul_bumpFun_of_harmonic U.isOpen hg.1 hδ hB

/-- **A jointly measurable version of the harmonic part.** If almost surely the restriction of the
random distribution `Y` to `U` has a harmonic representative, there are a measurable full-measure
set `S` of such outcomes and a jointly measurable `G : Ω × ℂ → ℝ` equal, for `ω ∈ S`, to every
harmonic representative on `U`. -/
theorem exists_measurable_harmonic_version {U D : Opens ℂ} (hUD : U ≤ D) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → DistOn D} (hY : Measurable Y)
    (hae : ∀ᵐ ω ∂P, ∃ g, IsHarmRep U (restrictDist U (Y ω)) g) :
    ∃ (S : Set Ω) (G : Ω × ℂ → ℝ), MeasurableSet S ∧ P Sᶜ = 0 ∧ Measurable G ∧
      (∀ ω ∈ S, ∃ g, IsHarmRep U (restrictDist U (Y ω)) g) ∧
      (∀ ω ∈ S, ∀ g, IsHarmRep U (restrictDist U (Y ω)) g → ∀ y ∈ (U : Set ℂ), G (ω, y) = g y) := by
  classical
  set S₀ : Set Ω := {ω | ∃ g, IsHarmRep U (restrictDist U (Y ω)) g} with hS₀
  set S : Set Ω := (toMeasurable P S₀ᶜ)ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hPS : P Sᶜ = 0 := by
    rw [hSdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  have hSS₀ : S ⊆ S₀ := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P S₀ᶜ h)
  have hex : ∀ x : U, ∃ δ : ℝ, 0 < δ ∧ closedBall (x : ℂ) δ ⊆ U := fun x => by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 U.isOpen x x.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩
  choose rad hrad0 hradU using hex
  let Gsub : U → Ω → ℝ := fun x => S.indicator fun ω =>
    Y ω (bumpTest (x : ℂ) (hrad0 x) ((hradU x).trans hUD)) / (rad x ^ 2 * bumpMass)
  have hval : ∀ ω ∈ S, ∀ g, IsHarmRep U (restrictDist U (Y ω)) g → ∀ x : U, Gsub x ω = g x := by
    intro ω hω g hg x
    simp only [Gsub, indicator_of_mem hω]
    rw [apply_bumpTest_of_isHarmRep hUD hg (hrad0 x) (hradU x)]
    have : 0 < rad x ^ 2 * bumpMass := by have := bumpMass_pos; have := hrad0 x; positivity
    exact mul_div_cancel_right₀ _ this.ne'
  have hcont : ∀ ω, Continuous fun x : U => Gsub x ω := by
    intro ω
    by_cases hω : ω ∈ S
    · obtain ⟨g, hg⟩ := hSS₀ hω
      have hgc : ContinuousOn g U := fun y hy => (hg.1 y hy).1.continuousAt.continuousWithinAt
      have e : (fun x : U => Gsub x ω) = fun x : U => g x := funext (hval ω hω g hg)
      rw [e]
      exact hgc.domRestrict
    · have e : (fun x : U => Gsub x ω) = fun _ => 0 := funext fun x => by
        simp only [Gsub, indicator_of_notMem hω]
      rw [e]; exact continuous_const
  have hmeas : ∀ x : U, Measurable (Gsub x) := fun x =>
    (((measurable_distOn_apply _).comp hY).div_const _).indicator hSm
  have hJ : Measurable (Function.uncurry Gsub) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  set s : Set (Ω × ℂ) := Prod.snd ⁻¹' (U : Set ℂ) with hs
  have hsm : MeasurableSet s := measurable_snd U.isOpen.measurableSet
  let G : Ω × ℂ → ℝ := fun p => if hp : p ∈ s then Gsub ⟨p.2, hp⟩ p.1 else 0
  have hGm : Measurable G := by
    refine Measurable.dite (f := fun q : s => Gsub ⟨q.1.2, q.2⟩ q.1.1) ?_ measurable_const hsm
    exact hJ.comp ((Measurable.subtype_mk (measurable_snd.comp measurable_subtype_coe)).prodMk
      (measurable_fst.comp measurable_subtype_coe))
  refine ⟨S, G, hSm, hPS, hGm, fun ω hω => hSS₀ hω, fun ω hω g hg y hy => ?_⟩
  have hys : (ω, y) ∈ s := hy
  simp only [G, hys, dite_true]
  exact hval ω hω g hg ⟨y, hy⟩


open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)

/-- **Exponential moment of the harmonic version at a point.** -/
theorem lintegral_exp_version_le {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) {S : Set Ω} {G : Ω × ℂ → ℝ} (hPS : P Sᶜ = 0)
    (hSrep : ∀ ω ∈ S, ∃ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g)
    (hG : ∀ ω ∈ S, ∀ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g →
      ∀ y ∈ (U : Set ℂ), G (ω, y) = g y)
    {y : ℂ} (hy : y ∈ D) {R : ℝ} (hR : 0 < R) (hRU : ∀ z ∈ D, dist z y < R → z ∈ U)
    (ht : koebeScale D y R ≤ 1 / 4) (lam : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (lam * G (ω, y))) ∂P ≤
      ENNReal.ofReal (Real.exp (2 * lam ^ 2 * koebeScale D y R)) := by
  obtain ⟨δ, hδ, hB, hmgf⟩ := exists_lintegral_exp_bump_le hUD hDc hDs hDne hh hd hy hR hRU ht
  have hyU : y ∈ (U : Set ℂ) := hB (mem_closedBall_self hδ.le)
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hmgf lam)
  have hSae : S ∈ ae P := mem_ae_iff.2 hPS
  filter_upwards [hSae] with ω hω
  obtain ⟨g, hg⟩ := hSrep ω hω
  rw [hG ω hω g hg y hyU, apply_bumpTest_of_isHarmRep hUD hg hδ hB]
  have : 0 < δ ^ 2 * bumpMass := by have := bumpMass_pos; positivity
  rw [mul_div_cancel_right₀ _ this.ne']

/-- The Koebe scale is monotone in the distance to the boundary. -/
lemma koebeScale_le {D : Set ℂ} {x : ℂ} {R a : ℝ} (hR : 0 < R) (hx : infDist x Dᶜ ≤ a) :
    koebeScale D x R ≤ (2 * a / (koebeCovConst * R)) ^ koebeDistExp⁻¹ := by
  have hc := koebeCovConst_pos
  have h0 := infDist_nonneg (x := x) (s := Dᶜ)
  exact Real.rpow_le_rpow (by positivity) (by gcongr) (inv_nonneg.2 koebeDistExp_pos.le)

/-- **Choice of the parameters.** For `R, η > 0`, eventually in `n`:
`(1/2)^(n+2) ≤ R`, `τₙ ≤ 1/4` and `2 λₙ² τₙ ≤ 1`, where `τₙ = (2 · 2 (1/2)^n / (c R))^(1/C₂)` and
`λₙ = n log 8 / η`. -/
lemma eventually_params {R : ℝ} (hR : 0 < R) (η : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) ^ (n + 2) ≤ R ∧
      (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4 ∧
      2 * ((n : ℝ) * Real.log 8 / η) ^ 2 *
        (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 := by
  have hc := koebeCovConst_pos
  have hC := koebeDistExp_pos
  set A := (4 / (koebeCovConst * R)) ^ koebeDistExp⁻¹ with hA
  set q := (1 / 2 : ℝ) ^ koebeDistExp⁻¹ with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.2 hC)
  have hτ : ∀ n : ℕ, (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ =
      A * q ^ n := by
    intro n
    have e : 2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R) =
        4 / (koebeCovConst * R) * (1 / 2 : ℝ) ^ n := by ring
    rw [e, Real.mul_rpow (by positivity) (by positivity), hA, hq,
      Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp_rw [hτ]
  have t1 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (Filter.tendsto_add_atTop_nat 2)
  have t2 : Filter.Tendsto (fun n : ℕ => A * q ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul A
  have t3 : Filter.Tendsto (fun n : ℕ => 2 * ((n : ℝ) * Real.log 8 / η) ^ 2 * (A * q ^ n))
      Filter.atTop (nhds 0) := by
    have := (tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 (by rwa [abs_of_nonneg hq0])).const_mul
      (2 * (Real.log 8 / η) ^ 2 * A)
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    ring
  exact ((t1.eventually (ge_mem_nhds hR)).and (t2.eventually (ge_mem_nhds (by norm_num)))).and
    (t3.eventually (ge_mem_nhds one_pos)) |>.mono fun n hn => ⟨hn.1.1, hn.1.2, hn.2⟩


/-! ### Borel–Cantelli on dyadic layers and Proposition 3.3 -/


/-- The dyadic layer `{y ∈ D ∩ B(c, 3R) : 2^{-n-2} ≤ dist(y, ∂D) ≤ 2 · 2^{-n}}` of a patch. -/
def layerSet (D : Set ℂ) (c : ℂ) (R : ℝ) (n : ℕ) : Set ℂ :=
  D ∩ ball c (3 * R) ∩ {y | (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y Dᶜ} ∩
    {y | infDist y Dᶜ ≤ 2 * (1 / 2 : ℝ) ^ n}

lemma measurableSet_layerSet {D : Set ℂ} (hD : IsOpen D) (c : ℂ) (R : ℝ) (n : ℕ) :
    MeasurableSet (layerSet D c R n) :=
  ((hD.measurableSet.inter measurableSet_ball).inter
    (measurableSet_le measurable_const (continuous_infDist_pt _).measurable)).inter
    (measurableSet_le (continuous_infDist_pt _).measurable measurable_const)

lemma layerSet_subset_ball (D : Set ℂ) (c : ℂ) (R : ℝ) (n : ℕ) :
    layerSet D c R n ⊆ ball c (3 * R) := fun _ hy => hy.1.1.2

/-- The bump ball around a point of the inner layer lies in the outer layer. -/
lemma closedBall_subset_layerSet {D : Set ℂ} {c w : ℂ} {R : ℝ} {n : ℕ}
    (hnR : (1 / 2 : ℝ) ^ (n + 2) ≤ R) (hwc : dist w c < 2 * R)
    (h1 : (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w Dᶜ) (h2 : infDist w Dᶜ ≤ (1 / 2 : ℝ) ^ n) :
    closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ layerSet D c R n := by
  intro y hy
  rw [mem_closedBall] at hy
  set ε := (1 / 2 : ℝ) ^ (n + 2) with hε
  have hε0 : 0 < ε := by positivity
  have e1 : (1 / 2 : ℝ) ^ (n + 1) = 2 * ε := by rw [hε, pow_succ, pow_succ]; ring
  have e2 : (1 / 2 : ℝ) ^ n = 4 * ε := by rw [hε, pow_succ, pow_succ]; ring
  have l1 := infDist_le_infDist_add_dist (x := w) (y := y) (s := Dᶜ)
  have l2 := infDist_le_infDist_add_dist (x := y) (y := w) (s := Dᶜ)
  rw [dist_comm] at l1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · by_contra hyD
    have := infDist_le_dist_of_mem (x := w) (show y ∈ Dᶜ from hyD)
    rw [dist_comm] at this
    linarith
  · rw [mem_ball]
    have := dist_triangle y w c
    linarith
  · show ε ≤ infDist y Dᶜ
    linarith
  · show infDist y Dᶜ ≤ 2 * (1 / 2 : ℝ) ^ n
    linarith

lemma layerSet_subset {D U : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcR : ∀ y ∈ D, dist y c < 4 * R → y ∈ U) (n : ℕ) : layerSet D c R n ⊆ U :=
  fun y hy => hcR y hy.1.1.1 (by have := hy.1.1.2; rw [mem_ball] at this; linarith)

/-- **Expected layer integral.** -/
theorem lintegral_layer_le {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) {S : Set Ω} {G : Ω × ℂ → ℝ} (hPS : P Sᶜ = 0)
    (hGm : Measurable G)
    (hSrep : ∀ ω ∈ S, ∃ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g)
    (hG : ∀ ω ∈ S, ∀ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g →
      ∀ y ∈ (U : Set ℂ), G (ω, y) = g y)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hcR : ∀ y ∈ D, dist y c < 4 * R → y ∈ U) {n : ℕ}
    (hτ : (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4)
    {l : ℝ}
    (hl : 2 * l ^ 2 * (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1) :
    ∫⁻ ω, (∫⁻ y in layerSet D c R n, ENNReal.ofReal (Real.exp (l * G (ω, y)))) ∂P ≤
      ENNReal.ofReal (Real.exp 1) * volume (ball c (3 * R)) := by
  have hm : Measurable fun p : Ω × ℂ => ENNReal.ofReal (Real.exp (l * G p)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hGm))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc ∫⁻ y in layerSet D c R n, ∫⁻ ω, ENNReal.ofReal (Real.exp (l * G (ω, y))) ∂P
      ≤ ∫⁻ _ in layerSet D c R n, ENNReal.ofReal (Real.exp 1) := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        have hyD : y ∈ (D : Set ℂ) := hy.1.1.1
        have hyc : dist y c < 3 * R := hy.1.1.2
        have hRU : ∀ z ∈ D, dist z y < R → z ∈ U := fun z hz hzy =>
          hcR z hz (by have := dist_triangle z y c; linarith)
        have hk := koebeScale_le (D := (D : Set ℂ)) (x := y) hR hy.2
        refine (lintegral_exp_version_le hUD hDc hDs hDne hh hd hPS hSrep hG hyD hR hRU
          (hk.trans hτ) l).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 2 * l ^ 2)
        linarith
    _ = ENNReal.ofReal (Real.exp 1) * volume (layerSet D c R n) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (Real.exp 1) * volume (ball c (3 * R)) := by
        gcongr; exact layerSet_subset_ball _ _ _ _


lemma eight_pow_mul_half_pow_sq (n : ℕ) : (8 : ℝ) ^ n * ((1 / 2 : ℝ) ^ (n + 2)) ^ 2 =
    2 ^ n / 16 := by
  have key : (8 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ 2 = 2 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]; norm_num
  have e2 : ((1 / 2 : ℝ) ^ (n + 2)) ^ 2 = ((1 / 2 : ℝ) ^ n) ^ 2 * (1 / 16) := by
    rw [pow_add]; ring
  rw [e2, ← mul_assoc, key]; ring

/-- **Borel–Cantelli on the dyadic layers of a patch** (proof of Proposition 3.3). Let
`D ∩ B(c, 4R) ⊆ U`. For every `η > 0`, almost surely, for all large `n`, every harmonic
representative `g` of `h − h_U` on `U` satisfies `|g| < η` on the layer
`{w ∈ D ∩ B(c, 2R) : 2^{-n-1} ≤ dist(w, ∂D) ≤ 2^{-n}}`. -/
theorem ae_eventually_abs_lt {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcR : ∀ y ∈ D, dist y c < 4 * R → y ∈ U) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g →
      ∀ w ∈ (D : Set ℂ), dist w c < 2 * R → (1 / 2 : ℝ) ^ (n + 1) ≤ infDist w (D : Set ℂ)ᶜ →
        infDist w (D : Set ℂ)ᶜ ≤ (1 / 2 : ℝ) ^ n → |g w| < η := by
  have hsubm : Measurable fun ω => h ω - hU ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hh.measurable).sub
        ((measurable_distOn_apply φ).comp hd.isZBGFFExtOn.measurable)
  obtain ⟨S, G, hSm, hPS, hGm, hSrep, hG⟩ :=
    exists_measurable_harmonic_version hUD hsubm hd.ae_harmonic
  set lam : ℕ → ℝ := fun n => n * Real.log 8 / η with hlam
  set e₁ := expNegInvGlue 1 with he₁
  set I : ℕ → ℝ → Ω → ℝ≥0∞ := fun n l ω =>
    ∫⁻ y in layerSet D c R n, ENNReal.ofReal (Real.exp (l * G (ω, y))) with hI
  have hIm : ∀ n l, Measurable (I n l) := fun n l =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hGm))).lintegral_prod_right'
  set F : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (Real.exp (lam n * η) *
      (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
      ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)} with hF
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_params hR η)
  -- the probability of a bad layer
  set X : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1) * volume (ball c (3 * R)) with hX
  set K : ℝ≥0∞ := ENNReal.ofReal e₁ * (X + X) / ENNReal.ofReal (bumpMass / 16) with hK
  have hc₁ := bumpMass_pos
  have hPF : ∀ n ≥ n₀, P (F n) ≤ K * 2⁻¹ ^ n := by
    intro n hn
    obtain ⟨-, hτ, hl⟩ := hn₀ n hn
    have hl' : 2 * (-lam n) ^ 2 *
        (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 := by
      rwa [neg_sq]
    have h1 := lintegral_layer_le hUD hDc hDs hDne hh hd hPS hGm hSrep hG hR hcR hτ hl
    have h2 := lintegral_layer_le hUD hDc hDs hDne hh hd hPS hGm hSrep hG hR hcR hτ hl'
    have hexp : Real.exp (lam n * η) = 8 ^ n := by
      have : lam n * η = n * Real.log 8 := by simp only [hlam]; field_simp
      rw [this, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have hden : ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) =
        ENNReal.ofReal (bumpMass / 16) * 2 ^ n := by
      rw [hexp, ← mul_assoc, eight_pow_mul_half_pow_sq, show (2 : ℝ) ^ n / 16 * bumpMass =
        bumpMass / 16 * 2 ^ n by ring, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    have ha0 : ENNReal.ofReal (bumpMass / 16) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have hden0 : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ 0 :=
      mul_ne_zero ha0 (pow_ne_zero _ two_ne_zero)
    have hdentop : ENNReal.ofReal (bumpMass / 16) * 2 ^ n ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    have hmeasF : AEMeasurable (fun ω => ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)) P :=
      (measurable_const.mul ((hIm n _).add (hIm n _))).aemeasurable
    calc P (F n) ≤ (∫⁻ ω, ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω) ∂P) /
          (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          have := meas_ge_le_lintegral_div hmeasF hden0 hdentop
          simp only [hF, hden]
          exact this
      _ = ENNReal.ofReal e₁ * ((∫⁻ ω, I n (lam n) ω ∂P) + ∫⁻ ω, I n (-lam n) ω ∂P) /
          (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          rw [lintegral_const_mul (f := fun ω => I n (lam n) ω + I n (-lam n) ω) _
            ((hIm n _).add (hIm n _)), lintegral_add_left (hIm n _)]
      _ ≤ ENNReal.ofReal e₁ * (X + X) / (ENNReal.ofReal (bumpMass / 16) * 2 ^ n) := by
          gcongr
      _ = K * 2⁻¹ ^ n := by
          rw [hK, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top),
            ENNReal.inv_pow, ← mul_assoc, ← div_eq_mul_inv]
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_)
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have : X ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    exact ENNReal.add_ne_top.2 ⟨this, this⟩
  have hsum : ∑' k, P (F (k + n₀)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' k : ℕ, K * 2⁻¹ ^ k) ?_ (ENNReal.tsum_le_tsum fun k =>
      (hPF (k + n₀) (by omega)).trans (mul_le_mul_right
        (pow_le_pow_of_le_one zero_le (ENNReal.inv_le_one.2 one_le_two) (Nat.le_add_right k n₀))
        K))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top hKtop ENNReal.ofNat_ne_top
  -- Borel–Cantelli
  filter_upwards [ae_eventually_notMem hsum, mem_ae_iff.2 hPS] with ω hev hωS
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hev
  refine ⟨K₀ + n₀, fun n hn g hg w _hwD hwc h1 h2 => ?_⟩
  have hn' : n₀ ≤ n := by omega
  have hnotF : ω ∉ F n := by
    have := hK₀ (n - n₀) (by omega)
    rwa [Nat.sub_add_cancel hn'] at this
  obtain ⟨hεR, -, -⟩ := hn₀ n hn'
  have hball := closedBall_subset_layerSet hεR hwc h1 h2
  have hLU := layerSet_subset hR hcR n (U := (U : Set ℂ))
  have hBU : closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ U := hball.trans hLU
  have hIeq : ∀ l, ∫⁻ y in layerSet D c R n, ENNReal.ofReal (Real.exp (l * g y)) = I n l ω :=
    fun l => setLIntegral_congr_fun (measurableSet_layerSet D.isOpen c R n) fun y hy => by
      rw [hG ω hωS g hg y (hLU hy)]
  have hJ := fun l => ofReal_exp_mul_le_lintegral_of_harmonic U.isOpen hg.1 (by positivity) hBU
    l hball
  by_contra hlt
  push Not at hlt
  apply hnotF
  show ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) ≤
    ENNReal.ofReal e₁ * (I n (lam n) ω + I n (-lam n) ω)
  have hlam0 : 0 ≤ lam n := by simp only [hlam]; positivity
  have hpos : 0 ≤ ((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass := by positivity
  rcases le_abs'.1 hlt with hneg | hpos'
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (-lam n * g w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (-lam n) ω := by rw [← hIeq]; exact hJ (-lam n)
      _ ≤ _ := by gcongr; exact le_add_self
  · calc ENNReal.ofReal (Real.exp (lam n * η) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass))
        ≤ ENNReal.ofReal (Real.exp (lam n * g w) * (((1 / 2 : ℝ) ^ (n + 2)) ^ 2 * bumpMass)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.2 (by nlinarith)) hpos)
      _ ≤ ENNReal.ofReal e₁ * I n (lam n) ω := by rw [← hIeq]; exact hJ (lam n)
      _ ≤ _ := by gcongr; exact le_self_add


/-- A point of `D` close to a boundary point lies in a dyadic layer of high index. -/
lemma exists_layer_index {D : Set ℂ} {x : ℂ} (hd0 : 0 < infDist x Dᶜ) {N : ℕ}
    (hdN : infDist x Dᶜ < (1 / 2 : ℝ) ^ N) :
    ∃ n ≥ N, (1 / 2 : ℝ) ^ (n + 1) ≤ infDist x Dᶜ ∧ infDist x Dᶜ ≤ (1 / 2 : ℝ) ^ n := by
  set d := infDist x Dᶜ
  have hd1 : d < 1 := lt_of_lt_of_le hdN (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := d⁻¹) (y := 2)
    (by rw [le_inv_comm₀ one_pos hd0, inv_one]; exact hd1.le) one_lt_two
  have e : ∀ k : ℕ, (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ := fun k => by rw [one_div, inv_pow]
  refine ⟨n, ?_, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ N < 2 ^ (n + 1) := by
      refine lt_trans ?_ hn2
      rw [e, lt_inv_comm₀ hd0 (by positivity)] at hdN
      exact hdN
    have := (pow_lt_pow_iff_right₀ one_lt_two).1 h1
    omega
  · rw [e, inv_le_comm₀ (by positivity) hd0]; exact hn2.le
  · rw [e, le_inv_comm₀ hd0 (by positivity)]; exact hn1

/-- **Proposition 3.3 on a patch.** If `D ∩ B(c, 4R) ⊆ U`, then almost surely every harmonic
representative `g` of `h − h_U` on `U` tends to `0` at every point of `∂D ∩ B(c, R)`. -/
theorem ae_tendsto_patch {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcR : ∀ y ∈ D, dist y c < 4 * R → y ∈ U) :
    ∀ᵐ ω ∂P, ∀ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g →
      ∀ z₀ ∈ frontier (D : Set ℂ), dist z₀ c < R → Tendsto g (𝓝[(U : Set ℂ)] z₀) (𝓝 0) := by
  have hall := ae_all_iff.2 fun m : ℕ =>
    ae_eventually_abs_lt hUD hDc hDs hDne hh hd hR hcR (η := 1 / ((m : ℝ) + 1)) (by positivity)
  filter_upwards [hall] with ω hω g hg z₀ hz₀ hz₀c
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hω m
  refine ⟨min R ((1 / 2 : ℝ) ^ N), by positivity, fun {x} hxU hxz => ?_⟩
  have hxD : x ∈ (D : Set ℂ) := hUD hxU
  have hz₀D : z₀ ∈ (D : Set ℂ)ᶜ := fun h => hz₀.2 (by rwa [D.isOpen.interior_eq])
  have hd0 : 0 < infDist x (D : Set ℂ)ᶜ :=
    (IsClosed.notMem_iff_infDist_pos D.isOpen.isClosed_compl ⟨z₀, hz₀D⟩).1 (fun h => h hxD)
  have hdx : infDist x (D : Set ℂ)ᶜ ≤ dist x z₀ := infDist_le_dist_of_mem hz₀D
  have hdN : infDist x (D : Set ℂ)ᶜ < (1 / 2 : ℝ) ^ N :=
    lt_of_le_of_lt hdx (lt_of_lt_of_le hxz (min_le_right _ _))
  obtain ⟨n, hnN, h1, h2⟩ := exists_layer_index hd0 hdN
  have hxc : dist x c < 2 * R := by
    have := dist_triangle x z₀ c
    have := lt_of_lt_of_le hxz (min_le_left _ _)
    linarith
  have := hN n hnN g hg x hxD hxc h1 h2
  rw [Real.dist_eq, sub_zero]
  exact lt_trans this hm

/-- **Proposition 3.3 (boundary vanishing of the harmonic projection).** Let `D ≠ ℂ` be a simply
connected domain, `U ⊆ D` open (`U = D ∖ K` for the deterministic relatively closed `K = D ∖ U`),
`h` a zero-boundary GFF on `D` and `h = h_U + (h − h_U)` a Markov decomposition. Almost surely,
the harmonic function `h₁` on `U` representing `h − h_U` satisfies `h₁(z) → 0` as `z → z₀`,
`z ∈ U`, for every `z₀ ∈ ∂D ∖ cl(D ∖ U)`. -/
theorem ae_tendsto_markov_sub_frontier {U D : Opens ℂ} (hUD : U ≤ D)
    (hDc : IsConnected (D : Set ℂ)) (hDs : IsSimplyConnected (D : Set ℂ))
    (hDne : (D : Set ℂ) ≠ univ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition U D h hU P) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g U →
      (∀ φ : TestOn U, restrictDist U (h ω - hU ω) φ = ∫ x, g x * φ x) →
      ∀ z₀ ∈ frontier (D : Set ℂ) \ closure ((D : Set ℂ) \ U),
        Tendsto g (𝓝[(U : Set ℂ)] z₀) (𝓝 0) := by
  classical
  set c : ℕ → ℂ := TopologicalSpace.denseSeq ℂ with hc
  have hpatch : ∀ p : ℕ × ℕ, ∀ᵐ ω ∂P,
      (∀ y ∈ D, dist y (c p.1) < 4 * (1 / ((p.2 : ℝ) + 1)) → y ∈ U) →
      ∀ g, IsHarmRep U (restrictDist U (h ω - hU ω)) g →
      ∀ z₀ ∈ frontier (D : Set ℂ), dist z₀ (c p.1) < 1 / ((p.2 : ℝ) + 1) →
        Tendsto g (𝓝[(U : Set ℂ)] z₀) (𝓝 0) := by
    intro p
    by_cases hgood : ∀ y ∈ D, dist y (c p.1) < 4 * (1 / ((p.2 : ℝ) + 1)) → y ∈ U
    · filter_upwards [ae_tendsto_patch hUD hDc hDs hDne hh hd (c := c p.1)
        (R := 1 / ((p.2 : ℝ) + 1)) (by positivity) hgood] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hgood
  filter_upwards [ae_all_iff.2 hpatch] with ω hω g hgh hgr z₀ hz₀
  obtain ⟨ε, hε, hεK⟩ : ∃ ε > 0, ∀ y ∈ (D : Set ℂ) \ U, ε ≤ dist z₀ y := by
    have := hz₀.2
    rw [Metric.mem_closure_iff] at this
    push Not at this
    obtain ⟨ε, hε, h⟩ := this
    exact ⟨ε, hε, h⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 5 by positivity)
  set Rk : ℝ := 1 / ((k : ℝ) + 1) with hRk
  have hRk0 : 0 < Rk := by positivity
  obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z₀ Rk hRk0
  have hgood : ∀ y ∈ D, dist y (c j) < 4 * Rk → y ∈ U := by
    intro y hyD hyc
    by_contra hyU
    have h1 := hεK y ⟨hyD, hyU⟩
    have h2 := dist_triangle z₀ (c j) y
    rw [dist_comm (c j) y] at h2
    linarith
  exact hω (j, k) hgood g ⟨hgh, hgr⟩ z₀ hz₀.1 hj


/-- **Proposition 3.3, source form.** Let `D ≠ ℂ` be a simply connected domain and `K` a
deterministic set, closed in `D` (`D ∖ K` open). For a Markov decomposition of the zero-boundary
GFF `h` on `D` with respect to `D ∖ K`, almost surely the harmonic function `h₁` on `D ∖ K` agreeing
with the projection `h − h_{D∖K}` of `h` onto `H^⊥(D ∖ K)` satisfies
`lim_{D∖K ∋ z → z₀} h₁(z) = 0` for all `z₀ ∈ ∂D ∖ cl K`. -/
theorem ae_tendsto_harmonic_frontier {D : Opens ℂ} (hDc : IsConnected (D : Set ℂ))
    (hDs : IsSimplyConnected (D : Set ℂ)) (hDne : (D : Set ℂ) ≠ univ) {K : Set ℂ}
    (hK : IsOpen ((D : Set ℂ) \ K)) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h hU : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P)
    (hd : IsMarkovDecomposition ⟨(D : Set ℂ) \ K, hK⟩ D h hU P) :
    ∀ᵐ ω ∂P, ∀ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g ((D : Set ℂ) \ K) →
      (∀ φ : TestOn ⟨(D : Set ℂ) \ K, hK⟩,
        restrictDist ⟨(D : Set ℂ) \ K, hK⟩ (h ω - hU ω) φ = ∫ x, g x * φ x) →
      ∀ z₀ ∈ frontier (D : Set ℂ) \ closure K,
        Tendsto g (𝓝[(D : Set ℂ) \ K] z₀) (𝓝 0) := by
  have hUD : (⟨(D : Set ℂ) \ K, hK⟩ : Opens ℂ) ≤ D := fun x hx => hx.1
  filter_upwards [ae_tendsto_markov_sub_frontier hUD hDc hDs hDne hh hd] with ω hω g hg hgr z₀ hz₀
  refine hω g hg hgr z₀ ⟨hz₀.1, fun hcl => hz₀.2 (closure_mono ?_ hcl)⟩
  intro y hy
  by_contra hyK
  exact hy.2 ⟨hy.1, hyK⟩


end GFF
end InteractingSLE
