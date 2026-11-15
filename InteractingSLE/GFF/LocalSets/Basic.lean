import InteractingSLE.GFF.Markov
import LQGMetric.Papers.MQ.ZBCM
import SupercriticalConformalCovariance.GM24.TVReduce

/-!
# Local tools for the GFF on subdomains: Cameron–Martin shifts and local Markov decompositions

Infrastructure for §3.1 of the specification (`source/spec/p001-048.md#prop-3.4`, PDF pp. 46–48),
used for Proposition 3.4 (absolute continuity) in `InteractingSLE.GFF.LocalSets.AbsCont`.

Carriers: fields are `LQGMetric.DistOn D = 𝒟'(D)` (cylinder σ-algebra), the zero-boundary GFF is
`LQGMetric.IsZeroBoundaryGFF D` on an admissible open `D` (`LQGMetric.ZBAdmissible D`: every test
function has finite `H⁻¹(D)` norm), a function `F` is turned into a distribution on `U` by
SupercriticalConformalCovariance's `smoothDist U F = (φ ↦ ∫ φ F)`.

## Main results

* `restrictAdd U T F = (T + F)|_U ∈ 𝒟'(U)`;
* `map_add_smoothDist_absolutelyContinuous` : **Cameron–Martin**: for a zero-boundary GFF `X` on an
  admissible `V` and `f ∈ C_c^∞(V)`, `law(X + f)` and `law(X)` are mutually absolutely continuous
  (LQGMetric `MQ.map_tiltMeasure_cmSigma`, QuantumZipper's abstract Gaussian tilt);
* `map_restrict_add_harmonic_absolutelyContinuous` : for bounded open `U` with `cl U ⊆ W` and
  harmonic `u₁, u₂` on `W`, `law(Z|_U + u₁) ≪ law(Z|_U + u₂)` (cut-off shift `χ (u₁ − u₂)`);
* `map_add_absolutelyContinuous_of_indepFun` : mixtures of mutually comparable translates;
* `exists_restrictAdd_decomposition` : `(h + F)|_U = Z|_U + Y` with `Z` a zero-boundary GFF on `W`
  and `Y` an independent, almost surely harmonic (on `W`) distribution (Proposition 3.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open LQGMetric QuantumZipper QuantumZipper.CameronMartin
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply integrable_test_mul)

namespace InteractingSLE
namespace GFF

/-- Two measures on `𝒟'(V)` compare as their pushforwards under the pairing map do. -/
lemma absolutelyContinuous_of_map_distEval {V : Opens ℂ} {μ ν : Measure (DistOn V)}
    (h : μ.map (distEval V) ≪ ν.map (distEval V)) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hνA => ?_
  obtain ⟨B, hB, rfl⟩ := hA
  have := h (s := B)
  rw [Measure.map_apply (measurable_distEval V) hB,
    Measure.map_apply (measurable_distEval V) hB] at this
  exact this hνA

/-- The tilted measure and `P` are mutually absolutely continuous. -/
lemma tiltMeasure_absolutelyContinuous {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : I → Ω → ℝ} (σ : I →₀ ℝ) : tiltMeasure X P σ ≪ P :=
  withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_tiltMeasure {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsGaussianProcess X P) (hmeas : ∀ i, Measurable (X i))
    (σ : I →₀ ℝ) : P ≪ tiltMeasure X P σ :=
  withDensity_absolutelyContinuous'
    (measurable_tiltDensity hX hmeas σ).real_toNNReal.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      simp only [ne_eq, ENNReal.coe_eq_zero, Real.toNNReal_eq_zero, not_le]
      exact Real.exp_pos _)

lemma continuous_zsSub {V : Set ℂ} (f : MarkovZB.zsSub V) :
    Continuous (f : ℂ → ℝ) :=
  f.2.1.continuous

/-- **Cameron–Martin for the zero-boundary GFF, `𝒟'(V)` form.** For a zero-boundary GFF `X` on
an admissible open `V` and `f ∈ C_c^∞(V)`, the laws of `X + f` and `X` are mutually absolutely
continuous. -/
theorem map_add_smoothDist_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : Opens ℂ} (hadm : ZBAdmissible V) {X : Ω → DistOn V} (hX : IsZeroBoundaryGFF V X P)
    (f : MarkovZB.zsSub (V : Set ℂ)) :
    P.map (fun ω => X ω + smoothDist V f) ≪ P.map X ∧
      P.map X ≪ P.map (fun ω => X ω + smoothDist V f) := by
  rcases (V : Set ℂ).eq_empty_or_nonempty with hV | hne
  · have h0 : smoothDist V (f : ℂ → ℝ) = 0 := by
      ext φ
      have : (φ : ℂ → ℝ) = 0 := by
        funext x
        exact image_eq_zero_of_notMem_tsupport fun hx => by
          simpa [hV] using φ.tsupport_subset hx
      rw [smoothDist_apply (continuous_zsSub f).continuousOn]
      simp [this]
    simp only [h0, add_zero]
    exact ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩
  set Xp : TestOn V → Ω → ℝ := fun φ ω => X ω φ
  have hmeas : ∀ φ, Measurable (Xp φ) := hX.process.measurable
  have hS : Measurable fun T : DistOn V => T + smoothDist V f :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have key := MQ.map_tiltMeasure_cmSigma hadm hne hX.process f
  have e1 : (P.map fun ω => X ω + smoothDist V f).map (distEval V) =
      (tiltMeasure Xp P (MQ.cmSigma f)).map (fun ω j => Xp j ω) := by
    rw [key, Measure.map_map (measurable_distEval V) (f := fun ω => X ω + smoothDist V f)
      (hS.comp hX.measurable)]
    congr 1
    funext ω j
    change X ω j + smoothDist V f j = X ω j + ∫ x, (f : ℂ → ℝ) x * j x
    rw [smoothDist_apply (continuous_zsSub f).continuousOn]
    simp only [mul_comm]
  have e2 : (P.map X).map (distEval V) = P.map (fun ω j => Xp j ω) := by
    rw [Measure.map_map (measurable_distEval V) hX.measurable]
    rfl
  have hp : Measurable fun ω j => Xp j ω := measurable_pi_iff.mpr hmeas
  constructor
  · refine absolutelyContinuous_of_map_distEval ?_
    rw [e1, e2]
    exact (tiltMeasure_absolutelyContinuous _).map hp
  · refine absolutelyContinuous_of_map_distEval ?_
    rw [e1, e2]
    exact (absolutelyContinuous_tiltMeasure hX.process.gaussian hmeas _).map hp


/-- A smooth cutoff: for compact `K ⊆ W` open there is `χ ∈ C_c^∞(W)` with `χ = 1` on `K`. -/
lemma exists_cutoff {K W : Set ℂ} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ W ∧ EqOn χ 1 K := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨χ, hχ, -, hsupp, h1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (Metric.isOpen_thickening (δ := δ) (E := K)) hK.isClosed
    (Metric.self_subset_thickening hδ K)
  have hts : tsupport χ ⊆ Metric.cthickening δ K := by
    rw [tsupport, hsupp]
    exact Metric.closure_thickening_subset_cthickening δ K
  exact ⟨χ, hχ, (hK.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hts,
    hts.trans hδW, fun x hx => (h1 x).1 hx⟩

/-- `χ u` is smooth on `ℂ` if `χ` is smooth with `tsupport χ ⊆ W` and `u` is smooth on `W`. -/
lemma contDiff_mul_of_tsupport_subset {n : WithTop ℕ∞} {χ u : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W)
    (hχ : ContDiff ℝ n χ) (hχW : tsupport χ ⊆ W) (hu : ContDiffOn ℝ n u W) :
    ContDiff ℝ n fun x => χ x * u x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ W
  · exact hχ.contDiffAt.mul (hu.contDiffAt (hW.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hχW h)
    have hev : (fun x => χ x * u x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- A harmonic function on an open set is smooth there. -/
lemma contDiffOn_of_harmonicOnNhd {n : WithTop ℕ∞} {u : ℂ → ℝ} {W : Set ℂ}
    (hu : InnerProductSpace.HarmonicOnNhd u W) : ContDiffOn ℝ n u W := fun x hx =>
  (HarmonicAt.analyticAt (hu x hx)).contDiffAt.contDiffWithinAt

/-- **Shifting by a harmonic function, locally.** Let `Z` be a zero-boundary GFF on an
admissible open set `W` and `U` a bounded open set with `cl U ⊆ W`. For harmonic `u₁, u₂` on
`W`, the law of `Z|_U + u₁` is absolutely continuous with respect to that of `Z|_U + u₂`. -/
theorem map_restrict_add_harmonic_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W U : Opens ℂ} (hadm : ZBAdmissible W) (hUb : Bornology.IsBounded (U : Set ℂ))
    (hUW : closure (U : Set ℂ) ⊆ W) {Z : Ω → DistOn W} (hZ : IsZeroBoundaryGFF W Z P)
    {u₁ u₂ : ℂ → ℝ} (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ W)
    (hu₂ : InnerProductSpace.HarmonicOnNhd u₂ W) :
    P.map (fun ω => restrictDist U (Z ω) + smoothDist U u₁) ≪
      P.map (fun ω => restrictDist U (Z ω) + smoothDist U u₂) := by
  have hUW' : U ≤ W := fun x hx => hUW (subset_closure hx)
  obtain ⟨χ, hχ, hχc, hχW, hχ1⟩ := exists_cutoff hUb.isCompact_closure W.isOpen hUW
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => u₁ x - u₂ x) W :=
    (contDiffOn_of_harmonicOnNhd hu₁).sub (contDiffOn_of_harmonicOnNhd hu₂)
  let g : MarkovZB.zsSub (W : Set ℂ) :=
    ⟨fun x => χ x * (u₁ x - u₂ x), contDiff_mul_of_tsupport_subset W.isOpen hχ hχW hd,
      hχc.mul_right, (tsupport_mul_subset_left).trans hχW⟩
  have hc₁ : ContinuousOn u₁ U := (contDiffOn_of_harmonicOnNhd (n := 0) hu₁).continuousOn.mono hUW'
  have hc₂ : ContinuousOn u₂ U := (contDiffOn_of_harmonicOnNhd (n := 0) hu₂).continuousOn.mono hUW'
  set Φ : DistOn W → DistOn U := fun T => restrictDist U T + smoothDist U u₂
  have hΦ : Measurable Φ := measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (measurable_restrictDist U)).add_const _
  have hS : Measurable fun T : DistOn W => T + smoothDist W g :=
    measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const _
  have key : ∀ T : DistOn W, Φ (T + smoothDist W g) = restrictDist U T + smoothDist U u₁ := by
    intro T
    ext φ
    simp only [Φ, add_apply, restrictDist_apply]
    rw [smoothDist_apply (g.2.1.continuous.continuousOn), smoothDist_apply hc₂,
      smoothDist_apply hc₁, coe_testIncl hUW', add_assoc, ← integral_add]
    · congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : φ x = 0
      · simp [hx]
      · have hxU : x ∈ (U : Set ℂ) := φ.tsupport_subset (subset_tsupport _ hx)
        have : χ x = 1 := hχ1 (subset_closure hxU)
        change φ x * (χ x * (u₁ x - u₂ x)) + φ x * u₂ x = φ x * u₁ x
        rw [this]
        ring
    · have := integrable_test_mul (B := W) (g.2.1.continuous.continuousOn) (testIncl U W φ)
      rwa [coe_testIncl hUW'] at this
    · exact integrable_test_mul hc₂ φ
  have hZm := hZ.measurable
  calc P.map (fun ω => restrictDist U (Z ω) + smoothDist U u₁)
      = (P.map fun ω => Z ω + smoothDist W g).map Φ := by
        rw [Measure.map_map hΦ (f := fun ω => Z ω + smoothDist W g) (hS.comp hZm)]
        congr 1
        funext ω
        exact (key (Z ω)).symm
    _ ≪ (P.map Z).map Φ := ((map_add_smoothDist_absolutelyContinuous hadm hZ g).1).map hΦ
    _ = P.map (fun ω => restrictDist U (Z ω) + smoothDist U u₂) := Measure.map_map hΦ hZm

/-- `(T + F)|_U ∈ 𝒟'(U)`: the restriction to `U` of the distribution `T` on `D` plus the function
`F` (meaningful for `U ⊆ D` and `F` continuous on `U`). -/
def restrictAdd (U : Opens ℂ) {D : Opens ℂ} (T : DistOn D) (F : ℂ → ℝ) : DistOn U :=
  restrictDist U T + smoothDist U F

lemma testIncl_testIncl' {U V D : Opens ℂ} (hUV : U ≤ V) (hVD : V ≤ D) (φ : TestOn U) :
    testIncl V D (testIncl U V φ) = testIncl U D φ := by
  ext x
  rw [coe_testIncl hVD, coe_testIncl hUV, coe_testIncl (hUV.trans hVD)]

lemma restrictDist_restrictDist {U V D : Opens ℂ} (hUV : U ≤ V) (hVD : V ≤ D) (T : DistOn D) :
    restrictDist U (restrictDist V T) = restrictDist U T := by
  ext φ
  simp only [restrictDist_apply, testIncl_testIncl' hUV hVD]

lemma restrictDist_add (U : Opens ℂ) {D : Opens ℂ} (T S : DistOn D) :
    restrictDist U (T + S) = restrictDist U T + restrictDist U S := by
  ext φ
  simp only [restrictDist_apply, add_apply]

lemma restrictDist_sub (U : Opens ℂ) {D : Opens ℂ} (T S : DistOn D) :
    restrictDist U (T - S) = restrictDist U T - restrictDist U S := by
  ext φ
  simp only [restrictDist_apply, sub_apply]

lemma measurable_add_distOn (U : Opens ℂ) :
    Measurable fun p : DistOn U × DistOn U => p.1 + p.2 :=
  measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp measurable_fst).add
      ((measurable_distOn_apply φ).comp measurable_snd)

/-- The law of `Z + Y` for independent `Z, Y`, evaluated on a measurable set, as a mixture of
translates of the law of `Z`. -/
lemma map_add_apply_of_indepFun {α : Type*} [MeasurableSpace α] [Add α]
    (hadd : Measurable fun p : α × α => p.1 + p.2) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z Y : Ω → α} (hZ : Measurable Z)
    (hY : Measurable Y) (hi : IndepFun Z Y P) {A : Set α} (hA : MeasurableSet A) :
    P.map (fun ω => Z ω + Y ω) A = ∫⁻ ω, (P.map Z) {x | x + Y ω ∈ A} ∂P := by
  have hs : MeasurableSet ((fun p : α × α => p.1 + p.2) ⁻¹' A) := hadd hA
  have e : P.map (fun ω => Z ω + Y ω) =
      ((P.map Z).prod (P.map Y)).map fun p : α × α => p.1 + p.2 := by
    rw [← (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hY.aemeasurable).1 hi,
      Measure.map_map hadd (hZ.prodMk hY)]
    rfl
  rw [e, Measure.map_apply hadd hA, Measure.prod_apply_symm hs,
    lintegral_map (measurable_measure_prodMk_right hs) hY]
  rfl

/-- **Mixtures of mutually comparable translates.** If `Zᵢ ⫫ Yᵢ`, the `Zᵢ` have a common law
`ν`, each `Yᵢ` lies a.s. in a set `S` of shifts whose translates of `ν` are mutually absolutely
continuous, then `law(Z₁ + Y₁) ≪ law(Z₂ + Y₂)`. -/
theorem map_add_absolutelyContinuous_of_indepFun {α : Type*} [MeasurableSpace α] [Add α]
    (hadd : Measurable fun p : α × α => p.1 + p.2) {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {Z₁ Y₁ : Ω₁ → α} {Z₂ Y₂ : Ω₂ → α} (hZ₁ : Measurable Z₁)
    (hY₁ : Measurable Y₁) (hZ₂ : Measurable Z₂) (hY₂ : Measurable Y₂) (hi₁ : IndepFun Z₁ Y₁ P₁)
    (hi₂ : IndepFun Z₂ Y₂ P₂) (hlaw : P₁.map Z₁ = P₂.map Z₂) (S : Set α)
    (hS : ∀ y ∈ S, ∀ y' ∈ S, (P₁.map Z₁).map (· + y) ≪ (P₁.map Z₁).map (· + y'))
    (hY₁S : ∀ᵐ ω ∂P₁, Y₁ ω ∈ S) (hY₂S : ∀ᵐ ω ∂P₂, Y₂ ω ∈ S) :
    P₁.map (fun ω => Z₁ ω + Y₁ ω) ≪ P₂.map (fun ω => Z₂ ω + Y₂ ω) := by
  have hsh : ∀ y : α, Measurable fun x : α => x + y := fun y =>
    hadd.comp (measurable_id.prodMk measurable_const)
  refine Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [map_add_apply_of_indepFun hadd hZ₂ hY₂ hi₂ hA, ← hlaw] at h0
  have hmeas : ∀ {Ω : Type _} [MeasurableSpace Ω] {Y : Ω → α}, Measurable Y →
      Measurable fun ω => (P₁.map Z₁) {x | x + Y ω ∈ A} := fun {Ω} _ {Y} hY =>
    (measurable_measure_prodMk_right (μ := P₁.map Z₁) (hadd hA)).comp hY
  have hz := (lintegral_eq_zero_iff (hmeas hY₂)).1 h0
  obtain ⟨ω₀, hω₀, hω₀S⟩ := (hz.and hY₂S).exists
  have hzero : ∀ y ∈ S, (P₁.map Z₁) {x | x + y ∈ A} = 0 := by
    intro y hy
    have h1 := hS y hy (Y₂ ω₀) hω₀S
    have h2 : ((P₁.map Z₁).map (· + Y₂ ω₀)) A = 0 := by
      rw [Measure.map_apply (hsh _) hA]
      exact hω₀
    have h3 := h1 h2
    rwa [Measure.map_apply (hsh _) hA] at h3
  rw [map_add_apply_of_indepFun hadd hZ₁ hY₁ hi₁ hA]
  rw [lintegral_congr_ae (hY₁S.mono fun ω hω => hzero _ hω)]
  simp

/-- **Local Markov decomposition of `(h + F)|_U`.** For a zero-boundary GFF `h` on an admissible
`D`, `F` harmonic on `D`, and open `U ≤ W ≤ D`: `(h + F)|_U = Z + Y` with `Z` the restriction to
`U` of a zero-boundary GFF on `W`, `Y` independent of `Z` and almost surely a harmonic function on
`W` (restricted to `U`). -/
theorem exists_restrictAdd_decomposition {D W U : Opens ℂ} (hWD : W ≤ D) (hUW : U ≤ W)
    (hD : ZBAdmissible D) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn D} (hh : IsZeroBoundaryGFF D h P) {F : ℂ → ℝ}
    (hF : InnerProductSpace.HarmonicOnNhd F D) :
    ∃ (Z' : Ω → DistOn W) (Y : Ω → DistOn U), IsZeroBoundaryGFF W Z' P ∧ Measurable Y ∧
      IndepFun (fun ω => restrictDist U (Z' ω)) Y P ∧
      (∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u W ∧ Y ω = smoothDist U u) ∧
      ∀ ω, restrictAdd U (h ω) F = restrictDist U (Z' ω) + Y ω := by
  obtain ⟨G, hGm, hG⟩ := exists_markovMap hWD hD
  have hd := hG hh
  have hFW : InnerProductSpace.HarmonicOnNhd F W := hF.mono hWD
  have hcF : ContinuousOn F U :=
    ((contDiffOn_of_harmonicOnNhd (n := 0) hFW).continuousOn).mono hUW
  let Y : Ω → DistOn U := fun ω => restrictDist U (h ω - G (h ω)) + smoothDist U F
  have hsub : Measurable fun T : DistOn D => T - G T :=
    measurable_distOn_iff.2 fun φ =>
      (measurable_distOn_apply φ).sub ((measurable_distOn_apply φ).comp hGm)
  have hΦ : Measurable fun T : DistOn D => restrictDist U T + smoothDist U F :=
    measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp (measurable_restrictDist U)).add_const _
  have hYm : Measurable Y := hΦ.comp (hsub.comp hh.measurable)
  refine ⟨fun ω => restrictDist W (G (h ω)), Y, hd.isZeroBoundaryGFF, hYm, ?_, ?_, ?_⟩
  · have hi := hd.indepFun.comp (measurable_restrictDist U) hΦ
    refine hi.congr (Filter.Eventually.of_forall fun ω => ?_) Filter.EventuallyEq.rfl
    exact (restrictDist_restrictDist hUW hWD _).symm
  · filter_upwards [hd.ae_harmonic] with ω ⟨g, hg, hgrep⟩
    refine ⟨fun x => g x + F x, hg.add hFW, ?_⟩
    have hcg : ContinuousOn g U :=
      ((contDiffOn_of_harmonicOnNhd (n := 0) hg).continuousOn).mono hUW
    ext φ
    have e1 : restrictDist U (h ω - G (h ω)) φ = ∫ x, φ x * g x := by
      rw [← restrictDist_restrictDist hUW hWD, restrictDist_apply, hgrep, coe_testIncl hUW]
      simp only [mul_comm]
    simp only [Y, add_apply]
    rw [e1, smoothDist_apply hcF, smoothDist_apply (Y := fun x => g x + F x) (hcg.add hcF),
      ← integral_add
      (integrable_test_mul hcg φ) (integrable_test_mul hcF φ)]
    simp only [mul_add]
  · intro ω
    simp only [restrictAdd, Y, restrictDist_restrictDist hUW hWD, restrictDist_sub]
    abel

end GFF
end InteractingSLE
