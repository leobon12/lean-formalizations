import SmallGammaGeodesics.Core.Interfaces
import LQGMetric.Field.GFFLaw

/-!
# Universal locality by coin mixture (track CC, packet CC2, target T2)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D3** (GA5 (a9) generalized).
Axiom II (locality) of a strong γ-LQG metric gives, for **one** field `g` (a whole-plane GFF plus a
continuous function on one probability space) and an open `U`, a measurable `F` with
`D_g(·,·;U) = F(g|_U)` a.s. The functional `F` is only determined up to null sets of the law of `g|_U`,
so two fields need not share it. Here one functional is produced for **countably many** fields on
possibly different probability spaces (`UniversalLocality`, `Core/Interfaces.lean`).

**Proof (coin mixture).** Choose weights `w i > 0` with `∑ w i = 1`, and put the mixture
`μ = ∑ᵢ w i • (P i).map (Sigma.mk i)` on the sigma type `Σ i, Ω i`, with the field `Y ⟨i, ω⟩ = g i ω`.
Write `g i = h i + f i` with `h i` a whole-plane GFF. Then `Y − f_Y` is a whole-plane GFF under `μ`:
its law of mean-zero pairings is `∑ᵢ w i • ν = ν`, where `ν` is the common law of the mean-zero pairings
of the whole-plane GFF (`GFFLaw.map_pairProc_eq`), and being a whole-plane GFF only depends on that law
(`isWholePlaneGFF_of_map_pairProc_eq`). Axiom II for `Y` gives `F`. A `μ`-null set meets each slice in
a `P i`-null set, because `w i ≠ 0`.

Main results:
* `universalLocality`: `IsStrongLQGMetric γ D → UniversalLocality D`;
* `ae_internal_eq_of_ae_restrictTo_eq` (**pathwise locality**, GA5 (a9)): if `g₁|_U = g₂|_U` a.s. on
  one space, then `D_{g₁}(·,·;U) = D_{g₂}(·,·;U)` a.s.; `ae_internal_eq_of_ae_apply_eq` is the form with
  pairings against test functions supported in `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Measurability on a sigma type -/

section Sigma

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The inclusion of a slice into the sigma type is measurable. -/
theorem measurable_sigmaMk (i : ι) : Measurable (Sigma.mk i : Ω i → Sigma Ω) := fun _ hs =>
  (MeasurableSpace.measurableSet_iInf.1 hs) i

/-- A map out of the sigma type is measurable if it is measurable on each slice. -/
theorem measurable_of_sigma {β : Type*} [MeasurableSpace β] {F : Sigma Ω → β}
    (hF : ∀ i, Measurable fun ω => F ⟨i, ω⟩) : Measurable F := fun _ hs =>
  MeasurableSpace.measurableSet_iInf.2 fun i => hF i hs

end Sigma

/-! ## 2. Weights and the mixture measure -/

/-- Positive weights summing to one on a nonempty countable type. -/
theorem exists_pos_weights (ι : Type*) [Countable ι] [Nonempty ι] :
    ∃ w : ι → ℝ≥0∞, (∀ i, w i ≠ 0) ∧ ∑' i, w i = 1 := by
  obtain ⟨ε, hε, hsum⟩ := ENNReal.exists_pos_sum_of_countable one_ne_zero ι
  set S : ℝ≥0∞ := ∑' i, (ε i : ℝ≥0∞) with hS
  have hS0 : S ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum i))
    exact_mod_cast hε i
  have hStop : S ≠ ⊤ := ne_top_of_lt hsum
  refine ⟨fun i => (ε i : ℝ≥0∞) * S⁻¹, fun i => ?_, ?_⟩
  · refine mul_ne_zero ?_ (ENNReal.inv_ne_zero.2 hStop)
    exact_mod_cast (hε i).ne'
  · rw [ENNReal.tsum_mul_right, ← hS]
    exact ENNReal.mul_inv_cancel hS0 hStop

section Mixture

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- The **coin mixture** `∑ᵢ w i • (P i).map (Sigma.mk i)` on the sigma type. -/
def mixMeasure (w : ι → ℝ≥0∞) (P : ∀ i, Measure (Ω i)) : Measure (Sigma Ω) :=
  Measure.sum fun i => w i • (P i).map (Sigma.mk i)

theorem isProbabilityMeasure_mixMeasure {w : ι → ℝ≥0∞} (hw : ∑' i, w i = 1)
    {P : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] :
    IsProbabilityMeasure (mixMeasure w P) := by
  constructor
  rw [mixMeasure, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_sigmaMk _) MeasurableSet.univ, preimage_univ, measure_univ,
    mul_one]
  exact hw

/-- A property holding `mixMeasure`-a.e. holds `P i`-a.e. on each slice (`w i ≠ 0`). -/
theorem ae_of_ae_mixMeasure [Countable ι] {w : ι → ℝ≥0∞} (hw : ∀ i, w i ≠ 0)
    {P : ∀ i, Measure (Ω i)} {p : Sigma Ω → Prop} (h : ∀ᵐ x ∂mixMeasure w P, p x) (i : ι) :
    ∀ᵐ ω ∂P i, p ⟨i, ω⟩ := by
  have h1 := (Measure.ae_sum_iff.1 h) i
  rw [Measure.ae_ennreal_smul_measure_iff (hw i)] at h1
  exact ae_of_ae_map (measurable_sigmaMk i).aemeasurable h1

/-- The image of the mixture: the mixture of the images of the slices. -/
theorem map_mixMeasure {w : ι → ℝ≥0∞} {P : ∀ i, Measure (Ω i)} {β : Type*} [MeasurableSpace β]
    {F : Sigma Ω → β} (hF : Measurable F) :
    (mixMeasure w P).map F = Measure.sum fun i => w i • (P i).map fun ω => F ⟨i, ω⟩ := by
  rw [mixMeasure, Measure.map_sum hF.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ hF.aemeasurable, Measure.map_map hF (measurable_sigmaMk i)]
  rfl

/-- A mixture of copies of one measure is that measure. -/
theorem sum_smul_eq_of_tsum_eq_one {β : Type*} [MeasurableSpace β] {w : ι → ℝ≥0∞}
    (hw : ∑' i, w i = 1) (ν : Measure β) : Measure.sum (fun i => w i • ν) = ν := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_mul_right, hw, one_mul]

end Mixture

/-! ## 3. Being a whole-plane GFF only depends on the law of the mean-zero pairings -/

/-- **Being a whole-plane GFF only depends on the law of the mean-zero pairings** (the law of the field
modulo additive constants). Variant of `LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq`, which needs the
full law on `DistC`. -/
theorem isWholePlaneGFF_of_map_pairProc_eq {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    {ν : Measure T} {P : Measure Ω} {Y : T → DistC} (hY : Measurable Y) {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    (hlaw : ν.map (GFFLaw.pairProc Y) = P.map (GFFLaw.pairProc h)) : IsWholePlaneGFF Y ν := by
  have hpY : Measurable (GFFLaw.pairProc Y) := GFFLaw.measurable_pairProc hY
  have hph : Measurable (GFFLaw.pairProc h) := GFFLaw.measurable_pairProc hh.measurable
  have hev : ∀ φ : TestC0, Measurable fun x : TestC0 → ℝ => x φ := fun φ => measurable_pi_apply φ
  refine ⟨hY, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have hF : Measurable fun x : TestC0 → ℝ => I.restrict x := Finset.measurable_restrict I
    refine ⟨(hF.comp hpY).aemeasurable, ?_⟩
    change IsGaussian (ν.map ((fun x : TestC0 → ℝ => I.restrict x) ∘ GFFLaw.pairProc Y))
    rw [← Measure.map_map hF hpY, hlaw, Measure.map_map hF hph]
    exact (hh.gaussian.hasGaussianLaw I).isGaussian_map
  · calc ∫ t, Y t φ.1 ∂ν = ∫ x, (fun x : TestC0 → ℝ => x φ) x ∂(ν.map (GFFLaw.pairProc Y)) :=
          (integral_map hpY.aemeasurable (hev φ).aestronglyMeasurable).symm
      _ = ∫ x, (fun x : TestC0 → ℝ => x φ) x ∂(P.map (GFFLaw.pairProc h)) := by rw [hlaw]
      _ = ∫ ω, h ω φ.1 ∂P := integral_map hph.aemeasurable (hev φ).aestronglyMeasurable
      _ = 0 := hh.centered φ
  · have e1 := covariance_map (μ := ν) (X := fun x : TestC0 → ℝ => x φ)
      (Y := fun x : TestC0 → ℝ => x ψ) (hev φ).aestronglyMeasurable (hev ψ).aestronglyMeasurable
      hpY.aemeasurable
    have e2 := covariance_map (μ := P) (X := fun x : TestC0 → ℝ => x φ)
      (Y := fun x : TestC0 → ℝ => x ψ) (hev φ).aestronglyMeasurable (hev ψ).aestronglyMeasurable
      hph.aemeasurable
    have k := e1.symm.trans ((congrArg (fun μ => cov[fun x : TestC0 → ℝ => x φ,
      fun x : TestC0 → ℝ => x ψ; μ]) hlaw).trans e2)
    exact k.trans (hh.covariance_eq φ ψ)

/-! ## 4. Universal locality -/

/-- **Universal locality** (CC0 D3; GA5 (a9) generalized): for a strong γ-LQG metric, countably many
whole-plane GFFs plus continuous functions, on possibly different probability spaces, share one
locality functional on each open set. -/
theorem universalLocality {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) :
    UniversalLocality D := by
  intro U ι _ Ω _ P _ g hg
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ _ _ => 0, measurable_const, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨w, hw0, hw1⟩ := exists_pos_weights ι
  -- the continuous parts
  choose f hfm hfg using fun i => (hg i).2
  have : IsProbabilityMeasure (mixMeasure w P) := isProbabilityMeasure_mixMeasure hw1
  -- the mixed field and its continuous part
  set Y : Sigma Ω → DistC := fun p => g p.1 p.2 with hYdef
  set fY : Sigma Ω → C(ℂ, ℝ) := fun p => f p.1 p.2 with hfYdef
  have hYm : Measurable Y := measurable_of_sigma fun i => (hg i).1
  have hfYm : Measurable fY := measurable_of_sigma fun i => hfm i
  have hXm : Measurable fun p => Y p - ofCont (fY p) :=
    measurable_of_sigma fun i => (hfg i).measurable
  obtain ⟨i₀⟩ := hι
  have hX : IsWholePlaneGFF (fun p => Y p - ofCont (fY p)) (mixMeasure w P) := by
    refine isWholePlaneGFF_of_map_pairProc_eq hXm (hfg i₀) ?_
    rw [map_mixMeasure (GFFLaw.measurable_pairProc hXm)]
    have e : ∀ i, (P i).map (fun ω => GFFLaw.pairProc (fun p => Y p - ofCont (fY p)) ⟨i, ω⟩) =
        (P i₀).map (GFFLaw.pairProc fun ω => g i₀ ω - ofCont (f i₀ ω)) :=
      fun i => GFFLaw.map_pairProc_eq (hfg i) (hfg i₀)
    simp only [e]
    exact sum_smul_eq_of_tsum_eq_one hw1 _
  have hYc : IsGFFPlusCont Y (mixMeasure w P) := ⟨hYm, fY, hfYm, hX⟩
  obtain ⟨F, hF, hFae⟩ := hD.locality (mixMeasure w P) Y hYc U
  exact ⟨F, hF, fun i => ae_of_ae_mixMeasure hw0 hFae i⟩

/-! ## 5. Pathwise locality -/

section Pathwise

variable {γ : ℝ} {D : DistC → ContMetric} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Pathwise locality** (CC0 D3 corollary, GA5 (a9)): if two whole-plane GFFs plus continuous
functions on one probability space agree on `U` a.s., then so do their internal metrics on `U`. -/
theorem ae_internal_eq_of_ae_restrictTo_eq (hD : IsStrongLQGMetric γ D) {g₁ g₂ : Ω → DistC}
    (h₁ : IsGFFPlusCont g₁ P) (h₂ : IsGFFPlusCont g₂ P) (U : TopologicalSpace.Opens ℂ)
    (hU : ∀ᵐ ω ∂P, restrictTo U (g₁ ω) = restrictTo U (g₂ ω)) :
    ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (g₁ ω)).internal U z w = (D (g₂ ω)).internal U z w := by
  obtain ⟨F, -, hF⟩ := universalLocality hD U Bool (fun _ => Ω) (fun _ => P)
    (fun b => cond b g₁ g₂) (fun b => by cases b <;> assumption)
  filter_upwards [hF true, hF false, hU] with ω h1 h2 h3 z hz w hw
  have e1 : (D (g₁ ω)).internal U z w = F (restrictTo U (g₁ ω)) z w := h1 z hz w hw
  have e2 : (D (g₂ ω)).internal U z w = F (restrictTo U (g₂ ω)) z w := h2 z hz w hw
  rw [e1, e2, h3]

/-- A test function on `U`, seen on `ℂ`, has the same values. -/
theorem coe_monoCLM_top (U : TopologicalSpace.Opens ℂ) (φ : TestOn U) :
    ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ : TestC) : ℂ → ℝ) = φ := by
  ext x
  simp [TestFunction.monoCLM_apply]

/-- Two distributions with the same pairings against test functions supported in `U` have the same
restriction to `U`. -/
theorem restrictTo_eq_of_apply_eq {U : TopologicalSpace.Opens ℂ} {x y : DistC}
    (h : ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ U → x φ = y φ) : restrictTo U x = restrictTo U y := by
  ext φ
  show x (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ) =
    y (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) φ)
  refine h _ ?_
  rw [coe_monoCLM_top]
  exact φ.tsupport_subset

/-- **Pathwise locality**, pairing form: if a.s. `⟨g₁, φ⟩ = ⟨g₂, φ⟩` for every test function `φ`
supported in `U`, then `D_{g₁}(·,·;U) = D_{g₂}(·,·;U)` a.s. -/
theorem ae_internal_eq_of_ae_apply_eq (hD : IsStrongLQGMetric γ D) {g₁ g₂ : Ω → DistC}
    (h₁ : IsGFFPlusCont g₁ P) (h₂ : IsGFFPlusCont g₂ P) (U : TopologicalSpace.Opens ℂ)
    (hU : ∀ᵐ ω ∂P, ∀ φ : TestC, tsupport (φ : ℂ → ℝ) ⊆ U → g₁ ω φ = g₂ ω φ) :
    ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U, (D (g₁ ω)).internal U z w = (D (g₂ ω)).internal U z w :=
  ae_internal_eq_of_ae_restrictTo_eq hD h₁ h₂ U (hU.mono fun _ hω => restrictTo_eq_of_apply_eq hω)

end Pathwise

end SmallGammaGeodesics.CC
