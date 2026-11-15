/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LmRefl

/-!
# SB2(2)'s union mean: the mirrored junction configuration (retained set on the left)

Packet PROVE-SB2-LCMEAN (Theorem 1.4's SB2(2), the mean identification; supplement pp. 631–633). In B's stage chart the
retained upper prefix lies on the LEFT of the explored lower piece, so the relative hull meets the untouched original
real line on its RIGHT — the mirror image of SB2(1)'s configuration `FinRel.IsRelConfigJK` (supplement p. 631: "Use
S2, reflected"). Here:

* **`IsRelConfigJKL`**: the mirrored configuration, defined as `FinRel.IsRelConfigJK` of the reflected data under
  `R(z) = −z̄` (retained set `R(A)`, charts `R ∘ Ψ ∘ R`, `R ∘ Ψi ∘ R`, lift `conj ∘ LΨ ∘ R`, drivers `−w`, `−Wr`, traces
  `R ∘ η`, `R ∘ ηr`, words `y ↦ −β(−y)` with jumps `−S`, harmonic functions `−G ∘ R`); every clause of
  `IsRelConfigJK` holds in the reflected picture, where the retained set is on the right;
* **`ae_chartTransport_eq_couplingMean_of_relConfigJKL`**: FIN's union mean for the mirrored configuration, in the
  ORIGINAL picture and with the same hypotheses and conclusion as
  `FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK` (K2's `hmean` form): almost surely on `D`, for every test
  `ψ` off the relative hull,
  `chartTransport (c ω) 1 a χ (g ω + u₀) ψ = ∫ couplingMean κ (Wr ω) (u ω) (G ω + a + χ ℓ₀) ψ`.

Proof: reflect the field (`−h ∘ R`), the harmonic centring (`−u₀ ∘ R`), the sets, local-set means
(`FCKerD.IsLocalSetMean.reflect`), the individual-mean formulas (`rep_of_reflField_rep`, `LP.fwdMap_neg`,
`LP.im_logDerivFwd_neg`) and the chart (`Lf.reflChart`), apply FIN's lemma there, and reflect back
(`chartTransport_reflChart`, `Sec7.FlowReflect.integral_couplingMean_reflect`).

R48: serves Theorem 1.4 only. A conditional helper with a distinct name; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped ComplexConjugate
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Lm

open LP (reflectC)
open Sec7.FlowReflect (reflField reflTest reflData reflJumps)
open LocalSets WholeField

/-- **The mirrored junction configuration** (retained set on the left of the explored hull; the relative hull meets the
untouched original real line on its right): `FinRel.IsRelConfigJK` of the data reflected by `R(z) = −z̄`. -/
def IsRelConfigJKL (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ)
    (t u χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ) : Prop :=
  FinRel.IsRelConfigJK (reflectC '' A) (fun z => reflectC (Ψ (reflectC z))) (fun z => reflectC (Ψi (reflectC z)))
    (fun z => conj (LΨ (reflectC z))) (reflJumps Sb) (-w) (-Wr) (fun s => reflectC (η s))
    (fun s => reflectC (ηr s)) t u χ lam (reflData β₀) (reflData βE) (reflData βu) (reflJumps S₀) (reflJumps SE)
    (reflJumps Su) (fun z => -G₀ (reflectC z)) (fun z => -GE (reflectC z)) (fun z => -G (reflectC z))
    (fun z => -v (reflectC z))

theorem reflData_reflData (b : ℝ → ℝ) : reflData (reflData b) = b := by
  funext y
  simp only [Sec7.FlowReflect.reflData, neg_neg]

/-- **The mirrored configuration from a configuration of the reflected picture**: if the data `(A, Ψ, …)` satisfy
`FinRel.IsRelConfigJK` (e.g. built by `FinRel.isRelConfigJK_of_s2_liftOn` from reflected S2 data), their reflections
satisfy `IsRelConfigJKL`. -/
theorem isRelConfigJKL_of_reflect {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ}
    {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ}
    (hc : FinRel.IsRelConfigJK A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v) :
    IsRelConfigJKL (reflectC '' A) (fun z => reflectC (Ψ (reflectC z))) (fun z => reflectC (Ψi (reflectC z)))
      (fun z => conj (LΨ (reflectC z))) (reflJumps Sb) (-w) (-Wr) (fun s => reflectC (η s))
      (fun s => reflectC (ηr s)) t u χ lam (reflData β₀) (reflData βE) (reflData βu) (reflJumps S₀)
      (reflJumps SE) (reflJumps Su) (fun z => -G₀ (reflectC z)) (fun z => -GE (reflectC z))
      (fun z => -G (reflectC z)) (fun z => -v (reflectC z)) := by
  simp only [IsRelConfigJKL, Sec7.FlowReflect.reflectC_image_image, LP.reflectC_reflectC, Complex.conj_conj,
    neg_neg, reflData_reflData, Restart.FCPlumb.FCKerD.reflJumps_reflJumps']
  exact hc

theorem reflectC_mem_H_diff_iff {S : Set ℂ} {z : ℂ} : z ∈ H \ reflectC '' S ↔ reflectC z ∈ H \ S := by
  rw [LP.H_diff_reflectC_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [LP.reflectC_reflectC]
  · intro hz
    exact ⟨reflectC z, hz, LP.reflectC_reflectC z⟩

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- **The union mean of the mirrored junction configuration, read in the retained chart, is the relative coupling
mean** (K2's `hmean` form; SB2(2), supplement pp. 631–633): `FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK`
with the configuration `IsRelConfigJKL` (retained set on the left of the explored hull), every other hypothesis and the
conclusion unchanged. -/
theorem ae_chartTransport_eq_couplingMean_of_relConfigJKL {κ : ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (w ω) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (w ω) (t ω))) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g₂)
    {D : Set Ω}
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigJKL (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) (chiC κ) lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - chiC κ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - chiC κ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ fwdHull (w ω) (t ω)))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hℓ : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcinv : ∀ ω, ∀ y ∈ H, (c ω).2.1 y = Ψi ω y) {ℓ₀ : ℝ}
    (hlift : ∀ ω, ∀ y ∈ H, (c ω).2.2 ((c ω).2.1 y) = (LΨ ω ((c ω).2.1 y)).im + ℓ₀) (a : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wr ω) (u ω)) →
      Chart.chartTransport (hc ω) 1 a (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ y, couplingMean κ (Wr ω) (u ω) (fun z => G ω z + (a + chiC κ * ℓ₀)) y * ψ y := by
  have hcont : ContinuousOn u₀ H := Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀
  have hcentF : WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z)) =
      fun ω => reflField (WholeField.centredField h u₀ ω) :=
    funext (Restart.FCPlumb.FCKerD.centredField_reflect hcont h)
  have hKr : (fun ω => fwdHull (-(w ω)) (t ω)) = fun ω => reflectC '' fwdHull (w ω) (t ω) :=
    funext fun ω => LP.fwdHull_neg (w ω) (t ω)
  -- the reflected inputs
  have hh0' : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P := by
    rw [hcentF]
    exact isZeroBoundaryGFF_reflField hh0
  have hu₀' : InnerProductSpace.HarmonicOnNhd (fun z => -u₀ (reflectC z)) H := by
    have h1 := Sec7.FlowReflect.harmonicOnNhd_comp_reflectC hu₀
    rw [Sec7.FlowReflect.reflectC_image_H] at h1
    exact h1.neg
  have hu₀b' : ∃ M : ℝ, ∀ z ∈ H, |-u₀ (reflectC z)| ≤ M := by
    obtain ⟨M, hM⟩ := hu₀b
    exact ⟨M, fun z hz => by rw [abs_neg]; exact hM _ (Sec7.FlowReflect.reflectC_mem_H hz)⟩
  have hAm' : Measurable[mΩ, hittingSigma] fun ω => reflectC '' A ω :=
    Sec7.FlowReflect.measurable_image_reflectC.comp hAm
  have hKm' : Measurable[mΩ, hittingSigma] fun ω => fwdHull (-(w ω)) (t ω) := by
    rw [hKr]
    exact Sec7.FlowReflect.measurable_image_reflectC.comp hKm
  have hdA' : MeasurableSpace.comap (fun ω => reflectC '' A ω) hittingSigma ≤
      aeSigma (MeasurableSpace.comap
        (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) inferInstance) P := by
    rw [hcentF, comap_image_reflectC, comap_reflField]
    exact hdA
  have hlA' : IsLocalSet (fun ω => reflectC '' A ω)
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P := by
    rw [hcentF]
    exact Sec7.FlowReflect.IsLocalSet.reflectC hlA
  have hlK' : IsLocalSet (fun ω => fwdHull (-(w ω)) (t ω))
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P := by
    rw [hcentF, hKr]
    exact Sec7.FlowReflect.IsLocalSet.reflectC hlK
  have hU : (fun ω => reflectC '' A ω ∪ fwdHull (-(w ω)) (t ω)) =
      fun ω => reflectC '' (A ω ∪ fwdHull (w ω) (t ω)) := by
    funext ω
    rw [LP.fwdHull_neg, image_union]
  have hlU' : IsLocalSet (fun ω => reflectC '' A ω ∪ fwdHull (-(w ω)) (t ω))
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P := by
    rw [hcentF, hU]
    exact Sec7.FlowReflect.IsLocalSet.reflectC hlU
  have hunbA' : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (reflectC '' A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (reflectC '' A ω)) z) := by
    filter_upwards [hunbA] with ω hω using forall_not_isBounded_component_reflect hω
  have hunbK' : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (-(w ω)) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (-(w ω)) (t ω))) z) := by
    filter_upwards [hunbK] with ω hω
    rw [LP.fwdHull_neg]
    exact forall_not_isBounded_component_reflect hω
  have hg' : IsLocalSetMean (fun ω => reflectC '' A ω ∪ fwdHull (-(w ω)) (t ω))
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P
      (fun ω => reflField (g ω)) := by
    rw [hcentF, hU]
    exact Restart.FCPlumb.FCKerD.IsLocalSetMean.reflect hg
  have hg₁' : IsLocalSetMean (fun ω => reflectC '' A ω)
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P
      (fun ω => reflField (g₁ ω)) := by
    rw [hcentF]
    exact Restart.FCPlumb.FCKerD.IsLocalSetMean.reflect hg₁
  have hg₂' : IsLocalSetMean (fun ω => fwdHull (-(w ω)) (t ω))
      (WholeField.centredField (fun ω => reflField (h ω)) (fun z => -u₀ (reflectC z))) P
      (fun ω => reflField (g₂ ω)) := by
    rw [hcentF, hKr]
    exact Restart.FCPlumb.FCKerD.IsLocalSetMean.reflect hg₂
  have hind₁' : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ reflectC '' A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ reflectC '' A ω →
        reflField (g₁ ω) φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + -u₀ (reflectC z))
        (fun z => -G₀ ω (reflectC (reflectC (Ψ ω (reflectC z)))) - chiC κ * (conj (LΨ ω (reflectC z))).im)
        (H \ reflectC '' A ω) := by
    filter_upwards [hind₁] with ω h1 hωD w₁ hw₁ hrep₁ z hz
    have e := h1 hωD _ (harmonicOnNhd_neg_comp_reflectC hw₁) (rep_of_reflField_rep hrep₁)
      (reflectC_mem_H_diff_iff.1 hz)
    simp only [LP.reflectC_reflectC, conj_im] at e ⊢
    linarith
  have hind₂' : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (-(w ω)) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (-(w ω)) (t ω) →
        reflField (g₂ ω) φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + -u₀ (reflectC z))
        (fun z => -GE ω (reflectC (fwdMap (-(w ω)) (t ω) z)) - chiC κ * (logDerivFwd (-(w ω)) (t ω) z).im)
        (H \ fwdHull (-(w ω)) (t ω)) := by
    filter_upwards [hind₂, hcfg] with ω h2 hcω hωD w₂ hw₂ hrep₂ z hz
    have ht : 0 ≤ t ω := (hcω hωD).ht
    rw [LP.fwdHull_neg] at hw₂ hrep₂ hz
    have e := h2 hωD _ (harmonicOnNhd_neg_comp_reflectC hw₂) (rep_of_reflField_rep hrep₂)
      (reflectC_mem_H_diff_iff.1 hz)
    have e1 : fwdMap (-(w ω)) (t ω) z = reflectC (fwdMap (w ω) (t ω) (reflectC z)) := by
      rw [← LP.fwdMap_neg (w ω) ht, LP.reflectC_reflectC]
    have e2 : (logDerivFwd (-(w ω)) (t ω) z).im = -(logDerivFwd (w ω) (t ω) (reflectC z)).im := by
      rw [← LP.im_logDerivFwd_neg (w ω) ht, LP.reflectC_reflectC]
    simp only [LP.reflectC_reflectC] at e ⊢
    rw [e1, e2, LP.reflectC_reflectC]
    linarith
  -- the reflected chart
  have hc' : ∀ ω, (Lf.reflChart (c ω)).IsConformal := fun ω => Lf.isConformal_reflChart (hc ω)
  have hℓ' : ∀ ω, ContinuousOn (Lf.reflChart (c ω)).2.2 (Lf.reflChart (c ω)).dom := fun ω =>
    continuousOn_lift_reflChart (hc ω) (hℓ ω)
  have hcinv' : ∀ ω, ∀ y ∈ H, (Lf.reflChart (c ω)).2.1 y = reflectC (Ψi ω (reflectC y)) := by
    intro ω y hy
    rw [Lf.reflChart_inv, hcinv ω _ (Lf.refl_mem_H hy)]
    rfl
  have hlift' : ∀ ω, ∀ y ∈ H, (Lf.reflChart (c ω)).2.2 ((Lf.reflChart (c ω)).2.1 y) =
      (conj (LΨ ω (reflectC ((Lf.reflChart (c ω)).2.1 y)))).im + -ℓ₀ := by
    intro ω y hy
    have e := hlift ω _ (Lf.refl_mem_H hy)
    rw [Lf.refl_eq_reflectC] at e
    rw [Lf.reflChart_lift, Lf.reflChart_inv, Lf.refl_eq_reflectC, LP.reflectC_reflectC, conj_im, e]
    ring
  have hres := FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK (κ := κ) (P := P)
    (h := fun ω => reflField (h ω)) (u₀ := fun z => -u₀ (reflectC z)) hh0' hu₀' hu₀b' hAm' hKm' hdA' hlA' hlK'
    hlU' hunbA' hunbK' hg' hg₁' hg₂' hcfg hind₁' hind₂' hc' hℓ' hcinv' hlift' (-a)
  -- reflect back
  filter_upwards [hres, hcfg] with ω hr hcω hωD ψ hψ
  have hu : 0 ≤ u ω := (hcω hωD).hu
  have hdisj : Disjoint (tsupport ⇑(-reflTest ψ)) (fwdHull (-(Wr ω)) (u ω)) := by
    rw [LP.fwdHull_neg]
    exact Sec7.FlowReflect.disjoint_reflTest (by rwa [Sec7.FlowReflect.reflectC_image_image])
  have e := hr hωD (-reflTest ψ) hdisj
  rw [Restart.FCPlumb.FCKerD.smoothDist_reflect hcont, ← Sec7.FlowReflect.reflField_add,
    chartTransport_reflChart (hc ω) (hℓ ω) a (chiC κ), Sec7.FlowReflect.reflField_apply_eq,
    Sec7.FlowReflect.reflTest_neg, Sec7.FlowReflect.reflTest_reflTest, neg_neg] at e
  have hfun : (fun z => -G ω (reflectC z) + (-a + chiC κ * -ℓ₀)) =
      fun y => -(fun z => G ω z + (a + chiC κ * ℓ₀)) (reflectC y) := by
    funext y
    ring
  have hI := Sec7.FlowReflect.integral_couplingMean_reflect κ (-(Wr ω)) hu
    (fun z => G ω z + (a + chiC κ * ℓ₀)) ψ
  rw [neg_neg] at hI
  rw [e, ← hI, hfun]

end Mean

end InteractingSLE.Theorem14.SB.Lm
