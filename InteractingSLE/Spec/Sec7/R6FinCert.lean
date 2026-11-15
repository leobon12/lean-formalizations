/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6RelCert

/-!
# R.6 certificates from pathwise geometry, inner words and germ comparisons

PROVE-R6-CERT2. `R6Rel.R6Cert` (the phase-free certificate of PROVE-R6-NESTREL) combines three kinds of data of
different origin:

* the **pathwise current-face geometry** (the transition between the two current charts and its interval `J`, the
  collars at a shared-side point and an exposed point, their landing points and the local agreement of the two sets
  there, and the side conditions on the marks): `R6Geom`;
* the **inner word** (R.5 for the nested pocket with zero phase): the limits of the corrected inner reading at every
  non-jump point;
* the **germ comparisons** (`R6Cert.ae_r6Germ_outer_cf`): for all harmonic representatives, all nested conformal
  charts, collars and landings with local agreement of the two sets.

`r6Cert_of_geom` assembles a certificate deterministically. `ae_exists_r6Cert_of_family` does it almost surely for a
countable family of inner candidates (in the applications: the inner pocket read at the rational relative times
`q'`), each with its own almost sure word and germ statements, when almost surely on the event some live candidate
has the pathwise geometry.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.R6Fin

open PocketStopSide R6Rel

/-! ### The pathwise geometry -/

section Geom

/-- **A physical landing with local agreement** at the outer real point `y`: the outer inverse chart lands at `p`,
`p` lies in both sets or on the real line, and the two sets agree near `p` (the hypotheses of the germ comparison
`R6Cert.ae_r6Germ_outer_cf` at `y`). -/
def LocalLanding (outer : Chart) (EC EU : Set ℂ) (y : ℝ) (p : ℂ) : Prop :=
  Tendsto outer.2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧ p ∈ EC ∪ {z : ℂ | z.im = 0} ∧ p ∈ EU ∪ {z : ℂ | z.im = 0} ∧
    (∃ ε > 0, EU ∩ ball p ε ⊆ EC) ∧ (∃ ε > 0, EC ∩ ball p ε ⊆ EU)

/-- **The pathwise current-face geometry of R.6** between the outer current chart (word `(ρL, ρR)` at marks
`(vL, vR)`, set `EC`) and an inner current chart (word `(σL, σR)` at marks `(wL, wR)`, set `EU`): the current domains
are the complements of the two sets, R.6's transition geometry on a connected real interval `J`, a shared-side point
`y₀` (outside the outer exposed interval) and an exposed point `ξ` (inside it) with collars, non-jump images `η₀`, `η`
on the matching inner sides, equal canonical heights, and physical landings with local agreement of the two sets.
Everything in `R6Rel.R6Cert` except the inner limits and the germ comparisons. -/
def R6Geom (κ : ℝ) {nL nR mL mR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (σL : Fin (mL + 1) → ℝ)
    (σR : Fin (mR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (wL : Fin (mL + 1) → ℝ)
    (wR : Fin (mR + 1) → ℝ) (outer inner : Chart) (EC EU : Set ℂ) : Prop :=
  (outer.dom : Set ℂ) = H \ EC ∧ (inner.dom : Set ℂ) = H \ EU ∧
    ∃ (J : Set ℝ) (G Lg : ℂ → ℂ) (y₀ η₀ ξ η : ℝ) (p₀ p : ℂ), R6Transition outer inner J G Lg ∧
      (R6Collar outer inner J G Lg y₀ η₀ ∧ y₀ ∉ forceJumpSet vL vR ∧ y₀ ∉ Ioo (vL 0) (vR 0) ∧
        η₀ ∉ forceJumpSet wL wR ∧ η₀ ∉ Ioo (wL 0) (wR 0) ∧
        forceBoundaryData κ ρL ρR vL vR y₀ = forceBoundaryData κ σL σR wL wR η₀ ∧ LocalLanding outer EC EU y₀ p₀) ∧
      (R6Collar outer inner J G Lg ξ η ∧ ξ ∉ forceJumpSet vL vR ∧ ξ ∈ Ioo (vL 0) (vR 0) ∧
        η ∉ forceJumpSet wL wR ∧ η ∈ Ioo (wL 0) (wR 0) ∧
        forceBoundaryData κ ρL ρR vL vR ξ = forceBoundaryData κ σL σR wL wR η ∧ LocalLanding outer EC EU ξ p)

/-- The germ comparison in the form produced by `R6Cert.ae_r6Germ_outer_cf` for fixed harmonic representatives. -/
def GermAt (EC EU : Set ℂ) (v vI : ℂ → ℝ) : Prop :=
  ∀ outer inner : Chart, outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
    (outer.dom : Set ℂ) = H \ EC → (inner.dom : Set ℂ) = H \ EU →
    ∀ (p : ℂ) (ξ ρ : ℝ), p ∈ EC ∪ {z : ℂ | z.im = 0} → p ∈ EU ∪ {z : ℂ | z.im = 0} →
      (∃ ε > 0, EU ∩ ball p ε ⊆ EC) → (∃ ε > 0, EC ∩ ball p ε ⊆ EU) → 0 < ρ →
      H ∩ ball (ξ : ℂ) ρ ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
      Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → R6Germ outer v vI ξ

/-- The phase-`0` word data are the force-word data. -/
theorem phaseData_zero_eq (κ : ℝ) {mL mR : ℕ} (σL : Fin (mL + 1) → ℝ) (σR : Fin (mR + 1) → ℝ)
    (wL : Fin (mL + 1) → ℝ) (wR : Fin (mR + 1) → ℝ) (x : ℝ) :
    PhaseSel.phaseData κ σL σR wL wR 0 x = forceBoundaryData κ σL σR wL wR x := by
  simp only [PhaseSel.phaseData, zero_mul, add_zero]

/-- **A certificate from the pathwise geometry, the inner word and the germ comparison** (deterministic). -/
theorem r6Cert_of_geom {κ : ℝ} {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    {wL : Fin (mL + 1) → ℝ} {wR : Fin (mR + 1) → ℝ} {outer inner : Chart} {EC EU : Set ℂ} {u v vI : ℂ → ℝ}
    {aI : ℝ} (hgeom : R6Geom κ ρL ρR σL σR vL vR wL wR outer inner EC EU)
    (hlim : ∀ x : ℝ, x ∉ forceJumpSet wL wR →
      Tendsto (sideMean κ inner u vI) (𝓝[H] (x : ℂ)) (𝓝 (forceBoundaryData κ σL σR wL wR x - aI)))
    (hgerm : GermAt EC EU v vI) : R6Cert κ ρL ρR vL vR outer u v := by
  obtain ⟨hOd, hId, J, G, Lg, y₀, η₀, ξ, η, p₀, p, htr,
    ⟨hcol₀, hy₀j, hy₀o, hη₀j, hη₀o, hh₀, hl₀, hp₀C, hp₀U, hag₀, hag₀'⟩,
    ⟨hcol, hξj, hξi, hηj, hηi, hh, hl, hpC, hpU, hag, hag'⟩⟩ := hgeom
  have hO := htr.1
  have hI := htr.2.1
  have hinc := htr.2.2.1
  have hg₀ : R6Germ outer v vI y₀ := by
    obtain ⟨-, ⟨r₀, hr₀, hsub₀⟩, -, -⟩ := hcol₀
    exact hgerm outer inner hO hI hinc hOd hId p₀ y₀ r₀ hp₀C hp₀U hag₀ hag₀' hr₀ hsub₀ hl₀
  have hg : R6Germ outer v vI ξ := by
    obtain ⟨-, ⟨r, hr, hsub⟩, -, -⟩ := hcol
    exact hgerm outer inner hO hI hinc hOd hId p ξ r hpC hpU hag hag' hr hsub hl
  refine ⟨inner, J, G, Lg, mL, mR, σL, σR, wL, wR, vI, aI, y₀, η₀, ξ, η, htr,
    ⟨hcol₀, hy₀j, hy₀o, hη₀o, hh₀, ?_, hg₀⟩, ⟨hcol, hξj, hξi, hηi, hh, ?_, hg⟩⟩
  · rw [phaseData_zero_eq]; exact hlim η₀ hη₀j
  · rw [phaseData_zero_eq]; exact hlim η hηj

end Geom

/-! ### Almost surely, from a countable family of inner candidates -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Certificates almost surely on an event from a countable family of inner candidates**: the outer local-set mean
`g` and every candidate's mean `gU i` have harmonic representatives almost surely, every candidate's corrected reading
has its zero-phase word (offset `aI i`) almost surely on its live event `Live i`, and its germ comparison holds almost
surely; if almost surely on `E` some live candidate has the pathwise geometry, then almost surely on `E` the outer mean
has a harmonic representative with an R.6 certificate. -/
theorem ae_exists_r6Cert_of_family {κ : ℝ} {nL nR mL mR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {σL : Fin (mL + 1) → ℝ} {σR : Fin (mR + 1) → ℝ} {ι : Type*} [Countable ι] {u : ℂ → ℝ} {E : Set Ω}
    {EC : Ω → Set ℂ} {outer : Ω → Chart} {g : Ω → DistOn upperHalfPlaneOpens}
    {vL : Ω → Fin (nL + 1) → ℝ} {vR : Ω → Fin (nR + 1) → ℝ} {EU : ι → Ω → Set ℂ} {inner : ι → Ω → Chart}
    {gU : ι → Ω → DistOn upperHalfPlaneOpens} {wL : ι → Ω → Fin (mL + 1) → ℝ} {wR : ι → Ω → Fin (mR + 1) → ℝ}
    {aI : ι → ℝ} {Live : ι → Set Ω}
    (hg : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ EC ω))
    (hgU : ∀ i, ∀ᵐ ω ∂P, IsHarmonicDistOn (gU i ω) (H \ EU i ω))
    (hlim : ∀ i, ∀ᵐ ω ∂P, ω ∈ Live i → ∀ vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd vI (H \ EU i ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU i ω → gU i ω φ = ∫ z, vI z * φ z) →
      ∀ x : ℝ, x ∉ forceJumpSet (wL i ω) (wR i ω) →
        Tendsto (sideMean κ (inner i ω) u vI) (𝓝[H] (x : ℂ))
          (𝓝 (forceBoundaryData κ σL σR (wL i ω) (wR i ω) x - aI i)))
    (hgerm : ∀ i, ∀ᵐ ω ∂P, ∀ v vI : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ EC ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vI (H \ EU i ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EU i ω → gU i ω φ = ∫ z, vI z * φ z) →
      GermAt (EC ω) (EU i ω) v vI)
    (hgeom : ∀ᵐ ω ∂P, ω ∈ E → ∃ i, ω ∈ Live i ∧
      R6Geom κ ρL ρR σL σR (vL ω) (vR ω) (wL i ω) (wR i ω) (outer ω) (inner i ω) (EC ω) (EU i ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ EC ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ EC ω → g ω φ = ∫ z, v z * φ z) ∧
      R6Cert κ ρL ρR (vL ω) (vR ω) (outer ω) u v := by
  filter_upwards [hg, ae_all_iff.2 hgU, ae_all_iff.2 hlim, ae_all_iff.2 hgerm, hgeom] with ω hgω hgUω hlimω hgermω
    hgeomω hωE
  obtain ⟨v, hv, hvr⟩ := hgω
  obtain ⟨i, hi, hgi⟩ := hgeomω hωE
  obtain ⟨vI, hvI, hvIr⟩ := hgUω i
  exact ⟨v, hv, hvr, r6Cert_of_geom hgi (hlimω i hi vI hvI hvIr) (hgermω i v vI hv hvr hvI hvIr)⟩

end Family

end InteractingSLE.Sec7.R6Fin
