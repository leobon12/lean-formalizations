/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Chamber2
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Corollary 4.8 through a half-plane chart

Packet PROVE-WW-B11. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Corollary 4.8
(text dump L1156–1166), in the form needed on slit domains (proof of Proposition 4.18, L1611–1615: "The union
boundary lemma identifies its harmonic mean on every exposed open arc. The only exceptions are the finitely many
slit tips, starting prime ends, and original boundary jumps. Corollary 4.8 excludes singular contributions there and
identifies the bounded mean"; Proposition 4.20 for stopped lines, L1730–1736).

A slit domain `C = ℍ \ (K₁ ∪ K₂)` is naturally charted from `ℍ` (by composing inverse mapping-out functions), not
from the disc, and its prime ends are then read as points of `ℝ ∪ {∞}`. This file restates PROVE-WW-TRACE's
`ae_eqOn_of_condMean_global` for such charts:

* `tendsto_comp_cayleyInv_of_tendsto_real` (deterministic): if `u ∘ Φ → 0` at every real point outside a finite set
  `E`, then `u ∘ Φ ∘ cayleyInv → 0` at every circle point outside the finite set `{1} ∪ cayley(E)` (the point `1`
  is the prime end at `∞`);
* `isConformalBijection_comp_cayleyInv`: a half-plane chart `Φ : ℍ → C` gives the disc chart `Φ ∘ cayleyInv`;
* **`ae_eqOn_of_condMean_halfPlaneChart`** (Corollary 4.8 through a half-plane chart): almost surely, for every
  harmonic representative `w` of the conditional mean on `ℍ \ A`, every open `C ⊆ ℍ \ A` with a conformal bijection
  `Φ : ℍ → C`, and every bounded harmonic `v` on `C` such that `(w − v) ∘ Φ → 0` at every real point outside a finite
  set, `w = v` on `C`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open QuantumZipper (H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.WangWu

/-! ### From real boundary points to circle points -/

/-- A circle point other than `1` is the Cayley image of the real point `cayleyInv q`. -/
theorem cayleyInv_eq_ofReal_of_mem_sphere {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) :
    cayleyInv q = ((cayleyInv q).re : ℂ) := by
  have him : (cayleyInv q).im = 0 := by
    rw [QuantumZipper.CA.im_cayleyInv, mem_sphere_zero_iff_norm.1 hq]
    simp
  exact Complex.ext (by simp) (by simp [him])

/-- **Boundary limits at real points give boundary limits at circle points.** If `u ∘ Φ → 0` from `ℍ` at every real
point outside a finite set `E`, then `u ∘ Φ ∘ cayleyInv → 0` from the disc at every circle point outside the finite
set `{1} ∪ cayley(E)`. -/
theorem tendsto_comp_cayleyInv_of_tendsto_real {Φ : ℂ → ℂ} {u : ℂ → ℝ} {E : Set ℝ}
    (hlim : ∀ x : ℝ, x ∉ E → Tendsto (fun y => u (Φ y)) (𝓝[H] (x : ℂ)) (𝓝 0)) {q : ℂ}
    (hq : q ∈ sphere (0 : ℂ) 1) (hqE : q ∉ insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' E)) :
    Tendsto (fun ζ => u (Φ (cayleyInv ζ))) (𝓝[ball 0 1] q) (𝓝 0) := by
  have hq1 : q ≠ 1 := fun h => hqE (h ▸ mem_insert _ _)
  set x : ℝ := (cayleyInv q).re with hx
  have hxq : cayleyInv q = (x : ℂ) := cayleyInv_eq_ofReal_of_mem_sphere hq
  have hxE : x ∉ E := by
    intro hxE
    refine hqE (mem_insert_of_mem _ ⟨x, hxE, ?_⟩)
    show cayley (x : ℂ) = q
    rw [← hxq, QuantumZipper.CA.cayley_cayleyInv hq1]
  have hc : Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ =>
      QuantumZipper.CA.cayleyInv_mem_H hζ⟩
    rw [← hxq]
    exact (continuousAt_cayleyInv hq1).tendsto.mono_left nhdsWithin_le_nhds
  exact (hlim x hxE).comp hc

/-- The exceptional circle set `{1} ∪ cayley(E)` is finite for finite `E`. -/
theorem finite_insert_cayley_image {E : Set ℝ} (hE : E.Finite) :
    (insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' E)).Finite :=
  (hE.image _).insert 1

/-- **A half-plane chart gives a disc chart.** -/
theorem isConformalBijection_comp_cayleyInv {Φ : ℂ → ℂ} {C : Set ℂ} (hΦ : IsConformalBijection Φ H C) :
    IsConformalBijection (fun ζ => Φ (cayleyInv ζ)) (ball 0 1) C := by
  obtain ⟨hd, hb⟩ := InteractingSLE.isConformalBijection_cayleyInv
  refine ⟨fun ζ hζ => ?_, hΦ.2.comp hb⟩
  exact ((hΦ.1 _ (hb.mapsTo hζ)).differentiableAt
    (QuantumZipper.isOpen_H.mem_nhds (hb.mapsTo hζ))).comp_differentiableWithinAt ζ (hd ζ hζ)

/-! ### Corollary 4.8 through a half-plane chart -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Wang–Wu Corollary 4.8 through a half-plane chart.** Under the hypotheses of Lemma 4.6 (`h` a zero-boundary GFF,
`h₁` a version of its conditional mean given `𝒜`, `ℍ \ A` open), almost surely the following holds for every harmonic
representative `w` of the conditional mean on `ℍ \ A`: if `C ⊆ ℍ \ A` is open with a conformal bijection
`Φ : ℍ → C`, and `v` is a bounded harmonic function on `C` such that `w ∘ Φ − v ∘ Φ → 0` at every real point outside a
finite set `E` (the prime ends of `C` read through `Φ`, all but finitely many), then `w = v` on `C`. -/
theorem ae_eqOn_of_condMean_halfPlaneChart [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, w z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ H \ A ω →
      ∀ Φ : ℂ → ℂ, IsConformalBijection Φ H C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℝ, E.Finite →
      (∀ x : ℝ, x ∉ E → Tendsto (fun y => w (Φ y) - v (Φ y)) (𝓝[H] (x : ℂ)) (𝓝 0)) →
      EqOn w v C := by
  filter_upwards [ae_eqOn_of_condMean_global hh hmean hopen] with ω hω
  intro w hw hrep C hCo hCU Φ hΦ v hv hvb E hE hlim
  exact hω w hw hrep C hCo hCU _ (isConformalBijection_comp_cayleyInv hΦ) v hv hvb _
    (finite_insert_cayley_image hE) fun q hq hqE =>
      tendsto_comp_cayleyInv_of_tendsto_real (u := fun z => w z - v z) hlim hq hqE

/-- **Corollary 4.8 through a half-plane chart, for a field with bounded harmonic mean** (`F = h + F₀`,
`|F₀| ≤ M_F` on `ℍ`, `h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]`). -/
theorem ae_eqOn_of_condMean_add_halfPlaneChart [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ}
    (hF₀ : ∀ z ∈ H, |F₀ z| ≤ MF)
    {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, w z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ H \ A ω →
      ∀ Φ : ℂ → ℂ, IsConformalBijection Φ H C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℝ, E.Finite →
      (∀ x : ℝ, x ∉ E → Tendsto (fun y => w (Φ y) - v (Φ y)) (𝓝[H] (x : ℂ)) (𝓝 0)) →
      EqOn w v C := by
  filter_upwards [ae_eqOn_of_condMean_add_global hh h𝒜 hF₀ hmean hopen] with ω hω
  intro w hw hrep C hCo hCU Φ hΦ v hv hvb E hE hlim
  exact hω w hw hrep C hCo hCU _ (isConformalBijection_comp_cayleyInv hΦ) v hv hvb _
    (finite_insert_cayley_image hE) fun q hq hqE =>
      tendsto_comp_cayleyInv_of_tendsto_real (u := fun z => w z - v z) hlim hq hqE

/-! ### Slit domains charted from `ℍ` -/

section Slit

open QuantumZipper (fwdMapInv fwdHull)

variable {W : ℝ → ℝ} {t : ℝ}

/-- **Removing a Loewner hull in a half-plane chart.** If `Φ : ℍ → C` is a conformal bijection and `K_t` is the hull of
a continuous driver, then `Φ ∘ F_t` (`F_t` the inverse mapping-out function) is a conformal bijection of `ℍ` onto
`C \ Φ(K_t)`. -/
theorem isConformalBijection_comp_fwdMapInv {Φ : ℂ → ℂ} {C : Set ℂ} (hΦ : IsConformalBijection Φ H C)
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    IsConformalBijection (fun y => Φ (fwdMapInv W t y)) H (C \ Φ '' fwdHull W t) := by
  obtain ⟨hd, hb⟩ := InteractingSLE.isConformalBijection_fwdMapInv hW hW0 ht
  have hKH : fwdHull W t ⊆ H := fun z hz => hz.1
  have hb' : BijOn Φ (H \ fwdHull W t) (C \ Φ '' fwdHull W t) := by
    have h1 : BijOn Φ (H \ fwdHull W t) (Φ '' (H \ fwdHull W t)) :=
      (hΦ.2.injOn.mono sdiff_subset).bijOn_image
    rwa [hΦ.2.injOn.image_sdiff_subset hKH, hΦ.2.image_eq] at h1
  refine ⟨fun y hy => ?_, hb'.comp hb⟩
  have hFy : fwdMapInv W t y ∈ H := (hb.mapsTo hy).1
  exact ((hΦ.1 _ hFy).differentiableAt (QuantumZipper.isOpen_H.mem_nhds hFy)).comp_differentiableWithinAt y
    (hd y hy)

/-- **The reversed slit.** For the hull `K_s` of a continuous driver, `R ∘ F_s ∘ R` (`R(z) = −1/z`) is a conformal
bijection of `ℍ` onto `ℍ \ R(K_s)`: the chart of the domain slit by the reflected reverse hull. -/
theorem isConformalBijection_negInv_fwdMapInv_negInv (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    IsConformalBijection (fun y => negInv (fwdMapInv W t (negInv y))) H (H \ negInv '' fwdHull W t) := by
  have h1 := isConformalBijection_comp_fwdMapInv isConformalBijection_negInv hW hW0 ht
  obtain ⟨hd, hb⟩ := h1
  refine ⟨fun y hy => ?_, ?_⟩
  · have hRy : negInv y ∈ H := negInv_mem_H hy
    exact (hd _ hRy).comp y (differentiableOn_negInv y hy) (fun z hz => negInv_mem_H hz)
  · have hR : BijOn negInv H H := isConformalBijection_negInv.2
    exact hb.comp hR

/-- **Boundary limits through a removed hull at real points.** If `F_t(y) → x'` (a real point) as `y → x` in `ℍ`, and
`u ∘ Φ → ℓ` at `x'`, then `u ∘ Φ ∘ F_t → ℓ` at `x`. -/
theorem tendsto_comp_fwdMapInv_of_tendsto {Φ : ℂ → ℂ} {u : ℂ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) {x x' : ℂ} {ℓ : ℝ} (hF : Tendsto (fwdMapInv W t) (𝓝[H] x) (𝓝 x'))
    (hlim : Tendsto (fun y => u (Φ y)) (𝓝[H] x') (𝓝 ℓ)) :
    Tendsto (fun y => u (Φ (fwdMapInv W t y))) (𝓝[H] x) (𝓝 ℓ) := by
  have hmaps := (InteractingSLE.isConformalBijection_fwdMapInv hW hW0 ht).2.mapsTo
  exact hlim.comp (tendsto_nhdsWithin_iff.2 ⟨hF, eventually_nhdsWithin_of_forall fun y hy => (hmaps hy).1⟩)

end Slit

end InteractingSLE.WangWu
