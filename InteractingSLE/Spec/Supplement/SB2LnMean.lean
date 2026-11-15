/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LnPull

/-!
# SB2(2)'s union mean through B's stage chart (route α, P level)

Packet PROVE-SB2-LCMEAN, round 2. The source identifies SB2(2)'s union mean in physical coordinates (supplement p. 632:
"the finite-exception Poisson uniqueness argument identifies the entire mean, and the union kernel identifies its
zero-boundary Green covariance"). The retained set is `A₁ = A ∪ fill B_{<ℓ}` (the upper prefix and the filled earlier
lower pieces), the explored set `A₂ = fill B_{≤ℓ,s}` (the lower walk prefix through piece `ℓ` at own time `s`); in B's
stage-`ℓ` chart `c` they read as the chart image `A'` of `A` and the chordal hull `K_t` of piece `ℓ`, in the mirrored
configuration `Lm.IsRelConfigJKL`.

* **`IsStagePullback`**: the deterministic properties of the stage chart used (conformal chart with lift equal to the
  argument of its derivative; inverse with a continuous, proper boundary map `g` on `ℍ̄` with finite fibres sending `ℝ`
  into `(ℍ ∖ D) ∪ ℝ`; the domain's complement inside both sets; the set correspondences) — FIN's S2 data
  (`FinRel.isRelConfigJK_of_s2_liftOn`'s `hgc`, `hgi`, `hgf`) for the walk's run chart;
* `stageComp`: the physical relative component `{z ∈ ℍ ∖ (A₁ ∪ A₂) | c.1 z ∈ C'}`;
* **`IsStagePullback.hasUnionWordBoundaryOnC`**: the mirrored configuration in the chart and the physical
  individual-mean formulas give the physical union word datum;
* **`ae_eqOn_unionMean_of_stagePullback`**: the P-level union mean: almost surely on `D`, on the physical relative
  component, union mean `+ u₀ = v ∘ c.1 − χ c.2.2` (the relative candidate pulled back);
* **`ae_chartTransport_eq_couplingMean_of_stagePullback`**: K2's `hmean` form in the composite relative chart.

R48: Theorems 1.2–1.3 are not used. Conditional helpers with distinct names; the inputs are the actual objects'
properties (locality, means, the stage-chart geometry), none is a proof step of the conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Ln

open FinRel (freeNear HasUnionWordBoundaryOnC)
open _root_.InteractingSLE.Theorem14.SB.Union (relComp)
open LocalSets WholeField

/-- **The deterministic properties of a stage chart used to pull the union datum back**: `c` is B's stage chart, `g`
the boundary map of its inverse, `A₁`/`A₂` the physical retained/explored sets and `A₁'`/`A₂'` their chart images. -/
structure IsStagePullback (c : Chart) (g : ℂ → ℂ) (A₁ A₂ A₁' A₂' : Set ℂ) : Prop where
  conf : c.IsConformal
  liftc : ContinuousOn c.2.2 c.dom
  liftd : ∀ z ∈ (c.dom : Set ℂ), deriv c.1 z = ‖deriv c.1 z‖ * Complex.exp (c.2.2 z * Complex.I)
  gc : ContinuousOn g Hbar
  gi : EqOn g c.2.1 H
  gf : ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite
  gp : ∀ M : ℝ, ∃ R : ℝ, ∀ z ∈ Hbar, R < ‖z‖ → M < ‖g z‖
  gR : ∀ x : ℝ, g x ∈ (H \ (c.dom : Set ℂ)) ∪ {z : ℂ | z.im = 0}
  dom₁ : H \ (c.dom : Set ℂ) ⊆ A₁
  dom₂ : H \ (c.dom : Set ℂ) ⊆ A₂
  corr₁ : ∀ w ∈ H, c.2.1 w ∈ A₁ ↔ w ∈ A₁'
  corr₂ : ∀ w ∈ H, c.2.1 w ∈ A₂ ↔ w ∈ A₂'

/-- The physical relative component: the points off both sets whose chart image lies in `C'`. -/
def stageComp (c : Chart) (A₁ A₂ C' : Set ℂ) : Set ℂ := {z | z ∈ H \ (A₁ ∪ A₂) ∧ c.1 z ∈ C'}

theorem stageComp_subset (c : Chart) (A₁ A₂ C' : Set ℂ) : stageComp c A₁ A₂ C' ⊆ H \ (A₁ ∪ A₂) :=
  fun _ hz => hz.1

/-- **The physical union word datum through B's stage chart**: the mirrored configuration in the chart and the
physical individual-mean formulas (read through the chart) give the union word datum of `A₁ ∪ A₂` on the physical
relative component, with candidate `v ∘ c.1 − χ c.2.2`. -/
theorem IsStagePullback.hasUnionWordBoundaryOnC {c : Chart} {gb : ℂ → ℂ} {A₁ A₂ A : Set ℂ}
    {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ}
    {S₀ SE Su : Finset ℝ} {G₀ GE G v u₀ w₁ w₂ : ℂ → ℝ}
    (hp : IsStagePullback c gb A₁ A₂ A (fwdHull w t))
    (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ (c.1 z)) - χ * ((LΨ (c.1 z)).im + c.2.2 z)) (H \ A₁))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z)
      (fun z => GE (fwdMap w t (c.1 z)) - χ * ((logDerivFwd w t (c.1 z)).im + c.2.2 z)) (H \ A₂)) :
    HasUnionWordBoundaryOnC (stageComp c A₁ A₂ (relComp A Ψ Wr u)) A₁ A₂ u₀ (fun z => v (c.1 z) - χ * c.2.2 z)
      w₁ w₂ χ βu Su := by
  have hinvD : ∀ y ∈ H, c.2.1 y ∈ (c.dom : Set ℂ) := fun y hy => inv_mem_dom hp.conf hy
  set w₁' : ℂ → ℝ := fun y => w₁ (c.2.1 y) + u₀ (c.2.1 y) + χ * c.2.2 (c.2.1 y) with hw₁'
  set w₂' : ℂ → ℝ := fun y => w₂ (c.2.1 y) + u₀ (c.2.1 y) + χ * c.2.2 (c.2.1 y) with hw₂'
  have hc₁ : EqOn (fun y => w₁' y + (fun _ => (0 : ℝ)) y) (fun y => G₀ (Ψ y) - χ * (LΨ y).im) (H \ A) := by
    intro y hy
    have hz : c.2.1 y ∈ H \ A₁ := ⟨hp.conf.2.1 hy.1, fun h => hy.2 ((hp.corr₁ y hy.1).1 h)⟩
    have e := hw₁ hz
    simp only [hp.conf.2.2 y hy.1] at e
    simp only [hw₁']
    linarith
  have hc₂ : EqOn (fun y => w₂' y + (fun _ => (0 : ℝ)) y)
      (fun y => GE (fwdMap w t y) - χ * (logDerivFwd w t y).im) (H \ fwdHull w t) := by
    intro y hy
    have hz : c.2.1 y ∈ H \ A₂ := ⟨hp.conf.2.1 hy.1, fun h => hy.2 ((hp.corr₂ y hy.1).1 h)⟩
    have e := hw₂ hz
    simp only [hp.conf.2.2 y hy.1] at e
    simp only [hw₂']
    linarith
  have hdat := IsRelConfigJKL.hasUnionWordBoundaryOnK hc hc₁ hc₂
  have hpb : ∀ (wi : ℂ → ℝ), ∀ z ∈ H \ (A₁ ∪ A₂),
      wi z + u₀ z = (wi (c.2.1 (c.1 z)) + u₀ (c.2.1 (c.1 z)) + χ * c.2.2 (c.2.1 (c.1 z))) +
        (fun _ => (0 : ℝ)) (c.1 z) - χ * c.2.2 z := by
    intro wi z hz
    have hzD : z ∈ (c.dom : Set ℂ) := by
      by_contra hzD
      exact hz.2 (Or.inl (hp.dom₁ ⟨hz.1, hzD⟩))
    rw [(chart_fwd_mem_of_mem_dom hp.conf hzD).2]
    ring
  exact hasUnionWordBoundaryOnC_pullback hp.conf hp.liftc hp.liftd hp.gc hp.gi hp.gf hp.gp hp.gR
    (IsRelConfigJKL.isOpen_compl_union hc) hp.dom₁ hp.dom₂ hp.corr₁ hp.corr₂ (fun z hz => hz)
    (hpb w₁) (hpb w₂) (fun z _ => rfl) hdat

/-! ### The mirrored configuration read in the original picture -/

section Accessors

open LP (reflectC)

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ}
  {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G v : ℂ → ℝ}

theorem IsRelConfigJKL.inv_mem (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {y : ℂ} (hy : y ∈ H) : Ψi y ∈ H \ A := by
  have h := (FinRel.IsRelConfigJK.chart hc).inv_mem (reflectC y) (Sec7.FlowReflect.reflectC_mem_H hy)
  rw [Lm.reflectC_mem_H_diff_iff, LP.reflectC_reflectC, LP.reflectC_reflectC] at h
  exact h

theorem IsRelConfigJKL.fwd_inv (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {y : ℂ} (hy : y ∈ H) : Ψ (Ψi y) = y := by
  have h := (FinRel.IsRelConfigJK.chart hc).fwd_inv (reflectC y) (Sec7.FlowReflect.reflectC_mem_H hy)
  simp only [LP.reflectC_reflectC] at h
  have h2 := congrArg reflectC h
  rwa [LP.reflectC_reflectC, LP.reflectC_reflectC] at h2

theorem IsRelConfigJKL.relComp_subset
    (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v) :
    relComp A Ψ Wr u ⊆ H \ (A ∪ fwdHull w t) := by
  have h := Union.relComp_subset (FinRel.IsRelConfigJK.hullIn hc)
  rw [relComp_reflect, LP.fwdHull_neg, H_diff_union_image_reflectC] at h
  exact (image_subset_image_iff LP.reflectC_injective).1 h

/-- The relative candidate of the mirrored configuration, in the original picture. -/
theorem IsRelConfigJKL.cand (hc : Lm.IsRelConfigJKL A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    (z : ℂ) : v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im) := by
  have hu : 0 ≤ u := FinRel.IsRelConfigJK.hu hc
  have h := FinRel.IsRelConfigJK.cand hc (reflectC z)
  simp only [LP.reflectC_reflectC, LP.fwdMap_neg Wr hu, LP.im_logDerivFwd_neg Wr hu, Complex.conj_im] at h
  linarith

end Accessors

/-! ### The P-level union mean -/

section Mean

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

/-- **SB2(2)'s union mean through B's stage chart** (supplement p. 632): if the physical retained set `A₁` and
explored set `A₂` are local with means, `A₁` is determined by the field, the stage chart has the pull-back properties
`IsStagePullback` and, in it, the mirrored configuration `Lm.IsRelConfigJKL` holds with the individual means given by
the retained-chart and explored-chain formulas read through the chart, then almost surely on `D` the union mean plus
`u₀` is the relative candidate pulled back, `v ∘ c.1 − χ c.2.2`, on the physical relative component. -/
theorem ae_eqOn_unionMean_of_stagePullback
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A₁ A₂ : Ω → Set ℂ} (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hl₁ : IsLocalSet A₁ (WholeField.centredField h u₀) P) (hl₂ : IsLocalSet A₂ (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean A₂ (WholeField.centredField h u₀) P g₂)
    {c : Ω → Chart} {gb : Ω → ℂ → ℂ} {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ}
    {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ} {t u : Ω → ℝ} {χ lam : ℝ} {β₀ βE βu : Ω → ℝ → ℝ}
    {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ} {D : Set Ω}
    (hpb : ∀ᵐ ω ∂P, ω ∈ D → IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) (A ω) (fwdHull (w ω) (t ω)))
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → Lm.IsRelConfigJKL (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω)
      (t ω) (u ω) χ lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z)
        (fun z => G₀ ω (Ψ ω ((c ω).1 z)) - χ * ((LΨ ω ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₁ ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) ((c ω).1 z)) -
        χ * ((logDerivFwd (w ω) (t ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A₁ ω ∪ A₂ ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A₁ ω ∪ A₂ ω) → g ω φ = ∫ z, wU z * φ z) →
      EqOn (fun z => wU z + u₀ z) (fun z => v ω ((c ω).1 z) - χ * (c ω).2.2 z)
        (stageComp (c ω) (A₁ ω) (A₂ ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω))) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundaryOnC (stageComp (c ω) (A₁ ω) (A₂ ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω))) (A₁ ω) (A₂ ω) u₀
        (fun z => v ω ((c ω).1 z) - χ * (c ω).2.2 z) w₁ w₂ χ (βu ω) (Su ω) := by
    filter_upwards [hpb, hcfg, hind₁, hind₂] with ω hp hc h1 h2 hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    exact (hp hωD).hasUnionWordBoundaryOnC (hc hωD) (h1 hωD w₁ hw₁ hr₁) (h2 hωD w₂ hw₂ hr₂)
  have hsurv := FinRel.ae_survivingWordBoundaryOn_unionC hh0 hA₁m hA₂m hd₁ hl₁ hl₂ hunb₁ hunb₂ hg hg₁ hg₂
    (fun ω => stageComp (c ω) (A₁ ω) (A₂ ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω))) u₀
    (fun ω z => v ω ((c ω).1 z) - χ * (c ω).2.2 z) χ βu Su hword
  exact Union.ae_eqOn_physicalMean_of_boundaryOn hh0 hu₀ hu₀b (measurable_union_hitting hA₁m hA₂m) hlU hg _ χ
    (Eventually.of_forall fun ω _ => stageComp_subset _ _ _ _) hsurv

/-- **SB2(2)'s union mean in K2's `hmean` form**: under the hypotheses of `ae_eqOn_unionMean_of_stagePullback` (with
`χ = χ(κ)`), for a family of conformal charts `crel ω` with continuous lifts whose inverse is the stage chart's inverse
after the retained inverse, `crel.2.1 = c.2.1 ∘ Ψi` on `ℍ`, and whose lift along it is the sum of the two lifts plus a
constant `ℓ₀`: almost surely on `D`, for every test `ψ` off the relative hull,
`chartTransport (crel ω) 1 a χ (g ω + u₀) ψ = ∫ couplingMean κ (Wr ω) (u ω) (G ω + a + χ ℓ₀) ψ`. -/
theorem ae_chartTransport_eq_couplingMean_of_stagePullback {κ : ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A₁ A₂ : Ω → Set ℂ} (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hd₁ : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hl₁ : IsLocalSet A₁ (WholeField.centredField h u₀) P) (hl₂ : IsLocalSet A₂ (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P)
    (hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z))
    (hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A₁ ω ∪ A₂ ω) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean A₂ (WholeField.centredField h u₀) P g₂)
    {c : Ω → Chart} {gb : Ω → ℂ → ℂ} {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ}
    {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ} {t u : Ω → ℝ} {lam : ℝ} {β₀ βE βu : Ω → ℝ → ℝ}
    {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ} {D : Set Ω}
    (hpb : ∀ᵐ ω ∂P, ω ∈ D → IsStagePullback (c ω) (gb ω) (A₁ ω) (A₂ ω) (A ω) (fwdHull (w ω) (t ω)))
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → Lm.IsRelConfigJKL (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω)
      (t ω) (u ω) (chiC κ) lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z)
        (fun z => G₀ ω (Ψ ω ((c ω).1 z)) - chiC κ * ((LΨ ω ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₁ ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ A₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) ((c ω).1 z)) -
        chiC κ * ((logDerivFwd (w ω) (t ω) ((c ω).1 z)).im + (c ω).2.2 z)) (H \ A₂ ω))
    {crel : Ω → Chart} (hcr : ∀ ω, (crel ω).IsConformal) (hcrℓ : ∀ ω, ContinuousOn (crel ω).2.2 (crel ω).dom)
    (hcrinv : ∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.1 y = (c ω).2.1 (Ψi ω y)) {ℓ₀ : ℝ}
    (hcrlift : ∀ᵐ ω ∂P, ω ∈ D → ∀ y ∈ H, (crel ω).2.2 ((crel ω).2.1 y) =
      (LΨ ω (Ψi ω y)).im + (c ω).2.2 ((crel ω).2.1 y) + ℓ₀) (a : ℝ) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ ψ : TestOn upperHalfPlaneOpens, Disjoint (tsupport ψ) (fwdHull (Wr ω) (u ω)) →
      Chart.chartTransport (hcr ω) 1 a (chiC κ) (g ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ y, couplingMean κ (Wr ω) (u ω) (fun z => G ω z + (a + chiC κ * ℓ₀)) y * ψ y := by
  have hmean := ae_eqOn_unionMean_of_stagePullback hh0 hu₀ hu₀b hA₁m hA₂m hd₁ hl₁ hl₂ hlU hunb₁ hunb₂ hg hg₁ hg₂
    hpb hcfg hind₁ hind₂
  filter_upwards [hmean, hpb, hcfg, hcrinv, hcrlift, hg.2.1] with ω hm hp hc hi hl hgω hωD ψ hψ
  obtain ⟨wU, hwU, hrepU⟩ := hgω
  have hEq := hm hωD wU hwU hrepU
  have hp' := hp hωD
  have hc' := hc hωD
  -- the inverse relative chart image of the complement of the relative hull lies in the physical component
  have hpt : ∀ y ∈ H \ fwdHull (Wr ω) (u ω), (crel ω).2.1 y ∈
      stageComp (c ω) (A₁ ω) (A₂ ω) (relComp (A ω) (Ψ ω) (Wr ω) (u ω)) ∧
        (c ω).1 ((crel ω).2.1 y) = Ψi ω y := by
    intro y hy
    rw [hi hωD y hy.1]
    have hwA := IsRelConfigJKL.inv_mem hc' hy.1
    have hwR : Ψi ω y ∈ relComp (A ω) (Ψ ω) (Wr ω) (u ω) :=
      ⟨hwA, by rw [IsRelConfigJKL.fwd_inv hc' hy.1]; exact hy⟩
    have hwK := IsRelConfigJKL.relComp_subset hc' hwR
    have hc1 : (c ω).1 ((c ω).2.1 (Ψi ω y)) = Ψi ω y := hp'.conf.2.2 _ hwA.1
    refine ⟨⟨⟨hp'.conf.2.1 hwA.1, ?_⟩, by rw [hc1]; exact hwR⟩, hc1⟩
    rintro (h1 | h2)
    · exact hwK.2 (Or.inl ((hp'.corr₁ _ hwA.1).1 h1))
    · exact hwK.2 (Or.inr ((hp'.corr₂ _ hwA.1).1 h2))
  have hsub : (crel ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ H \ (A₁ ω ∪ A₂ ω) := by
    rintro _ ⟨y, hy, rfl⟩
    exact stageComp_subset _ _ _ _ (hpt y hy).1
  have hOH : (crel ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ H := fun z hz => (hsub hz).1
  refine Union.chartTransport_eq_couplingMean_of_relComp (hcr ω) (hcrℓ ω)
    (LΨ := fun z => LΨ ω ((c ω).1 z) + ((c ω).2.2 z : ℂ) * Complex.I) (ℓ₀ := ℓ₀) (wU := wU) ?_ ?_ ?_
    (G := G ω) ?_ a hψ
  · intro y hy
    rw [hl hωD y hy.1, (hpt y hy).2]
    simp only [Complex.add_im, Complex.I_im, mul_one, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, add_zero]
  · exact ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU).add
      ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀).mono sdiff_subset)).mono hsub
  · exact Union.rep_add_smoothDist hOH (fun z hz => hwU z (hsub hz)) hu₀
      (fun φ hφ => hrepU φ (hφ.trans hsub))
  · intro y hy
    obtain ⟨hmem, hc1⟩ := hpt y hy
    have e := hEq hmem
    simp only at e
    rw [e, hc1, IsRelConfigJKL.cand hc', IsRelConfigJKL.fwd_inv hc' hy.1]
    simp only [Complex.add_im, Complex.I_im, mul_one, Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, add_zero]
    ring

end Mean

end InteractingSLE.Theorem14.SB.Ln
