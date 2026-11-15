/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UnionMean
import InteractingSLE.Spec.Sec5.Aux61SlitVChart

/-!
# Lemma SB2 at a junction: the union mean read in the retained chart is the relative coupling mean

Packet PROVE-T14-SB2UNION. K2's mean input (`hmean` of `SB.Cond.isCondFlowLineDriverOn_of_markedKernel`) asks for the
union mean read in the retained chart `c` with the flow rule:
`chartTransport c 1 a χ (M) ψ = ∫ couplingMean κ Wr u G' ψ` for tests `ψ` off the relative hull. This file turns the union mean identity of `SB2UnionMean` (on the relative
component) into that form, for any conformal chart `c` whose forward map is the retained chart `Ψ = c.1` and whose lift
along the inverse is `Im LΨ` up to a constant `ℓ₀` (`chartTransport_eq_couplingMean_of_relComp`, generic; the landed
GB6 version `Supp8.GB6LMean.chartTransport_eq_couplingMean` is the special case of the GB6 record chart):

* the transport is `∫ (m ∘ c⁻¹ + a + χ · lift ∘ c⁻¹) ψ` for the represented mean `m = wU + u₀`
  (`Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset`);
* on the relative component the candidate is `G ∘ f̃_u ∘ Ψ − χ (Im log f̃_u′ ∘ Ψ + Im LΨ)` and `Ψ ∘ c⁻¹ = id`;
* so the integrand is `G (f̃_u y) − χ Im log f̃_u′(y) + a + χ ℓ₀ = couplingMean κ Wr u (G + a + χ ℓ₀) y`.

`ae_chartTransport_eq_couplingMean_of_relConfigJ` combines it with `ae_eqOn_unionMean_of_relConfigJ`.

Deterministic except the last item. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.SB.Union

/-- **The transport of a represented union mean through the retained chart is the relative coupling mean.** Let `c` be
a conformal chart with continuous lift, whose inverse lands in `ℍ ∖ A`, whose lift along the inverse is `Im LΨ + ℓ₀`,
and `g'` a distribution represented by `wU` on `c⁻¹(ℍ ∖ K̃_u)`, with `wU + u₀` the relative candidate there. Then for
every test `ψ` off `K̃_u`, `chartTransport c 1 a χ (g' + u₀) ψ = ∫ couplingMean κ Wr u (G + a + χ ℓ₀) ψ`. -/
theorem chartTransport_eq_couplingMean_of_relComp {c : Chart} (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom)
    {Wr : ℝ → ℝ} {u : ℝ} {LΨ : ℂ → ℂ} {ℓ₀ : ℝ}
    (hlift : ∀ y ∈ H \ fwdHull Wr u, c.2.2 (c.2.1 y) = (LΨ (c.2.1 y)).im + ℓ₀)
    {g' : DistOn upperHalfPlaneOpens} {wU u₀ : ℂ → ℝ}
    (hwc : ContinuousOn (fun z => wU z + u₀ z) (c.2.1 '' (H \ fwdHull Wr u)))
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.2.1 '' (H \ fwdHull Wr u) →
      (g' + smoothDist upperHalfPlaneOpens u₀) φ = ∫ z, (wU z + u₀ z) * φ z)
    {κ : ℝ} {G : ℂ → ℝ}
    (hv : ∀ y ∈ H \ fwdHull Wr u, wU (c.2.1 y) + u₀ (c.2.1 y) =
      G (fwdMap Wr u y) - chiC κ * ((logDerivFwd Wr u y).im + (LΨ (c.2.1 y)).im))
    (a : ℝ) {ψ : TestOn upperHalfPlaneOpens} (hψ : Disjoint (tsupport ψ) (fwdHull Wr u)) :
    Chart.chartTransport hc 1 a (chiC κ) (g' + smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ y, couplingMean κ Wr u (fun z => G z + (a + chiC κ * ℓ₀)) y * ψ y := by
  have hψO : tsupport ψ ⊆ H \ fwdHull Wr u := fun y hy =>
    ⟨Coupling.tsupport_subset_H ψ hy, Set.disjoint_left.1 hψ hy⟩
  rw [Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hc hℓ sdiff_subset hwc hrep a (chiC κ) hψO]
  refine congrArg _ (funext fun y => ?_)
  by_cases hy : y ∈ tsupport ψ
  · have hyO := hψO hy
    rw [hv y hyO, hlift y hyO]
    simp only [couplingMean]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hy]
    ring

/-- The representation of the shifted mean on a subset of the union's complement (the `hrep` of
`chartTransport_eq_couplingMean_of_relComp`), from a harmonic representative of the centred union mean. -/
theorem rep_add_smoothDist {O : Set ℂ} (hOH : O ⊆ H) {g' : DistOn upperHalfPlaneOpens} {wU u₀ : ℂ → ℝ}
    (hwU : InnerProductSpace.HarmonicOnNhd wU O) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O → g' φ = ∫ z, wU z * φ z) :
    ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      (g' + smoothDist upperHalfPlaneOpens u₀) φ = ∫ z, (wU z + u₀ z) * φ z := by
  intro φ hφ
  have hu₀c : ContinuousOn u₀ H := Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀
  have hi₁ : Integrable fun z => wU z * φ z :=
    WholeField.integrable_mul_testOn (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU) φ hφ
  have hi₂ : Integrable fun z => u₀ z * φ z := WholeField.integrable_mul_testOn hu₀c φ (hφ.trans hOH)
  rw [add_apply, hrep φ hφ, Coupling.smoothDist_apply_eq hu₀c φ, ← integral_add hi₁ hi₂]
  simp only [add_mul]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}

open LocalSets

/-- **The union mean of the junction configuration, read in the retained chart, is the relative coupling mean** (K2's
`hmean` form; SB2, p. 632). Under the hypotheses of `ae_eqOn_unionMean_of_relConfigJ`, for a family of conformal
charts `c ω` with continuous lifts whose inverse is the retained inverse `Ψi ω` on `ℍ` and whose lift along it is
`Im LΨ + ℓ₀`: almost surely on `D`, for every test `ψ` off the relative hull,
`chartTransport (c ω) 1 a χ (g ω + u₀) ψ = ∫ couplingMean κ (Wr ω) (u ω) (G ω + a + χ ℓ₀) ψ`. -/
theorem ae_chartTransport_eq_couplingMean_of_relConfigJ {κ : ℝ}
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
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigJ (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
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
  have hmean := ae_eqOn_unionMean_of_relConfigJ hh0 hu₀ hu₀b hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁ hg₂ hcfg
    hind₁ hind₂
  filter_upwards [hmean, hcfg, hg.2.1] with ω hmω hcω hgω hωD ψ hψ
  obtain ⟨wU, hwU, hrepU⟩ := hgω
  have hcfgω := hcω hωD
  have hEq := hmω hωD wU hwU hrepU
  have hΨ := hcfgω.chart
  -- the inverse chart image of the complement of the relative hull lies in the relative component
  have hsub : (c ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ relComp (A ω) (Ψ ω) (Wr ω) (u ω) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hcinv ω y hy.1]
    exact ⟨hΨ.inv_mem y hy.1, by rw [hΨ.fwd_inv y hy.1]; exact hy⟩
  have hsubU : relComp (A ω) (Ψ ω) (Wr ω) (u ω) ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) :=
    relComp_subset hcfgω.hullIn
  have hOH : (c ω).2.1 '' (H \ fwdHull (Wr ω) (u ω)) ⊆ H := fun z hz => (hsubU (hsub hz)).1
  refine chartTransport_eq_couplingMean_of_relComp (hc ω) (hℓ ω) (LΨ := LΨ ω) (ℓ₀ := ℓ₀) (wU := wU)
    (fun y hy => hlift ω y hy.1) ?_ ?_ (fun y hy => ?_) a hψ
  · exact ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU).add
      ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀).mono sdiff_subset)).mono
      (hsub.trans hsubU)
  · exact rep_add_smoothDist hOH (fun z hz => hwU z (hsubU (hsub hz))) hu₀
      (fun φ hφ => hrepU φ (hφ.trans (hsub.trans hsubU)))
  · have hz : (c ω).2.1 y ∈ relComp (A ω) (Ψ ω) (Wr ω) (u ω) := hsub ⟨y, hy, rfl⟩
    have hΨy : Ψ ω ((c ω).2.1 y) = y := by rw [hcinv ω y hy.1]; exact hΨ.fwd_inv y hy.1
    have e := hEq hz
    simp only at e
    rw [e, hcfgω.cand, hΨy]

end InteractingSLE.Theorem14.SB.Union
