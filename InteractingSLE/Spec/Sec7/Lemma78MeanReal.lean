/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.GFF.LocalSets.GermMedian
import InteractingSLE.WangWu.Adapted
import InteractingSLE.Spec.Sec6.CondMeanStop

/-!
# Real-boundary decay of a local-set mean

Packet PROVE-PRIMEEND2, item (c) of `planning/handoffs/PROVE-PRIMEEND.md` ("the real-boundary decay of the union
mean"). Lemma 7.8's proof (p. 293): "On a trace-free original boundary interval, ordinary local-set boundary decay
gives the original datum." In the centred picture: the local-set mean `𝒞_A` of a zero-boundary GFF tends to `0` at
every real point away from `A`.

The comparison set is `∅`, through Proposition 3.8 (`IsLocalSetMean.ae_tendsto_sub_of_union`, landed). The germ
σ-algebra of `∅` is not trivial (its germ neighbourhoods contain a thickening of `ℝ` and of `∞`), but its mean is
still `0`: given the germs of `∅`, the field is (mean) + (a zero-boundary GFF on all of `ℍ`), whose conditional
variance is the full variance; comparing with the unconditional law (`𝒢 = ⊥`, mean `0`) by
`LocalSets.ae_apply_eq_of_isCondZeroBoundaryGFF` gives mean `0`.

## Main results

* `IsLocalSet.congr_ae`: local sets are a property of the law of `(A, h)` and the almost sure geometry, so they
  transfer along almost sure equality of the random sets;
* `isCondZeroBoundaryGFF_bot`: unconditionally, a zero-boundary GFF is `0 + GFF_ℍ`;
* `IsLocalSetMean.ae_apply_eq_zero_of_empty`: the local-set mean of `∅` is `0`;
* **`IsLocalSetMean.ae_tendsto_zero_of_real`**: almost surely, every harmonic representative of a local-set mean
  `𝒞_A` tends to `0` at every real point having a neighbourhood that misses `A`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal

namespace InteractingSLE.Sec7

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv IsZeroBoundaryGFF)
open LocalSets

section Transfer

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Local sets transfer along almost sure equality of the random set.** -/
theorem IsLocalSet.congr_ae {A A' : Ω → Set ℂ} (hA : IsLocalSet A h P) (he : ∀ᵐ ω ∂P, A' ω = A ω) :
    IsLocalSet A' h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hgeom, Ω', mΩ', P', hP', A'', h₁, h₂, hA'', hh₁, hh₂, hgeom', hharm, hcond, hlaw⟩ := hA
  have hpair : (fun ω => (A' ω, h ω)) =ᵐ[P] fun ω => (A ω, h ω) := by
    filter_upwards [he] with ω hω
    rw [hω]
  refine ⟨hm.congr hpair.symm, ?_, Ω', mΩ', P', hP', A'', h₁, h₂, hA'', hh₁, hh₂, hgeom', hharm, hcond, ?_⟩
  · filter_upwards [hgeom, he] with ω hω hω'
    rw [hω']
    exact hω
  · rw [hlaw]
    exact Measure.map_congr hpair.symm

end Transfer

section Empty

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Unconditionally, a zero-boundary GFF is `0 + GFF_ℍ`.** -/
theorem isCondZeroBoundaryGFF_bot (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) :
    IsCondZeroBoundaryGFF P ⊥ (fun _ => H) (fun ω => h ω - (0 : DistOn upperHalfPlaneOpens)) := by
  intro φ
  refine Eventually.of_forall fun ω => ?_
  rw [condExp_bot]
  simp only [sub_zero]
  exact integral_exp_field hh φ

/-- **The local-set mean of the empty set is zero**: given the germs of `∅` (near `ℝ` and `∞`), the field is its
mean plus a zero-boundary GFF on all of `ℍ`; comparing variances with the unconditional law gives mean `0`. -/
theorem IsLocalSetMean.ae_apply_eq_zero_of_empty (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun _ => (∅ : Set ℂ)) h P g)
    (φ : TestOn upperHalfPlaneOpens) : ∀ᵐ ω ∂P, g ω φ = 0 := by
  have hle : germSigma (fun _ : Ω => (∅ : Set ℂ)) h ≤ mΩ := germSigma_le measurable_const hh.measurable
  have h0 : Measurable[⊥] fun _ : Ω => (0 : DistOn upperHalfPlaneOpens) := measurable_const
  have := ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) (𝒢 := ⊥) bot_le hle hh.measurable h0 hg.1
    (isCondZeroBoundaryGFF_bot hh) hg.2.2 φ MeasurableSet.univ
    (fun c => Eventually.of_forall fun ω _ => by simp only [sdiff_empty])
  filter_upwards [this] with ω hω
  exact (hω (mem_univ ω)).symm

/-- `∅` and a hitting-measurable random set are conditionally independent given the field. -/
theorem condIndepEv_empty {A : Ω → Set ℂ} (hhm : Measurable h) (hA : Measurable[mΩ, hittingSigma] A) :
    CondIndepEv (MeasurableSpace.comap h inferInstance) (MeasurableSpace.comap A hittingSigma)
      (MeasurableSpace.comap (fun _ : Ω => (∅ : Set ℂ)) hittingSigma) P := by
  refine (Sec6.condIndepEv_of_le_aeSigma hhm.comap_le hA.comap_le ?_).symm
  rw [MeasurableSpace.comap_const]
  exact bot_le

/-- **Real-boundary decay of a local-set mean** (Lemma 7.8, p. 293: "On a trace-free original boundary interval,
ordinary local-set boundary decay gives the original datum", in centred form). Let `A` be a local set of the
zero-boundary GFF `h` on `ℍ` and `g` a version of `𝒞_A`. Almost surely, every harmonic representative `v` of `g` on
`ℍ \ A` tends to `0` at every real point `x` having a neighbourhood that misses `A`. -/
theorem IsLocalSetMean.ae_tendsto_zero_of_real (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, v z * φ z) →
      ∀ x : ℝ, (∃ r > 0, Disjoint (ball (x : ℂ) r) (A ω)) → Tendsto v (𝓝[H \ A ω] (x : ℂ)) (𝓝 0) := by
  have hloc₀ := WangWu.isLocalSet_empty hh (P := P)
  obtain ⟨g₀, hg₀⟩ := IsLocalSet.exists_isLocalSetMean hh measurable_const hloc₀
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion ((fun _ : Ω => (∅ : Set ℂ)) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion ((fun _ : Ω => (∅ : Set ℂ)) ω)) z) := by
    refine Eventually.of_forall fun ω => not_isBounded_of_isPreconnected_union_real ?_
    rw [empty_union]
    have e : {w : ℂ | w.im = 0} = range ((↑) : ℝ → ℂ) := by
      ext w
      simp only [mem_ofPred_eq, mem_range]
      exact ⟨fun hw => ⟨w.re, Complex.ext (by simp) (by simp [hw])⟩, fun ⟨t, ht⟩ => by rw [← ht]; simp⟩
    rw [e]
    exact isPreconnected_range Complex.continuous_ofReal
  have hgU : IsLocalSetMean (fun ω => A ω ∪ (fun _ : Ω => (∅ : Set ℂ)) ω) h P g := by
    simpa only [union_empty] using hg
  have h38 := IsLocalSetMean.ae_tendsto_sub_of_union hh hA measurable_const (condIndepEv_empty hh.measurable hA)
    hloc hloc₀ hunb hgU hg₀
  have hzero : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, g₀ ω φ = 0 := by
    have hall := ae_forall_apply_eq_of_bump (T₁ := g₀) (T₂ := fun _ => 0) (O := fun _ => H)
      (Eventually.of_forall fun _ => ⟨QuantumZipper.isOpen_H, subset_rfl⟩)
      (hg₀.2.1.mono fun ω hω => by simpa only [sdiff_empty] using hω)
      (Eventually.of_forall fun _ => ?_)
      (fun x δ hδ hB => (IsLocalSetMean.ae_apply_eq_zero_of_empty hh hg₀ _).mono fun ω hω _ => by
        rw [hω, zero_apply])
    · filter_upwards [hall] with ω hω φ
      exact hω φ (φ.tsupport_subset)
    · exact ⟨fun _ => 0, fun z _ => InnerProductSpace.harmonicAt_const 0, fun φ _ => by simp⟩
  filter_upwards [h38, hzero, hloc.2.1] with ω ⟨u, hu, hrep, hlim⟩ hz ⟨_, hAo⟩ v hv hvrep x ⟨r, hr, hdis⟩
  have hlimx : Tendsto u (𝓝[H \ (A ω ∪ ∅)] (x : ℂ)) (𝓝 0) :=
    hlim (x : ℂ) (Or.inr (by simp)) ⟨r, hr, fun z hz => (Set.disjoint_left.1 hdis hz.2 hz.1).elim⟩
  simp only [union_empty] at hu hrep hlimx
  -- `u = v` on `ℍ \ A`
  have huv : EqOn u v (H \ A ω) := by
    refine Sec6.eqOn_of_integral_mul_eq hAo sdiff_subset hu hv fun φ hφ => ?_
    rw [← hrep φ hφ, hz φ, sub_zero, hvrep φ hφ]
  refine hlimx.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact huv hz

end Empty

end InteractingSLE.Sec7
