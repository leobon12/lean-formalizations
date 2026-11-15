import InteractingSLE.Spec.Coupling.CompactCoupling
import InteractingSLE.Spec.Coupling.CompactTransfer
import LQGMetric.Field.StandardBorelRange

/-!
# The compactness step: from finite families to the whole countable family

Packet PROVE-T11-ASM (obligation 4 of `planning/handoffs/PROVE-T11-L312.md` §4; Astra §1 p. 6, "One compactness step,
with no Kolmogorov extension theorem"). Fix an integrated evolution on a standard Borel space `(Ω₀, P₀)` and a
countable family `(U i, s i)` of stops. A coupling `μ` of `P₀` with a field law `α` on `Ω₀ × 𝒟'(ℍ)` is *sampled at*
`(U, s)` (`IsSampledCoupling`) when, for every test function `ψ` supported in `U` and every event `A₀` of the stopped
σ-algebra at `s` on `Ω₀`,

  `∫_{A₀ × 𝒟'} exp(i x(ψ)) dμ = ∫_{A₀} exp(i (𝔥_s, ψ) − E_s(ψ)/2) dP₀`   (Astra (1.10), tested on `Ω₀`-events).

* `exists_isSampledCoupling_of_finite`: if every finite subfamily has a coupling of `P₀` and `α` sampled at all its
  members (the finite-family step, Astra pp. 5–6), then one coupling of `P₀` and `α` is sampled at every member
  (`exists_limit_coupling` along an exhausting sequence of finite subfamilies);
* `isFamilySampled_of_isSampledCoupling`: on `Ω₀ × 𝒟'(ℍ)` with the pulled-back evolution, the field `h(ω, x) = x`
  of such a coupling satisfies `IsFamilySampled` (the hypothesis of `isOptionalHullCoupling_of_isFamilySampled`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}

/-- A coupling `μ` of the driving law `P₀` with a field on `ℍ` is **sampled at** `(U, s)`: the protected-kernel
constraint (Astra (1.10)) tested against the events of the stopped σ-algebra at `s` on `Ω₀`. -/
def IsSampledCoupling (κ : ℝ) (W : ℝ≥0 → Ω₀ → ℝ) (u : Ω₀ → ℝ≥0 → ℂ → ℝ) (P₀ : Measure Ω₀)
    (U : Set ℂ) {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)) : Prop :=
  ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ A₀ : Set Ω₀,
    MeasurableSet[hs.measurableSpace] A₀ →
      ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
        ∫ ω in A₀, cfAt κ W u ψ 1 s ω ∂P₀

theorem integral_preimage_fst_eq (A₀ : Set Ω₀) (hA₀ : MeasurableSet A₀)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)) :
    ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
      ∫ p, A₀.indicator (fun _ => (1 : ℂ)) (id p.1) * Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ := by
  rw [← integral_indicator (measurable_fst hA₀)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : p.1 ∈ A₀
  · simp [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.fst ⁻¹' A₀ from hp)]
  · simp [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.fst ⁻¹' A₀ from hp)]

variable [StandardBorelSpace Ω₀]

/-- **The compactness step.** If every finite subfamily of the countable family `(U i, s i)` admits a coupling of
`P₀` and `α` sampled at all its members, then a single coupling of `P₀` and `α` is sampled at every member. -/
theorem exists_isSampledCoupling_of_finite [IsProbabilityMeasure P₀] (κ : ℝ) (W : ℝ≥0 → Ω₀ → ℝ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ) {ι : Type*} [Countable ι] (U : ι → Set ℂ) (s : ι → Ω₀ → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0))
    (α : Measure (LQGMetric.DistOn upperHalfPlaneOpens)) [IsProbabilityMeasure α]
    (hfin : ∀ F : Finset ι, ∃ μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i ∈ F, IsSampledCoupling κ W u P₀ (U i) (hs i) μ) :
    ∃ μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i, IsSampledCoupling κ W u P₀ (U i) (hs i) μ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨μ, h1, h2, h3, -⟩ := hfin ∅
    exact ⟨μ, h1, h2, h3, fun i => isEmptyElim i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set F : ℕ → Finset ι := fun n => (Finset.range n).image e with hF
  have hFmem : ∀ i, ∃ k, ∀ n, k < n → i ∈ F n := fun i => by
    obtain ⟨k, rfl⟩ := he i
    exact ⟨k, fun n hn => Finset.mem_image.2 ⟨k, Finset.mem_range.2 hn, rfl⟩⟩
  choose μ hμp hμ1 hμ2 hμs using fun n => hfin (F n)
  have : ∀ n, IsProbabilityMeasure (μ n) := hμp
  obtain ⟨μ', φ, hμ'p, hμ'1, hμ'2, hφ, hlim⟩ :=
    exists_limit_coupling (Y := Ω₀) measurable_id μ hμ1 hμ2
  refine ⟨μ', hμ'p, hμ'1, hμ'2, fun i ψ hψ A₀ hA₀ => ?_⟩
  have hA₀m : MeasurableSet A₀ := (hs i).measurableSpace_le _ hA₀
  obtain ⟨k, hk⟩ := hFmem i
  have hg : Measurable (A₀.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hA₀m
  have hf : Measurable fun x : LQGMetric.DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (x ψ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (LQGMetric.measurable_distOn_apply ψ)))
  have hL := hlim (A₀.indicator fun _ => (1 : ℂ)) (fun x => Complex.exp (Complex.I * (x ψ : ℂ)))
    hg hf ⟨1, fun y => by by_cases hy : y ∈ A₀ <;> simp [hy]⟩
    ⟨1, fun x => by rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le⟩
  simp only [← integral_preimage_fst_eq A₀ hA₀m ψ] at hL
  have hev : ∀ᶠ n in atTop, ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ (φ n) =
      ∫ ω in A₀, cfAt κ W u ψ 1 (s i) ω ∂P₀ := by
    filter_upwards [eventually_gt_atTop k] with n hn
    exact hμs (φ n) i (hk (φ n) (hn.trans_le (hφ.id_le n))) ψ hψ A₀ hA₀
  exact tendsto_nhds_unique hL (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- **The compactness step for arbitrary product-form constraints** (used for the sampling constraint above and, in
the same way, for the projection-independence constraints (1.10) needed for locality). For a countable family of
tests `t ∈ T i`, each given by a measurable event `A i t ⊆ Ω₀`, a bounded measurable `f i t` of the field and a value
`c i t`: if every finite subfamily admits a coupling of `P₀` and `α` with `∫_{A i t × 𝒟'} f i t = c i t`, then one
coupling does for all members. -/
theorem exists_coupling_of_finite_tests [IsProbabilityMeasure P₀] {ι : Type*} [Countable ι]
    {T : ι → Type*} (A : ∀ i, T i → Set Ω₀) (hA : ∀ i t, MeasurableSet (A i t))
    (f : ∀ i, T i → LQGMetric.DistOn upperHalfPlaneOpens → ℂ) (hf : ∀ i t, Measurable (f i t))
    (hfb : ∀ i t, ∃ C, ∀ x, ‖f i t x‖ ≤ C) (c : ∀ i, T i → ℂ)
    (α : Measure (LQGMetric.DistOn upperHalfPlaneOpens)) [IsProbabilityMeasure α]
    (hfin : ∀ F : Finset ι, ∃ μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i ∈ F, ∀ t, ∫ p in Prod.fst ⁻¹' A i t, f i t p.2 ∂μ = c i t) :
    ∃ μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
        ∀ i t, ∫ p in Prod.fst ⁻¹' A i t, f i t p.2 ∂μ = c i t := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain ⟨μ, h1, h2, h3, -⟩ := hfin ∅
    exact ⟨μ, h1, h2, h3, fun i => isEmptyElim i⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set F : ℕ → Finset ι := fun n => (Finset.range n).image e with hF
  have hFmem : ∀ i, ∃ k, ∀ n, k < n → i ∈ F n := fun i => by
    obtain ⟨k, rfl⟩ := he i
    exact ⟨k, fun n hn => Finset.mem_image.2 ⟨k, Finset.mem_range.2 hn, rfl⟩⟩
  choose μ hμp hμ1 hμ2 hμs using fun n => hfin (F n)
  have : ∀ n, IsProbabilityMeasure (μ n) := hμp
  obtain ⟨μ', φ, hμ'p, hμ'1, hμ'2, hφ, hlim⟩ :=
    exists_limit_coupling (Y := Ω₀) measurable_id μ hμ1 hμ2
  refine ⟨μ', hμ'p, hμ'1, hμ'2, fun i t => ?_⟩
  obtain ⟨k, hk⟩ := hFmem i
  have hg : Measurable ((A i t).indicator fun _ => (1 : ℂ)) := measurable_const.indicator (hA i t)
  have hconv : ∀ ν : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      ∫ p in Prod.fst ⁻¹' A i t, f i t p.2 ∂ν =
        ∫ p, (A i t).indicator (fun _ => (1 : ℂ)) (id p.1) * f i t p.2 ∂ν := fun ν => by
    rw [← integral_indicator (measurable_fst (hA i t))]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    by_cases hp : p.1 ∈ A i t
    · simp [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.fst ⁻¹' A i t from hp)]
    · simp [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.fst ⁻¹' A i t from hp)]
  have hL := hlim ((A i t).indicator fun _ => (1 : ℂ)) (f i t) hg (hf i t)
    ⟨1, fun y => by by_cases hy : y ∈ A i t <;> simp [hy]⟩ (hfb i t)
  simp only [← hconv] at hL
  have hev : ∀ᶠ n in atTop, ∫ p in Prod.fst ⁻¹' A i t, f i t p.2 ∂μ (φ n) = c i t := by
    filter_upwards [eventually_gt_atTop k] with n hn
    exact hμs (φ n) i (hk (φ n) (hn.trans_le (hφ.id_le n))) t
  exact tendsto_nhds_unique hL (tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm))

omit [StandardBorelSpace Ω₀] in
/-- **A coupling sampled at every member of an exhausting family is family-sampled** on `Ω₀ × 𝒟'(ℍ)`, with the
pulled-back evolution and the field `h(ω, x) = x`. -/
theorem isFamilySampled_of_isSampledCoupling
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) (hκ : 0 < κ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {ι : Type} [Countable ι] (U : ι → Set ℂ) (s : ι → Ω₀ → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0))
    (hsafe : ∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)))
    (hexh : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω)
    {μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)} (hμ : μ.map Prod.fst = P₀)
    (hsamp : ∀ i, IsSampledCoupling κ W u P₀ (U i) (hs i) μ) :
    IsFamilySampled κ ρL ρR μ (filtrationFst 𝓕₀ (LQGMetric.DistOn upperHalfPlaneOpens))
      (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun p => ζ p.1)
      (fun p => p.2) := by
  refine ⟨fun p => u p.1, fun p s => hu p.1 s, ι, inferInstance, U, fun i p => s i p.1,
    fun i => isStoppingTime_fst hμ (hs i), fun i => ?_, fun i => ?_, ?_⟩
  · have h := hsafe i
    rw [← hμ] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  · refine isSampledAt_fst hμ (hs i) fun ψ hψ A₀ hA₀ => ?_
    have hA₀m : MeasurableSet A₀ := (hs i).measurableSpace_le _ hA₀
    rw [hsamp i ψ hψ A₀ hA₀]
    have hτs : ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := by
      filter_upwards [hsafe i] with ω h using ⟨h.1, h.2.mono_left hψ⟩
    have hm := aestronglyMeasurable_cfAt_of_stoppingTime hE hκ u hu ψ (hs i) hτs 1
    rw [← hμ] at hm ⊢
    exact setIntegral_map hA₀m hm measurable_fst.aemeasurable
  · rw [← hμ] at hexh
    exact ae_of_ae_map measurable_fst.aemeasurable hexh

end Coupling

end InteractingSLE
