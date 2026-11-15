import InteractingSLE.Spec.Coupling.Assembly11Tau
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# Theorem 1.1: from a family-sampled coupling to the frozen optional hull specification

Packet PROVE-T11-ASM (obligations 5–7 of `planning/handoffs/PROVE-T11-L312.md` §4; Astra §1). The frozen
`IsOptionalHullCoupling` has four conjuncts: the evolution, the measurability of the field, the GFF law of
`h − 𝔥₀`, and, for some measurability witness `hX` of the killed driving process and every stopping time `τ < ζ` of
the frozen driving filtration, locality of `K_τ` and the conditional law of `h` off `K_τ`.

* `isMeasurableKilledDriving_of_adaptedBefore`: the witness `hX`, from the adaptedness of the driving coordinates;
* `IsFamilySampled`: the output of the compactness step (Astra p. 6) on one probability space: the protected-kernel
  constraint `IsSampledAt` on a countable family of stops that exhausts avoidance;
* `condExp_clause_of_isFamilySampled`: the conditional-law conjunct, at every frozen stopping time
  (`condExp_cexp_eq_frozenRHS_of_family`);
* `isOptionalHullCoupling_of_isFamilySampled`: the frozen predicate, given locality at every frozen stopping time
  (a separate input: Astra (1.14) and Lemma 3.6 (i) ⇒ (iii); it is a hypothesis of this conditional helper only).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

universe u

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The killed driving process is measurable as soon as its coordinates are adapted before `ζ`. -/
theorem isMeasurableKilledDriving_of_adaptedBefore (hW : AdaptedBefore 𝓕 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ i, AdaptedBefore 𝓕 ζ (VR i)) :
    IsMeasurableKilledDriving W VL VR ζ := by
  intro r A hA
  have hk : Measurable fun ω => (Girsanov.killed ζ W r ω,
      fun i => Girsanov.killed ζ (VL i) r ω, fun i => Girsanov.killed ζ (VR i) r ω) :=
    ((Girsanov.measurable_killed hW r).mono (𝓕.le r) le_rfl).prodMk
      ((measurable_pi_iff.2 fun i => (Girsanov.measurable_killed (hVL i) r).mono (𝓕.le r) le_rfl).prodMk
        (measurable_pi_iff.2 fun i => (Girsanov.measurable_killed (hVR i) r).mono (𝓕.le r) le_rfl))
  have hlt : MeasurableSet {ω | (r : ℝ≥0∞) < ζ ω} := by
    have h1 := 𝓕.le r _ (hW r univ MeasurableSet.univ)
    simpa only [mem_univ, and_true] using h1
  have e : {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} =
      {ω | (r : ℝ≥0∞) < ζ ω} ∩ (fun ω => (Girsanov.killed ζ W r ω,
        fun i => Girsanov.killed ζ (VL i) r ω, fun i => Girsanov.killed ζ (VR i) r ω)) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa only [Girsanov.killed_of_lt h1] using h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simpa only [Girsanov.killed_of_lt h1] using h2
  rw [e]
  exact hlt.inter (hk hA)

theorem IsIntegratedSLEEvolution.isMeasurableKilledDriving
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsMeasurableKilledDriving W VL VR ζ :=
  isMeasurableKilledDriving_of_adaptedBefore hE.2.1 hE.2.2.1 hE.2.2.2.1

/-- **The output of the compactness step** (Astra p. 6, on one probability space): bounded harmonic extensions `u`
of the data at every time, and a countable family `(U i, s i)` of stopping times of the usual augmentation with
`s i < ζ` and `U i` unswallowed at `s i`, exhausting avoidance, at each member of which the field satisfies the
protected-kernel constraint `IsSampledAt` (Astra (1.10)). -/
def IsFamilySampled (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) :
    Prop :=
  ∃ u : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) ∧
    ∃ (ι : Type) (_ : Countable ι) (U : ι → Set ℂ) (s : ι → Ω → ℝ≥0)
      (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0)),
      (∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) ∧
      (∀ i, IsSampledAt κ W u P h (U i) (hs i)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω

/-- **The conditional-law conjunct of the frozen Theorem 1.1** for a family-sampled coupling. -/
theorem condExp_clause_of_isFamilySampled
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hfam : IsFamilySampled κ ρL ρR P 𝓕 W VL VR ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) (uτ : Ω → ℂ → ℝ)
    (huτ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (uτ ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (uτ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  obtain ⟨u, hu, ι, _, U, s, hs, hsafe, hsamp, hexh⟩ := hfam
  have hh' : ∀ ψ, Measurable fun ω => h ω ψ := fun ψ =>
    (LQGMetric.measurable_distOn_apply ψ).comp hh
  exact condExp_cexp_eq_frozenRHS_of_family hE hκ u hu h hh' U s hs hsafe hsamp hexh hX hτ hτζ uτ huτ φ

/-- **The frozen optional hull specification from a family-sampled coupling**, given locality of `K_τ` at every
frozen stopping time `τ < ζ` (conditional helper: the locality input is Astra (1.14) with Lemma 3.6). -/
theorem isOptionalHullCoupling_of_isFamilySampled
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
        (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P)
    (hfam : IsFamilySampled κ ρL ρR P 𝓕 W VL VR ζ h)
    (hloc : ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0),
      IsStoppingTime (drivingFiltration P hX) τ → (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
        IsLocalSet (fun ω => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0)) h P) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h :=
  ⟨hE, hh, hgff, IsIntegratedSLEEvolution.isMeasurableKilledDriving hE, fun τ hτ hτζ =>
    ⟨hloc _ τ hτ hτζ, fun uτ huτ φ =>
      condExp_clause_of_isFamilySampled hE hκ hh hfam _ τ hτ hτζ uτ huτ φ⟩⟩

end Coupling

end InteractingSLE
