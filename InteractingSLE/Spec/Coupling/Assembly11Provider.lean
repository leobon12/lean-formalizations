import InteractingSLE.Spec.Coupling.CompactFamily
import InteractingSLE.Spec.Coupling.SafeFamily
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Theorem 1.1: the assembly of the coupling (conditional on the named inputs still open)

Packet PROVE-T11-ASM (obligations 4–7 of `planning/handoffs/PROVE-T11-L312.md` §4; Astra §1). The coupling of
Theorem 1.1 is built on `Ω₀ × 𝒟'(ℍ)`, `Ω₀` a standard Borel space carrying an integrated evolution:

1. the lifetime has an announcing sequence (PROVE-T11-ANN, `exists_isAnnouncingSeq`, imported) at an admissible seed,
   and the countable family of safe stops of rational-ball sets exhausts avoidance (`exists_safeFamily`);
2. finite subfamilies admit couplings sampled at their members (the named input `FiniteFamilyStatement`,
   Astra pp. 5–6; packet PROVE-T11-KER);
3. one compactness step gives a single coupling sampled at every member (`exists_isSampledCoupling_of_finite`),
   which is family-sampled on `Ω₀ × 𝒟'(ℍ)` (`isFamilySampled_of_isSampledCoupling`);
4. the frozen conditional-law clause at every frozen stopping time follows (`condExp_cexp_eq_frozenRHS_of_family`).

Main results:
* `exists_familySampledCoupling`: steps 1–3 from the named inputs `Thm22StdBorelStatement` (Theorem 2.2 on a
  standard Borel space) and `FiniteFamilyStatement`; at an inadmissible seed the family is empty (`ζ = 0` a.s.);
* `exists_isOptionalHullCoupling_of_inputs`: the frozen statement of Theorem 1.1 from these inputs and the locality
  input `LocalityStatement` (Astra (1.14) with Lemma 3.6, for the couplings of step 3).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

universe u

namespace InteractingSLE

namespace Coupling

open Ito

/-! ### The field law transfers to a coupling -/

theorem isZBGFFProcess_comp_snd {Ω₀ : Type*} [MeasurableSpace Ω₀]
    {α : Measure (LQGMetric.DistOn upperHalfPlaneOpens)}
    {μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)} (hμ : μ.map Prod.snd = α)
    {X : LQGMetric.TestOn upperHalfPlaneOpens → LQGMetric.DistOn upperHalfPlaneOpens → ℝ}
    (hX : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens X α) :
    LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ p => X φ p.2) μ := by
  obtain ⟨hm, hg, hc, hcov⟩ := hX
  have hsnd : AEMeasurable (Prod.snd : Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens → _) μ :=
    measurable_snd.aemeasurable
  refine ⟨fun φ => (hm φ).comp measurable_snd, ⟨fun I => ?_⟩, fun φ => ?_, fun φ ψ => ?_⟩
  · have h := hg.hasGaussianLaw I
    refine ⟨((hμ ▸ h.aemeasurable).comp_aemeasurable hsnd), ?_⟩
    have e := AEMeasurable.map_map_of_aemeasurable (hμ ▸ h.aemeasurable) hsnd
    rw [show (fun p : Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens => I.restrict fun t => X t p.2) =
      (fun x => I.restrict fun t => X t x) ∘ Prod.snd from rfl, ← e, hμ]
    exact h.isGaussian_map
  · rw [← hc φ, ← hμ, integral_map hsnd ((hm φ).aestronglyMeasurable)]
  · rw [← hcov φ ψ, ← hμ, covariance_map ((hm φ).aestronglyMeasurable) ((hm ψ).aestronglyMeasurable)
      hsnd]
    rfl

/-! ### The lifetime at an inadmissible seed -/

theorem ae_zeta_eq_zero_of_threshold {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ∀ᵐ ω ∂P, ζ ω = 0 := by
  filter_upwards [hE.2.2.2.2] with ω hP
  by_contra hne
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -, -⟩ := hP
  apply hnt 0 h0
  have e1 : (fun i => VL i 0 ω) = xL := funext hvL0
  have e2 : (fun i => VR i 0 ω) = xR := funext hvR0
  simp only at hw0 ⊢
  rw [hw0, e1, e2]
  exact hseed

/-! ### The named inputs still open -/

/-- **Named input: Theorem 2.2 (existence) on a standard Borel space.** The frozen
`exists_isIntegratedSLEEvolution` (still `DRAFT_SORRY`, PROVE-SEC2-PATCH2) with the probability space standard Borel
(any evolution is pushed to one on countably many canonical coordinates). -/
def Thm22StdBorelStatement (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∃ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (P₀ : Measure Ω₀)
    (_ : IsProbabilityMeasure P₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W : ℝ≥0 → Ω₀ → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ

/-- **Named input: the finite-family step** (Astra pp. 5–6, Gaussian resampling; packet PROVE-T11-KER). For an
integrated evolution on a standard Borel space, bounded harmonic extensions `u`, and a countable family of stops
`s i < ζ` protecting compact sets `K i ⊇ U i`, there is a field law `α` (a zero-boundary GFF plus the time-zero
harmonic mean) such that every finite subfamily admits a coupling of the driving law and `α` sampled at all its
members. -/
def FiniteFamilyStatement (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∀ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (P₀ : Measure Ω₀)
    (_ : IsProbabilityMeasure P₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W : ℝ≥0 → Ω₀ → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ →
    ∀ (u : Ω₀ → ℝ≥0 → ℂ → ℝ), (∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) →
    ∀ (ι : Type) (_ : Countable ι) (U K : ι → Set ℂ) (s : ι → Ω₀ → ℝ≥0)
      (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s i ω : WithTop ℝ≥0)),
    (∀ i, IsCompact (K i) ∧ K i ⊆ H ∧ U i ⊆ K i) →
    (∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (K i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) →
    ∃ α : Measure (LQGMetric.DistOn upperHalfPlaneOpens), IsProbabilityMeasure α ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z) α) ∧
      ∀ F : Finset ι, ∃ μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
        IsProbabilityMeasure μ ∧ μ.map Prod.fst = P₀ ∧ μ.map Prod.snd = α ∧
          ∀ i ∈ F, IsSampledCoupling κ W u P₀ (U i) (hs i) μ

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **The coupling of Theorem 1.1, all conjuncts but locality.** From Theorem 2.2 on a standard Borel space and the
finite-family step: a probability space `Ω₀ × 𝒟'(ℍ)` in universe `u` carrying an integrated evolution and a field
`h(ω, x) = x` with `h − 𝔥₀` a zero-boundary GFF, which is family-sampled (hence satisfies the frozen conditional-law
clause at every frozen stopping time, `condExp_clause_of_isFamilySampled`). -/
theorem exists_familySampledCoupling (hκ : 0 < κ) (hI1 : Thm22StdBorelStatement.{u} κ xL xR ρL ρR)
    (hI2 : FiniteFamilyStatement.{u} κ xL xR ρL ρR) :
    ∃ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀) (W : ℝ≥0 → Ω₀ → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ) (B : ℝ≥0 → Ω₀ → ℝ)
      (ζ : Ω₀ → ℝ≥0∞) (μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)),
      IsProbabilityMeasure μ ∧
      IsIntegratedSLEEvolution κ xL xR ρL ρR μ (filtrationFst 𝓕₀ (LQGMetric.DistOn upperHalfPlaneOpens))
        (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun t p => B t p.1)
        (fun p => ζ p.1) ∧
      (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
          (forceJumpSet xL xR) u₀ →
        LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ p => p.2 φ - ∫ z, u₀ z * φ z) μ) ∧
      IsFamilySampled κ ρL ρR μ (filtrationFst 𝓕₀ (LQGMetric.DistOn upperHalfPlaneOpens))
        (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun p => ζ p.1)
        (fun p => p.2) := by
  obtain ⟨Ω₀, mΩ₀, hSB, P₀, hP₀, 𝓕₀, W, VL, VR, B, ζ, hE⟩ := hI1
  set u : Ω₀ → ℝ≥0 → ℂ → ℝ := fun ω s => Impl.forceExt κ (weightWord ρL ρR)
    (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω) with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    Impl.isBoundedHarmonicExtension_forceExt κ (weightWord ρL ρR) _ _
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: `ζ = 0` almost surely and the family is empty
    have hζ0 := ae_zeta_eq_zero_of_threshold hE hseed
    set U0 : Empty → Set ℂ := fun i => i.elim
    set s0 : Empty → Ω₀ → ℝ≥0 := fun i => i.elim
    have hs0 : ∀ i, IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s0 i ω : WithTop ℝ≥0) :=
      fun i => i.elim
    obtain ⟨α, hαp, hαG, hfin⟩ := hI2 Ω₀ mΩ₀ hSB P₀ hP₀ 𝓕₀ W VL VR B ζ hE u hu Empty inferInstance
      U0 U0 s0 hs0 (fun i => i.elim) (fun i => i.elim)
    obtain ⟨μ, hμp, hμ1, hμ2, -⟩ := hfin ∅
    have hexh : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ U0 i ∧ t ≤ s0 i ω := by
      filter_upwards [hζ0] with ω h t ht
      rw [h] at ht
      exact absurd ht not_lt_zero
    exact ⟨Ω₀, mΩ₀, 𝓕₀, W, VL, VR, B, ζ, μ, hμp, IsIntegratedSLEEvolution.fst hμ1 hE,
      fun u₀ hu₀ => isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀),
      isFamilySampled_of_isSampledCoupling hE hκ u hu U0 s0 hs0 (fun i => i.elim) hexh hμ1
        (fun i => i.elim)⟩
  · -- an admissible seed: the announcing sequence and the safe family of rational-ball sets
    obtain ⟨T, hT⟩ := exists_isAnnouncingSeq hE hκ hseed
    obtain ⟨s, hs, -, hsafe, hexh⟩ := exists_safeFamily hE hT
    set U : RatBallSet × ℕ → Set ℂ := fun i => ballsU i.1.1 with hU
    set K : RatBallSet × ℕ → Set ℂ := fun i => ballsK i.1.1 with hK
    have hKc : ∀ i, IsCompact (K i) ∧ K i ⊆ H ∧ U i ⊆ K i := fun i =>
      ⟨isCompact_ballsK _, i.1.2, ballsU_subset_ballsK _⟩
    have hsafeK : ∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (K i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := hsafe
    have hsafeU : ∀ i, ∀ᵐ ω ∂P₀, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (U i) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω)) := fun i =>
      (hsafeK i).mono fun ω h => ⟨h.1, h.2.mono_left (hKc i).2.2⟩
    have hexhU : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K' : Set ℂ, IsCompact K' → K' ⊆ H →
        Disjoint K' (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K' ⊆ U i ∧ t ≤ s i ω := hexh
    obtain ⟨α, hαp, hαG, hfin⟩ := hI2 Ω₀ mΩ₀ hSB P₀ hP₀ 𝓕₀ W VL VR B ζ hE u hu (RatBallSet × ℕ)
      inferInstance U K s hs hKc hsafeK
    obtain ⟨μ, hμp, hμ1, hμ2, hμs⟩ := exists_isSampledCoupling_of_finite κ W u U s hs α hfin
    exact ⟨Ω₀, mΩ₀, 𝓕₀, W, VL, VR, B, ζ, μ, hμp, IsIntegratedSLEEvolution.fst hμ1 hE,
      fun u₀ hu₀ => isZBGFFProcess_comp_snd hμ2 (hαG u₀ hu₀),
      isFamilySampled_of_isSampledCoupling hE hκ u hu U s hs hsafeU hexhU hμ1 hμs⟩

/-- **Theorem 1.1, conditional provider form** (frozen arguments all implicit, every universe; PROVE-COMMON provider
convention). From Theorem 2.2 on a standard Borel space and the finite-family step, the coupling of
`exists_familySampledCoupling` satisfies every conjunct of the frozen `IsOptionalHullCoupling` except locality; given
locality of `K_τ` for that coupling at every frozen stopping time (`hloc`, the input still open: Astra (1.14) with
Lemma 3.6), it satisfies the frozen statement. -/
theorem exists_isOptionalHullCoupling_of_inputs {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (_hF : IsOrderedForceWord xL xR := by assumption)
    (hI1 : Thm22StdBorelStatement.{u} κ xL xR ρL ρR) (hI2 : FiniteFamilyStatement.{u} κ xL xR ρL ρR)
    (hloc : ∀ (Ω₀ : Type u) (mΩ₀ : MeasurableSpace Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
      (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ)
      (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)),
      IsProbabilityMeasure μ →
      IsIntegratedSLEEvolution κ xL xR ρL ρR μ
        (filtrationFst 𝓕₀ (LQGMetric.DistOn upperHalfPlaneOpens)) (fun t p => W t p.1)
        (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun t p => B t p.1) (fun p => ζ p.1) →
      IsFamilySampled κ ρL ρR μ (filtrationFst 𝓕₀ (LQGMetric.DistOn upperHalfPlaneOpens))
        (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun p => ζ p.1)
        (fun p => p.2) →
      ∀ (hX : IsMeasurableKilledDriving (fun t (p : Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens) => W t p.1)
          (fun i t p => VL i t p.1) (fun i t p => VR i t p.1) (fun p => ζ p.1))
        (τ : Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens → WithTop ℝ≥0),
        IsStoppingTime (drivingFiltration μ hX) τ → (∀ᵐ p ∂μ, (τ p : ℝ≥0∞) < ζ p.1) →
          IsLocalSet (fun p => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal p.1)
            ((τ p).untopD 0 : ℝ≥0)) (fun p => p.2) μ) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by
  obtain ⟨Ω₀, mΩ₀, 𝓕₀, W, VL, VR, B, ζ, μ, hμp, hE, hgff, hfam⟩ :=
    exists_familySampledCoupling hκ hI1 hI2
  exact ⟨Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens, inferInstance, μ, hμp, _, _, _, _, _, _,
    fun p => p.2, isOptionalHullCoupling_of_isFamilySampled hE hκ measurable_snd hgff hfam
      (hloc Ω₀ mΩ₀ 𝓕₀ W VL VR B ζ μ hμp hE hfam)⟩

end Coupling

end InteractingSLE
