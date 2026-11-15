/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLimPhase
import InteractingSLE.Spec.Sec7.PocketStopSideFinalComparison
import InteractingSLE.Spec.Sec7.Aux119Heights

/-!
# Reference-germ comparison with an unselected exposed phase

PROVE-STRIPSYS38. The marked-union comparison is independent of the numerical
boundary word. Here its target is Aux. 122's phase word, with one scalar shared
by every exposed face. Geometry, reference heights and inherited lift data remain
explicit in the cover; phase zero is not assumed in its last identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop Aux119Heights PhaseSel

section Cover

variable {Ω ι : Type*}

/-- The same physical reference witnesses as the canonical cover, with the
height identity allowed one common lattice phase on the exposed interval. -/
def PocketStopPhaseBoundaryCover (κ : ℝ) {nL nR : ℕ}
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart)
    (a : ℝ) (u : ℂ → ℝ) (K : Ω → Set ℂ) (δ : Ω → ℝ) (q : ℝ≥0)
    (B : ι → Ω → Set ℂ) (gB : ι → Ω → DistOn upperHalfPlaneOpens)
    (liftB : ι → Ω → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
    ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
      ∃ (i : ι) (p : ℂ) (b d : ℝ),
        p ∈ K ω ∪ {z : ℂ | z.im = 0} ∧ p ∈ B i ω ∪ {z : ℂ | z.im = 0} ∧
        (∃ r > 0, B i ω ∩ ball p r ⊆ K ω) ∧
        (∃ r > 0, K ω ∩ ball p r ⊆ B i ω) ∧
        Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))
          (𝓝[H \ (K ω ∪ B i ω)] p) ∧
        Tendsto (fun z => harmRep (gB i ω) (H \ B i ω) z + u z + chiC κ * liftB i ω z)
          (map (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))) (𝓝 b) ∧
        Tendsto (fun z => (relChart c γ q ω).2.2 z - liftB i ω z)
          (map (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ))) (𝓝 d) ∧
        b + chiC κ * d = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) ξ - a


end Cover

section Comparison

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The history-marked comparison transfers reference limits before phase
selection. No determination or conditional independence is needed. -/
theorem pocketStopPhaseSideLimit_of_marked_referenceCover
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart}
    {a : ℝ} {u : ℂ → ℝ} {K : Ω → Set ℂ} {q : ℝ≥0}
    (hKm : Measurable[mΩ, hittingSigma] K) (hKloc : IsLocalSet K h₀ P)
    (hKunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    {B : ι → Ω → Set ℂ} (hBm : ∀ i, Measurable[mΩ, hittingSigma] (B i))
    (hBloc : ∀ i, IsLocalSet (B i) h₀ P)
    (hPairLocal : ∀ i, WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap K hittingSigma ⊔ MeasurableSpace.comap (B i) hittingSigma)
      (fun ω => K ω ∪ B i ω) h₀ P)
    (hBunb : ∀ i, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (B i ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (B i ω)) z))
    {gB : ι → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (B i) h₀ P (gB i))
    {liftB : ι → Ω → ℂ → ℝ}
    {δ : Ω → ℝ}
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hcover : PocketStopPhaseBoundaryCover κ ρL ρR P A γ xL xR c a u K δ q B gB liftB) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u K δ q := by
  refine ⟨hLattice, ?_⟩
  intro g hg
  have hcmp := fun i => ae_tendsto_sub_of_marked_union hh₀ hKm (hBm i)
    hKloc (hBloc i) (hPairLocal i) hKunb (hBunb i) hg (hgB i)
  have hcmpAll := ae_all_iff.2 hcmp
  have hrep : ∀ᵐ ω ∂P, ∀ i, IsHarmonicDistOn (gB i ω) (H \ B i ω) :=
    ae_all_iff.2 fun i => (hgB i).2.1
  unfold PocketStopPhaseBoundaryCover at hcover
  filter_upwards [hcmpAll, hrep, hcover] with ω hωcmp hωrep hωcover
    hωA hq v hv hvr ξ hξ
  obtain ⟨i, p, b, d, hpK, hpB, hBK, hKB, hinv, hheight, hlift, hword⟩ :=
    hωcover hωA hq ξ hξ
  obtain ⟨hvB, hvBr⟩ := harmRep_spec (hωrep i)
  have hzero := hωcmp i v (harmRep (gB i ω) (H \ B i ω)) hv hvr hvB hvBr
    p hpK hpB hBK hKB
  have hheight' := tendsto_map'_iff.1 hheight
  have hlift' := tendsto_map'_iff.1 hlift
  have hsum := (hzero.comp hinv).add (hheight'.add (hlift'.const_mul (chiC κ)))
  rw [zero_add, hword] at hsum
  exact hsum.congr fun y => by
    dsimp only [Function.comp_def]
    ring

end Comparison

end InteractingSLE.Sec7.PocketStopSide
