/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuLim

/-!
# SB2(2)'s kernel half at B's stage `ℓ`: K2 at every stop of the relative versions

Packet PROVE-SB2-LCMEAN, round 13. Assembly of the kernel half at one stage of the lower walk B, at the `P` level:

* the relative versions at announced stops (F2b, `Ms.StageVersionS`) with the canonical relative chart
  `Mo.hullChart (fillH (K ω)) (x₀ ω)` of a compact dyadic-hit measurable retained hull `K`;
* the line family's union line sets `A₁ t ∪ A₂ t` (`Ml.exists_sb2LineFamily_cf`): measurable, relatively closed,
  local, history-avoidance local for `𝓖 t`;
* the line mean at every stop (`hmean`), chart-pairing integrability and seed admissibility on the live event.

**`ae_isStopDrvMatch_of_lines`**: almost surely on the live event, for every `m`, the frozen driver `W m` is the
canonical driver code of (word, canonical chart field) before the stop `V m`
(`Mt.hullChart_k2Inputs`, `Mt.lineSets_inputs`, `Mt.hasSafeLaw_hasSafeMembers_of_stageLines`,
`Mu.ae_isStopDrvMatch_of_stageVersionS`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

omit mΩ [StandardBorelSpace Ω] in
/-- The canonical relative chart family is conformal at every sample. -/
theorem isConformal_canon (x₀ : Ω → ℝ) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (ω : Ω) : (Mo.hullChart (fillH (K ω)) (x₀ ω)).IsConformal :=
  Mo.isConformal_hullChart (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω)

/-- **K2 at every stop of SB2(2)'s relative versions at B's stage `ℓ`**: from the line family's union line sets with
their locality, the line mean at every stop, chart-pairing integrability and seed admissibility on the live event,
almost surely on the live event every frozen driver `W m` is the canonical driver code of (word, canonical chart
field) before its stop. -/
theorem ae_isStopDrvMatch_of_lines (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β₁ ω) ∈ types)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hBc : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hBl : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hmean : ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
        (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
              (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ)
        F P)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β₁ F w → ω ∈ seedCell κ ψ β₁ F w) :
    ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω) := by
  obtain ⟨hc, hliftc, hlift, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  obtain ⟨hlocC, g, hg⟩ := Mt.lineSets_inputs hh hu₀ hBm hBc hBl hloc
  have hle : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  refine ae_isStopDrvMatch_of_stageVersionS h12p h13 hκ hh.1 S hβ₁ hF htypes hcover
    (isConformal_canon x₀ hKc hKp) (fun z => hle _ (hdom z)) (fun z => (hfwd z).mono hle le_rfl)
    (fun z => (hliftm z).mono hle le_rfl) hliftc hint (fun m w hw => ?_) hseed
  have hFw : MeasurableSet[lineFiltC P 𝓖 0] (seedCell κ ψ β₁ F w) := measurableSet_seedCell hβ₁ hF w
  have h2 := Mt.hasSafeLaw_hasSafeMembers_of_stageLines hh hu₀ (S.ver m) hw hFw (isConformal_canon x₀ hKc hKp)
    hliftc hlift hdom hfwd hliftm (fun t ω => A₁ t ω ∪ A₂ t ω) hBm hBc hlocC
    (fun t => (S.ver m).hull w hw t) g hg (hmean g hg m w hw)
  rw [S.Λ_eq m w] at h2
  exact h2

end InteractingSLE.Theorem14.SB.Mu
