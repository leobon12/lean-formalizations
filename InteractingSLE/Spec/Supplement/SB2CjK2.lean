/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CiMean
import InteractingSLE.Spec.Supplement.SB2MuInt

/-!
# K2 at one stage over NOJUMP's version structures (the composite)

Packet PROVE-SB2-CONDFIN (round 4, D39/D41). **`ae_k2_stage`**: LCMEAN's "K2(ℓ)" assembled — from a relative version
at announced stops (`Na.StageVersionS`), the law of the canonical chart field given the version's initial σ-algebra
with a bounded word, the line family's union line sets with their locality, the line mean at every stop, the cell-wide
stop bound `V ≤ thr` and the version-level (I4) clause, almost surely on the live event:

* every frozen driver `W m` is the canonical driver code of (word, canonical chart field) before its stop `V m`;
* the canonical code's lifetime is the relative lifetime `relLife`.

Pieces: `Ci.ae_isStopDrvMatch_of_lines` (stops), `Mu.integrableOn_chartPairing_of_law` (integrability),
`Ci.hseed_of_le_thr` (seed cells), `Ci.ae_canonLife_eq_relLife` ((I4)). The stage index, chart and family are
arbitrary, so this serves the relative root and the tail stages alike.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cj

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {c : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **K2 at one stage** (the composite): the stopped code match at every stop and the lifetime identity. -/
theorem ae_k2_stage (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) c types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hc : Measurable[lineFiltC P 𝓖 0] c) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (c ω) ∈ types)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hBc : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hBl : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hmean : ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w →
        (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ c w))
              (geomRW (S.ver m).W (cellXR κ ψ c w)) ω ((S.ver m).a t ω).toNNReal) z * φ z)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (c ω₀).fn (c ω₀).jumps)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, ∀ y ∉ (c ω).jumps, |(c ω).fn y| ≤ M)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ ψ c w) (cellXR κ ψ c w) ω)
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ c w) (cellXR κ ψ c w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ F →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ ψ
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω := by
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hseed := Ci.hseed_of_le_thr S hle
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
        (h ω) φ) F P := fun φ =>
    Mu.integrableOn_chartPairing_of_law hle0 hF (hle0 _ hF) subset_rfl (Mu.isConformal_canon x₀ hKc hKp)
      (fun z => hle0 _ (hdom z)) (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc
      hh.1 (chiC κ) (Y := fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (Eventually.of_forall fun _ _ => rfl) hM0 hM hlaw (ψ * chiC κ) φ
  have hstop := Ci.ae_isStopDrvMatch_of_lines h12p h13 hκ hh hu₀ S hK hKc hKp hx₀ hc hF htypes hcover hBm hBc hBl
    hloc hmean hint hseed
  have hZm : Measurable fun ω =>
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hlifeEq := Ci.ae_canonLife_eq_relLife h12p h13 hκ S hle0 hF hc hZm hlaw htypes hcover hseed hstop hlife
  filter_upwards [hstop, hlifeEq] with ω h1 h2 hω
  exact ⟨h1 hω, h2 hω⟩

end InteractingSLE.Theorem14.SB.Cj
