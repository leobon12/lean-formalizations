/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrLife2
import InteractingSLE.Spec.Supplement.SB2CrMean
import InteractingSLE.Spec.Supplement.SB2CjK2

/-!
# K2 at the root in B's own time (the composite)

Packet PROVE-SB2-CONDFIN (round 8, D44). `Cj.ae_k2_stage` for the root's versions `Cr.RootVersionS`: almost surely on
the root event `Fr`, every version is the canonical code of `(β₁, chart field)` before its stop, and the canonical
lifetime is the relative lifetime. The law of the chart field is asked on a B-time-`0` event `FB ⊇ Fr` (D44:
`stageEvent ∩ {relOff ≥ ℓ} ∩ {0 < ζ_ℓ}`, F3LAW's law given `lineFiltC 𝓖 0`). The line mean is asked only where the
relative clock is positive (`Cr.ae_lineMean_pos_root` gives it from the B-time line family).

* `hseed_of_le_thr_root`; **`ae_k2_root`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cr

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms Mu
open Supp8.GB6.RelDrv (IsStopDrvMatch)

section Seed

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Fr : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **Seed admissibility on the root's type cells** from the cell-wide stop bound `V 0 ≤ thr` and the announced
stops (`Ci.hseed_of_le_thr` on the root event). -/
theorem hseed_of_le_thr_root (S : RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ c types pc tL L relLife)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ ψ c w) (cellXR κ ψ c w) ω) :
    ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w := by
  intro w hw
  filter_upwards [hle w hw, S.ann 0] with ω h1 hann hω
  refine ⟨hω, fun hs => ?_⟩
  have hxL0 : ∀ ω i, cellXL κ ψ c w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (c ω)).2.1
  have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ c w ω j := fun ω => (FCDet.isOrderedForceWord_typeXL (c ω)).2.2.2
  have hz := thr_eq_zero_of_seed (S.ver 0).W_zero (S.ver 0).W_cont hxL0 hxR0 hs
  have hpos : 0 < S.V 0 ω := lt_of_le_of_lt zero_le ((hann hω.1).1 0)
  have h2 := h1 hω
  rw [hz] at h2
  exact absurd (lt_of_lt_of_le hpos h2) (lt_irrefl _)

end Seed

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {Fr FB : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {c : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **K2 at the root** (the composite): on the root event, the stopped code match at every stop and the lifetime
identity. -/
theorem ae_k2_root (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : RootVersionS κ ψ P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) c types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hc : Measurable[lineFiltC P 𝓖 0] c) (hFB : MeasurableSet[lineFiltC P 𝓖 0] FB)
    (hFrB : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ FB)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (c ω) ∈ types)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hBc : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hBl : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hmean : ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c Fr w →
        0 < (S.ver m).a t ω → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ c w))
              (geomRW (S.ver m).W (cellXR κ ψ c w)) ω ((S.ver m).a t ω).toNNReal) z * φ z)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ FB → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (c ω₀).fn (c ω₀).jumps)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, ∀ y ∉ (c ω).jumps, |(c ω).fn y| ≤ M)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ ψ c w) (cellXR κ ψ c w) ω)
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c Fr w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ c w) (cellXR κ ψ c w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ Fr →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ ψ
        (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω := by
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hseed := hseed_of_le_thr_root S hle
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
        (h ω) φ) Fr P := fun φ =>
    (Mu.integrableOn_chartPairing_of_law hle0 hFB (hle0 _ hFB) subset_rfl (Mu.isConformal_canon x₀ hKc hKp)
      (fun z => hle0 _ (hdom z)) (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc
      hh.1 (chiC κ) (Y := fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (Eventually.of_forall fun _ _ => rfl) hM0 hM hlaw (ψ * chiC κ) φ).mono_set_ae hFrB
  have hstop := ae_isStopDrvMatch_of_rootLines h12p h13 hκ hh hu₀ S hK hKc hKp hx₀ hc htypes hcover hBm hBc hBl
    hloc hmean hint hseed
  have hZm : Measurable fun ω =>
      Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hlifeEq := ae_canonLife_eq_relLife_root h12p h13 hκ S hle0 hFB hFrB hc hZm hlaw htypes hcover hseed hstop
    hlife
  filter_upwards [hstop, hlifeEq] with ω h1 h2 hω
  exact ⟨h1 hω, h2 hω⟩

end InteractingSLE.Theorem14.SB.Cr
