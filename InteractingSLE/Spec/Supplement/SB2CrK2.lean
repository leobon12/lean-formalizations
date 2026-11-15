/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrStage
import InteractingSLE.Spec.Supplement.SB2CiK2

/-!
# K2 at the root in B's own time: the versions are the canonical code before every stop

Packet PROVE-SB2-CONDFIN (round 8, D44). `Ci.ae_isStopDrvMatch_of_stageVersionS` and `Ci.ae_isStopDrvMatch_of_lines`
for the root's versions `Cr.RootVersionS`. LCMEAN's core `Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on` conditions on
each version's `𝓗 0` (the entrance), where the root event, the word and the stops' record are measurable. (S) and
(L) come from the B-time line family (`Cr.hasSafeLaw_hasSafeMembers_of_rootLines`).

* `ae_isStopDrvMatch_of_rootVersionS`; **`ae_isStopDrvMatch_of_rootLines`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cr

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms Mt Mu
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {Fr : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **The root's relative versions are the canonical driver code before every stop**, from K2's (S) and (L) at
every stop on every admissible type cell of the root event. -/
theorem ae_isStopDrvMatch_of_rootVersionS (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hhm : Measurable h)
    (S : RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ β₁ types pc tL L relLife)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (β₁ ω) ∈ types)
    (hc : ∀ ω, (Φ ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ) Fr P)
    (hker : ∀ m, ∀ w ∈ types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P (S.ver m).𝓗 (seedCell κ ψ β₁ Fr w) (S.V m) (S.ver m).W
          (geomLW (S.ver m).W (cellXL κ ψ β₁ w)) (geomRW (S.ver m).W (cellXR κ ψ β₁ w))
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P (S.ver m).𝓗 (seedCell κ ψ β₁ Fr w) (S.V m) (S.ver m).W
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)))
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β₁ Fr w → ω ∈ seedCell κ ψ β₁ Fr w) :
    ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) := by
  suffices hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ Fr → IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) by
    filter_upwards [ae_all_iff.2 hm] with ω hω hF' m using hω m hF'
  intro m
  set Vd := S.ver m with hVd
  have hβ₁' : Measurable[Vd.𝓗 0] β₁ := hβ₁.mono Vd.marks_le le_rfl
  have hcell : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
      IsStopDrvMatch (driverCode h12p hκ ψ (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω)))
        (fun t => Vd.W t ω) (S.V m ω) := by
    intro w hw
    obtain ⟨hlaw, hmem⟩ := hker m w hw
    have hxL0 : ∀ ω i, cellXL κ ψ β₁ w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.1
    have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ β₁ w ω j := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.2
    have hxLa : ∀ ω, Antitone (cellXL κ ψ β₁ w ω) := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).1
    have hxRm : ∀ ω, Monotone (cellXR κ ψ β₁ w ω) := fun ω =>
      (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.1
    have hword : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
        flowLineNL (β₁ ω).fn (β₁ ω).jumps 0 = w.1 ∧ flowLineNR (β₁ ω).fn (β₁ ω).jumps 0 = w.2.1 ∧
        truncWord w.1 w.2.1 (padFL κ ψ (β₁ ω).fn (β₁ ω).jumps) =
          ((cellXL κ ψ β₁ w ω, cellXR κ ψ β₁ w ω), (typedRhoL w, typedRhoR w)) :=
      Eventually.of_forall fun ω hω => k2_word_of_mem_wordTypeCell hω.1
    have hVthr : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
        S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω := by
      have h1 := Vd.Λ_le w hw
      rw [S.Λ_eq m w] at h1
      exact h1
    exact Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on h12p h13 hκ (le_refl (Vd.𝓗 0))
      (measurableSet_seedCell hβ₁' Vd.root_meas w) hβ₁' (measurable_cellXL hβ₁' w) (measurable_cellXR hβ₁' w)
      hxL0 hxR0 hxLa hxRm hword Vd.W_zero Vd.W_cont Vd.W_adapted hhm hc hdom hfwd hliftm hlc
      (fun φ => (hint φ).mono_set (seedCell_subset w)) (S.record_meas m) (S.ρ_meas m) (S.ρ_rule m)
      (S.ρs_meas m) (S.ρs_rule m) (S.ρs_fin m) (S.ρs_mono m) (S.V_eq m)
      ((S.ann m).mono fun ω h hω => h (seedCell_subset w hω)) hVthr hlaw hmem
  filter_upwards [(ae_ball_iff htypes).2 hcell, hcover, (ae_ball_iff htypes).2 hseed] with ω hcode hcov hsd hF'
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (β₁ ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hF'
  exact hcode w₀ hw₀ (hsd w₀ hw₀ ⟨hF', hw₀e⟩)

variable {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **K2 at the root from the B-time line family**: the root's versions in the canonical hull chart are the canonical
driver code of `(β₁, chart field)` before every stop, almost surely on the root event, from the line sets' locality,
the hull clause and the line mean where the clock is positive. -/
theorem ae_isStopDrvMatch_of_rootLines (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : RootVersionS κ ψ P Fr 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L relLife)
    (hK : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (β₁ ω) ∈ types)
    (hBm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hBc : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hBl : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P)
    (hmean : ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
        0 < (S.ver m).a t ω → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ ψ β₁ w))
              (geomRW (S.ver m).W (cellXR κ ψ β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ)
        Fr P)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β₁ Fr w → ω ∈ seedCell κ ψ β₁ Fr w) :
    ∀ᵐ ω ∂P, ω ∈ Fr → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω) := by
  obtain ⟨hc, hliftc, hlift, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hK hKc hKp hx₀
  obtain ⟨hlocC, g, hg⟩ := Mt.lineSets_inputs hh hu₀ hBm hBc hBl hloc
  have hle : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  refine ae_isStopDrvMatch_of_rootVersionS h12p h13 hκ hh.1 S hβ₁ htypes hcover
    (isConformal_canon x₀ hKc hKp) (fun z => hle _ (hdom z)) (fun z => (hfwd z).mono hle le_rfl)
    (fun z => (hliftm z).mono hle le_rfl) hliftc hint (fun m w hw => ?_) hseed
  have h2 := hasSafeLaw_hasSafeMembers_of_rootLines hh hu₀ (S.ver m) hw hβ₁ (isConformal_canon x₀ hKc hKp)
    hliftc hlift hdom hfwd hliftm (fun t ω => A₁ t ω ∪ A₂ t ω) hBm hBc hlocC
    (fun t => (S.ver m).hull w hw t) g hg (hmean g hg m w hw)
  rw [S.Λ_eq m w] at h2
  exact h2

end InteractingSLE.Theorem14.SB.Cr
