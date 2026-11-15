/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CiKer
import InteractingSLE.Spec.Supplement.SB2MuK2
import InteractingSLE.Spec.Supplement.SB2MuSeed

/-!
# K2 at a stage, (I4) and the seed cells, over NOJUMP's version structures

Packet PROVE-SB2-CONDFIN (round 3, D39). LCMEAN's `Mu.ae_isStopDrvMatch_of_lines`, `Mu.ae_canonLife_eq_relLife` and
`Mu.hseed_of_le_thr`, verbatim, over `Na.StageVersionS`. Generated from the landed originals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ci

open Mt hiding hBK_of_hull hasSafeLaw_hasSafeMembers_of_stageLines
open Mu hiding ae_isStopDrvMatch_of_stageVersionS ae_isStopDrvMatch_of_lines
  ae_canonLife_eq_relLife hseed_of_le_thr

section K2
open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

/-- **K2 at every stop of SB2(2)'s relative versions at B's stage `ℓ`**: from the line family's union line sets with
their locality, the line mean at every stop, chart-pairing integrability and seed admissibility on the live event,
almost surely on the live event every frozen driver `W m` is the canonical driver code of (word, canonical chart
field) before its stop. -/
theorem ae_isStopDrvMatch_of_lines (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL L relLife)
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
  have h2 := Ci.hasSafeLaw_hasSafeMembers_of_stageLines hh hu₀ (S.ver m) hw hFw (isConformal_canon x₀ hKc hKp)
    hliftc hlift hdom hfwd hliftm (fun t ω => A₁ t ω ∪ A₂ t ω) hBm hBc hlocC
    (fun t => (S.ver m).hull w hw t) g hg (hmean g hg m w hw)
  rw [S.Λ_eq m w] at h2
  exact h2

end K2

section Life
open Restart Exist Exist.Staged Exist.StagedLaw Sec2.Assembly Lv Supp8.Q3Stop Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)



variable {κ ψ : ℝ} {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
  {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
  {L relLife : Ω → ℝ≥0∞}

/-- **(I4): the canonical lifetime is the relative lifetime**, almost surely on the live event. -/
theorem ae_canonLife_eq_relLife (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ c types pc tL L relLife) (h𝒢 : 𝒢 ≤ mΩ)
    (hF : MeasurableSet[𝒢] F) (hc : Measurable[𝒢] c) {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) Y (c ω₀).fn (c ω₀).jumps)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w → ω ∈ seedCell κ ψ c F w)
    (hstop : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ (c ω, Y ω))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc (cellXL κ ψ c w) (cellXR κ ψ c w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ F → (driverCode h12p hκ ψ (c ω, Y ω)).2 = relLife ω := by
  have hE : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 →
      (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w)
        (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w) (cellXR κ ψ c w) ω :=
    fun r w _ => ae_lt_thr_frozenCanon h12p h13 hκ ψ h𝒢 hF hc hY hlaw w (r : ℝ).toNNReal
  have hL : ∀ r : ℚ, ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c F w → relLife ω < ⊤ →
      (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal t ω = (S.ver m).W t ω) →
      FCDet.thr (typedRhoL w) (typedRhoR w) (frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal) (cellXL κ ψ c w)
        (cellXR κ ψ c w) ω ≤ relLife ω :=
    fun r w hw => hlife w hw _ (continuous_frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal)
  filter_upwards [ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hE r),
    ae_all_iff.2 fun r => (ae_ball_iff htypes).2 (hL r), (ae_ball_iff htypes).2 hseed, hcover, hstop, S.V_sup]
    with ω hEω hLω hsω hcov hst hsup hFω
  have hst' := hst hFω
  have hge : relLife ω ≤ (driverCode h12p hκ ψ (c ω, Y ω)).2 := by
    rw [← hsup hFω]
    exact le_of_stops hst'
  refine le_antisymm ?_ hge
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (c ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hFω
  have hcell : ω ∈ wordTypeCell κ ψ c F w₀ := ⟨hFω, hw₀e⟩
  have hseedω := hsω w₀ hw₀ hcell
  have hfin : relLife ω < ⊤ := lt_of_lt_of_le hlt le_top
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hq : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal r := rfl
  have hq1 : relLife ω < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hq ▸ hr1
  have hq2 : (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (driverOf h12p hκ ψ (c ω, Y ω)).2 := hq ▸ hr2
  have h1 := hEω r w₀ hw₀ hcell hq2
  have hcont : ∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω →
      frozenCanon h12p hκ ψ c Y (r : ℝ).toNNReal t ω = (S.ver m).W t ω := by
    intro m t ht
    have hVr : S.V m ω ≤ relLife ω := (hsup hFω) ▸ le_iSup (fun m => S.V m ω) m
    have htq : t ≤ (r : ℝ).toNNReal := by
      have : (t : ℝ≥0∞) < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := lt_of_lt_of_le ht (hVr.trans hq1.le)
      exact (ENNReal.coe_lt_coe.1 this).le
    obtain ⟨-, hagree⟩ := eqOn_of_isStopDrvMatch_of_isDriverCodeMatch (hst' m)
      (isDriverCodeMatch_driverOf h12p hκ ψ (c ω, Y ω)) ((S.ver m).W_cont ω).continuousOn
      (continuousOn_driverOf h12p hκ ψ (c ω, Y ω))
    simp only [frozenCanon, hq2, ↓reduceIte, min_eq_left htq]
    exact (hagree t ht).symm
  have h2 := hLω r w₀ hw₀ hseedω hfin hcont
  exact absurd (lt_of_lt_of_le h1 h2) (not_lt.2 hq1.le)

end Life

section Seed
open Restart Exist.StagedLaw Lv Supp8.Q3Stop Ms

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **Seed admissibility on the type cells** from the cell-wide stop bound `V 0 ≤ thr` and the announced stops. -/
theorem hseed_of_le_thr (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ c types pc tL L relLife)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W (cellXL κ ψ c w) (cellXR κ ψ c w) ω) :
    ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c F w → ω ∈ seedCell κ ψ c F w := by
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

end InteractingSLE.Theorem14.SB.Ci
