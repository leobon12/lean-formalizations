/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtLift
import InteractingSLE.Spec.Supplement.SB2MtLines
import InteractingSLE.Spec.Supplement.SB2ZsSucc

/-!
# SB2(2)'s relative versions match the canonical driver code before every stop

Packet PROVE-SB2-LCMEAN, round 13. For SB2(2)'s relative versions at announced stops at B's stage `ℓ` (F2b,
`Ms.StageVersionS`) with K2's (S) and (L) at every stop on every admissible type cell of F3's word, almost surely on
the live event, for every `m`, the stop `V m` is at most the lifetime of the canonical driver code of (F3's word, the
chart field), and the frozen driver `W m` is that code at the dyadic times before `V m`:

* **`ae_isStopDrvMatch_of_stageVersionS`**: SB2(1)'s `Lv.ae_isStopDrvMatch_of_versionS` for SB2(2)'s versions, with
  the stopped K2 converse `Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on` on every type cell. The version bounds the
  stop by the threshold only on the seed-admissible part of a cell (`Ms.StageVersionG.Λ_le`), so the lemma asks that
  the live event lies there almost surely (`hseed`; the relative seed is admissible — discharged with the relative
  word's local heights).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord} {types : Set WordType}
  {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **SB2(2)'s relative versions are the canonical driver code before every stop.** For relative versions at
announced stops with K2's (S) and (L) at every stop on every admissible type cell of the word `β₁`, almost surely on
the live event, for every `m`, `V m` is at most the lifetime of the canonical driver code of `(β₁, chart field)` and
`W m` is that code at the dyadic times before `V m`. -/
theorem ae_isStopDrvMatch_of_stageVersionS (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hhm : Measurable h)
    (S : StageVersionS κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L relLife)
    (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁) (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β₁ ω) ∈ types)
    (hc : ∀ ω, (Φ ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (hlc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      IntegrableOn (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ) F P)
    (hker : ∀ m, ∀ w ∈ types,
      HasSafeLaw κ (typedRhoL w) (typedRhoR w) P (S.ver m).𝓗 (seedCell κ ψ β₁ F w) (S.V m) (S.ver m).W
          (geomLW (S.ver m).W (cellXL κ ψ β₁ w)) (geomRW (S.ver m).W (cellXR κ ψ β₁ w))
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
        HasSafeMembers P (S.ver m).𝓗 (seedCell κ ψ β₁ F w) (S.V m) (S.ver m).W
          (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)))
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β₁ F w → ω ∈ seedCell κ ψ β₁ F w) :
    ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) := by
  suffices hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ F → IsStopDrvMatch (driverCode h12p hκ ψ
      (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω) (S.V m ω) by
    filter_upwards [ae_all_iff.2 hm] with ω hω hF' m using hω m hF'
  intro m
  set Vd := S.ver m with hVd
  have hcell : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
      IsStopDrvMatch (driverCode h12p hκ ψ (β₁ ω, Chart.chartTransport (hc ω) 1 0 (chiC κ) (h ω)))
        (fun t => Vd.W t ω) (S.V m ω) := by
    intro w hw
    obtain ⟨hlaw, hmem⟩ := hker m w hw
    have hxL0 : ∀ ω i, cellXL κ ψ β₁ w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.1
    have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ β₁ w ω j := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.2
    have hxLa : ∀ ω, Antitone (cellXL κ ψ β₁ w ω) := fun ω => (FCDet.isOrderedForceWord_typeXL (β₁ ω)).1
    have hxRm : ∀ ω, Monotone (cellXR κ ψ β₁ w ω) := fun ω =>
      (FCDet.isOrderedForceWord_typeXL (β₁ ω)).2.2.1
    have hword : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
        flowLineNL (β₁ ω).fn (β₁ ω).jumps 0 = w.1 ∧ flowLineNR (β₁ ω).fn (β₁ ω).jumps 0 = w.2.1 ∧
        truncWord w.1 w.2.1 (padFL κ ψ (β₁ ω).fn (β₁ ω).jumps) =
          ((cellXL κ ψ β₁ w ω, cellXR κ ψ β₁ w ω), (typedRhoL w, typedRhoR w)) :=
      Eventually.of_forall fun ω hω => k2_word_of_mem_wordTypeCell hω.1
    have hVthr : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
        S.V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ β₁ w) (cellXR κ ψ β₁ w) ω := by
      have h1 := Vd.Λ_le w hw
      rw [S.Λ_eq m w] at h1
      exact h1
    exact Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on h12p h13 hκ Vd.marks_le
      (measurableSet_seedCell hβ₁ hF w) hβ₁ (measurable_cellXL hβ₁ w) (measurable_cellXR hβ₁ w) hxL0 hxR0 hxLa
      hxRm hword Vd.W_zero Vd.W_cont Vd.W_adapted hhm hc hdom hfwd hliftm hlc
      (fun φ => (hint φ).mono_set (seedCell_subset w)) S.record_meas (S.ρ_meas m) (S.ρ_rule m) (S.ρs_meas m)
      (S.ρs_rule m) (S.ρs_fin m) (S.ρs_mono m) (S.V_eq m)
      ((S.ann m).mono fun ω h hω => h (seedCell_subset w hω)) hVthr hlaw hmem
  filter_upwards [(ae_ball_iff htypes).2 hcell, hcover, (ae_ball_iff htypes).2 hseed] with ω hcode hcov hsd hF'
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (β₁ ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ types := hw₀e ▸ hcov hF'
  exact hcode w₀ hw₀ (hsd w₀ hw₀ ⟨hF', hw₀e⟩)

end InteractingSLE.Theorem14.SB.Mu
