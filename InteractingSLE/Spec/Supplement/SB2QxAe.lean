/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxVer
import InteractingSLE.Spec.Supplement.SB2NaStmt
import InteractingSLE.Spec.Supplement.SB2ZsSucc
import InteractingSLE.Spec.Supplement.SB2QxFlow

/-!
# The terminal hull identity of the step `ℓ → ℓ + 2`, almost surely, from F2b′'s successor versions

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8). The relative versions
`Na.StageVersionS` of B's stage `ℓ` (F2b′'s successor, `Na.SB2LowerStageVersionStatement3`), with its coverage clause
(every B-time before the lifetime is before some stop), the type cover and seed admissibility of its live event
`F`, K2's
stopped driver match (`Mu.ae_isStopDrvMatch_of_lines`) and the identification of the canonical lifetime
(`Mu.ae_canonLife_eq_relLife`), give almost surely on `F` the hull after the piece:

* **`ae_fill_eq_stepHull_of_versions`**: `fill S₂ = fill K ∪ c⁻¹(K_T)` (`c = Mo.hullChart (fill K) x₀`, `T` the
  canonical lifetime, record driver `Qw.recDrv`), given the stage-set facts of B's stage (`hphys`, proved from
  `Qx.stageSet_capSpec_subset` / `Qx.stageSet_succ_succ_subset` by the consumer of the line family).

R48: Theorem 1.2 enters only through `Theorem12ParamStatement` (the canonical driver code).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qx

open Restart Exist Exist.Staged Exist.StagedLaw Qw Supp8.Q3Stop Lv
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The terminal hull identity, almost surely on F2b′'s live event.** -/
theorem ae_fill_eq_stepHull_of_versions (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {ψ : ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord} {types : Set WordType}
    (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (S : Na.StageVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc tL L relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (t : ℝ≥0∞) < L ω → ∃ m, (S.ver m).a t ω < S.V m ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w)
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, IsStopDrvMatch (driverCode h12p hκ ψ
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ F →
      (driverOf h12p hκ ψ (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 =
        relLife ω)
    (hA₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω)) {S₂ : Ω → Set ℂ}
    (hphys : ∀ᵐ ω ∂P, ω ∈ F → IsHPHull (fillH (S₂ ω)) →
      fillH (K ω) ⊆ fillH (S₂ ω) ∧ (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ H) ∧
        (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ fillH (S₂ ω)) ∧
        S₂ ω ∩ H ⊆ fillH (K ω) ∪ ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L ω), A₂ (Real.toNNReal q) ω) :
    ∀ᵐ ω ∂P, ω ∈ F → relLife ω ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ ψ
        (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))) →
      IsHPHull (fillH (S₂ ω)) →
      fillH (S₂ ω) = stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ ψ
        (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
        ((driverOf h12p hκ ψ
          (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2.toNNReal : ℝ) := by
  have hH : ∀ᵐ ω ∂P, ∀ (q : ℚ) (m : ℕ), ∀ w ∈ types, ω ∈ seedCell κ ψ β F w →
      (S.ver m).a (Real.toNNReal q) ω < (S.ver m).Λ w ω →
      H \ (A₁ (Real.toNNReal q) ω ∪ A₂ (Real.toNNReal q) ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a (Real.toNNReal q) ω).toNNReal) := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun m => (ae_ball_iff htypes).2 fun w hw => ?_
    exact (S.ver m).hull w hw _
  have hR : ∀ᵐ ω ∂P, ∀ (r : ℚ) (m : ℕ), ∀ w ∈ types, ω ∈ seedCell κ ψ β F w →
      ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < (S.ver m).Λ w ω → ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ (S.ver m).a t ω := by
    refine ae_all_iff.2 fun r => ae_all_iff.2 fun m => (ae_ball_iff htypes).2 fun w hw => ?_
    exact (S.ver m).reach w hw _
  have hC2 : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ F → ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L ω →
      ∃ m, (S.ver m).a (Real.toNNReal q) ω < S.V m ω := ae_all_iff.2 fun q => hcl2 _
  have hA₁' : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω) := ae_all_iff.2 hA₁
  have hVl : ∀ᵐ ω ∂P, ∀ m, ω ∈ F → S.V m ω < relLife ω := ae_all_iff.2 S.V_lt
  have hsd : ∀ᵐ ω ∂P, ∀ w ∈ types, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w :=
    (ae_ball_iff htypes).2 hseed
  filter_upwards [hH, hR, hC2, hA₁', hVl, hsd, S.V_sup, hcover, hK2, hlife, hphys] with ω hHω hRω hC2ω hA₁ω hVlω
    hsdω hVsω hcovω hK2ω hlifeω hphysω hωF hrel hg hZ
  have hwT : angleWordType κ ψ (β ω) ∈ types := hcovω hωF
  have hseedω : ω ∈ seedCell κ ψ β F (angleWordType κ ψ (β ω)) := hsdω _ hwT ⟨hωF, rfl⟩
  have hlife' := hlifeω hωF
  have hT : (driverOf h12p hκ ψ
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 ≠ ⊤ := by
    rw [hlife']; exact hrel
  obtain ⟨hKZ, hA₂H, hA₂Z, hcovS⟩ := hphysω hωF hZ
  have hVlt : ∀ m, S.V m ω < (driverOf h12p hκ ψ
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 := fun m => by
    rw [hlife']; exact hVlω m hωF
  have hVsup : ⨆ m, S.V m ω = (driverOf h12p hκ ψ
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 := by
    rw [hlife']; exact hVsω hωF
  have hmatch : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < S.V m ω → (S.ver m).W s ω = (driverOf h12p hκ ψ
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).1 s := fun m s hs =>
    (Lv.eqOn_of_isStopDrvMatch_of_isDriverCodeMatch (hK2ω hωF m) (Mu.isDriverCodeMatch_driverOf h12p hκ ψ _)
      ((S.ver m).W_cont ω).continuousOn (Mu.continuousOn_driverOf h12p hκ ψ _)).2 s hs
  have hhull : ∀ (q : ℚ) (m : ℕ), (S.ver m).a (Real.toNNReal q) ω < S.V m ω →
      H \ (fillH (K ω) ∪ A₂ (Real.toNNReal q) ω) = (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => (S.ver m).W r.toNNReal ω) ((S.ver m).a (Real.toNNReal q) ω).toReal) := by
    intro q m hqm
    have h1 := hHω q m _ hwT hseedω (by rw [S.Λ_eq m]; exact hqm)
    rw [hA₁ω q hωF] at h1
    exact h1
  have hreach : ∀ (r : ℚ) (m : ℕ), ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < S.V m ω →
      ∃ t, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ (S.ver m).a t ω := fun r m hr =>
    hRω r m _ hwT hseedω (by rw [S.Λ_eq m]; exact hr)
  have key := fill_eq_stepHull_at (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω) (Mz.isRegularDriver_driverOf h12p hκ ψ _) hg
    hT hZ hKZ (A₂ := fun t => A₂ t ω) (L := L ω) hA₂H hA₂Z hcovS (W := fun m s => (S.ver m).W s ω)
    (a := fun m t => (S.ver m).a t ω)
    (fun m => (S.ver m).clock_cont ω) (fun m => (S.ver m).clock_zero ω) (V := fun m => S.V m ω) hVlt hVsup
    hmatch hhull (fun q hq => hC2ω q hωF hq) hreach
  exact key

end InteractingSLE.Theorem14.SB.Qx
