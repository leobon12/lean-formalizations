/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoTail
import InteractingSLE.Spec.Supplement.SB2CrVer

/-!
# The root step of SB2(2)'s induction: the two version lemmas (D80)

Packet PROVE-SB2-CONDFIN, round 15 (decision D80: the root step of (P1)). F3LAW's joint step
`Fo.mvLaw_succ_succ_jointX` reads NOJUMP's versions only through two lemmas, both typed over the tail versions
`Na.StageVersionS`: the terminal hull identity (`Fo.ae_fill_eq_stepHull_joint`, via
`Qx.ae_fill_eq_stepHull_of_versions`) and the finiteness of the relative lifetime (`Fl.ae_relLife_ne_top_of_versions`).
At the root NOJUMP's statement gives `Cr.RootVersionS` (D48; tail start `entrR`, clock `0` up to the entrance). Both
lemmas read only fields the two structures share verbatim (`hull`, `reach`, `V_lt`, `V_sup`, `Λ_eq`, the clock and
driver fields); the tail start enters only through the versions' clauses, so the proofs carry over unchanged:

* **`ae_fill_eq_stepHull_of_versions_root`**, **`ae_relLife_ne_top_of_versions_root`**,
  **`ae_fill_eq_stepHull_joint_root`** (generated from the landed texts with the version type renamed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cd

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Lk Mf Qw Qx Supp8.Q3Stop Lv Fl Fo
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **Root twin** (`Cr.RootVersionS`, D80) of `Qx.ae_fill_eq_stepHull_of_versions`.
**The terminal hull identity, almost surely on F2b′'s live event.** -/
theorem ae_fill_eq_stepHull_of_versions_root (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {ψ : ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord} {types : Set WordType}
    (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (S : Cr.RootVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc tL L relLife)
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


/-- **Root twin** (`Cr.RootVersionS`, D80) of `Fl.ae_relLife_ne_top_of_versions`.
**The relative lifetime is finite, almost surely on F2b′'s live event, where the retained set after the piece
fills to a hull.** -/
theorem ae_relLife_ne_top_of_versions_root {κ ψ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord}
    {types : Set WordType} (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : Cr.RootVersionS κ ψ P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc tL L relLife)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ ψ (β ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w)
    (hA₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω)) {S₂ : Ω → Set ℂ}
    (hphys : ∀ᵐ ω ∂P, ω ∈ F → IsHPHull (fillH (S₂ ω)) →
      fillH (K ω) ⊆ fillH (S₂ ω) ∧ (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ H) ∧
        (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ fillH (S₂ ω)) ∧
        S₂ ω ∩ H ⊆ fillH (K ω) ∪ ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < L ω), A₂ (Real.toNNReal q) ω) :
    ∀ᵐ ω ∂P, ω ∈ F → IsHPHull (fillH (S₂ ω)) → relLife ω ≠ ⊤ := by
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
  have hA₁' : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω) := ae_all_iff.2 hA₁
  have hsd : ∀ᵐ ω ∂P, ∀ w ∈ types, ω ∈ wordTypeCell κ ψ β F w → ω ∈ seedCell κ ψ β F w :=
    (ae_ball_iff htypes).2 hseed
  filter_upwards [hH, hR, hA₁', hsd, S.V_sup, hcover, hphys] with ω hHω hRω hA₁ω hsdω hVsω hcovω hphysω hωF hZ
  have hwT : angleWordType κ ψ (β ω) ∈ types := hcovω hωF
  have hseedω : ω ∈ seedCell κ ψ β F (angleWordType κ ψ (β ω)) := hsdω _ hwT ⟨hωF, rfl⟩
  obtain ⟨hKZ, hA₂H, hA₂Z, -⟩ := hphysω hωF hZ
  refine ne_top_of_versions_at (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω) hZ hKZ (A₂ := fun t => A₂ t ω) hA₂H hA₂Z
    (W := fun m s => (S.ver m).W s ω) (fun m => (S.ver m).W_cont ω) (fun m => (S.ver m).W_zero ω)
    (a := fun m t => (S.ver m).a t ω) (fun m => (S.ver m).clock_cont ω) (fun m => (S.ver m).clock_zero ω)
    (V := fun m => S.V m ω) (hVsω hωF) (fun q m hqm => ?_) (fun r m hr => ?_)
  · have h1 := hHω q m _ hwT hseedω (by rw [S.Λ_eq m]; exact hqm)
    rw [hA₁ω q hωF] at h1
    exact h1
  · exact hRω r m _ hwT hseedω (by rw [S.Λ_eq m]; exact hr)


/-- **Root twin** (`Cr.RootVersionS`, D80) of `Fo.ae_fill_eq_stepHull_joint`. -/
theorem ae_fill_eq_stepHull_joint_root (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) {F : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord}
    {types : Set Supp8.Q3Stop.WordType} (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (S : Cr.RootVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc
      tL (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → Lv.angleWordType κ (-(Real.pi / 2)) (β ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ Lv.wordTypeCell κ (-(Real.pi / 2)) β F w →
      ω ∈ Lv.seedCell κ (-(Real.pi / 2)) β F w)
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, Supp8.GB6.RelDrv.IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ F → (driverOf h12p hκ (-(Real.pi / 2))
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    (hWC : ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (hrun : ∀ᵐ ω ∂P, ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∀ᵐ ω ∂P, ω ∈ F → relLife ω ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))) →
      IsHPHull (fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω)) →
      fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) =
        stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ (-(Real.pi / 2))
          (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
          ((driverOf h12p hκ (-(Real.pi / 2))
            (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2.toNNReal : ℝ) := by
  have hA₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω) := by
    intro q
    filter_upwards [hA (Real.toNNReal q), hA 0, hKF, hrun, hFl] with ω hq h0 hK hr hl hωF
    have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
          none := by
      rw [hr]; exact hl hωF
    obtain ⟨-, hlen⟩ := walk_instr_of_launch hl'
    rw [hK hωF, h0.1, hq.1]
    unfold fillVer
    beta_reduce
    rw [WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl]
  exact ae_fill_eq_stepHull_of_versions_root h12p hκ hKc hKp htypes S hcl2 hcover hseed hK2 hlife hA₁
    (ae_phys_joint u l k ℓ hA hWC hrun hKF hFl)


end InteractingSLE.Theorem14.SB.Cd
