/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonCover

/-!
# GW4: the actual finite-word mean on every nonexposed access

Combine the constructed real-characteristic cover with the proved local-set
boundary decay. This discharges all current accesses outside the exposed
seed interval, with every fiber over the finite original marks excluded.
No reference cover, branch or increment-law hypothesis is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Sec7.PhaseSel Sec7.PocketStopSide
  Sec7.Aux119Heights LocalSets WholeField MartChar

/-- The component's canonical corrected mean has the full typed word at
every nonexposed access. The physical exceptional set is explicitly the
image of the original height marks, so its fibers need not be finite. -/
theorem ae_component_boundary_limits_outside_seed_interval
    {Ω : Type*} [MeasurableSpace Ω] {k : ℝ} (hk : 0 < k)
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B)
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω))
    (d : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens)
    (hg : IsLocalSetMean (B t) (centredField X u₀) ν g) :
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      let q := (lineClock F Wd GT V t ω).toNNReal
      ∃ E : Set ℂ, E.Finite ∧ E = Complex.ofReal '' (c₀.jumps : Set ℝ) ∧
        ∀ ξ : ℝ, ξ ∉ componentLineJumps k c₀ F X Wd GT R V t ω →
          ξ ∉ Ioo (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
            (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω) →
          extendFrom H (componentLineChart F Wd GT R V t ω).2.1 (ξ : ℂ) ∉ E →
          Tendsto (fun y => harmRep (g ω) (H \ B t ω) (fwdMapInv (wpath R ω) q y) +
              u₀ (fwdMapInv (wpath R ω) q y) +
              chiC k * (logDerivFwd (wpath R ω) q (fwdMapInv (wpath R ω) q y)).im)
            (𝓝[H] (ξ : ℂ)) (𝓝 (componentLinePhaseData k c₀ F X Wd GT R V d t ω ξ)) := by
  filter_upwards [ae_component_real_germs (k := k) hX hloc hR0 hRc t g hg]
    with ω hReal hlt
  dsimp only
  refine ⟨Complex.ofReal '' (c₀.jumps : Set ℝ), c₀.jumps.finite_toSet.image _, rfl, ?_⟩
  intro ξ hJump hOutside hPhysical
  obtain ⟨x, a, hx, ha, hξ, hWord⟩ := componentRealAccess_outside_seed_interval
    hk d t (hRc ω) (hR0 ω) hJump hOutside hPhysical
  have h := hReal hlt x hx a ha
  rw [← hξ, hWord] at h
  exact h

end InteractingSLE.Theorem14.GW4Fix
