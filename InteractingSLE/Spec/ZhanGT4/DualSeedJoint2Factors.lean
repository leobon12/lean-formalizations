/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2At
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformMeas

/-!
# Measurable normalized seeded densities with a random frozen hull

PROVE-ZHAN-GT4-A22. The normalized divided differences remain measurable at
coincident seeds. The hull and chart may be random; all own-map observables
come from `FrzMeasR`, including their values at the real seed coordinates.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol)

/-- The normalized seeded log density is measurable on a protected event.
The original source and seed coordinates are measurable inputs; image-chain
coordinates are obtained from the random-hull mapping-out function. -/
theorem measurable_seed_normEll_random_hull {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {d : Ω → SeedData n} {A : Ω → Set ℂ} {T : Ω → ℝ} {G : Set Ω} {s κ : ℝ}
    {rr : Fin n → ℝ} (hs : 0 ≤ s)
    (hM : ∀ u ∈ Icc (0 : ℝ) s,
      FrzMeasR (fun ω => (d ω).W) (fun ω => (d ω).W') (fun ω => (d ω).a)
        A (fun ω => (d ω).φ) T G u)
    {q : ℕ → Ω → ℂ} (hq : MarkSeq A (fun ω => (d ω).φ) G (fun ω => (d ω).ζ₀) q)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0,
      Disjoint (ball ((d ω).V m s : ℂ) ρ) (imgHull (d ω).W (A ω) s))
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hV : ∀ m, Measurable (G.indicator fun ω => (d ω).V m s))
    (hV₀ : Measurable (G.indicator fun ω => (d ω).V₀ s))
    (hG₀ : Measurable (G.indicator fun ω => (d ω).G₀ s)) :
    Measurable (G.indicator fun ω => (d ω).normEll s) := by
  have hMs := hM s ⟨hs, le_rfl⟩
  have hA21 : Measurable (G.indicator fun ω => (d ω).A21 s) := by
    convert (hMs.measurable_frzImgD hq hv).div hG₀ using 1
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, SeedData.A21, Pi.div_apply]
    · simp only [indicator_of_notMem hω, Pi.div_apply, zero_div]
  refine SeedData.measurable_indicator_normEll hMs.meas hdκ hdr
    hMs.measurable_frzA (hMs.measurable_frzImg hq hv) hA21 (measurable_frzLogFR hs hM)
    (fun m => hMs.measurable_F_at 0 (hV m) (fun ω hω => hcl ω hω m))
    (fun m => hMs.measurable_F_at 1 (hV m) (fun ω hω => hcl ω hω m))
    (hMs.drv.indicator hMs.meas) hV₀ hV ?_
  intro ω hω m
  obtain ⟨ρ, hρ, hc⟩ := hcl ω hω m
  exact (d ω).deriv_F_zero
    (((hMs.own ω hω).ownExt_props (hMs.mem ω hω) hc).1.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (by positivity))))

end InteractingSLE.ZhanGT4
