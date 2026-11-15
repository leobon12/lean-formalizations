/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdMart
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdSeeds

/-!
# The seeded row from integrated seeds and the actual amalgamated force law

Packet PROVE-ZHAN-GT4-A22. The positive first-prefix row has no residual
band-nonvanishing premise. The opposite original drift uses precisely
`mirrorSourceCharge`, retaining the distinction between seeds and ordinary marks.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The concrete row martingale from integrated seed data, protected
geometry and the original marginal with the amalgamated source charge. -/
theorem seedHeightField_row_facts_of_integrated_seeds {n : ℕ} {P : Measure Ω} {κ S p s : ℝ} (hκ : 0 < κ)
    (rr : Fin n → ℝ) (W₁ : ℝ → ℝ) (V : Fin n → ℝ → ℝ)
    (W₂ : Ω → ℝ → ℝ) (as Ws bt Wt : Ω → ℝ → ℝ → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B D : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (hS : 0 < S) (hT : ∀ ω, 0 < T ω) (hs : s ∈ Ioc (0 : ℝ) S)
    (h0 : ∀ ω, W₂ ω 0 = p)
    (hdW : ∀ ω, (fun u => W₂ ω u - W₂ ω 0) = driftDriver (Real.sqrt (16 / κ)) B D ω)
    (h : ∀ ω, TwoViewRect W₁ (W₂ ω) S (T ω) (as ω) (Ws ω) (bt ω) (Wt ω))
    (hq₁ : ∀ ω, ∃ q, IsForwardSol W₁ ((W₂ ω 0 : ℝ) : ℂ) S q)
    (hW₂ : ∀ ω, Continuous (W₂ ω))
    (hq₂ : ∀ ω, ∃ q, IsForwardSol (W₂ ω) (0 : ℂ) (T ω) q)
    (hW₁0 : W₁ 0 = 0) (hseed : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hinj : Function.Injective fun m => V m s)
    (hclear : ∀ ω m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull (W₂ ω) v))
    (hB : IsFilteredBrownianReal 𝓕 B P) (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hBc : ∀ ω, Continuous (B · ω)) (hDc : ∀ ω, Continuous (D · ω))
    (hVm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => (frzChart (W₂ ω) u 0).re - p)
    (hStop : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {rad a₀ γ Γ lam L Tm c₀ C₀ : ℝ} (hr : 0 < rad) (ha : 0 < a₀) (hg : 0 < γ)
    (hc : 0 < c₀) (hC : 0 ≤ C₀) (hL : ScaleOK rad a₀ γ Γ lam Tm L)
    (hTTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    (hd9 : ∀ ω, (seedTView κ rr W₁ (W₂ ω) (bt ω) (Wt ω) V s).D9Const
      (fwdHull (fun u => W₁ u - p) s) (T ω) rad a₀ γ Γ lam)
    (hgap : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      c₀ ≤ |(fwdMap (W₂ ω) t 0).re| ∧ |(fwdMap (W₂ ω) t 0).re| ≤ C₀)
    (hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal ω)
        (mirrorSourceCharge κ rr /
          (W₂ ω t - (frzChart (W₂ ω) t 0).re)) (Icc (0 : ℝ) (T ω)) t) :
    Martingale (fun (t : ℝ≥0) ω =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v)
        ω s (min (t : ℝ) (T ω))) 𝓕 P ∧
    (∀ ω, Continuous fun t : ℝ≥0 =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v)
        ω s (min (t : ℝ) (T ω))) ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) ω, |seedHeightField
      (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v) ω s (min (t : ℝ) (T ω))| ≤ C) ∧
    ∀ ω, seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v) ω s 0 = 1 := by
  have hsI := Ioc_subset_Icc_self hs
  have hne : ∀ ω v, v ∈ Icc (0 : ℝ) (T ω) →
      ∀ i, (seedSView κ rr W₁ (W₂ ω) (as ω) (Ws ω) V v).gapVal i s ≠ 0 := by
    intro ω v hv
    obtain ⟨q, hq⟩ := hq₁ ω
    exact (h ω).seed_gapVal_ne hS (NNReal.coe_pos.2 (hT ω)) hs hv hq hseed hinj (hclear ω)
  have hcoef : (16 / κ) * (-1 / 2 + ∑ m, -(κ / 4) * rr m) = mirrorSourceCharge κ rr := by
    rw [mul_add, Finset.mul_sum]
    convert mirrorSourceCharge_eq hκ.ne' rr using 1
    ring
  exact seedHeightField_row_facts hκ rr W₁ V W₂ as Ws bt Wt 𝓕 B D T hS hT hsI h0 hdW h
    hq₁ hW₂ hq₂ (fun m => (hseed m).zero.trans hW₁0) hclear hne hB hDm hBc hDc hVm hStop
    hr ha hg hc hC hL hTTm hd9 (fun m => (hseed m).ne s hs) hinj hgap
    (fun ω t ht => by simpa only [hcoef] using hD ω t ht)

end InteractingSLE.ZhanGT4
