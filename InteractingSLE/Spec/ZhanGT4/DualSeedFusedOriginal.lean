/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedMart

/-!
# The normalized opposite-view density from actual source records

Packet PROVE-ZHAN-GT4-A22. The fused density is a bounded continuous
martingale under the original marginal with its amalgamated charge.
Its identification with a concrete seeded height field is a separate
geometric reciprocity step.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The fused opposite density divided by its actual entrance value. -/
def FrzData.seedAccessDensity {n : ℕ} (d : FrzData n) (p : ℝ) (S t : ℝ≥0) : ℝ :=
  Real.exp (d.seedAccessEll p (min (t : ℝ) S) (d.W (min (t : ℝ) S)) - d.seedAccessEll p 0 (d.W 0))

/-- Original source records give the true normalized martingale, continuous
paths, a uniform deterministic bound and literal entrance one. No stochastic
opposite-view field, generator or martingale is a premise. -/
theorem seedAccess_density_facts {n : ℕ} {P : Measure Ω} {κ : ℝ} (hκ : 0 < κ) (rr : Fin n → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B D : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (d : Ω → FrzData n)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ p : ℝ} {ζ : Fin n → ℝ} {V : Ω → ℝ → ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ₀ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdζ : ∀ ω, (d ω).ζ = ζ)
    (hB : IsFilteredBrownianReal 𝓕 B P)
    (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hBc : ∀ ω, Continuous (B · ω)) (hDc : ∀ ω, Continuous (D · ω))
    (hVm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => V ω u)
    (hV : ∀ ω, ∀ u ∈ Icc (0 : ℝ) (S ω), V ω u = (d ω).seedAccessSource p u)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {r a₀ γ Γ lam L Tm c₀ C₀ : ℝ} (hr : 0 < r) (ha : 0 < a₀) (hg : 0 < γ)
    (hc : 0 < c₀) (hC : 0 ≤ C₀) (hL : ScaleOK r a₀ γ Γ lam Tm L)
    (hST : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hd9 : ∀ ω, (d ω).D9Const A (S ω) r a₀ γ Γ lam)
    (hq₀ : ∀ ω, ∃ q, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) q)
    (hq : ∀ ω m, ∃ q, IsForwardSol (d ω).W' ((d ω).ζ m) ((d ω).a (S ω)) q)
    (hζ₀ : ∀ ω m, (d ω).ζ m ≠ (d ω).ζ₀) (hζ : ∀ ω, Function.Injective (d ω).ζ)
    (hqS : ∀ ω, ∃ q, IsForwardSol (d ω).W (p : ℂ) (S ω) q)
    (hgap : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω),
      c₀ ≤ |(fwdMap (d ω).W t p).re| ∧ |(fwdMap (d ω).W t p).re| ≤ C₀)
    (hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω)
        ((d ω).κ * (d ω).seedAccessExponent / ((d ω).W t - (d ω).seedAccessSource p t))
        (Icc (0 : ℝ) (S ω)) t) :
    Martingale (fun t ω => (d ω).seedAccessDensity p (S ω) t) 𝓕 P ∧
      (∀ ω, Continuous (fun t => (d ω).seedAccessDensity p (S ω) t)) ∧
      (∃ C : ℝ, ∀ t ω, |(d ω).seedAccessDensity p (S ω) t| ≤ C) ∧
      ∀ ω, (d ω).seedAccessDensity p (S ω) 0 = 1 := by
  obtain ⟨ρ, K, hρ, hf⟩ := exists_isDriftLogField_seedAccess hκ rr 𝓕 B D S d
    hdW hdκ hdr hdφ hdζ₀ hdζ (fun u => hB.2.1 u) hDm hBc hDc hVm hV hS hr ha hg hc hC hL
    hST h hd9 hq₀ hq hζ₀ hζ hqS hgap hD
  obtain ⟨hm, -⟩ := hf.normalized_martingale_zero hB hBc (Real.sqrt_nonneg _) hρ hS
  obtain ⟨hcont, hb⟩ := hf.normalized_path_facts hBc hρ
  refine ⟨?_, ?_, ⟨Real.exp (2 * K), ?_⟩, ?_⟩
  · simpa only [FrzData.seedAccessDensity, ← hdW] using hm
  · simpa only [FrzData.seedAccessDensity, ← hdW] using hcont
  · simpa only [FrzData.seedAccessDensity, ← hdW] using hb
  · intro ω
    simp only [FrzData.seedAccessDensity, NNReal.coe_zero]
    rw [min_eq_left (S ω).coe_nonneg, sub_self, Real.exp_zero]

end InteractingSLE.ZhanGT4
