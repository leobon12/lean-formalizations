/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2StopGen
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZeroId

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: good horizons of the stopped records

Packet PROVE-A1-G3LAW2. For regular G3 marginals (continuous Brownian paths, `GoodSmallG3` small curve at every
sample), at every frozen time `σ ≤ S₂ᵏ(y₀)` (including `σ = 0`):

* **`g3_isGoodTime_le`**: the small exit `S₁ᵏ(x₀)` is a good horizon of the small curve against the frozen large
  hull;
* **`g3_isGoodTime_stop`**: it is also good for the small driver stopped at `S₁ᵏ(x₀)` (lifetime `⊤`) against the
  large driver stopped at `σ` — the replacement data of the stopped records.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Loc

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The small exit is a good horizon at every frozen time `σ ≤ S₂ᵏ`** (including `σ = 0`). -/
theorem g3_isGoodTime_le (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (x₀ : X) :
    A1Ref.IsGoodTime y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ (g3S₁ x y W₁ ζ₁ k x₀) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h0 | hσ
  · subst h0
    obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
    have h0ζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₂ y₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₂ζ k y₀)
    obtain ⟨τ', hτ', hk⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 h0ζ
    rw [NNReal.coe_zero] at hτ' ⊢
    exact isGoodTime_zero_time hτ' hk (hS₁ k x₀).2 (by rw [ENNReal.ofReal_coe_nnreal]; exact (hS₁ k x₀).1)
  · exact (g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀).2.2.1

/-- **The small exit is a good horizon of the stopped records**: the small driver stopped at `S₁ᵏ(x₀)` (lifetime `⊤`)
against the large driver stopped at the frozen time `σ ≤ S₂ᵏ(y₀)`. -/
theorem g3_isGoodTime_stop (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (x₀ : X) :
    A1Ref.IsGoodTime y (Strip.extPath fun t => W₁ (min t (g3S₁ x y W₁ ζ₁ k x₀)) x₀) ⊤ 0
      (Strip.extPath fun t => W₂ (min t σ) y₀) σ (g3S₁ x y W₁ ζ₁ k x₀) := by
  obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hg := g3_isGoodTime_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσS x₀
  set S := g3S₁ x y W₁ ζ₁ k x₀ with hSdef
  have hSζ : (S : ℝ≥0∞) < ζ₁ x₀ := (hS₁ k x₀).1
  have hσζ : (σ : ℝ≥0∞) < ζ₂ y₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₂ζ k y₀)
  have hcS : ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hSζ)
  have hcσ : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 (σ : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc (h₂.path y₀).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hσζ)
  have hdS : Continuous (A1Ref.stopDrv (Strip.extPath (W₁ · x₀)) S) := A1Ref.continuous_stopDrv hcS S.coe_nonneg
  have hdσ : Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y₀)) σ) := A1Ref.continuous_stopDrv hcσ σ.coe_nonneg
  rw [extPath_stop_eq (W₁ · x₀) S, extPath_stop_eq (W₂ · y₀) σ]
  obtain ⟨T₁, hST₁, hc₁⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 hSζ
  obtain ⟨T₂, hσT₂, hc₂⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 hσζ
  refine isGoodTime_repl hg hdS ENNReal.ofReal_lt_top ?_ ?_
  · exact physHull_congr_of_continuousOn hc₁ hdS.continuousOn S.coe_nonneg hST₁
      fun u hu => (A1Ref.stopDrv_eqOn _ _ hu).symm
  · exact physHull_congr_of_continuousOn hc₂ hdσ.continuousOn σ.coe_nonneg hσT₂
      fun u hu => (A1Ref.stopDrv_eqOn _ _ hu).symm

end Loc

end InteractingSLE.ZhanGT4.A1G3L2
