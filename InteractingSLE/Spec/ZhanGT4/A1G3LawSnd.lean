/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawCol
import InteractingSLE.Spec.ZhanGT4.A1G3LawSample

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the per-sample frozen law

Packet PROVE-A1-G3LAW (R83). The image curve is the small curve (on `X`), the conditioning curve the large curve (on
`Y`), frozen at the height `σ`. For regular G3 marginals with continuous Brownian paths at every sample and a
`GoodSmallG3` small curve at every sample (the patched marginals):

* `g3Col`: the column of G3 records at the frozen sample `y₀` and height `σ`;
* **`g3_isSeedSampleLaw`**: at every frozen sample `y₀` and every height `σ ∈ (0, S₂ᵐ(y₀)]`, under the rectangle
  density `P₁.withDensity (x ↦ M(S₁ᵐ(x), σ))` (exactly the family density of A1-RECTLAW2's small-curve direction at a
  protected frozen time), every image datum that agrees with the seeded capacity coordinates of the column up to the
  cap (driver, the four image forces in the order of the small image word, the residual as the noise, the cap the
  capacity horizon, the other caps image capacities at own-time stopping times) satisfies the one-sample law
  `IsSeedSampleLaw`. This is the per-sample frozen law with the compensated residual as the noise, from the seeded
  (D10) on G3's records.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family Girsanov

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The column of (G3) records at the frozen sample `y₀` and height `σ` (rectangle `m`). -/
abbrev g3Col (κ x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (σ : ℝ) (y₀ : Y) : X → SeedData 3 :=
  fun ω => g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m σ (ω, y₀)

omit mY in
/-- The seeded measure of the column is the rectangle density at the height `σ`. -/
theorem seedMeasure_g3Col (κ x y : ℝ) (P₁ : Measure X) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ)
    (VR₁ : Fin 3 → ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (σ : ℝ) (y₀ : Y) :
    seedMeasure P₁ (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (g3S₁ x y W₁ ζ₁ m) =
      P₁.withDensity fun ω => ENNReal.ofReal (g3M κ x y W₁ VL₁ VR₁ ζ₁ W₂ m (ω, y₀) (g3S₁ x y W₁ ζ₁ m ω) σ) :=
  rfl

/-- **The per-sample frozen law of the small image curve** (G3, small-curve direction) at every protected frozen
time: under the rectangle density at height `σ ∈ (0, S₂ᵐ(y₀)]`, image data equal to the seeded capacity coordinates of
the column up to the cap satisfy `IsSeedSampleLaw`, with the residual as the noise. -/
theorem g3_isSeedSampleLaw {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    {P₁ : Measure X} [IsProbabilityMeasure P₁] {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX}
    {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (y₀ : Y) {σ : ℝ} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ m y₀)
    {W : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞} {VL : Fin 1 → ℝ≥0 → X → ℝ} {VR : Fin 3 → ℝ≥0 → X → ℝ}
    {N : ℝ≥0 → X → ℝ} {Scap : ℕ → X → ℝ≥0} {m' : ℕ}
    (hSm : ∀ ω, Scap m' ω = seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (g3S₁ x y W₁ ζ₁ m) ω)
    (hW : ∀ ω t, t ≤ Scap m' ω →
      W t ω = seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (g3S₁ x y W₁ ζ₁ m) t ω)
    (hVL : ∀ ω i t, t ≤ Scap m' ω → VL i t ω =
      seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (g3S₁ x y W₁ ζ₁ m) (g3ChargeEquiv (.inl i)) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m' ω → VR j t ω =
      seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀) (g3S₁ x y W₁ ζ₁ m) (g3ChargeEquiv (.inr j)) t ω)
    (hN : ∀ ω t, t ≤ Scap m' ω → N t ω = seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ) (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m' ω : ℝ≥0∞) ≤ ζ ω)
    (Tk : ℕ → X → ℝ≥0) (hTk : ∀ k, IsStoppingTime 𝓖₁ fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ g3S₁ x y W₁ ζ₁ m ω →
      (Scap k ω : ℝ) = (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, g3S₁ x y W₁ ζ₁ m ω ≤ Tk k ω → Scap m' ω ≤ Scap k ω) :
    IsSeedSampleLaw (P₁.withDensity fun ω =>
        ENNReal.ofReal (g3M κ x y W₁ VL₁ VR₁ ζ₁ W₂ m (ω, y₀) (g3S₁ x y W₁ ζ₁ m ω) σ))
      W ζ VL VR N Scap m' := by
  rw [← seedMeasure_g3Col]
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, -, hsepO, -, -, -, -, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m y₀ hσ hσS
  have hrate : ∀ ω m'', ∀ t ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ m ω),
      IntervalIntegrable (fun u => 2 / ((g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).V m'' u -
        (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).W u)) volume 0 t := by
    intro ω m'' t ht
    fin_cases m''
    · exact (hrec ω).lo.integrable t ht
    · exact (hrec ω).hi.integrable t ht
    · refine intervalIntegrable_rate_of_ne (hrec ω).own.cont.continuousOn ((hrec ω).mark 2).cont
        (fun u hu => ?_) t ht
      have hu0 : (0 : ℝ) ≤ u := hu.1
      have huS : u.toNNReal ≤ g3S₁ x y W₁ ζ₁ m ω := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]; exact hu.2
      have hW' : (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).W u = W₁ u.toNNReal ω :=
        eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) m ω hu
      have hV' : (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).V 2 u = VR₁ 1 u.toNNReal ω := rfl
      rw [hV', hW']
      exact hsepO ω _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 huS) (hgood₁ m ω).1)
  have hκd : ∀ ω, (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).κ = kh κ := fun ω =>
    congrArg SeedData.κ (hrec ω).source
  have hrd : ∀ ω, (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ m σ y₀ ω).r = g3RR κ := fun ω =>
    congrArg SeedData.r (hrec ω).source
  exact isSeedSampleLaw_of_column hpp hk hcol hrate g3ChargeEquiv
    (fun ω i => imageCharge_g3_left (by linarith) (hκd ω) (hrd ω) i)
    (fun ω j => imageCharge_g3_right (by linarith) (hκd ω) (hrd ω) j) hSm hW hVL hVR hN hζ Tk hTk hcap₁ hcap₂

end InteractingSLE.ZhanGT4.A1G3Law
