/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawAssemble

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: (1.7) at the stop

Packet PROVE-A1-RECTLAW2 (R83). The per-stop inputs `hrect` and `hopt` of `ResStopInput` for (Eight), image curve
the small curve (on `X`), conditioning curve the large curve (on `Y`), on the patched cofinal rectangles
`eightS₁`, `eightS₂` of A1-ASSEMBLE:

* **`eight_patched_rows`**: the rows `t ↦ M(s, t ∧ S₂ᵐ)` of every rectangle's seeded height field are continuous
  martingales of the large curve's filtration (A1-EIGHTFIN's `eight_rows`, with A1-ASSEMBLE's rectangle data
  `eight_rect` and rows `isRowStoch_large_lifeExit`), and the rectangles are bounded;
* **`eightSnd_hopt`**: optional sampling of the rows at `τ ∧ S₂ᵐ` for every stopping time `τ`: the family density
  `D τ m (x, y) = M(S₁ᵐ(x), τ(y) ∧ S₂ᵐ(y))` has the same integrals as the exit density `M(S₁ᵐ(x), S₂ᵐ(y))` over every
  event of the record stopped at `τ ∧ S₂ᵐ`;
* `eightSnd_hrect`: (1.7) on the exit records gives the rectangle identity.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The Eight rectangle density at small own time `s` and large own time `t`. -/
abbrev eightM (κ x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (z : X × Y) (s t : ℝ) : ℝ :=
  seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) z s t

/-- **The rows of the patched Eight rectangles are continuous martingales; the rectangles are bounded.** -/
theorem eight_patched_rows {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₂.IsRightContinuous]
    {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
    {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
    {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) :
    (∀ m, ∃ U : ℝ≥0, (∀ ω, eightS₁ x W₁ ζ₁ m ω ≤ U) ∧ ∀ ω, eightS₂ x W₂ ζ₂ m ω ≤ U) ∧
    (∀ m (ω₁ : X) (s : ℝ), 0 ≤ s → s ≤ eightS₁ x W₁ ζ₁ m ω₁ →
      Martingale (fun (t : ℝ≥0) y => eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) s
        (min (t : ℝ) (eightS₂ x W₂ ζ₂ m y))) 𝓖₂ P₂) ∧
    (∀ m (ω₁ : X) (y : Y) (s : ℝ), 0 ≤ s → s ≤ eightS₁ x W₁ ζ₁ m ω₁ →
      Continuous fun t : ℝ≥0 => eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) s (min (t : ℝ) (eightS₂ x W₂ ζ₂ m y))) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨hU, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  obtain ⟨hrow, hrowc⟩ := eight_rows (by linarith) 𝓖₂ (eightS₁ x W₁ ζ₁) (eightS₂ x W₂ ζ₂) (cofH₁ (-x) ![])
    (cofH₂ (-x) ![]) (cofδ (-x) ![]) (cofq (-x) ![]) (cofd (-x) ![]) (cofTm (-x) ![]) hs₂ hF.pp h₁.path rfl rfl
    hgood₁ hsep₁ hc₂ h0₂ hgood₂ hS₂pos (x₀ := fun _ => -(-x)) (fun m => (hF.pp m).sep_pos) (fun _ => by linarith)
    (fun m => hF.disjoint_ball_neg_src m) (fun m => isRowStoch_large_lifeExit hx h₂ hB₂ hF hlt₂ m)
  exact ⟨hU, hrow, hrowc⟩

/-- **(1.7) on the exit records gives the rectangle identity** (`ResStopInput.hrect`). -/
theorem eightSnd_hrect {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓐 : ℕ → MeasurableSpace X}
    {𝓑 : ℕ → MeasurableSpace Y} (hA : ∀ m, 𝓐 m ≤ mX) (hB : ∀ m, 𝓑 m ≤ mY) {D₀ : ℕ → X × Y → ℝ≥0∞}
    (hd : ∀ m, RectDens (𝓐 m) (𝓑 m) P₁ P₂ μ (D₀ m)) :
    ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂) :=
  fun m A B hA' hB' => rect_of_rectDens (hA m) (hB m) (hd m) A B hA' hB'

/-- **Optional sampling of the patched Eight rows at `τ ∧ S₂ᵐ`** (`ResStopInput.hopt`, small-curve direction): for
every stopping time `τ` of the large curve's (right-continuous) filtration, almost every small sample `x` and every
event `B` of the σ-algebra stopped at `τ ∧ S₂ᵐ`, the exit density and the family density at the stop have the same
integral over `B`. -/
theorem eightSnd_hopt {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₂.IsRightContinuous]
    {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
    {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
    {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0))
    {τ : Y → ℝ≥0} (hτ : IsStoppingTime 𝓖₂ fun y => (τ y : WithTop ℝ≥0)) (m : ℕ) :
    ∀ᵐ ω₁ ∂P₁, ∀ B, MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] B →
      ∫⁻ y in B, ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) (eightS₁ x W₁ ζ₁ m ω₁)
          (eightS₂ x W₂ ζ₂ m y)) ∂P₂ =
        ∫⁻ y in B, ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) (eightS₁ x W₁ ζ₁ m ω₁)
          (min (τ y) (eightS₂ x W₂ ζ₂ m y) : ℝ≥0)) ∂P₂ := by
  obtain ⟨hU, hrow, hrowc⟩ := eight_patched_rows hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ (𝓖₂ := 𝓖₂)
  obtain ⟨U, -, hU₂⟩ := hU m
  set M : X → ℝ≥0 → Y → ℝ := fun ω₁ t y => eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) (eightS₁ x W₁ ζ₁ m ω₁)
    (min (t : ℝ) (eightS₂ x W₂ ζ₂ m y)) with hM
  have hval : ∀ ω₁ y (r : ℝ≥0), r ≤ eightS₂ x W₂ ζ₂ m y →
      M ω₁ r y = eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (ω₁, y) (eightS₁ x W₁ ζ₁ m ω₁) r := fun ω₁ y r hr => by
    simp only [hM, min_eq_left (NNReal.coe_le_coe.2 hr)]
  refine opt_of_martingale (P₁ := P₁) (M := M)
    (D₀ := fun z => ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m z (eightS₁ x W₁ ζ₁ m z.1) (eightS₂ x W₂ ζ₂ m z.2)))
    (D := fun z => ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m z (eightS₁ x W₁ ζ₁ m z.1)
      (min (τ z.2) (eightS₂ x W₂ ζ₂ m z.2) : ℝ≥0)))
    (Eventually.of_forall fun ω₁ => hrow m ω₁ _ (NNReal.coe_nonneg _) le_rfl)
    (fun ω₁ y t => (hrowc m ω₁ y _ (NNReal.coe_nonneg _) le_rfl).continuousWithinAt)
    (fun ω₁ t y => (seedHeightField_pos _ _ _ _).le) (hτ.min (hs₂ m)) (hs₂ m) (fun y => min_le_right _ _)
    (T := U) (fun y => WithTop.coe_le_coe.2 (hU₂ y)) (fun ω₁ y => ?_) (fun ω₁ y => ?_)
  · show _ = ENNReal.ofReal (M ω₁ (eightS₂ x W₂ ζ₂ m y) y)
    rw [hval ω₁ y _ le_rfl]
  · simp only [stoppedValue]
    rw [← WithTop.coe_min]
    show _ = ENNReal.ofReal (M ω₁ (min (τ y) (eightS₂ x W₂ ζ₂ m y)) y)
    rw [hval ω₁ y _ (min_le_right _ _)]

end InteractingSLE.ZhanGT4.A1RLaw
