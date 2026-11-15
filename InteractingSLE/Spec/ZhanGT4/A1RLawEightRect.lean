/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawEightDens
import InteractingSLE.Spec.ZhanGT4.A1RLawEightFam
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Patched

/-!
# Zhan's A.1 under R83, (Eight): the patched rectangles are protected rectangle fields

Packet PROVE-A1-RECTLAW2 (R83). For patched regular Eight marginals (continuous Brownian paths, `GoodSmallEight` at
every sample, right-continuous filtrations) and A1-ASSEMBLE's cofinal rectangles `eightS₁`, `eightS₂`:

* **`eight_patched_isRectField`**: every rectangle's seeded height field is an `A1Patch.IsRectField` — bounded above and
  away from `0`, with continuous column and row martingales (A1-ASSEMBLE's source columns and A1-EIGHTFIN's rows,
  through A1-EIGHTSEED's `isRectField_of_sourceR`);
* **`measurable_eightFstD`**: the large direction's densities `eightFstD` are jointly measurable in the frozen time and
  the sample (A22's measurability on the rectangles and the column continuity, Carathéodory) — input `hD` of
  `hasFamilyLawFstC_eight_of_inputs`;
* **`eightFst_hopt`**: optional sampling of the columns at `τ ∧ S₁ᵏ` (`ResStopInputFst.hopt`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The patched Eight rectangles are protected rectangle fields.** -/
theorem eight_patched_isRectField {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous]
    [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (m : ℕ) :
    IsRectField P₁ P₂ 𝓖₁ 𝓖₂ (eightS₁ x W₁ ζ₁ m) (eightS₂ x W₂ ζ₂ m)
      (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m)) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨hU, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  obtain ⟨-, hrow, hrowc⟩ := eight_patched_rows hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ (𝓖₂ := 𝓖₂)
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  -- the pathwise ingredients (A1-EIGHTSEED's `seedFieldInputM_of_eight`)
  set S₁ := eightS₁ x W₁ ζ₁ with hS₁def
  set S₂ := eightS₂ x W₂ ζ₂ with hS₂def
  have hK₂ : ∀ y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → fwdHull (frzPath W₂ (-x) t y) t ⊆ cofH₂ (-x) ![] m :=
    fun y t ht htS => fwdHull_frzPath_subset (hc₂ m y) ht htS (hgood₂ m y).2
  have hc₂t : ∀ y (t : ℝ), t ≤ S₂ m y → ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t) := fun y t htS =>
    (hc₂ m y).mono (Icc_subset_Icc_right htS)
  have hex : ∀ x' y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → ∃ a W', OwnData (eightDrv W₁ S₁ m x')
      (fwdHull (frzPath W₂ (-x) t y) t) (frzChart (frzPath W₂ (-x) t y) t) (S₁ m x') a W' :=
    fun x' y t ht htS => exists_ownData_of_encl (continuous_eightDrv (h₁.path x').2.2.2.1 (hgood₁ m x').1)
      (eightDrv_zero (h₁.path x').1) (hgood₁ m x').2.1 (continuous_frzPath (hc₂t y t htS) ht) ht (hF.pp m).sep_pos
      (hF.pp m).sep (hgood₁ m x').2.2.2 (hK₂ y t ht htS)
  have hrec : ∀ x' y (t : ℝ), 0 < t → t ≤ S₂ m y → IsSourceRecord (cofH₁ (-x) ![] m) (cofH₂ (-x) ![] m) (-x)
      (cofTm (-x) ![] m) (kh κ) (eightRR κ) (frzPath W₂ (-x) t y) t
      (eightRec κ (-x) W₁ VL₁ VR₁ W₂ S₁ m t (x', y)) (Strip.extPath (VL₁ 0 · x')) (Strip.extPath (VR₁ 0 · x'))
      (S₁ m x') := fun x' y t ht htS => by
    have hne : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x' → VL₁ 0 s x' ≠ W₁ s x' ∧ VR₁ 0 s x' ≠ W₁ s x' := fun s hs hsS =>
      hsep₁ x' s hs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) (hgood₁ m x').1)
    exact isSourceRecord_eightRec (h₁.path x') rfl rfl (hgood₁ m x').1 (hgood₁ m x').2.1
      (fun s hs hsS => (hne s hs hsS).1) (fun s hs hsS => (hne s hs hsS).2) (hc₂t y t htS) (h0₂ y) ht
      (htS.trans (hgood₂ m y).1) (hgood₁ m x').2.2.1 (hF.pp m).sep_pos (hF.pp m).sep (hgood₁ m x').2.2.2
      (hK₂ y t ht.le htS)
  have hlt : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
  refine isRectField_of_sourceR (hF.pp m) hk (hs₁ m) (hs₂ m) (hU m) (fun y hS => ?_) (fun x' y t ht htS =>
    ⟨_, _, _, hrec x' y t ht htS⟩) (fun x' y s hs hsS => normEll_eightRec_zero (hc₂t y 0 (S₂ m y).coe_nonneg)
      (h0₂ y) (hex x' y 0 le_rfl (S₂ m y).coe_nonneg) hs hsS) (hrow m) (hrowc m)
  exact isSourceColumn_of_stoch (fun x' => hrec x' y _ hS le_rfl) (hs₁ m)
    (isColumnStoch_eightRec_of_reg hk h₁ hB₁ (hs₁ m) (fun ω => (hgood₁ m ω).1)
      (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).2)
      (fun ω s hsS => smallEight_sepP_of_good hx (h₁.path ω) (hg₁ ω) s (hlt ω s hsS)))

/-- **The large direction's densities are jointly measurable** in the frozen time and the sample (input `hD` of
`hasFamilyLawFstC_eight_of_inputs`): the column `s ↦ M(s ∧ S₁ᵏ, S₂ᵏ)` is continuous (`IsRectField.col_cont`) and
measurable in the sample at each `s` (A22's `isFieldMeas_eight_of_patched`), so Carathéodory applies. -/
theorem measurable_eightFstD {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2 := by
  have hR := eight_patched_isRectField hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)
  have hM := isFieldMeas_eight_of_patched hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k
  have hS₁ := measurable_of_isStoppingTime hR.stop₁
  have hS₂ := measurable_of_isStoppingTime hR.stop₂
  set N := seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) k) with hN
  have hu : Measurable (Function.uncurry fun (s : ℝ≥0) (z : X × Y) =>
      N z (min (s : ℝ) (eightS₁ x W₁ ζ₁ k z.1)) (eightS₂ x W₂ ζ₂ k z.2)) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun z => hR.col_cont z.1 z.2) fun s => ?_
    exact hM (fun z => min (s : ℝ) (eightS₁ x W₁ ζ₁ k z.1)) (fun z => (eightS₂ x W₂ ζ₂ k z.2 : ℝ))
      (measurable_const.min (hS₁.comp measurable_fst).coe_nnreal_real)
      (hS₂.comp measurable_snd).coe_nnreal_real (fun z => le_min s.coe_nonneg (NNReal.coe_nonneg _))
      (fun z => NNReal.coe_nonneg _) (fun z => ⟨(), min_le_right _ _, le_rfl⟩)
  have e : (fun p : ℝ≥0 × (X × Y) => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2) = fun p =>
      ENNReal.ofReal (Function.uncurry (fun (s : ℝ≥0) (z : X × Y) =>
        N z (min (s : ℝ) (eightS₁ x W₁ ζ₁ k z.1)) (eightS₂ x W₂ ζ₂ k z.2)) p) := by
    funext p
    simp only [eightFstD, Function.uncurry, hN, NNReal.coe_min]
  rw [e]
  exact hu.ennreal_ofReal

/-- **Optional sampling of the patched Eight columns at `τ ∧ S₁ᵏ`** (`ResStopInputFst.hopt`, large direction): for every
stopping time `τ` of the small curve's (right-continuous) filtration, almost every large sample `y` and every event `A`
of the σ-algebra stopped at `τ ∧ S₁ᵏ`, the exit density and the family density at the stop have the same integral
over `A`. -/
theorem eightFst_hopt {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
    {τ : X → ℝ≥0} (hτ : IsStoppingTime 𝓖₁ fun x => (τ x : WithTop ℝ≥0)) (m : ℕ) :
    ∀ᵐ y ∂P₂, ∀ A, MeasurableSet[(hτ.min (hs₁ m)).measurableSpace] A →
      ∫⁻ x' in A, ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (x', y) (eightS₁ x W₁ ζ₁ m x')
          (eightS₂ x W₂ ζ₂ m y)) ∂P₁ =
        ∫⁻ x' in A, eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (τ x') m (x', y) ∂P₁ := by
  have hR := eight_patched_isRectField hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)
  obtain ⟨U, hU₁, -⟩ := hR.bdd
  set M : Y → ℝ≥0 → X → ℝ := fun y s x' => eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (x', y)
    (min (s : ℝ) (eightS₁ x W₁ ζ₁ m x')) (eightS₂ x W₂ ζ₂ m y) with hMdef
  have hval : ∀ y x' (r : ℝ≥0), r ≤ eightS₁ x W₁ ζ₁ m x' →
      M y r x' = eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (x', y) r (eightS₂ x W₂ ζ₂ m y) := fun y x' r hr => by
    simp only [hMdef, min_eq_left (NNReal.coe_le_coe.2 hr)]
  refine opt_of_martingale_fst (P₂ := P₂) (M := M)
    (D₀ := fun z => ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m z (eightS₁ x W₁ ζ₁ m z.1) (eightS₂ x W₂ ζ₂ m z.2)))
    (D := fun z => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (τ z.1) m z)
    (Eventually.of_forall fun y => hR.col y) (fun y x' t => (hR.col_cont x' y).continuousWithinAt)
    (fun y t x' => (seedHeightField_pos _ _ _ _).le) (hτ.min (hs₁ m)) (hs₁ m) (fun x' => min_le_right _ _)
    (T := U) (fun x' => WithTop.coe_le_coe.2 (hU₁ x')) (fun x' y => ?_) (fun x' y => ?_)
  · show _ = ENNReal.ofReal (M y (eightS₁ x W₁ ζ₁ m x') x')
    rw [hval y x' _ le_rfl]
  · simp only [stoppedValue]
    rw [← WithTop.coe_min]
    show _ = ENNReal.ofReal (M y (min (τ x') (eightS₁ x W₁ ζ₁ m x')) x')
    rw [hval y x' _ (min_le_right _ _)]
    rfl

/-- **The per-stop inputs of the large direction from the remaining record facts** (`ResStopInputFst` for (Eight)):
the records are the stopped σ-algebras of the patched exits (`𝓐'` stopped at `τ ∧ S₁ᵐ`), the exit density is the
patched seeded height field at the rectangle corner, (1.7) on the records is the coupling's `RectDens` hypothesis and
the optional sampling is `eightFst_hopt`. The caps `S`, forces `VL`, `VR` and image data are arbitrary; their record
facts (`hSm`, `hstop`, `hgW`, `hgVL`, `hgVR`, `hgS`, `hgζ`) and the clock exhaustion `hcov` are the remaining
inputs. -/
def eightFstResStop {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0)) {μ : Measure (X × Y)}
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) ω
        (eightS₁ x W₁ ζ₁ m ω.1) (eightS₂ x W₂ ζ₂ m ω.2)))
    {τ : X → ℝ≥0} (hτ : IsStoppingTime 𝓖₁ fun x => (τ x : WithTop ℝ≥0)) {nL nR : ℕ}
    {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
    {VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ} {VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ} {S : ℝ≥0 → ℕ → X × Y → ℝ≥0}
    {𝓔 : Set (Set X)}
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] fun z => S (τ z.1) m z)
    (hstop : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
        (Prod.fst ⁻¹' B ∩ {z | s < S (τ z.1) m z}))
    (hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → rDrvFst live xj Wj ζj xk Wk τ r z = f z)
    (hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → VL (τ z.1) i r z = f z)
    (hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → VR (τ z.1) j r z = f z)
    (hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] ({z | S (τ z.1) k z ≤ r} ∩ {z | r < S (τ z.1) m z}))
    (hgζ : ∀ m z, (S (τ z.1) m z : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk τ z)
    (hcov : ∀ᵐ z ∂μ, live (τ z.1) z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.2))
        (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤ S (τ z.1) m z) :
    ResStopInputFst P₁ P₂ μ live xj Wj ζj xk Wk VL VR S (eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂) τ 𝓔 where
  𝓐 m := (hs₁ m).measurableSpace
  𝓐' m := (hτ.min (hs₁ m)).measurableSpace
  𝓑 m := (hs₂ m).measurableSpace
  D₀ m ω := ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) ω
    (eightS₁ x W₁ ζ₁ m ω.1) (eightS₂ x W₂ ζ₂ m ω.2))
  hA' m := IsStoppingTime.measurableSpace_mono _ _ fun _ => min_le_right _ _
  hA m := (hs₁ m).measurableSpace_le
  hB m := (hs₂ m).measurableSpace_le
  hD₀ m := by
    have hM := isFieldMeas_eight_of_patched hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m
    exact (hM (fun ω => (eightS₁ x W₁ ζ₁ m ω.1 : ℝ)) (fun ω => (eightS₂ x W₂ ζ₂ m ω.2 : ℝ))
      ((measurable_of_isStoppingTime (hs₁ m)).comp measurable_fst).coe_nnreal_real
      ((measurable_of_isStoppingTime (hs₂ m)).comp measurable_snd).coe_nnreal_real (fun ω => NNReal.coe_nonneg _)
      (fun ω => NNReal.coe_nonneg _) fun ω => ⟨(), le_rfl, le_rfl⟩).ennreal_ofReal
  hrect m A B hA hB := rect_of_rectDens (hs₁ m).measurableSpace_le (hs₂ m).measurableSpace_le (hd m) A B hA hB
  hopt m := eightFst_hopt hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hτ m
  hSm := hSm
  hstop := hstop
  hgW := hgW
  hgVL := hgVL
  hgVR := hgVR
  hgS := hgS
  hgζ := hgζ
  hcov := hcov

omit mX mY in
/-- **`hgζ` of the large direction**: the masked caps at the stop precede the image lifetime (FORCES's
`capFst_le_rLifeFst`). -/
theorem eightFst_hgζ (xs : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ)
    (ζ₂' : Y → ℝ≥0∞) (G₁ : Set X) (G₂ : Set Y) (τ : X → ℝ≥0) (m : ℕ) (z : X × Y) :
    (maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z : ℝ≥0∞) ≤
      rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) xs W₁ τ z := by
  have hmask : maskCap G₁ G₂ (eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z ≤
      eightFstCap xs W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' (τ z.1) m z := by
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hG.1 hG.2]
    · rw [maskCap_of_not_mem hG]; exact bot_le
  have hcap := A1Forces.capFst_le_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (xj := 0) (Wj := W₂)
    (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (xk := xs) (Wk := W₁) (τ := fun _ => τ z.1)
    (eightFstOwn xs W₁' ζ₁' W₂' ζ₂' (τ z.1) m) z
  have hlife := (cImg_congr_of_eq (z := z) (τ := fun z => τ z.1) (τ₀ := fun _ => τ z.1)
    (live := fun t (z : X × Y) => (t : ℝ≥0∞) < ζ₁ z.1) (xj := 0) (Wj := fun t (z : X × Y) => W₂ t z.2)
    (ζj := fun z : X × Y => lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) (xk := xs) (Wk := fun t (z : X × Y) => W₁ t z.1)
    rfl).1
  refine (ENNReal.coe_le_coe.2 hmask).trans (hcap.trans ?_)
  exact hlife.symm.le

end InteractingSLE.ZhanGT4.A1RLaw
