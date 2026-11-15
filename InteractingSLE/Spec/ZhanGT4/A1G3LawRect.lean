/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRMain
import InteractingSLE.Spec.ZhanGT4.A1FamilyRect
import InteractingSLE.Spec.ZhanGT4.A1LawStop

/-!
# Zhan's A.1 under R83, (G3): the rectangle field of the patched rectangles; (1.7) and optional sampling at a stop

Packet PROVE-A1-G3LAW (R83). The per-stop inputs `hrect` and `hopt` of A1-RECTLAW2's `ResStopInput` /
`ResStopInputFst` for (G3), in both directions, on the patched cofinal rectangles `g3S₁`, `g3S₂` of A1-ASSEMBLE:

* **`g3_isRectField`**: for regular G3 marginals in right-continuous filtrations with continuous Brownian paths at
  every sample and a `GoodSmallG3` small curve at every sample, the seeded height field of every rectangle is an
  `IsRectField`: bounded above and below by positive constants, its columns (small own time running, stopped at
  `S₁ᵐ`, large height `S₂ᵐ`) are continuous martingales of the small curve's filtration, and its rows (large time
  running, stopped at `S₂ᵐ`) are continuous martingales of the large curve's filtration (A1-G3CALC's column calculus,
  A1-G3RECTROW's rows);
* **`g3Snd_hopt`** (small image curve, conditioning on the large curve): optional sampling of the rows at
  `τ ∧ S₂ᵐ`; **`g3Fst_hopt`** (large image curve, conditioning on the small curve): optional sampling of the columns
  at `τ ∧ S₁ᵐ`;
* `g3_hrect`: (1.7) on the exit records gives the rectangle identity.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family

/-- The (G3) rectangle density at small own time `s` and large own time `t`. -/
abbrev g3M {X Y : Type*} (κ x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (m : ℕ) (z : X × Y) (s t : ℝ) : ℝ :=
  seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) z s t

section Field

variable {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The seeded height field of every patched (G3) rectangle is a rectangle field**: two-sided bounds, column
martingales in the small curve's filtration, row martingales in the large curve's filtration, all with continuous
paths. -/
theorem g3_isRectField {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X} [IsProbabilityMeasure P₁] {P₂ : Measure Y}
    [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} [h𝓖₁ : 𝓖₁.IsRightContinuous]
    [h𝓖₂ : 𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) :
    IsRectField P₁ P₂ 𝓖₁ 𝓖₂ (g3S₁ x y W₁ ζ₁ m) (g3S₂ x y W₂ ζ₂ m)
      (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m)) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨hU, hgood₁, hsep₁, hsepO, hneP, hc₂, h0₂, hgood₂, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (cofGN (-y) (x - y) ![x - y]) (-y) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hrow, hrowc⟩ := A1G3RR.g3RectRow κ hκ4 hκ8 y x hyx hx X Y mX mY inferInstance inferInstance P₁
    inferInstance P₂ inferInstance 𝓖₁ 𝓖₂ h𝓖₁ h𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂ h₁ hB₁ hg₁
  set S₁ := g3S₁ x y W₁ ζ₁ with hS₁
  set S₂ := g3S₂ x y W₂ ζ₂ with hS₂
  have hpp := isProtectedPairG_cofG hne
  have hP := h₁.path
  have hK₂ : ∀ m y' (t : ℝ), 0 ≤ t → t ≤ S₂ m y' →
      fwdHull (frzPath W₂ (-y) t y') t ⊆ cofGH₂ (-y) (x - y) ![x - y] m :=
    fun m y' t ht htS => fwdHull_frzPath_subset (hc₂ m y') ht htS (hgood₂ m y').2
  have hc₂t : ∀ m y' (t : ℝ), t ≤ S₂ m y' → ContinuousOn (Strip.extPath (W₂ · y')) (Icc 0 t) := fun m y' t htS =>
    (hc₂ m y').mono (Icc_subset_Icc_right htS)
  have hex : ∀ m x' y' (t : ℝ), 0 ≤ t → t ≤ S₂ m y' → ∃ a W', OwnData (eightDrv W₁ S₁ m x')
      (fwdHull (frzPath W₂ (-y) t y') t) (frzChart (frzPath W₂ (-y) t y') t) (S₁ m x') a W' :=
    fun m x' y' t ht htS =>
    exists_ownData_of_encl (continuous_eightDrv (hP x').2.2.2.1 (hgood₁ m x').1) (eightDrv_zero (hP x').1)
      (hgood₁ m x').2.1 (continuous_frzPath (hc₂t m y' t htS) ht) ht (hpp m).pair.sep_pos (hpp m).pair.sep
      (hgood₁ m x').2.2.2 (hK₂ m y' t ht htS)
  have hrec : ∀ x' y' (t : ℝ), 0 < t → t ≤ S₂ m y' → IsSourceRecordG (cofGH₁ (-y) (x - y) ![x - y] m)
      (cofGH₂ (-y) (x - y) ![x - y] m) (-y) (cofGq (-y) (x - y) ![x - y] m) (cofGTm (-y) (x - y) ![x - y] m)
      (kh κ) (g3RR κ) (frzPath W₂ (-y) t y') t (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t (x', y'))
      (Strip.extPath (VL₁ 0 · x')) (Strip.extPath (VR₁ 0 · x')) (S₁ m x') := fun x' y' t ht htS => by
    have hlt : ∀ s : ℝ≥0, s ≤ S₁ m x' → (s : ℝ≥0∞) < ζ₁ x' := fun s hsS =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) (hgood₁ m x').1
    have h2d : 0 < 2 * cofGd (-y) (x - y) ![x - y] m := by have := (hpp m).pair.rad_pos; positivity
    exact isSourceRecordG_g3Rec (hP x') rfl rfl (by simp; linarith) (by simpa using qlo_le_cofGq hne m)
      (hgood₁ m x').1 (hgood₁ m x').2.1
      (fun s hs hsS => (hsep₁ x' s hs (hlt s hsS)).1) (fun s hs hsS => (hsep₁ x' s hs (hlt s hsS)).2)
      (fun s hsS => hsepO x' s (hlt s hsS)) h2d ((hpp m).pair.prot.mono_right subset_union_left)
      (hc₂t m y' t htS) (h0₂ y') ht (htS.trans (hgood₂ m y').1) (hgood₁ m x').2.2.1 (hpp m).pair.sep_pos
      (hpp m).pair.sep (hgood₁ m x').2.2.2 (hK₂ m y' t ht.le htS)
  refine isRectField_of_sourceG (hpp m) hk (hs₁ m) (hs₂ m) (hU m) (fun y' hpos => ?_)
    (fun x' y' t ht htS => ⟨_, _, _, hrec x' y' t ht htS⟩) (fun x' y' s hs hsS => ?_) (hrow m) (hrowc m)
  · have hlt : ∀ ω (s : ℝ≥0), s ≤ S₁ m ω → (s : ℝ≥0∞) < ζ₁ ω := fun ω s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgood₁ m ω).1
    have hst := isColumnStoch_g3Rec_of_reg (t₂ := (S₂ m y' : ℝ)) (y₀ := y') (W₂ := W₂) hk h₁ hB₁ (hs₁ m)
      (fun ω => (hgood₁ m ω).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω j s hs hsS => ?_)
      (fun ω s hsS => hneP ω s (hlt ω s hsS))
    · exact isSourceColumnG_of_stoch (fun x' => hrec x' y' _ hpos le_rfl) (hs₁ m) hst
    · fin_cases j
      · exact (hsep₁ ω s hs (hlt ω s hsS)).2
      · exact hsepO ω s (hlt ω s hsS)
      · exact hneP ω s (hlt ω s hsS)
  · exact normEll_g3Rec_zero (hc₂t m y' 0 (S₂ m y').coe_nonneg) (h0₂ y')
      (hex m x' y' 0 le_rfl (S₂ m y').coe_nonneg) hs hsS

end Field

/-! ### Optional sampling and (1.7) from a rectangle field -/

section Opt

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0} {N : X × Y → ℝ → ℝ → ℝ}

/-- **Rows at a stop** (conditioning curve on `Y`): for every stopping time `τ` of the row filtration, almost every
`x` and every event `B` of the σ-algebra stopped at `τ ∧ S₂`, the exit density `N(S₁, S₂)` and the stopped density
`N(S₁, τ ∧ S₂)` have the same integral over `B`. -/
theorem IsRectField.opt_snd [IsFiniteMeasure P₂] (R : IsRectField P₁ P₂ 𝓖₁ 𝓖₂ S₁ S₂ N) {τ : Y → ℝ≥0}
    (hτ : IsStoppingTime 𝓖₂ fun y => (τ y : WithTop ℝ≥0)) :
    ∀ᵐ x ∂P₁, ∀ B, MeasurableSet[(hτ.min R.stop₂).measurableSpace] B →
      ∫⁻ y in B, ENNReal.ofReal (N (x, y) (S₁ x) (S₂ y)) ∂P₂ =
        ∫⁻ y in B, ENNReal.ofReal (N (x, y) (S₁ x) (min (τ y) (S₂ y) : ℝ≥0)) ∂P₂ := by
  obtain ⟨U, -, hU₂⟩ := R.bdd
  obtain ⟨c, C, hc, hcC⟩ := R.bound
  set M : X → ℝ≥0 → Y → ℝ := fun x t y => N (x, y) (S₁ x) (min (t : ℝ) (S₂ y)) with hM
  have hval : ∀ x y (r : ℝ≥0), r ≤ S₂ y → M x r y = N (x, y) (S₁ x) r := fun x y r hr => by
    simp only [hM, min_eq_left (NNReal.coe_le_coe.2 hr)]
  refine opt_of_martingale (P₁ := P₁) (M := M)
    (D₀ := fun z => ENNReal.ofReal (N z (S₁ z.1) (S₂ z.2)))
    (D := fun z => ENNReal.ofReal (N z (S₁ z.1) (min (τ z.2) (S₂ z.2) : ℝ≥0)))
    (Eventually.of_forall fun x => R.row x _ (NNReal.coe_nonneg _) le_rfl)
    (fun x y t => (R.row_cont x y _ (NNReal.coe_nonneg _) le_rfl).continuousWithinAt)
    (fun x t y => hc.le.trans ((hcC x y _ _ (NNReal.coe_nonneg _) le_rfl
      (le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) (min_le_right _ _)).1))
    (hτ.min R.stop₂) R.stop₂ (fun y => min_le_right _ _) (T := U) (fun y => WithTop.coe_le_coe.2 (hU₂ y))
    (fun x y => ?_) (fun x y => ?_)
  · simp only [stoppedValue]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, hval x y _ le_rfl]
  · simp only [stoppedValue]
    rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
      hval x y _ (min_le_right _ _)]

/-- **Columns at a stop** (conditioning curve on `X`): for every stopping time `τ` of the column filtration, every
`y` and every event `A` of the σ-algebra stopped at `τ ∧ S₁`, the exit density `N(S₁, S₂)` and the stopped density
`N(τ ∧ S₁, S₂)` have the same integral over `A`. -/
theorem IsRectField.opt_fst [IsFiniteMeasure P₁] (R : IsRectField P₁ P₂ 𝓖₁ 𝓖₂ S₁ S₂ N) {τ : X → ℝ≥0}
    (hτ : IsStoppingTime 𝓖₁ fun x => (τ x : WithTop ℝ≥0)) :
    ∀ᵐ y ∂P₂, ∀ A, MeasurableSet[(hτ.min R.stop₁).measurableSpace] A →
      ∫⁻ x in A, ENNReal.ofReal (N (x, y) (S₁ x) (S₂ y)) ∂P₁ =
        ∫⁻ x in A, ENNReal.ofReal (N (x, y) (min (τ x) (S₁ x) : ℝ≥0) (S₂ y)) ∂P₁ := by
  obtain ⟨U, hU₁, -⟩ := R.bdd
  obtain ⟨c, C, hc, hcC⟩ := R.bound
  set M : Y → ℝ≥0 → X → ℝ := fun y s x => N (x, y) (min (s : ℝ) (S₁ x)) (S₂ y) with hM
  have hval : ∀ x y (r : ℝ≥0), r ≤ S₁ x → M y r x = N (x, y) r (S₂ y) := fun x y r hr => by
    simp only [hM, min_eq_left (NNReal.coe_le_coe.2 hr)]
  refine opt_of_martingale_fst (P₂ := P₂) (M := M)
    (D₀ := fun z => ENNReal.ofReal (N z (S₁ z.1) (S₂ z.2)))
    (D := fun z => ENNReal.ofReal (N z (min (τ z.1) (S₁ z.1) : ℝ≥0) (S₂ z.2)))
    (Eventually.of_forall fun y => R.col y) (fun y x t => (R.col_cont x y).continuousWithinAt)
    (fun y s x => hc.le.trans ((hcC x y _ _ (le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
      (min_le_right _ _) (NNReal.coe_nonneg _) le_rfl).1))
    (hτ.min R.stop₁) R.stop₁ (fun x => min_le_right _ _) (T := U) (fun x => WithTop.coe_le_coe.2 (hU₁ x))
    (fun x y => ?_) (fun x y => ?_)
  · simp only [stoppedValue]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, hval x y _ le_rfl]
  · simp only [stoppedValue]
    rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe,
      hval x y _ (min_le_right _ _)]

/-- **(1.7) on the exit records gives the rectangle identity** (`ResStopInput.hrect`, both directions). -/
theorem hrect_of_rectDens {μ : Measure (X × Y)} {𝓐 : ℕ → MeasurableSpace X} {𝓑 : ℕ → MeasurableSpace Y}
    (hA : ∀ m, 𝓐 m ≤ mX) (hB : ∀ m, 𝓑 m ≤ mY) {D₀ : ℕ → X × Y → ℝ≥0∞}
    (hd : ∀ m, RectDens (𝓐 m) (𝓑 m) P₁ P₂ μ (D₀ m)) :
    ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂) :=
  fun m A B hA' hB' => rect_of_rectDens (hA m) (hB m) (hd m) A B hA' hB'

end Opt

end InteractingSLE.ZhanGT4.A1G3Law
