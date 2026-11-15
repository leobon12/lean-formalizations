/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopMain

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: the masked caps on the stopped records

Packet PROVE-A1-G3LAW2. The large direction's mirror of `A1G3L2SndStopRec`: image curve the large curve on `Y`
(start `0`, lifetime `lifeEnd`), conditioning curve the small curve on `X` (start `y`, live while alive), records
`𝓐' m` stopped at `τ ∧ S₁ᵐ` (`g3Fτ`) on `X` and `𝓑 m` stopped at `S₂ᵐ` on `Y`. On `{τ ≤ S₁ᵐ}` the small curve is
alive, so the record set is `(G₁ ∩ {τ ≤ S₁ᵐ}) × G₂` (`g3FstRecSet`).

The per-sample facts of the patched large curve — `S₂ᵏ < lifeEnd` and `S₂ᵏ` a good horizon at `0 < σ ≤ S₁ᵏ` — are
PROVE-A1-G3LARGE's (`g3Fst_lt_lifeEnd`, `g3Fst_isGoodTime`); they enter here as the named hypotheses `hlife`, `hgood`
of the conditional helpers (`σ = 0` is good by the empty frozen hull, `isGoodTime_zero_frozen`).

* **`g3FstStop_pos`**, **`g3FstStop_cap_eq`**: a positive masked cap forces a good pair and `σ ≤ S₁ᵏ`; at the stop the
  masked cap is the indicator of the record set of the record cap `capFst True … g3Fτ S₂ᵐ`;
* **`measurableSet_g3FstRecSet`**, **`g3Fst_good_le`**, **`g3Fst_good_stop`**, **`measurable_g3FstRecCap`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

/-- **At the frozen time `0` every positive horizon before the lifetime is good** (any frozen start `xk`). -/
theorem isGoodTime_zero_frozen {xj xk : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞} {τ' : ℝ} (hτ' : 0 < τ')
    (hk : ContinuousOn wk (Icc 0 τ')) {S : ℝ} (hS : 0 < S) (hSζ : ENNReal.ofReal S < ζj) :
    A1Ref.IsGoodTime xj wj ζj xk wk 0 S := by
  refine ⟨hS, lt_of_lt_of_le hSζ (le_min le_rfl (le_iInf₂ fun s hs => ?_))⟩
  rw [physHull_zero_eq xk hτ' hk, closure_empty, inter_empty] at hs
  exact absurd hs not_nonempty_empty

section Gen

variable {X Y : Type*} {live live' : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → Y → ℝ} {ζj ζj' : Y → ℝ≥0∞}
  {Wk Wk' : ℝ≥0 → X → ℝ}

/-- The large-direction cap reads only the two sample paths. -/
theorem capFst_congr_data {τ : X → ℝ≥0} {T : X × Y → ℝ} {z : X × Y} (hl : live (τ z.1) z.1 ↔ live' (τ z.1) z.1)
    (hWj : (Wj · z.2) = (Wj' · z.2)) (hζ : ζj z.2 = ζj' z.2) (hWk : (Wk · z.1) = (Wk' · z.1)) :
    capFst live xj Wj ζj xk Wk τ T z = capFst live' xj Wj' ζj' xk Wk' τ T z := by
  classical
  simp only [capFst, Set.indicator, Set.mem_ofPred_eq, hWj, hζ, hWk]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd (hl.1 h1) h2 | exact absurd (hl.2 h2) h1

/-- On a live sample the cap with the trivial live event is the cap. -/
theorem capFst_true_eq {τ₁ τ₂ : X → ℝ≥0} {T : X × Y → ℝ} {z : X × Y} (hl : live (τ₂ z.1) z.1)
    (hτ : τ₁ z.1 = τ₂ z.1) :
    capFst (fun _ _ => True) xj Wj ζj xk Wk τ₁ T z = capFst live xj Wj ζj xk Wk τ₂ T z := by
  unfold capFst
  rw [indicator_of_mem (show z ∈ {w : X × Y | (fun (_ : ℝ≥0) (_ : X) => True) (τ₁ w.1) w.1} from trivial),
    indicator_of_mem (show z ∈ {w : X × Y | live (τ₂ w.1) w.1} from hl), hτ]

/-- The minimum of two caps with finite clocks is the cap at the minimum own time. -/
theorem min_capFst_eq {τ : X → ℝ≥0} {T T' : X × Y → ℝ} {z : X × Y}
    (hfin : live (τ z.1) z.1 → clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1)
      (T z) ≠ ∞)
    (hfin' : live (τ z.1) z.1 → clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1))
      (τ z.1) (T' z) ≠ ∞) :
    min (capFst live xj Wj ζj xk Wk τ T z) (capFst live xj Wj ζj xk Wk τ T' z) =
      capFst live xj Wj ζj xk Wk τ (fun z => min (T z) (T' z)) z := by
  rcases le_total (T z) (T' z) with h | h
  · rw [min_eq_left (capFst_mono h hfin'), capFst_congr_pt (T' := fun z => min (T z) (T' z)) (min_eq_left h).symm]
  · rw [min_eq_right (capFst_mono h hfin), capFst_congr_pt (T' := fun z => min (T z) (T' z)) (min_eq_right h).symm]

end Gen

/-- The frozen time of the large direction stopped at the small exit: `τ ∧ S₁ᵐ`. -/
def g3Fτ {X : Type*} (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (τ : X → ℝ≥0) (m : ℕ) (x' : X) : ℝ≥0 :=
  min (τ x') (g3S₁ x y W₁ ζ₁ m x')

/-- The record set of rectangle `m` of the large direction at the stop `τ`: good pair and `τ ≤ S₁ᵐ`. -/
def g3FstRecSet {X Y : Type*} (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (G₁ : Set X) (G₂ : Set Y)
    (τ : X → ℝ≥0) (m : ℕ) : Set (X × Y) :=
  {z | z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ τ z.1 ≤ g3S₁ x y W₁ ζ₁ m z.1}

section Pos

variable {X Y : Type*} {x y : ℝ} {W₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hag₁ hag₂

/-- On the good pairs the masked cap is the patched cap. -/
theorem g3FstStop_mask_eq {σ : ℝ≥0} (k : ℕ) {z : X × Y} (h1 : z.1 ∈ G₁) (h2 : z.2 ∈ G₂) :
    maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z =
      g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z := by
  rw [maskCap_of_mem h1 h2]
  obtain ⟨hW₁a, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  unfold g3FstCap
  refine capFst_congr_data ?_ eW₂ ?_ eW₁
  · show ((σ : ℝ≥0∞) < ζ₁o z.1) ↔ ((σ : ℝ≥0∞) < ζ₁ z.1)
    rw [hζ₁a]
  · show lifeEnd (W₂o · z.2) (VL₂o 0 · z.2) (ζ₂o z.2) = lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)
    rw [eW₂, eV₂, hζ₂a]

/-- **A positive masked cap forces a good pair and `σ ≤ S₁ᵏ`.** -/
theorem g3FstStop_pos {σ : ℝ≥0} {k : ℕ} {z : X × Y}
    (hpos : 0 < maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z) :
    z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ σ ≤ g3S₁ x y W₁ ζ₁ k z.1 := by
  have hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂ := by
    by_contra h
    rw [maskCap_of_not_mem h] at hpos
    exact lt_irrefl 0 hpos
  rw [g3FstStop_mask_eq hag₁ hag₂ k hG.1 hG.2] at hpos
  refine ⟨hG.1, hG.2, ?_⟩
  by_contra hg
  have h0 : g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z = 0 := by
    unfold g3FstCap
    exact capFst_of_nonpos (by simp only [g3FstOwn, hg, ↓reduceIte, le_refl])
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **The masked cap at the stop is the indicator of the record set of the record cap** (small exits before the
small lifetime). -/
theorem g3FstStop_cap_eq (hS₁ζ : ∀ m x', (g3S₁ x y W₁ ζ₁ m x' : ℝ≥0∞) < ζ₁ x') (τ : X → ℝ≥0) (m : ℕ)
    (z : X × Y) :
    maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.1) m z =
      (g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m).indicator
        (capFst (fun _ _ => True) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
          (g3Fτ x y W₁ ζ₁ τ m) fun z => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ)) z := by
  by_cases hM : z ∈ g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m
  · rw [indicator_of_mem hM]
    obtain ⟨h1, h2, hle⟩ := hM
    rw [g3FstStop_mask_eq hag₁ hag₂ m h1 h2]
    have hτm : g3Fτ x y W₁ ζ₁ τ m z.1 = τ z.1 := min_eq_left hle
    have hl : (τ z.1 : ℝ≥0∞) < ζ₁ z.1 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hle) (hS₁ζ m z.1)
    unfold g3FstCap
    rw [capFst_true_eq (live := fun t x' => (t : ℝ≥0∞) < ζ₁ x') (τ₂ := fun _ => τ z.1) hl hτm]
    refine capFst_congr_pt ?_
    simp only [g3FstOwn, hle, ↓reduceIte]
  · rw [indicator_of_notMem hM]
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [g3FstStop_mask_eq hag₁ hag₂ m hG.1 hG.2]
      have hle : ¬ τ z.1 ≤ g3S₁ x y W₁ ζ₁ m z.1 := fun h => hM ⟨hG.1, hG.2, h⟩
      unfold g3FstCap
      exact capFst_of_nonpos (by simp only [g3FstOwn, hle, ↓reduceIte, le_refl])
    · exact maskCap_of_not_mem hG

end Pos

section Rec

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {τ : X → ℝ≥0}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hlife : ∀ (k : ℕ) (_ : X) (y₀ : Y),
    (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀))
  (hgood : ∀ (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0}, 0 < σ → σ ≤ g3S₁ x y W₁ ζ₁ k x₀ →
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x' => (τ x' : WithTop ℝ≥0))

/-- The product of the two stopped records of rectangle `m` (large direction). -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₁ m)))
  (IsStoppingTime.measurableSpace (hs₂ m))

omit [MeasurableSpace Y] in
/-- The stopped frozen time is measurable for the small record. -/
theorem measurable_g3Fτ (m : ℕ) :
    Measurable[(hτ.min (hs₁ m)).measurableSpace] (g3Fτ x y W₁ ζ₁ τ m) :=
  measurable_stop_self (hτ.min (hs₁ m)) fun x' => by simp only [g3Fτ, WithTop.coe_min]

omit [MeasurableSpace Y] in
/-- `{τ ≤ S₁ᵏ} ∩ {τ ≤ S₁ᵐ}` is an event of the small record of rectangle `m`. -/
theorem measurableSet_g3Fst_le_le (k m : ℕ) :
    MeasurableSet[(hτ.min (hs₁ m)).measurableSpace]
      {x' | τ x' ≤ g3S₁ x y W₁ ζ₁ k x' ∧ τ x' ≤ g3S₁ x y W₁ ζ₁ m x'} := by
  have h := hτ.measurableSet_inter_le (hs₁ m) _ (hτ.measurableSet_le_stopping_time (hs₁ k))
  convert h using 1
  ext x'
  simp only [mem_ofPred_eq, mem_inter_iff, WithTop.coe_le_coe]

/-- **The record set of the large direction is an event of the records.** -/
theorem measurableSet_g3FstRecSet {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂)
    (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0) (m : ℕ) :
    MeasurableSet[𝓡 m] (g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m) := by
  have hG₁m : MeasurableSet[(hτ.min (hs₁ m)).measurableSpace] G₁ :=
    measurableSet_stop_of_conull hG₁ hG₁0 (hτ.min (hs₁ m))
  have hG₂m : MeasurableSet[(hs₂ m).measurableSpace] G₂ := measurableSet_stop_of_conull hG₂ hG₂0 (hs₂ m)
  have hle : MeasurableSet[(hτ.min (hs₁ m)).measurableSpace] {x' | τ x' ≤ g3S₁ x y W₁ ζ₁ m x'} := by
    have h := measurableSet_g3Fst_le_le hs₁ hτ m m
    simpa only [and_self] using h
  have e : g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m = (G₁ ∩ {x' | τ x' ≤ g3S₁ x y W₁ ζ₁ m x'}) ×ˢ G₂ := by
    ext z
    simp only [g3FstRecSet, mem_ofPred_eq, mem_prod, mem_inter_iff]
    tauto
  rw [e]
  exact @MeasurableSet.prod X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace _ _ (hG₁m.inter hle) hG₂m

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The large exits are positive. -/
theorem g3_rect_S₂_pos (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    (h₁ : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (h₂ : ∀ ω, IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] (W₂ · ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (B₂ · ω) (ζ₂ ω))
    (hB₂ : ∀ ω, Continuous (B₂ · ω)) (m : ℕ) (y₀ : Y) : 0 < (g3S₂ x y W₂ ζ₂ m y₀ : ℝ) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  obtain ⟨-, -, -, -, -, -, -, -, hpos, -⟩ := g3_rect hκ4 hκ8 hyx hx h₁ hg₁ hB₁ h₂ hB₂ (isEnclFamily_cofG hne)
  exact hpos m y₀

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood

/-- **The large exit is a good horizon at every frozen time `σ ≤ S₁ᵏ`** (incl. `σ = 0`). -/
theorem g3Fst_good_le (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ σ) with h0 | hσ
  · subst h0
    obtain ⟨hS₁, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
    obtain ⟨τ', hτ', hk⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₁ k x₀).1)
    rw [NNReal.coe_zero] at hτ' ⊢
    exact isGoodTime_zero_frozen hτ' hk (g3_rect_S₂_pos hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ k y₀)
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hlife k x₀ y₀)
  · exact hgood k x₀ y₀ hσ hσS

/-- **The large exit is a good horizon of the stopped records**: the large driver stopped at `S₂ᵏ(y₀)` (lifetime
`⊤`) against the small driver stopped at the frozen time `σ ≤ S₁ᵏ(x₀)`. -/
theorem g3Fst_good_stop (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    A1Ref.IsGoodTime 0 (Strip.extPath fun t => W₂ (min t (g3S₂ x y W₂ ζ₂ k y₀)) y₀) ⊤ y
      (Strip.extPath fun t => W₁ (min t σ) x₀) σ (g3S₂ x y W₂ ζ₂ k y₀) := by
  obtain ⟨hS₁, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hg := g3Fst_good_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood k x₀ y₀ hσS
  set S := g3S₂ x y W₂ ζ₂ k y₀ with hSdef
  have hSζ : (S : ℝ≥0∞) < ζ₂ y₀ := (hlife k x₀ y₀).trans_le (lifeEnd_le _ _ _)
  have hσζ : (σ : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hσS) (hS₁ k x₀).1
  have hcS : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 (S : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc (h₂.path y₀).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hSζ)
  have hcσ : ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 (σ : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hσζ)
  have hdS : Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y₀)) S) := A1Ref.continuous_stopDrv hcS S.coe_nonneg
  have hdσ : Continuous (A1Ref.stopDrv (Strip.extPath (W₁ · x₀)) σ) := A1Ref.continuous_stopDrv hcσ σ.coe_nonneg
  rw [extPath_stop_eq (W₂ · y₀) S, extPath_stop_eq (W₁ · x₀) σ]
  obtain ⟨T₂, hST₂, hc₂⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 hSζ
  obtain ⟨T₁, hσT₁, hc₁⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 hσζ
  refine isGoodTime_repl hg hdS ENNReal.ofReal_lt_top ?_ ?_
  · exact physHull_congr_of_continuousOn hc₂ hdS.continuousOn S.coe_nonneg hST₂
      fun u hu => (A1Ref.stopDrv_eqOn _ _ hu).symm
  · exact physHull_congr_of_continuousOn hc₁ hdσ.continuousOn σ.coe_nonneg hσT₁
      fun u hu => (A1Ref.stopDrv_eqOn _ _ hu).symm

omit hgood in
/-- **The record cap is record-measurable** for a record-measurable own time below `S₂ᵐ`. -/
theorem measurable_g3FstRecCap (m : ℕ) {T : X × Y → ℝ} (hT : Measurable[𝓡 m] T)
    (hTle : ∀ z, 0 < T z → T z ≤ g3S₂ x y W₂ ζ₂ m z.2) :
    Measurable[𝓡 m] (capFst (fun _ _ => True) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
      (g3Fτ x y W₁ ζ₁ τ m) T) := by
  obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ x', ((g3Fτ x y W₁ ζ₁ τ m x' : ℝ≥0) : ℝ≥0∞) < ζ₁ x' := fun x' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₁ m x').1
  refine measurable_capFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace) (𝓑 := (hs₂ m).measurableSpace)
    (live' := fun _ _ => True) (Wj' := fun t y' => W₂ (min t (g3S₂ x y W₂ ζ₂ m y')) y') (ζj' := fun _ => ⊤)
    (Wk' := fun t x' => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m x')) x') (ζk' := fun _ => ⊤)
    (measurable_g3Fτ hs₁ hτ m) MeasurableSet.univ (fun _ _ _ => ENNReal.coe_lt_top)
    (fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hS₂ζ m y')).continuousOn)
    (fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1)
    (fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hτζ x')).continuousOn)
    (fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1)
    (fun t => measurable_stopped_at h₂.progW (hs₂ m) t)
    (fun t => measurable_stopped_at' h₁.progW (hτ.min (hs₁ m)) (T := g3Fτ x y W₁ ζ₁ τ m)
      (fun x' => by simp only [g3Fτ, WithTop.coe_min]) t)
    measurable_const measurable_const hT fun z hz => ⟨Iff.rfl, fun _ => ⟨fun T' hT' =>
      A1Ref.continuousOn_extPath_Icc ((h₂.path z.2).2.2.2.1.mono fun t ht =>
        lt_of_lt_of_le ht (lifeEnd_le _ _ _)) hT',
      A1Ref.exists_continuousOn_extPath_beyond (h₁.path z.1).2.2.2.1 (hτζ z.1), ?_, le_top, fun t ht => ?_,
      fun t ht => by simp only [min_eq_left ht]⟩⟩
  · have h1 : ENNReal.ofReal (T z) ≤ ENNReal.ofReal (g3S₂ x y W₂ ζ₂ m z.2) := ENNReal.ofReal_le_ofReal (hTle z hz)
    rw [ENNReal.ofReal_coe_nnreal] at h1
    exact h1.trans (hlife m z.1 z.2).le
  · have htS : t ≤ g3S₂ x y W₂ ζ₂ m z.2 := by
      have := ht.le.trans (hTle z (lt_of_le_of_lt t.coe_nonneg ht))
      exact_mod_cast this
    simp only [min_eq_left htS]

end Rec

end InteractingSLE.ZhanGT4.A1G3L2
