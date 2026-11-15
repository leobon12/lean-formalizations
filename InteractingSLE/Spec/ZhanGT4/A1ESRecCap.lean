/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndWire
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopFacts

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the masked caps on the stopped records

Packet PROVE-A1-EIGHTSNDREC (the (Eight) mirror of PROVE-A1-G3LAW2's `A1G3L2SndStop{Loc,Rec,Facts}`). Setting of
`EightSndRecordStatement`: patched regular Eight marginals in the usual augmentations (`W₁, …`), original data
`W₁o, …` agreeing with them on measurable conull sets `G₁`, `G₂`, the patched exits `S₁ᵐ`, `S₂ᵐ` as stopping times and
a stop `τ` of the large curve. The records of rectangle `m` are the stopped σ-algebras `𝓐 m` of `S₁ᵐ` and `𝓑' m` of
`τ ∧ S₂ᵐ`.

* **`eight_isGoodTime_le`**, **`eight_isGoodTime_stop`**: the small exit `S₁ᵏ` is a good horizon at every frozen time
  `σ ≤ S₂ᵏ` (`σ = 0` included), also for the stopped replacement data;
* **`eightStop_pos`**: a positive masked cap forces a good pair, `τ ≤ S₂ᵐ` and the large curve live at `τ`;
* **`eightStop_cap_eq`**: the masked cap at the stop is the indicator of the record set `eightRecSet` of the record
  cap (live event `True`, frozen time `eightSτ = τ ∧ S₂ᵐ`, own time `S₁ᵐ`);
* **`measurableSet_eightRecSet`**, **`measurable_eightRecCap`**: both are record-measurable;
* the record facts **`eightStop_hSm`**, **`eightStop_hstop`**, **`eightStop_hgS`** of `ResStopInput`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESRec

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1SeedGeom A1G3L2 A1ESnd

/-- The frozen time stopped at the large exit: `τ ∧ S₂ᵐ`. -/
def eightSτ {Y : Type*} (x : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (τ : Y → ℝ≥0) (m : ℕ) (y' : Y) : ℝ≥0 :=
  min (τ y') (eightS₂ x W₂ ζ₂ m y')

/-- The record set of rectangle `m` at the stop `τ`: good pair, `τ ≤ S₂ᵐ`, the large curve live at `τ`. -/
def eightRecSet {X Y : Type*} (x : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞)
    (G₁ : Set X) (G₂ : Set Y) (τ : Y → ℝ≥0) (m : ℕ) : Set (X × Y) :=
  {z | z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ τ z.2 ≤ eightS₂ x W₂ ζ₂ m z.2 ∧ eightSndLive W₂ VL₂ ζ₂ (τ z.2) z.2}

/-! ### Good horizons -/

section Loc

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The small exit is a good horizon at every frozen time `σ ≤ S₂ᵏ`** (including `σ = 0`; A1-GOODTIME's
`eightSnd_isGoodTime`). -/
theorem eight_isGoodTime_le (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (x₀ : X) :
    A1Ref.IsGoodTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) σ (eightS₁ x W₁ ζ₁ k x₀) :=
  (A1Good.eightSnd_isGoodTime hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀ hσS).1

/-- **The small exit is a good horizon of the stopped records**: the small driver stopped at `S₁ᵏ(x₀)` (lifetime `⊤`)
against the large driver stopped at the frozen time `σ ≤ S₂ᵏ(y₀)`. -/
theorem eight_isGoodTime_stop (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (x₀ : X) :
    A1Ref.IsGoodTime x (Strip.extPath fun t => W₁ (min t (eightS₁ x W₁ ζ₁ k x₀)) x₀) ⊤ 0
      (Strip.extPath fun t => W₂ (min t σ) y₀) σ (eightS₁ x W₁ ζ₁ k x₀) := by
  obtain ⟨hS₁, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hg := eight_isGoodTime_le hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσS x₀
  set S := eightS₁ x W₁ ζ₁ k x₀ with hSdef
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

/-! ### The masked caps on the record set -/

section Pos

variable {X Y : Type*} {x : ℝ} {W₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hag₁ hag₂

/-- On the good pairs the masked cap is the patched cap. -/
theorem eightStop_mask_eq {σ : ℝ≥0} (k : ℕ) {z : X × Y} (h1 : z.1 ∈ G₁) (h2 : z.2 ∈ G₂) :
    maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z =
      eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y₀ h2
  have hcg := eightSnd_data_congr (x := x) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
    (hag₁ x₀ h1).1 (hag₁ x₀ h1).2 hW₂a hV₂a hζ₂a σ
  exact (maskCap_of_mem h1 h2).trans (hcg.2.2.2.2 k)

/-- **A positive masked cap forces a good pair, `σ ≤ S₂ᵏ` and the large curve live at `σ`.** -/
theorem eightStop_pos {σ : ℝ≥0} {k : ℕ} {z : X × Y}
    (hpos : 0 < maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z) :
    z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ σ ≤ eightS₂ x W₂ ζ₂ k z.2 ∧ eightSndLive W₂ VL₂ ζ₂ σ z.2 := by
  have hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂ := by
    by_contra h
    rw [maskCap_of_not_mem h] at hpos
    exact lt_irrefl 0 hpos
  rw [eightStop_mask_eq hag₁ hag₂ k hG.1 hG.2] at hpos
  refine ⟨hG.1, hG.2, ?_, ?_⟩
  · by_contra hg
    have h0 : eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z = 0 := by
      unfold eightSndCap
      exact capSnd_of_nonpos (by simp only [eightSndOwn, hg, ↓reduceIte, le_refl])
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  · by_contra hnl
    unfold eightSndCap capSnd at hpos
    rw [Set.indicator_of_notMem (show z ∉ {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2} from hnl)]
      at hpos
    simp at hpos

/-- **The masked cap at the stop is the indicator of the record set of the record cap.** -/
theorem eightStop_cap_eq (τ : Y → ℝ≥0) (m : ℕ) (z : X × Y) :
    maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.2) m z =
      (eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m).indicator
        (capSnd (fun _ _ => True) x W₁ ζ₁ 0 W₂ (eightSτ x W₂ ζ₂ τ m) fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) z := by
  by_cases hM : z ∈ eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m
  · rw [indicator_of_mem hM]
    obtain ⟨h1, h2, hle, hl⟩ := hM
    rw [eightStop_mask_eq hag₁ hag₂ m h1 h2]
    have hτm : eightSτ x W₂ ζ₂ τ m z.2 = τ z.2 := min_eq_left hle
    unfold eightSndCap capSnd
    rw [indicator_of_mem (show z ∈ {w : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => τ z.2) w.2) w.2} from hl),
      indicator_of_mem (show z ∈ {w : X × Y | (fun (_ : ℝ≥0) (_ : Y) => True) (eightSτ x W₂ ζ₂ τ m w.2) w.2}
        from trivial)]
    simp only [eightSndOwn, hle, ↓reduceIte, hτm]
  · rw [indicator_of_notMem hM]
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [eightStop_mask_eq hag₁ hag₂ m hG.1 hG.2]
      by_cases hle : τ z.2 ≤ eightS₂ x W₂ ζ₂ m z.2
      · have hnl : ¬ eightSndLive W₂ VL₂ ζ₂ (τ z.2) z.2 := fun hl => hM ⟨hG.1, hG.2, hle, hl⟩
        unfold eightSndCap capSnd
        rw [Set.indicator_of_notMem (show z ∉ {w : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => τ z.2) w.2) w.2}
          from hnl)]
        simp
      · unfold eightSndCap
        exact capSnd_of_nonpos (by simp only [eightSndOwn, hle, ↓reduceIte, le_refl])
    · exact maskCap_of_not_mem hG

end Pos

/-! ### Record measurability -/

section Rec

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {τ : Y → ℝ≥0}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0))

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

omit [MeasurableSpace X] in
/-- The stopped frozen time is measurable for the large record. -/
theorem measurable_eightSτ (m : ℕ) :
    Measurable[(hτ.min (hs₂ m)).measurableSpace] (eightSτ x W₂ ζ₂ τ m) :=
  measurable_stop_self (hτ.min (hs₂ m)) fun y' => by simp only [eightSτ, WithTop.coe_min]

omit [MeasurableSpace X] in
/-- `{τ ≤ S₂ᵏ} ∩ {τ ≤ S₂ᵐ}` is an event of the large record of rectangle `m`. -/
theorem measurableSet_eight_le_le (k m : ℕ) :
    MeasurableSet[(hτ.min (hs₂ m)).measurableSpace]
      {y' | τ y' ≤ eightS₂ x W₂ ζ₂ k y' ∧ τ y' ≤ eightS₂ x W₂ ζ₂ m y'} := by
  have h := hτ.measurableSet_inter_le (hs₂ m) _ (hτ.measurableSet_le_stopping_time (hs₂ k))
  convert h using 1
  ext y'
  simp only [mem_ofPred_eq, mem_inter_iff, WithTop.coe_le_coe]

include h₂ in
/-- **The record set is an event of the records.** -/
theorem measurableSet_eightRecSet {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂)
    (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0) (m : ℕ) :
    MeasurableSet[𝓡 m] (eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m) := by
  have hG₁m : MeasurableSet[(hs₁ m).measurableSpace] G₁ := measurableSet_stop_of_conull hG₁ hG₁0 (hs₁ m)
  have hG₂m : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] G₂ :=
    measurableSet_stop_of_conull hG₂ hG₂0 (hτ.min (hs₂ m))
  have hle : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] {y' | τ y' ≤ eightS₂ x W₂ ζ₂ m y'} := by
    have h := measurableSet_eight_le_le hs₂ hτ m m
    simpa only [and_self] using h
  have hcW : ∀ y', ContinuousOn (W₂ · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.1
  have hcV : ∀ y', ContinuousOn (VL₂ 0 · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.2.1 0
  have hprog := isStronglyProgressive_indicator_isStripLife h₂.evol.2.1 h₂.progW (h₂.progVL 0) hcW hcV
  have hI := measurable_stoppedValue' hprog (hτ.min (hs₂ m)) (T := eightSτ x W₂ ζ₂ τ m)
    fun y' => by simp only [eightSτ, WithTop.coe_min]
  have hL : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace]
      {y' | τ y' ≤ eightS₂ x W₂ ζ₂ m y' ∧ eightSndLive W₂ VL₂ ζ₂ (τ y') y'} := by
    have e : {y' | τ y' ≤ eightS₂ x W₂ ζ₂ m y' ∧ eightSndLive W₂ VL₂ ζ₂ (τ y') y'} =
        {y' | τ y' ≤ eightS₂ x W₂ ζ₂ m y'} ∩
          ((fun y' => {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (eightSτ x W₂ ζ₂ τ m y')}.indicator
            (fun _ => (1 : ℝ)) y') ⁻¹' {1}) := by
      ext y'
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hle', hl⟩
        refine ⟨hle', ?_⟩
        rw [show eightSτ x W₂ ζ₂ τ m y' = τ y' from min_eq_left hle', indicator_of_mem (show y' ∈
          {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ y')} from hl)]
      · rintro ⟨hle', h1⟩
        refine ⟨hle', ?_⟩
        rw [show eightSτ x W₂ ζ₂ τ m y' = τ y' from min_eq_left hle'] at h1
        by_contra hnl
        rw [indicator_of_notMem (show y' ∉ {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ y')}
          from hnl)] at h1
        exact zero_ne_one h1
    rw [e]
    exact hle.inter (hI (measurableSet_singleton 1))
  have e : eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m =
      G₁ ×ˢ (G₂ ∩ {y' | τ y' ≤ eightS₂ x W₂ ζ₂ m y' ∧ eightSndLive W₂ VL₂ ζ₂ (τ y') y'}) := by
    ext z
    simp only [eightRecSet, mem_ofPred_eq, mem_prod, mem_inter_iff]
  rw [e]
  exact @MeasurableSet.prod X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace _ _ hG₁m (hG₂m.inter hL)

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The record cap is record-measurable** for a record-measurable own time below `S₁ᵐ`. -/
theorem measurable_eightRecCap (m : ℕ) {T : X × Y → ℝ} (hT : Measurable[𝓡 m] T)
    (hTle : ∀ z, 0 < T z → T z ≤ eightS₁ x W₁ ζ₁ m z.1) :
    Measurable[𝓡 m] (capSnd (fun _ _ => True) x W₁ ζ₁ 0 W₂ (eightSτ x W₂ ζ₂ τ m) T) := by
  obtain ⟨hS₁, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ y', ((eightSτ x W₂ ζ₂ τ m y' : ℝ≥0) : ℝ≥0∞) < ζ₂ y' := fun y' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₂ζ m y')
  refine measurable_capSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace) (𝓑 := (hτ.min (hs₂ m)).measurableSpace)
    (live' := fun _ _ => True) (Wj' := fun t x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') (ζj' := fun _ => ⊤)
    (Wk' := fun t y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y') (ζk' := fun _ => ⊤)
    (measurable_eightSτ hs₂ hτ m) MeasurableSet.univ (fun _ _ _ => ENNReal.coe_lt_top)
    (fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hS₁ m x').1).continuousOn)
    (fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1)
    (fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hτζ y')).continuousOn)
    (fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1)
    (fun t => measurable_stopped_at h₁.progW (hs₁ m) t)
    (fun t => measurable_stopped_at' h₂.progW (hτ.min (hs₂ m)) (T := eightSτ x W₂ ζ₂ τ m)
      (fun y' => by simp only [eightSτ, WithTop.coe_min]) t)
    measurable_const measurable_const hT fun z hz => ⟨Iff.rfl, fun _ => ⟨fun T' hT' =>
      A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT',
      A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 (hτζ z.2), ?_, le_top, fun t ht => ?_,
      fun t ht => by simp only [min_eq_left ht]⟩⟩
  · have h1 : ENNReal.ofReal (T z) ≤ ENNReal.ofReal (eightS₁ x W₁ ζ₁ m z.1) :=
      ENNReal.ofReal_le_ofReal (hTle z hz)
    rw [ENNReal.ofReal_coe_nnreal] at h1
    exact h1.trans (hS₁ m z.1).1.le
  · have htS : t ≤ eightS₁ x W₁ ζ₁ m z.1 := by
      have := ht.le.trans (hTle z (lt_of_le_of_lt t.coe_nonneg ht))
      exact_mod_cast this
    simp only [min_eq_left htS]

end Rec

/-! ### The record facts of the caps -/

section Facts

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y} {τ : Y → ℝ≥0}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

/-- The masked caps at the stop. -/
local notation "𝓢" => maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hSm`**: the masked cap at the stop is record-measurable. -/
theorem eightStop_hSm (m : ℕ) : Measurable[𝓡 m] fun z => (𝓢) (τ z.2) m z := by
  have e : (fun z => (𝓢) (τ z.2) m z) = (eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m).indicator
      (capSnd (fun _ _ => True) x W₁ ζ₁ 0 W₂ (eightSτ x W₂ ζ₂ τ m) fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) :=
    funext (eightStop_cap_eq hag₁ hag₂ τ m)
  rw [e]
  have hS₁m : Measurable[(hs₁ m).measurableSpace] (eightS₁ x W₁ ζ₁ m) :=
    measurable_stop_self (hs₁ m) fun _ => rfl
  have hT : Measurable[𝓡 m] fun z : X × Y => (eightS₁ x W₁ ζ₁ m z.1 : ℝ) :=
    (hS₁m.comp (@measurable_fst X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace)).coe_nnreal_real
  exact (measurable_eightRecCap hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m hT fun z _ => le_rfl).indicator
    (measurableSet_eightRecSet h₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m)

/-- **`hstop`**: events of the stopped σ-algebra at `τ` cut by the cap event are record events. -/
theorem eightStop_hstop (m : ℕ) (s : ℝ≥0) (C : Set Y) (hC : MeasurableSet[hτ.measurableSpace] C) :
    MeasurableSet[𝓡 m] (Prod.snd ⁻¹' C ∩ {z | s < (𝓢) (τ z.2) m z}) :=
  A1MultiMark.measurableSet_snd_inter_cap hτ (hs₂ m) (𝓐 := (hs₁ m).measurableSpace)
    (measurableSet_lt measurable_const
      (eightStop_hSm hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m))
    (fun _ hz => WithTop.coe_le_coe.2 (eightStop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.2.1) hC

omit hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ in
/-- The clock up to the own time of a raw cap is finite on live samples. -/
theorem eightStop_fin (k : ℕ) {σ : ℝ≥0} {z : X × Y} (hl : eightSndLive W₂ VL₂ ζ₂ σ z.2) :
    clkSup x (Strip.extPath (W₁ · z.1)) (ζ₁ z.1) 0 (Strip.extPath (W₂ · z.2)) σ
      (eightSndOwn x W₁ ζ₁ W₂ ζ₂ σ k z) ≠ ∞ := by
  by_cases hle : σ ≤ eightS₂ x W₂ ζ₂ k z.2
  · have hown : eightSndOwn x W₁ ζ₁ W₂ ζ₂ σ k z = eightS₁ x W₁ ζ₁ k z.1 := by
      simp only [eightSndOwn, hle, ↓reduceIte]
    rw [hown, clkSup_eq_of_isGoodTime (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT)
      (by simpa [Strip.extPath] using (h₁.path z.1).1)
      (A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1)
      (by simpa [Strip.extPath] using (h₂.path z.2).1) σ.coe_nonneg
      (eight_isGoodTime_le hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k z.2 hle z.1)]
    exact ENNReal.ofReal_ne_top
  · rw [clkSup_of_nonpos (by simp only [eightSndOwn, hle, ↓reduceIte, le_refl])]
    exact ENNReal.zero_ne_top

/-- **`hgS`**: the cap comparisons are record events. -/
theorem eightStop_hgS (m k : ℕ) (r : ℝ≥0) :
    MeasurableSet[𝓡 m] ({z | (𝓢) (τ z.2) k z ≤ r} ∩ {z | r < (𝓢) (τ z.2) m z}) := by
  set Tkm : X × Y → ℝ := fun z => if τ z.2 ≤ eightS₂ x W₂ ζ₂ k z.2 ∧ τ z.2 ≤ eightS₂ x W₂ ζ₂ m z.2 then
    (min (eightS₁ x W₁ ζ₁ k z.1) (eightS₁ x W₁ ζ₁ m z.1) : ℝ) else 0 with hTkm
  set R := eightRecSet x W₂ VL₂ ζ₂ G₁ G₂ τ m with hR
  -- on the record set, `min(S_k, S_m)` is the record cap at `Tkm`
  have hmin : ∀ z ∈ R, min ((𝓢) (τ z.2) k z) ((𝓢) (τ z.2) m z) =
      capSnd (fun _ _ => True) x W₁ ζ₁ 0 W₂ (eightSτ x W₂ ζ₂ τ m) Tkm z := by
    intro z hz
    obtain ⟨h1, h2, hle, hl⟩ := hz
    rw [eightStop_mask_eq hag₁ hag₂ k h1 h2, eightStop_mask_eq hag₁ hag₂ m h1 h2]
    unfold eightSndCap
    rw [min_capSnd_eq (fun hl' => eightStop_fin hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k hl')
      (fun hl' => eightStop_fin hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m hl'),
      capSnd_true_eq (τ₂ := fun _ => τ z.2) hl (min_eq_left hle)]
    refine capSnd_congr_pt ?_
    simp only [hTkm, eightSndOwn, hle, and_true]
    split_ifs <;> simp
  have hRm := measurableSet_eightRecSet h₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m
  -- the own time `Tkm` is record-measurable
  have hTm : Measurable[𝓡 m] Tkm := by
    have hE := measurableSet_eight_le_le hs₂ hτ k m
    have hmin₁ : Measurable[(hs₁ m).measurableSpace]
        fun x' => min (eightS₁ x W₁ ζ₁ k x') (eightS₁ x W₁ ζ₁ m x') :=
      (measurable_stop_self ((hs₁ k).min (hs₁ m)) fun x' => by simp only [WithTop.coe_min]).mono
        (((hs₁ k).min (hs₁ m)).measurableSpace_mono (hs₁ m) fun _ => min_le_right _ _) le_rfl
    refine Measurable.ite (p := fun z : X × Y => τ z.2 ≤ eightS₂ x W₂ ζ₂ k z.2 ∧ τ z.2 ≤ eightS₂ x W₂ ζ₂ m z.2)
      ?_ ?_ measurable_const
    · exact @measurable_snd X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace _ hE
    · exact (hmin₁.comp (@measurable_fst X Y (hs₁ m).measurableSpace
        (hτ.min (hs₂ m)).measurableSpace)).coe_nnreal_real
  have hTle : ∀ z, 0 < Tkm z → Tkm z ≤ eightS₁ x W₁ ζ₁ m z.1 := by
    intro z hz
    simp only [hTkm] at hz ⊢
    split_ifs at hz ⊢ with h
    · exact_mod_cast min_le_right _ _
    · exact absurd hz (lt_irrefl 0)
  have hcm := measurable_eightRecCap hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m hTm hTle
  have hSm := eightStop_hSm hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m
  have e : {z | (𝓢) (τ z.2) k z ≤ r} ∩ {z | r < (𝓢) (τ z.2) m z} =
      R ∩ ({z | capSnd (fun _ _ => True) x W₁ ζ₁ 0 W₂ (eightSτ x W₂ ζ₂ τ m) Tkm z ≤ r} ∩
        {z | r < (𝓢) (τ z.2) m z}) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hk, hm⟩
      have hzR : z ∈ R := eightStop_pos hag₁ hag₂ (zero_le.trans_lt hm)
      refine ⟨hzR, ?_, hm⟩
      rw [← hmin z hzR]
      exact (min_le_left _ _).trans hk
    · rintro ⟨hzR, hk, hm⟩
      refine ⟨?_, hm⟩
      rw [← hmin z hzR] at hk
      rcases min_choice ((𝓢) (τ z.2) k z) ((𝓢) (τ z.2) m z) with h | h
      · rwa [h] at hk
      · rw [h] at hk
        exact absurd (hm.trans_le hk) (lt_irrefl _)
  rw [e]
  exact hRm.inter ((measurableSet_le hcm measurable_const).inter (measurableSet_lt measurable_const hSm))

end Facts

end InteractingSLE.ZhanGT4.A1ESRec
