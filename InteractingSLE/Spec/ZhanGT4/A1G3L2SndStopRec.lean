/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopLoc
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndFinal
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkRecord

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the masked caps on the stopped records

Packet PROVE-A1-G3LAW2. Setting of `hasFamilyLawC_g3_of_stop`'s input `hstop`: patched regular G3 marginals in the
usual augmentations (`W₁, …`), original data `W₁o, …` agreeing with them on measurable conull sets `G₁`, `G₂`, the
patched exits `S₁ᵐ`, `S₂ᵐ` as stopping times and a stop `τ` of the large curve. The records of rectangle `m` are the
stopped σ-algebras `𝓐 m` of `S₁ᵐ` and `𝓑' m` of `τ ∧ S₂ᵐ`.

* **`g3Stop_pos`**: a positive masked cap forces a good pair, `τ ≤ S₂ᵐ` and the large curve live at `τ`;
* **`g3Stop_cap_eq`**: the masked cap at the stop is the indicator of the record set `g3RecSet` (good pair,
  `τ ≤ S₂ᵐ`, live) of the record cap: the image clock (live event `True`) of the patched data at the frozen time
  `g3Sτ = τ ∧ S₂ᵐ` and own time `S₁ᵐ`;
* **`measurableSet_g3RecSet`**, **`measurable_g3RecCap`**: both are record-measurable (stopped replacement data,
  A1-FORCES's `measurable_capSnd_of_stopped`);
* the record facts **`g3Stop_hSm`**, **`g3Stop_hstop`**, **`g3Stop_hgS`** of `ResStopInput`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

/-- The frozen time stopped at the large exit: `τ ∧ S₂ᵐ`. -/
def g3Sτ {Y : Type*} (x y : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (τ : Y → ℝ≥0) (m : ℕ) (y' : Y) : ℝ≥0 :=
  min (τ y') (g3S₂ x y W₂ ζ₂ m y')

/-- The record set of rectangle `m` at the stop `τ`: good pair, `τ ≤ S₂ᵐ`, the large curve live at `τ`. -/
def g3RecSet {X Y : Type*} (x y : ℝ) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (G₁ : Set X)
    (G₂ : Set Y) (τ : Y → ℝ≥0) (m : ℕ) : Set (X × Y) :=
  {z | z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ τ z.2 ≤ g3S₂ x y W₂ ζ₂ m z.2 ∧ g3SndLive W₂ VL₂ ζ₂ (τ z.2) z.2}

section Pos

variable {X Y : Type*} {x y : ℝ} {W₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hag₁ hag₂

/-- On the good pairs the masked cap is the patched cap. -/
theorem g3Stop_mask_eq {σ : ℝ≥0} (k : ℕ) {z : X × Y} (h1 : z.1 ∈ G₁) (h2 : z.2 ∈ G₂) :
    maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z =
      g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y₀ h2
  have hcg := g3Snd_data_congr (x := x) (y := y) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
    (hag₁ x₀ h1).1 (hag₁ x₀ h1).2 hW₂a hV₂a hζ₂a σ
  exact (maskCap_of_mem h1 h2).trans (hcg.2.2.2.2 k)

/-- **A positive masked cap forces a good pair, `σ ≤ S₂ᵏ` and the large curve live at `σ`.** -/
theorem g3Stop_pos {σ : ℝ≥0} {k : ℕ} {z : X × Y}
    (hpos : 0 < maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) σ k z) :
    z.1 ∈ G₁ ∧ z.2 ∈ G₂ ∧ σ ≤ g3S₂ x y W₂ ζ₂ k z.2 ∧ g3SndLive W₂ VL₂ ζ₂ σ z.2 := by
  have hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂ := by
    by_contra h
    rw [maskCap_of_not_mem h] at hpos
    exact lt_irrefl 0 hpos
  rw [g3Stop_mask_eq hag₁ hag₂ k hG.1 hG.2] at hpos
  refine ⟨hG.1, hG.2, ?_, ?_⟩
  · by_contra hg
    have h0 : g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k z = 0 := by
      unfold g3SndCap
      exact capSnd_of_nonpos (by simp only [g3SndOwn, hg, ↓reduceIte, le_refl])
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  · by_contra hnl
    unfold g3SndCap capSnd at hpos
    rw [Set.indicator_of_notMem (show z ∉ {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => σ) z.2) z.2} from hnl)] at hpos
    simp at hpos

/-- **The masked cap at the stop is the indicator of the record set of the record cap.** -/
theorem g3Stop_cap_eq (τ : Y → ℝ≥0) (m : ℕ) (z : X × Y) :
    maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) (τ z.2) m z =
      (g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m).indicator
        (capSnd (fun _ _ => True) y W₁ ζ₁ 0 W₂ (g3Sτ x y W₂ ζ₂ τ m) fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) z := by
  by_cases hM : z ∈ g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m
  · rw [indicator_of_mem hM]
    obtain ⟨h1, h2, hle, hl⟩ := hM
    rw [g3Stop_mask_eq hag₁ hag₂ m h1 h2]
    have hτm : g3Sτ x y W₂ ζ₂ τ m z.2 = τ z.2 := min_eq_left hle
    unfold g3SndCap capSnd
    rw [indicator_of_mem (show z ∈ {w : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => τ z.2) w.2) w.2} from hl),
      indicator_of_mem (show z ∈ {w : X × Y | (fun (_ : ℝ≥0) (_ : Y) => True) (g3Sτ x y W₂ ζ₂ τ m w.2) w.2}
        from trivial)]
    simp only [g3SndOwn, hle, ↓reduceIte, hτm]
  · rw [indicator_of_notMem hM]
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [g3Stop_mask_eq hag₁ hag₂ m hG.1 hG.2]
      by_cases hle : τ z.2 ≤ g3S₂ x y W₂ ζ₂ m z.2
      · have hnl : ¬ g3SndLive W₂ VL₂ ζ₂ (τ z.2) z.2 := fun hl => hM ⟨hG.1, hG.2, hle, hl⟩
        unfold g3SndCap capSnd
        rw [Set.indicator_of_notMem (show z ∉ {w : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => τ z.2) w.2) w.2}
          from hnl)]
        simp
      · unfold g3SndCap
        exact capSnd_of_nonpos (by simp only [g3SndOwn, hle, ↓reduceIte, le_refl])
    · exact maskCap_of_not_mem hG

end Pos

section Rec

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {τ : Y → ℝ≥0}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0))

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

omit [MeasurableSpace X] in
/-- The stopped frozen time is measurable for the large record. -/
theorem measurable_g3Sτ (m : ℕ) :
    Measurable[(hτ.min (hs₂ m)).measurableSpace] (g3Sτ x y W₂ ζ₂ τ m) :=
  measurable_stop_self (hτ.min (hs₂ m)) fun y' => by simp only [g3Sτ, WithTop.coe_min]

omit [MeasurableSpace X] in
/-- `{τ ≤ S₂ᵏ} ∩ {τ ≤ S₂ᵐ}` is an event of the large record of rectangle `m`. -/
theorem measurableSet_g3_le_le (k m : ℕ) :
    MeasurableSet[(hτ.min (hs₂ m)).measurableSpace]
      {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ k y' ∧ τ y' ≤ g3S₂ x y W₂ ζ₂ m y'} := by
  have h := hτ.measurableSet_inter_le (hs₂ m) _ (hτ.measurableSet_le_stopping_time (hs₂ k))
  convert h using 1
  ext y'
  simp only [mem_ofPred_eq, mem_inter_iff, WithTop.coe_le_coe]

include h₂ in
/-- **The record set is an event of the records.** -/
theorem measurableSet_g3RecSet {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂)
    (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0) (m : ℕ) :
    MeasurableSet[𝓡 m] (g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m) := by
  have hG₁m : MeasurableSet[(hs₁ m).measurableSpace] G₁ := measurableSet_stop_of_conull hG₁ hG₁0 (hs₁ m)
  have hG₂m : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] G₂ :=
    measurableSet_stop_of_conull hG₂ hG₂0 (hτ.min (hs₂ m))
  have hle : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ m y'} := by
    have h := measurableSet_g3_le_le hs₂ hτ m m
    simpa only [and_self] using h
  have hcW : ∀ y', ContinuousOn (W₂ · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.1
  have hcV : ∀ y', ContinuousOn (VL₂ 0 · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.2.1 0
  have hprog := isStronglyProgressive_indicator_isStripLife h₂.evol.2.1 h₂.progW (h₂.progVL 0) hcW hcV
  have hI := measurable_stoppedValue' hprog (hτ.min (hs₂ m)) (T := g3Sτ x y W₂ ζ₂ τ m)
    fun y' => by simp only [g3Sτ, WithTop.coe_min]
  have hL : MeasurableSet[(hτ.min (hs₂ m)).measurableSpace]
      {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ m y' ∧ g3SndLive W₂ VL₂ ζ₂ (τ y') y'} := by
    have e : {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ m y' ∧ g3SndLive W₂ VL₂ ζ₂ (τ y') y'} =
        {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ m y'} ∩
          ((fun y' => {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (g3Sτ x y W₂ ζ₂ τ m y')}.indicator
            (fun _ => (1 : ℝ)) y') ⁻¹' {1}) := by
      ext y'
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨hle', hl⟩
        refine ⟨hle', ?_⟩
        rw [show g3Sτ x y W₂ ζ₂ τ m y' = τ y' from min_eq_left hle', indicator_of_mem (show y' ∈
          {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ y')} from hl)]
      · rintro ⟨hle', h1⟩
        refine ⟨hle', ?_⟩
        rw [show g3Sτ x y W₂ ζ₂ τ m y' = τ y' from min_eq_left hle'] at h1
        by_contra hnl
        rw [indicator_of_notMem (show y' ∉ {ω | Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ y')}
          from hnl)] at h1
        exact zero_ne_one h1
    rw [e]
    exact hle.inter (hI (measurableSet_singleton 1))
  have e : g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m =
      G₁ ×ˢ (G₂ ∩ {y' | τ y' ≤ g3S₂ x y W₂ ζ₂ m y' ∧ g3SndLive W₂ VL₂ ζ₂ (τ y') y'}) := by
    ext z
    simp only [g3RecSet, mem_ofPred_eq, mem_prod, mem_inter_iff]
  rw [e]
  exact @MeasurableSet.prod X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace _ _ hG₁m (hG₂m.inter hL)

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The record cap is record-measurable** for a record-measurable own time below `S₁ᵐ`. -/
theorem measurable_g3RecCap (m : ℕ) {T : X × Y → ℝ} (hT : Measurable[𝓡 m] T)
    (hTle : ∀ z, 0 < T z → T z ≤ g3S₁ x y W₁ ζ₁ m z.1) :
    Measurable[𝓡 m] (capSnd (fun _ _ => True) y W₁ ζ₁ 0 W₂ (g3Sτ x y W₂ ζ₂ τ m) T) := by
  obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ y', ((g3Sτ x y W₂ ζ₂ τ m y' : ℝ≥0) : ℝ≥0∞) < ζ₂ y' := fun y' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₂ζ m y')
  refine measurable_capSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace) (𝓑 := (hτ.min (hs₂ m)).measurableSpace)
    (live' := fun _ _ => True) (Wj' := fun t x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') (ζj' := fun _ => ⊤)
    (Wk' := fun t y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y') (ζk' := fun _ => ⊤)
    (measurable_g3Sτ hs₂ hτ m) MeasurableSet.univ (fun _ _ _ => ENNReal.coe_lt_top)
    (fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hS₁ m x').1).continuousOn)
    (fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1)
    (fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hτζ y')).continuousOn)
    (fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1)
    (fun t => measurable_stopped_at h₁.progW (hs₁ m) t)
    (fun t => measurable_stopped_at' h₂.progW (hτ.min (hs₂ m)) (T := g3Sτ x y W₂ ζ₂ τ m)
      (fun y' => by simp only [g3Sτ, WithTop.coe_min]) t)
    measurable_const measurable_const hT fun z hz => ⟨Iff.rfl, fun _ => ⟨fun T' hT' =>
      A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT',
      A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 (hτζ z.2), ?_, le_top, fun t ht => ?_,
      fun t ht => by simp only [min_eq_left ht]⟩⟩
  · have h1 : ENNReal.ofReal (T z) ≤ ENNReal.ofReal (g3S₁ x y W₁ ζ₁ m z.1) := ENNReal.ofReal_le_ofReal (hTle z hz)
    rw [ENNReal.ofReal_coe_nnreal] at h1
    exact h1.trans (hS₁ m z.1).1.le
  · have htS : t ≤ g3S₁ x y W₁ ζ₁ m z.1 := by
      have := ht.le.trans (hTle z (lt_of_le_of_lt t.coe_nonneg ht))
      exact_mod_cast this
    simp only [min_eq_left htS]

end Rec

end InteractingSLE.ZhanGT4.A1G3L2
