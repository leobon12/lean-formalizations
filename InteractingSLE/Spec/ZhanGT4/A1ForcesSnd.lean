/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesLaw

/-!
# Zhan's A.1 (R80): force points and caps with the conditioning curve on `Y` (`FrozenFamily`, `FamilyRect.ofRect`)

Packet PROVE-A1-FORCES. The mirrors of `A1ForcesFam` and `A1ForcesCap` for A1-FROZEN's `FrozenFamily` (conditioning
curve on `Y`, image curve on `X`), obtained from the `X`-conditioning versions on `Y × X` through `Prod.swap`:

* `rForceSnd` (the force point of a frozen-chart mark read from the conditioning sample, e.g. the frozen tip), with
  `rForceSnd_eq_swap`, **`measurable_rForceSnd`** (`FrozenFamily.measurable_VL`) and
  **`exists_measurable_rForceSnd_of_stopped`** (`hgVL` of `FamilyRect.ofRect`);
* `capSnd`, with `capSnd_eq_swap`, **`measurable_capSnd`** (`measurable_S`), **`measurable_capSnd_of_stopped`**
  (`hSm`), **`measurableSet_capSnd_le_inter`** (`hgS`), **`capSnd_le_rLife`** (`hgζ`), **`cover_capSnd`** (`hcov`),
  `capSnd_eq_of_isGoodTime`, `capSnd_mono`, `capSnd_of_nonpos`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Forces

open A2X A1Ref A1Core A1Marg

section Snd

variable {X Y : Type*}

/-! ### Force points -/

/-- **The family's force point of the mark `p`** (conditioning curve on `Y`, image curve on `X`, stop `τ`). -/
abbrev rForceSnd (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (τ : Y → ℝ≥0) (p : Y → ℝ) : ℝ≥0 → X × Y → ℝ :=
  canonForce {z : X × Y | live (τ z.2) z.2} xj xk (fun z t => Wj t z.1) (fun z => ζj z.1) (fun z t => Wk t z.2)
    (fun z => τ z.2) (fun z => p z.2)

theorem rForceSnd_eq_swap (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (τ : Y → ℝ≥0) (p : Y → ℝ) (t : ℝ≥0) (z : X × Y) :
    rForceSnd live xj Wj ζj xk Wk τ p t z = rForceFst live xj Wj ζj xk Wk τ p t z.swap := rfl

/-- **`FrozenFamily.measurable_VL`**: the force points at the deterministic frozen time `σ` are jointly measurable. -/
theorem measurable_rForceSnd [MeasurableSpace X] [MeasurableSpace Y] {live : ℝ≥0 → Y → Prop}
    (hlive : MeasurableSet {q : ℝ≥0 × Y | live q.1 q.2}) {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    {Wk : ℝ≥0 → Y → ℝ} {ζk : Y → ℝ≥0∞} (hlk : ∀ s y, live s y → (s : ℝ≥0∞) < ζk y)
    (hjc : ∀ x, ContinuousOn (Wj · x) {t | (t : ℝ≥0∞) < ζj x}) (hj0 : ∀ x, Wj 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk · y) {t | (t : ℝ≥0∞) < ζk y}) (hk0 : ∀ y, Wk 0 y = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    (xj xk : ℝ) {p : ℝ≥0 → Y → ℝ} (hp : Measurable fun q : ℝ≥0 × Y => p q.1 q.2) (t : ℝ≥0) :
    Measurable fun q : ℝ≥0 × (X × Y) => rForceSnd live xj Wj ζj xk Wk (fun _ => q.1) (p q.1) t q.2 :=
  (measurable_rForceFst (X := Y) (Y := X) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk xj xk hp t).comp
    (measurable_fst.prodMk (measurable_swap.comp measurable_snd))

/-- **`hgVL` (`hgVR`) of `FamilyRect.ofRect`** (conditioning curve on `Y`): the mirror of
`exists_measurable_rForceFst_of_stopped`. -/
theorem exists_measurable_rForceSnd_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y]
    {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞} {Wk Wk' : ℝ≥0 → Y → ℝ}
    {ζk' : Y → ℝ≥0∞} {τ : Y → ℝ≥0} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × Y | live' q.1 q.2}) (hlk : ∀ s y, live' s y → (s : ℝ≥0∞) < ζk' y)
    (hjc : ∀ x, ContinuousOn (Wj' · x) {t | (t : ℝ≥0∞) < ζj' x}) (hj0' : ∀ x, Wj' 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk' · y) {t | (t : ℝ≥0∞) < ζk' y}) (hk0' : ∀ y, Wk' 0 y = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    {p p' : Y → ℝ} (hp' : Measurable p') {cap : X × Y → ℝ≥0} {T : X × Y → ℝ} (r : ℝ≥0)
    (hloc : ∀ z : X × Y, r < cap z →
      live (τ z.2) z.2 ∧ live' (τ z.2) z.2 ∧
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T)) ∧ Wj 0 z.1 = 0 ∧
      (∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ')) ∧ Wk 0 z.2 = 0 ∧
      IsGoodTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z) ∧
      IsGoodTime xj (Strip.extPath (Wj' · z.1)) (ζj' z.1) xk (Strip.extPath (Wk' · z.2)) (τ z.2) (T z) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T z → Wj' t z.1 = Wj t z.1) ∧ (∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2) ∧
      (cap z : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z))
    (hp : ∀ z : X × Y, r < cap z → p' z.2 = p z.2) :
    ∃ f : X × Y → ℝ, Measurable f ∧ ∀ z, r < cap z → rForceSnd live xj Wj ζj xk Wk τ p r z = f z := by
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rForceFst_of_stopped (X := Y) (Y := X) (cap := fun w => cap w.swap)
    (T := fun w => T w.swap) (p := p) hτ hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk hp' r
    (fun w hw => hloc w.swap hw) (fun w hw => hp w.swap hw)
  exact ⟨fun z => f z.swap, hf.comp measurable_swap, fun z hz => hfe z.swap hz⟩

/-! ### Caps -/

/-- **The cap** of the image curve (on `X`) at its own time `T z`, for the conditioning curve (on `Y`) at the stop
`τ`: the clock up to `T z` on the live event. -/
def capSnd (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (τ : Y → ℝ≥0) (T : X × Y → ℝ) (z : X × Y) : ℝ≥0 :=
  ({z : X × Y | live (τ z.2) z.2}.indicator (fun z => clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk
    (Strip.extPath (Wk · z.2)) (τ z.2) (T z)) z).toNNReal

variable {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
  {τ : Y → ℝ≥0} {T T' : X × Y → ℝ} {z : X × Y}

theorem capSnd_eq_swap (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (τ : Y → ℝ≥0) (T : X × Y → ℝ) (z : X × Y) :
    capSnd live xj Wj ζj xk Wk τ T z = capFst live xj Wj ζj xk Wk τ (fun w => T w.swap) z.swap := rfl

/-- On the fibre over `y` only the frozen time `τ y` is read (`FrozenFamily.Sat`). -/
theorem capSnd_at (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (τ : Y → ℝ≥0) (T : ℝ≥0 → X × Y → ℝ) (z : X × Y) :
    capSnd live xj Wj ζj xk Wk (fun _ => τ z.2) (T (τ z.2)) z =
      capSnd live xj Wj ζj xk Wk τ (fun z => T (τ z.2) z) z := rfl

theorem capSnd_congr_pt (h : T z = T' z) : capSnd live xj Wj ζj xk Wk τ T z = capSnd live xj Wj ζj xk Wk τ T' z :=
  capFst_congr_pt (X := Y) (Y := X) (z := z.swap) (T := fun w => T w.swap) (T' := fun w => T' w.swap) h

theorem capSnd_of_nonpos (hT : T z ≤ 0) : capSnd live xj Wj ζj xk Wk τ T z = 0 :=
  capFst_of_nonpos (X := Y) (Y := X) (z := z.swap) (T := fun w => T w.swap) hT

/-- At a good own time the cap is the clock (A1-FAMILY's `hSm`, `hcap₁`). -/
theorem capSnd_eq_of_isGoodTime (hlive : live (τ z.2) z.2)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T))
    (hj0 : Wj 0 z.1 = 0) (hk : ∃ τ' : ℝ, (τ z.2 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ'))
    (hk0 : Wk 0 z.2 = 0)
    (hT : IsGoodTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z)) :
    capSnd live xj Wj ζj xk Wk τ T z =
      (A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z)).toNNReal :=
  capFst_eq_of_isGoodTime (X := Y) (Y := X) (z := z.swap) (T := fun w => T w.swap) hlive hj hj0 hk hk0 hT

/-- The cap is monotone in the own time (A1-FAMILY's `hcap₂`). -/
theorem capSnd_mono (hTT : T z ≤ T' z)
    (hfin : live (τ z.2) z.2 → clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2)
      (T' z) ≠ ∞) :
    capSnd live xj Wj ζj xk Wk τ T z ≤ capSnd live xj Wj ζj xk Wk τ T' z :=
  capFst_mono (X := Y) (Y := X) (z := z.swap) (T := fun w => T w.swap) (T' := fun w => T' w.swap) hTT hfin

/-- **`hgζ`**: the cap is below the masked canonical image lifetime. -/
theorem capSnd_le_rLife (T : X × Y → ℝ) (z : X × Y) :
    (capSnd live xj Wj ζj xk Wk τ T z : ℝ≥0∞) ≤ rLife live xj Wj ζj xk Wk τ z :=
  capFst_le_rLifeFst (X := Y) (Y := X) (fun w => T w.swap) z.swap

/-- **`hcov`**: the clock exhaustion for caps at own times exhausting the contact time with finite clocks. -/
theorem cover_capSnd {Tm : ℕ → X × Y → ℝ} (hlive : live (τ z.2) z.2)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T))
    (hj0 : Wj 0 z.1 = 0) (hk : ∃ τ' : ℝ, (τ z.2 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ'))
    (hk0 : Wk 0 z.2 = 0)
    (hex : ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk
      (Strip.extPath (Wk · z.2)) (τ z.2) → ∃ m, (s : ℝ) < Tm m z)
    (hfin : ∀ m, clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) (Tm m z) ≠ ∞) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2))
      (τ z.2) → ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) s ≤
        capSnd live xj Wj ζj xk Wk τ (Tm m) z :=
  cover_capFst (X := Y) (Y := X) (z := z.swap) (Tm := fun m w => Tm m w.swap) hlive hj hj0 hk hk0 hex hfin

/-- **`hgS`, set form** (mirror of `capFst_le_inter_eq`). -/
theorem capSnd_le_inter_eq {Tk Tm : X × Y → ℝ}
    (hfin : ∀ z : X × Y, live (τ z.2) z.2 → clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk
      (Strip.extPath (Wk · z.2)) (τ z.2) (Tk z) ≠ ∞) (r : ℝ≥0) :
    {z | capSnd live xj Wj ζj xk Wk τ Tk z ≤ r} ∩ {z | r < capSnd live xj Wj ζj xk Wk τ Tm z} =
      {z | capSnd live xj Wj ζj xk Wk τ (fun z => min (Tk z) (Tm z)) z ≤ r} ∩
        {z | r < capSnd live xj Wj ζj xk Wk τ Tm z} := by
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases le_total (Tk z) (Tm z) with h | h
    · rwa [capSnd_congr_pt (T' := Tk) (min_eq_left h)]
    · rw [capSnd_congr_pt (T' := Tm) (min_eq_right h)]
      exact (capSnd_mono h (hfin z)).trans h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases le_total (Tk z) (Tm z) with h | h
    · rwa [capSnd_congr_pt (T' := Tk) (min_eq_left h)] at h1
    · rw [capSnd_congr_pt (T' := Tm) (min_eq_right h)] at h1
      exact absurd (h1.trans_lt h2) (lt_irrefl _)

/-- **`hgS` of `FamilyRect.ofRect`** (mirror of `measurableSet_capFst_le_inter`). -/
theorem measurableSet_capSnd_le_inter [𝓜 : MeasurableSpace (X × Y)] {Tk Tm : X × Y → ℝ}
    (hmin : Measurable (capSnd live xj Wj ζj xk Wk τ fun z => min (Tk z) (Tm z)))
    (hm : Measurable (capSnd live xj Wj ζj xk Wk τ Tm))
    (hfin : ∀ z : X × Y, live (τ z.2) z.2 → clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk
      (Strip.extPath (Wk · z.2)) (τ z.2) (Tk z) ≠ ∞) (r : ℝ≥0) :
    MeasurableSet ({z | capSnd live xj Wj ζj xk Wk τ Tk z ≤ r} ∩ {z | r < capSnd live xj Wj ζj xk Wk τ Tm z}) := by
  rw [capSnd_le_inter_eq hfin r]
  exact (measurableSet_le hmin measurable_const).inter (measurableSet_lt measurable_const hm)

/-- **`FrozenFamily.measurable_S`**: the caps at the deterministic frozen time are jointly measurable. -/
theorem measurable_capSnd [MeasurableSpace X] [MeasurableSpace Y]
    (hlive : MeasurableSet {q : ℝ≥0 × Y | live q.1 q.2}) {ζk : Y → ℝ≥0∞}
    (hlk : ∀ s y, live s y → (s : ℝ≥0∞) < ζk y)
    (hjc : ∀ x, ContinuousOn (Wj · x) {t | (t : ℝ≥0∞) < ζj x}) (hj0 : ∀ x, Wj 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk · y) {t | (t : ℝ≥0∞) < ζk y}) (hk0 : ∀ y, Wk 0 y = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    {T : ℝ≥0 → X × Y → ℝ} (hT : Measurable fun q : ℝ≥0 × (X × Y) => T q.1 q.2) :
    Measurable fun q : ℝ≥0 × (X × Y) => capSnd live xj Wj ζj xk Wk (fun _ => q.1) (T q.1) q.2 :=
  (measurable_capFst (X := Y) (Y := X) (T := fun σ w => T σ w.swap) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
    (hT.comp (measurable_fst.prodMk (measurable_swap.comp measurable_snd)))).comp
    (measurable_fst.prodMk (measurable_swap.comp measurable_snd))

/-- **`hSm` of `FamilyRect.ofRect`** (mirror of `measurable_capFst_of_stopped`). -/
theorem measurable_capSnd_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y] {live' : ℝ≥0 → Y → Prop}
    {Wj' : ℝ≥0 → X → ℝ} {ζj' : X → ℝ≥0∞} {Wk' : ℝ≥0 → Y → ℝ} {ζk' : Y → ℝ≥0∞} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × Y | live' q.1 q.2}) (hlk : ∀ s y, live' s y → (s : ℝ≥0∞) < ζk' y)
    (hjc : ∀ x, ContinuousOn (Wj' · x) {t | (t : ℝ≥0∞) < ζj' x}) (hj0' : ∀ x, Wj' 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk' · y) {t | (t : ℝ≥0∞) < ζk' y}) (hk0' : ∀ y, Wk' 0 y = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    (hT : Measurable T)
    (hloc : ∀ z : X × Y, 0 < T z → (live (τ z.2) z.2 ↔ live' (τ z.2) z.2) ∧ (live (τ z.2) z.2 →
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T)) ∧
      (∃ τ' : ℝ, (τ z.2 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ')) ∧
      ENNReal.ofReal (T z) ≤ ζj z.1 ∧ ENNReal.ofReal (T z) ≤ ζj' z.1 ∧
      (∀ t : ℝ≥0, (t : ℝ) < T z → Wj' t z.1 = Wj t z.1) ∧ (∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2))) :
    Measurable (capSnd live xj Wj ζj xk Wk τ T) :=
  (measurable_capFst_of_stopped (X := Y) (Y := X) (T := fun w => T w.swap) (live := live) (Wj := Wj) (ζj := ζj)
    (Wk := Wk) hτ hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk (hT.comp measurable_swap)
    (fun w hw => hloc w.swap hw)).comp measurable_swap

end Snd

end InteractingSLE.ZhanGT4.A1Forces
