/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1LargeDensSeed

/-!
# Zhan's A.1 (R80): the small curve's seed forces read only the stopped records

Packet PROVE-A1-G3ROW (A1-LARGEDENS "What remains" 4). Source: Astra, *Follow-up proofs* §A.1.5
(`ig1_followup_proofs.txt` L409–L425: the rectangle data are functions of the two stopped records), follow-up 5 §1.3
(L203–L222).

A1-LARGEDENS defined the family seed forces `rSeedSnd` (limits of A1-FORCES's masked canonical forces at the
frozen-chart points `I(0) ± 1/(n + 1)`) and proved them jointly measurable (`measurable_rSeedSnd`). `FamilyRect.ofRect`
also asks (`hgVL`/`hgVR`) that, before the cap, each image datum agrees with a function measurable for the stopped
records. For the ordinary marks this is A1-FORCES's `exists_measurable_rForceSnd_of_stopped`; here it is proved for the
seeds:

* `canonForce_eq_pt`: the masked canonical force at a sample reads its point at that sample only;
* **`rSeedSnd_congr`**: two data that agree up to a horizon good for both (and whose clock reaches the time `r`) have
  the same seed forces at `r` — the points `I(0) ± 1/(n + 1)` agree because the canonical image drivers agree on
  `[0, imgClk]` (A1-SEEDGEOM's `imgDrv_congr`), and every approximating force agrees (A1-FORCES's `rForceFst_congr`);
* **`exists_measurable_rSeedSnd_of_stopped`**: hence the seed forces agree on `{r < cap}` with the record-measurable
  seed forces of the stopped replacement data (A1-FORCES's `hloc` form).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Row

open A2X A1Ref A1Marg A1SeedGeom A1Forces A1LargeDens

/-- **The masked canonical force at a sample reads its point at that sample only.** -/
theorem canonForce_eq_pt {Ω : Type*} (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞)
    (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (p : Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    canonForce L xj xk wj ζj wk τ p t ω = canonForce L xj xk wj ζj wk τ (fun _ => p ω) t ω := rfl

section Snd

variable {X Y : Type*}

/-- **Locality of the seed forces** (conditioning curve on `Y`, image curve on `X`): if two data are live at the stop,
continuous and normalized, have a common good horizon `T`, agree up to `T` (image curve) and up to the stop
(conditioning curve), and the clock up to `T` reaches `r`, then their seed forces at `r` agree. -/
theorem rSeedSnd_congr {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → Y → ℝ} {τ : Y → ℝ≥0} {z : X × Y} {T : ℝ} (hlive : live (τ z.2) z.2)
    (hlive' : live' (τ z.2) z.2)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T))
    (hj0 : Wj 0 z.1 = 0)
    (hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.1 → ContinuousOn (Strip.extPath (Wj' · z.1)) (Icc 0 T))
    (hj0' : Wj' 0 z.1 = 0)
    (hk : ∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ'))
    (hk0 : Wk 0 z.2 = 0)
    (hk' : ∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.2)) (Icc 0 τ'))
    (hk0' : Wk' 0 z.2 = 0)
    (hT : IsGoodTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) T)
    (hT' : IsGoodTime xj (Strip.extPath (Wj' · z.1)) (ζj' z.1) xk (Strip.extPath (Wk' · z.2)) (τ z.2) T)
    (hjeq : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Wj' t z.1 = Wj t z.1) (hkeq : ∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2)
    (sgn : ℝ) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) T) :
    rSeedSnd live' xj Wj' ζj' xk Wk' τ sgn r z = rSeedSnd live xj Wj ζj xk Wk τ sgn r z := by
  have hjE : EqOn (Strip.extPath (Wj · z.1)) (Strip.extPath (Wj' · z.1)) (Icc 0 T) := fun s hs => by
    simp only [Strip.extPath]
    rw [hjeq _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)]
  have hkE : EqOn (Strip.extPath (Wk · z.2)) (Strip.extPath (Wk' · z.2)) (Icc 0 (τ z.2)) := fun s hs => by
    simp only [Strip.extPath]
    rw [hkeq _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hj00 : Strip.extPath (Wj · z.1) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hj0]
  have hj00' : Strip.extPath (Wj' · z.1) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hj0']
  have hk00 : Strip.extPath (Wk · z.2) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hk0]
  have hk00' : Strip.extPath (Wk' · z.2) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hk0']
  have hE := imgDrv_congr hj hj00 hj' hj00' hk hk00 hk' hk00' (τ z.2).coe_nonneg hT hT' hjE hkE
  have h0 : (0 : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) T :=
    r.coe_nonneg.trans hr
  -- the approximating points agree
  have hpt : ∀ e : ℝ, seedPt {z : X × Y | live' (τ z.2) z.2} xj xk (fun z t => Wj' t z.1) (fun z => ζj' z.1)
      (fun z t => Wk' t z.2) (fun z => τ z.2) e z = seedPt {z : X × Y | live (τ z.2) z.2} xj xk
      (fun z t => Wj t z.1) (fun z => ζj z.1) (fun z t => Wk t z.2) (fun z => τ z.2) e z := fun e => by
    simp only [seedPt, Set.indicator_of_mem (show z ∈ {z : X × Y | live' (τ z.2) z.2} from hlive'),
      Set.indicator_of_mem (show z ∈ {z : X × Y | live (τ z.2) z.2} from hlive)]
    rw [hE ⟨le_rfl, h0⟩]
  -- every approximating force agrees
  have hn : ∀ n : ℕ, canonForce {z : X × Y | live' (τ z.2) z.2} xj xk (fun z t => Wj' t z.1) (fun z => ζj' z.1)
      (fun z t => Wk' t z.2) (fun z => τ z.2) (seedPt {z : X × Y | live' (τ z.2) z.2} xj xk (fun z t => Wj' t z.1)
        (fun z => ζj' z.1) (fun z t => Wk' t z.2) (fun z => τ z.2) (sgn / ((n : ℝ) + 1))) r z =
      canonForce {z : X × Y | live (τ z.2) z.2} xj xk (fun z t => Wj t z.1) (fun z => ζj z.1)
        (fun z t => Wk t z.2) (fun z => τ z.2) (seedPt {z : X × Y | live (τ z.2) z.2} xj xk (fun z t => Wj t z.1)
          (fun z => ζj z.1) (fun z t => Wk t z.2) (fun z => τ z.2) (sgn / ((n : ℝ) + 1))) r z := fun n => by
    rw [canonForce_eq_pt, canonForce_eq_pt (p := seedPt _ _ _ _ _ _ _ _), hpt]
    exact rForceFst_congr (X := Y) (Y := X) (z := z.swap) (p := fun _ => _) (p' := fun _ => _) hlive hlive' hj hj0
      hj' hj0' hk hk0 hk' hk0' hT hT' hjeq hkeq rfl hr
  show limUnder atTop _ = limUnder atTop _
  exact congrArg _ (funext hn)

/-- **`hgVL` (`hgVR`) of `FamilyRect.ofRect` for the seeds** (conditioning curve on `Y`): with replacement data
`(Wj', ζj')`, `(Wk', ζk')`, `live'` satisfying A1-MARG's (m3) hypotheses (measurable for the records `𝓐`, `𝓑`), `τ`
record-measurable, if on `{r < cap}` the replacements agree with the original data up to a horizon `T z` good for both
whose clock reaches `cap z` (A1-FORCES's `hloc`), then the seed force at `r` agrees there with a record-measurable
function. -/
theorem exists_measurable_rSeedSnd_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y]
    {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞} {Wk Wk' : ℝ≥0 → Y → ℝ}
    {ζk' : Y → ℝ≥0∞} {τ : Y → ℝ≥0} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × Y | live' q.1 q.2}) (hlk : ∀ s y, live' s y → (s : ℝ≥0∞) < ζk' y)
    (hjc : ∀ x, ContinuousOn (Wj' · x) {t | (t : ℝ≥0∞) < ζj' x}) (hj0' : ∀ x, Wj' 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk' · y) {t | (t : ℝ≥0∞) < ζk' y}) (hk0' : ∀ y, Wk' 0 y = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    {cap : X × Y → ℝ≥0} {T : X × Y → ℝ} (sgn : ℝ) (r : ℝ≥0)
    (hloc : ∀ z : X × Y, r < cap z →
      live (τ z.2) z.2 ∧ live' (τ z.2) z.2 ∧
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T)) ∧ Wj 0 z.1 = 0 ∧
      (∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ')) ∧ Wk 0 z.2 = 0 ∧
      IsGoodTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z) ∧
      IsGoodTime xj (Strip.extPath (Wj' · z.1)) (ζj' z.1) xk (Strip.extPath (Wk' · z.2)) (τ z.2) (T z) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T z → Wj' t z.1 = Wj t z.1) ∧ (∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2) ∧
      (cap z : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z)) :
    ∃ f : X × Y → ℝ, Measurable f ∧ ∀ z, r < cap z → rSeedSnd live xj Wj ζj xk Wk τ sgn r z = f z := by
  have hC := canonHyp_of_paths (Ω := X × Y) (πj := Prod.fst) (πk := Prod.snd) (τ := fun z => τ z.2)
    measurable_fst measurable_snd (hτ.comp measurable_snd) hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk
  refine ⟨rSeedSnd live' xj Wj' ζj' xk Wk' τ sgn r, hC.measurable_canonSeed xj xk sgn r, fun z hz => ?_⟩
  obtain ⟨hl, hl', hj, hj0, hk, hk0, hT, hT', hjeq, hkeq, hcap⟩ := hloc z hz
  have hk' : ∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (hkc z.2) (hlk _ _ hl')
  have hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.1 → ContinuousOn (Strip.extPath (Wj' · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (hjc z.1) hT
  exact (rSeedSnd_congr hl hl' hj hj0 hj' (hj0' z.1) hk hk0 hk' (hk0' z.2) hT hT' hjeq hkeq sgn
    ((NNReal.coe_le_coe.2 hz.le).trans hcap)).symm

end Snd

end InteractingSLE.ZhanGT4.A1G3Row
