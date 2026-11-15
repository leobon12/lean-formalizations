/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargRect
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Zhan's A.1 (R80): locality of the canonical image, and its stopped-record measurability before the cap

Packet PROVE-A1-SEEDGEOM. `A1Family.FamilyRect.ofRect` asks (premise `hgW`), for every rectangle `m` and image time
`r`, for a function `f` on `X × Y`, measurable for the product `𝓐 m ⊗ 𝓑' m` of the two stopped records, equal to the
masked canonical image driver at `r` on `{r < cap}`. This is the Galmarino-type locality A1-FAMILY asked for
("the canonical image in the two stopped records").

* **Locality** (deterministic): the canonical clock and image driver read the image curve's driver only up to a good
  horizon `T` and the conditioning curve's driver only up to its frozen time `τ` (`imgClk_congr`, **`imgDrv_congr`**).
  The proof transports one image driver on `T` (A1Ref's `exists_isImgDrvOn`) to the second pair of drivers and uses
  uniqueness (`imgDrv_eqOn`) on both sides.
* **Before the cap** (`rDrv_congr`): the masked canonical image driver on `X × Y` at a stop is unchanged when both
  drivers are replaced by versions agreeing up to a good horizon of the image curve and up to the stop, at image times
  up to the clock of that horizon.
* **Record measurability** (**`exists_measurable_rDrv_of_stopped`**): if such replacement drivers (e.g. the two curves
  stopped at their rectangle exit and at the stop) are measurable for the records `𝓐`, `𝓑'`, A1-MARG's joint
  measurability (m3) (`A1Marg.measurable_rDrv_rLife`, run with the record σ-algebras as the measurable structures)
  gives `hgW` exactly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1SeedGeom

open A2X A1Ref A1Core

/-! ### Deterministic locality of the canonical image -/

section Det

/-- **The hull at `t` reads the driver on `[0, t]`** when both drivers are continuous slightly beyond `t`. -/
theorem physHull_congr_of_continuousOn {x : ℝ} {w w' : ℝ → ℝ} {t T' : ℝ} (hw : ContinuousOn w (Icc 0 T'))
    (hw' : ContinuousOn w' (Icc 0 T')) (ht : 0 ≤ t) (htT : t < T') (h : EqOn w w' (Icc 0 t)) :
    physHull x w t = physHull x w' t := by
  rw [physHull_eq_fwdHull, physHull_eq_fwdHull]
  exact LocalExt.fwdHull_congr_of_continuousOn (hw.add continuousOn_const) (hw'.add continuousOn_const) ht htT
    fun s hs => by simp only [h hs]

/-- **The canonical clock is local**: at `t` it reads curve `j`'s driver on `[0, t]` (both drivers continuous slightly
beyond `t`) and curve `k`'s driver on `[0, τ]`. -/
theorem imgClk_congr {xj xk τ t T' : ℝ} {wj wj' wk wk' : ℝ → ℝ} (hτ : 0 ≤ τ) (hkeq : EqOn wk wk' (Icc 0 τ))
    (hw : ContinuousOn wj (Icc 0 T')) (hw' : ContinuousOn wj' (Icc 0 T')) (htT : t < T')
    (hjeq : EqOn wj wj' (Icc 0 t)) : imgClk xj wj xk wk τ t = imgClk xj wj' xk wk' τ t := by
  unfold imgClk
  split_ifs with ht
  · rw [physMap_congr hτ hkeq, physHull_congr_of_continuousOn hw hw' ht.le htT hjeq]
  · rfl

/-- A good horizon leaves room for continuity slightly beyond it. -/
theorem exists_continuousOn_beyond_of_isGoodTime {xj xk τ T : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hT : IsGoodTime xj wj ζj xk wk τ T) :
    ∃ T', T < T' ∧ ContinuousOn wj (Icc 0 T') := by
  obtain ⟨T', hT', hTT'⟩ := exists_isGoodTime hT.1.le hT.2
  exact ⟨T', hTT', hj T' (hT'.2.trans_le contactTime_le)⟩

/-- **The canonical image driver is local**: if curve `j`'s two drivers agree on `[0, T]` with `T` good for both,
and curve `k`'s two drivers agree on `[0, τ]`, the two canonical image drivers agree on `[0, imgClk T]`. -/
theorem imgDrv_congr {xj xk τ T : ℝ} {wj wj' wk wk' : ℝ → ℝ} {ζj ζj' : ℝ≥0∞}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' → ContinuousOn wj' (Icc 0 T)) (hj0' : wj' 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0)
    (hk' : ∃ τ', τ < τ' ∧ ContinuousOn wk' (Icc 0 τ')) (hk0' : wk' 0 = 0) (hτ : 0 ≤ τ)
    (hT : IsGoodTime xj wj ζj xk wk τ T) (hT' : IsGoodTime xj wj' ζj' xk wk' τ T)
    (hjeq : EqOn wj wj' (Icc 0 T)) (hkeq : EqOn wk wk' (Icc 0 τ)) :
    EqOn (imgDrv xj wj ζj xk wk τ) (imgDrv xj wj' ζj' xk wk' τ) (Icc 0 (imgClk xj wj xk wk τ T)) := by
  obtain ⟨T₁, hT₁, hc₁⟩ := exists_continuousOn_beyond_of_isGoodTime hj hT
  obtain ⟨T₂, hT₂, hc₂⟩ := exists_continuousOn_beyond_of_isGoodTime hj' hT'
  have hcm₁ : ContinuousOn wj (Icc 0 (min T₁ T₂)) := hc₁.mono (Icc_subset_Icc_right (min_le_left _ _))
  have hcm₂ : ContinuousOn wj' (Icc 0 (min T₁ T₂)) := hc₂.mono (Icc_subset_Icc_right (min_le_right _ _))
  have hTm : T < min T₁ T₂ := lt_min hT₁ hT₂
  have hclk (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : imgClk xj wj xk wk τ t = imgClk xj wj' xk wk' τ t :=
    imgClk_congr hτ hkeq hcm₁ hcm₂ (ht.2.trans_lt hTm) (hjeq.mono (Icc_subset_Icc_right ht.2))
  have hhull (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : physHull xj wj t = physHull xj wj' t :=
    physHull_congr_of_continuousOn hcm₁ hcm₂ ht.1 (ht.2.trans_lt hTm) (hjeq.mono (Icc_subset_Icc_right ht.2))
  have hmap : physMap xk wk τ = physMap xk wk' τ := physMap_congr hτ hkeq
  obtain ⟨⟨W', hW'⟩, -, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
  have hW'' : IsImgDrvOn xj wj' xk wk' τ T W' := by
    refine ⟨hW'.1, ?_, fun t ht => ?_⟩
    · rw [← hmap]; exact hW'.2.1
    · rw [← hclk t ht, ← hmap, ← hhull t ht]; exact hW'.2.2 t ht
  have e₁ := imgDrv_eqOn hj hj0 hk hk0 hτ hT hW'
  have e₂ := imgDrv_eqOn hj' hj0' hk' hk0' hτ hT' hW''
  rw [← hclk T ⟨hT.1.le, le_rfl⟩] at e₂
  exact fun σ hσ => (e₁ hσ).trans (e₂ hσ).symm

end Det

/-! ### The masked canonical image driver before the cap -/

section Prod

variable {X Y : Type*}

/-- **The masked canonical image driver is unchanged by replacements agreeing before a good horizon** (image curve on
`X`, conditioning curve on `Y`, stop `τ`): at a live sample `z`, if the image curve's drivers agree up to `T`, good for
both, and the conditioning curve's drivers agree up to `τ z.2`, the two masked canonical image drivers agree at every
image time up to the clock of `T`. The live events may differ away from the stop. -/
theorem rDrv_congr {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞}
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
    (hjeq : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Wj' t z.1 = Wj t z.1) (hkeq : ∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) T) :
    rDrv live' xj Wj' ζj' xk Wk' τ r z = rDrv live xj Wj ζj xk Wk τ r z := by
  have hjE : EqOn (Strip.extPath (Wj · z.1)) (Strip.extPath (Wj' · z.1)) (Icc 0 T) := fun s hs => by
    simp only [Strip.extPath]
    rw [hjeq _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)]
  have hkE : EqOn (Strip.extPath (Wk · z.2)) (Strip.extPath (Wk' · z.2)) (Icc 0 (τ z.2)) := fun s hs => by
    simp only [Strip.extPath]
    rw [hkeq _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hE := imgDrv_congr hj (by simp only [Strip.extPath, Real.toNNReal_zero, hj0]) hj'
    (by simp only [Strip.extPath, Real.toNNReal_zero, hj0']) hk (by simp only [Strip.extPath, Real.toNNReal_zero, hk0])
    hk' (by simp only [Strip.extPath, Real.toNNReal_zero, hk0']) (τ z.2).coe_nonneg hT hT' hjE hkE
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) T) :=
    ⟨le_rfl, r.coe_nonneg.trans hr⟩
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive, ite_eq_left hlive']
  rw [hE ⟨r.coe_nonneg, hr⟩, hE h0]

/-- **`hgW` of `FamilyRect.ofRect` from stopped versions measurable for the records.** Let `𝓐` on `X` and `𝓑` on `Y`
be the records (as measurable structures), and `(Wj', ζj')`, `(Wk', ζk')`, `live'` replacement data satisfying
A1-MARG's (m3) hypotheses for them (continuity before the lifetimes, zero starts, measurable evaluations and
lifetimes, a jointly measurable live event inside the conditioning lifetime) with `τ` record-measurable. If on
`{r < cap}` the sample is live for both live events and the replacements agree with the original drivers up to a horizon
`T z`, good for both, whose clock reaches `cap z`, then the masked canonical image driver at `r` agrees on `{r < cap}`
with a record-measurable function. -/
theorem exists_measurable_rDrv_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y]
    {live live' : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → X → ℝ} {ζj ζj' : X → ℝ≥0∞} {Wk Wk' : ℝ≥0 → Y → ℝ}
    {ζk' : Y → ℝ≥0∞} {τ : Y → ℝ≥0} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × Y | live' q.1 q.2}) (hlk : ∀ s y, live' s y → (s : ℝ≥0∞) < ζk' y)
    (hjc : ∀ x, ContinuousOn (Wj' · x) {t | (t : ℝ≥0∞) < ζj' x}) (hj0' : ∀ x, Wj' 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk' · y) {t | (t : ℝ≥0∞) < ζk' y}) (hk0' : ∀ y, Wk' 0 y = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    {cap : X × Y → ℝ≥0} {T : X × Y → ℝ} (r : ℝ≥0)
    (hloc : ∀ z : X × Y, r < cap z →
      live (τ z.2) z.2 ∧ live' (τ z.2) z.2 ∧
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.1 → ContinuousOn (Strip.extPath (Wj · z.1)) (Icc 0 T)) ∧ Wj 0 z.1 = 0 ∧
      (∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.2)) (Icc 0 τ')) ∧ Wk 0 z.2 = 0 ∧
      IsGoodTime xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z) ∧
      IsGoodTime xj (Strip.extPath (Wj' · z.1)) (ζj' z.1) xk (Strip.extPath (Wk' · z.2)) (τ z.2) (T z) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T z → Wj' t z.1 = Wj t z.1) ∧ (∀ t ≤ τ z.2, Wk' t z.2 = Wk t z.2) ∧
      (cap z : ℝ) ≤ imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) (T z)) :
    ∃ f : X × Y → ℝ, Measurable f ∧ ∀ z, r < cap z → rDrv live xj Wj ζj xk Wk τ r z = f z := by
  have hm := (A1Marg.measurable_rDrv_rLife hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk xj xk).1 r
  refine ⟨fun z => rDrv live' xj Wj' ζj' xk Wk' (fun _ => τ z.2) r z,
    hm.comp ((hτ.comp measurable_snd).prodMk measurable_id), fun z hz => ?_⟩
  obtain ⟨hl, hl', hj, hj0, hk, hk0, hT, hT', hjeq, hkeq, hcap⟩ := hloc z hz
  have hk' : ∃ τ', ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (hkc z.2) (hlk _ _ hl')
  have hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.1 → ContinuousOn (Strip.extPath (Wj' · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (hjc z.1) hT
  show _ = rDrv live' xj Wj' ζj' xk Wk' τ r z
  exact (rDrv_congr hl hl' hj hj0 hj' (hj0' z.1) hk hk0 hk' (hk0' z.2) hT hT' hjeq hkeq
    ((NNReal.coe_le_coe.2 hz.le).trans hcap)).symm

/-- **Mirror of `rDrv_congr`** (image curve on `Y`, conditioning curve on `X`). -/
theorem rDrvFst_congr {live live' : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → Y → ℝ} {ζj ζj' : Y → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {z : X × Y} {T : ℝ} (hlive : live (τ z.1) z.1)
    (hlive' : live' (τ z.1) z.1)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T))
    (hj0 : Wj 0 z.2 = 0)
    (hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.2 → ContinuousOn (Strip.extPath (Wj' · z.2)) (Icc 0 T))
    (hj0' : Wj' 0 z.2 = 0)
    (hk : ∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ'))
    (hk0 : Wk 0 z.1 = 0)
    (hk' : ∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.1)) (Icc 0 τ'))
    (hk0' : Wk' 0 z.1 = 0)
    (hT : IsGoodTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) T)
    (hT' : IsGoodTime xj (Strip.extPath (Wj' · z.2)) (ζj' z.2) xk (Strip.extPath (Wk' · z.1)) (τ z.1) T)
    (hjeq : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Wj' t z.2 = Wj t z.2) (hkeq : ∀ t ≤ τ z.1, Wk' t z.1 = Wk t z.1) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) T) :
    rDrvFst live' xj Wj' ζj' xk Wk' τ r z = rDrvFst live xj Wj ζj xk Wk τ r z := by
  have hjE : EqOn (Strip.extPath (Wj · z.2)) (Strip.extPath (Wj' · z.2)) (Icc 0 T) := fun s hs => by
    simp only [Strip.extPath]
    rw [hjeq _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)]
  have hkE : EqOn (Strip.extPath (Wk · z.1)) (Strip.extPath (Wk' · z.1)) (Icc 0 (τ z.1)) := fun s hs => by
    simp only [Strip.extPath]
    rw [hkeq _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hE := imgDrv_congr hj (by simp only [Strip.extPath, Real.toNNReal_zero, hj0]) hj'
    (by simp only [Strip.extPath, Real.toNNReal_zero, hj0']) hk (by simp only [Strip.extPath, Real.toNNReal_zero, hk0])
    hk' (by simp only [Strip.extPath, Real.toNNReal_zero, hk0']) (τ z.1).coe_nonneg hT hT' hjE hkE
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) T) :=
    ⟨le_rfl, r.coe_nonneg.trans hr⟩
  simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive, ite_eq_left hlive']
  rw [hE ⟨r.coe_nonneg, hr⟩, hE h0]

/-- **Mirror of `exists_measurable_rDrv_of_stopped`** (image curve on `Y`, conditioning curve on `X`): `hgW` of
`FamilyRectFst.ofRect`. -/
theorem exists_measurable_rDrvFst_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y]
    {live live' : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → Y → ℝ} {ζj ζj' : Y → ℝ≥0∞} {Wk Wk' : ℝ≥0 → X → ℝ}
    {ζk' : X → ℝ≥0∞} {τ : X → ℝ≥0} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × X | live' q.1 q.2}) (hlk : ∀ s x, live' s x → (s : ℝ≥0∞) < ζk' x)
    (hjc : ∀ y, ContinuousOn (Wj' · y) {t | (t : ℝ≥0∞) < ζj' y}) (hj0' : ∀ y, Wj' 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk' · x) {t | (t : ℝ≥0∞) < ζk' x}) (hk0' : ∀ x, Wk' 0 x = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    {cap : X × Y → ℝ≥0} {T : X × Y → ℝ} (r : ℝ≥0)
    (hloc : ∀ z : X × Y, r < cap z →
      live (τ z.1) z.1 ∧ live' (τ z.1) z.1 ∧
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T)) ∧ Wj 0 z.2 = 0 ∧
      (∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ')) ∧ Wk 0 z.1 = 0 ∧
      IsGoodTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z) ∧
      IsGoodTime xj (Strip.extPath (Wj' · z.2)) (ζj' z.2) xk (Strip.extPath (Wk' · z.1)) (τ z.1) (T z) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T z → Wj' t z.2 = Wj t z.2) ∧ (∀ t ≤ τ z.1, Wk' t z.1 = Wk t z.1) ∧
      (cap z : ℝ) ≤ imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z)) :
    ∃ f : X × Y → ℝ, Measurable f ∧ ∀ z, r < cap z → rDrvFst live xj Wj ζj xk Wk τ r z = f z := by
  have hm := (A1Marg.measurable_rDrvFst_rLifeFst hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk xj xk).1 r
  refine ⟨fun z => rDrvFst live' xj Wj' ζj' xk Wk' (fun _ => τ z.1) r z,
    hm.comp ((hτ.comp measurable_fst).prodMk measurable_id), fun z hz => ?_⟩
  obtain ⟨hl, hl', hj, hj0, hk, hk0, hT, hT', hjeq, hkeq, hcap⟩ := hloc z hz
  have hk' : ∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.1)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (hkc z.1) (hlk _ _ hl')
  have hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.2 → ContinuousOn (Strip.extPath (Wj' · z.2)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (hjc z.2) hT
  show _ = rDrvFst live' xj Wj' ζj' xk Wk' τ r z
  exact (rDrvFst_congr hl hl' hj hj0 hj' (hj0' z.2) hk hk0 hk' (hk0' z.1) hT hT' hjeq hkeq
    ((NNReal.coe_le_coe.2 hz.le).trans hcap)).symm

end Prod

/-! ### Stopped processes are measurable for the stopped σ-algebra -/

section Stopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A progressive process stopped at a stopping time is measurable for the stopped σ-algebra** at every time: the
record of the curve stopped at `S` (for instance its rectangle exit) sees `t ↦ u (t ∧ S)`. -/
theorem measurable_stopped_at {u : ℝ≥0 → Ω → ℝ} (hu : IsStronglyProgressive 𝓕 u) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[hS.measurableSpace] fun ω => u (min t (S ω)) ω := by
  have hτ := hS.min_const t
  have hm := measurable_stoppedValue hu hτ
  have hle := hτ.measurableSpace_mono hS fun ω => min_le_left _ _
  have e : stoppedValue u (fun ω => min ((S ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0)) =
      fun ω => u (min t (S ω)) ω := by
    funext ω
    simp only [stoppedValue, ← WithTop.coe_min, min_comm]
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [e] at hm
  exact hm.mono hle le_rfl

end Stopped

end InteractingSLE.ZhanGT4.A1SeedGeom
