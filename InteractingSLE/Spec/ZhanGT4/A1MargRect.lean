/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargImg
import InteractingSLE.Spec.ZhanGT4.A1MargLive
import InteractingSLE.Spec.ZhanGT4.A1CoreRect

/-!
# (m1)–(m4) of A.1's rectangle cores for regular marginals on path spaces

Packet PROVE-A1-MARG (R76). The measurability clauses of `A1Core.IsRectImageCore` / `IsRectImageCoreFst`, for the
image curve on `X` and the conditioning curve on `Y` (and the mirror):

* `canonHyp_of_paths`: the standing hypotheses `CanonHyp` of the general measurability theorems (`A1MargImg.lean`)
  for two path families read through measurable maps (the compact hits jointly in the stop:
  `measurableSet_hit_stop`);
* **`measurable_rDrv_rLife`**, **`measurable_rDrvFst_rLifeFst`**: (m3)–(m4) on `ℝ≥0 × (X × Y)`;
* `measurableSet_live_of_isStronglyProgressive`: a progressive live event is jointly measurable in time and sample.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core

section Paths

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]

/-- **The standing hypotheses for two path families read through measurable maps.** -/
theorem canonHyp_of_paths {πj : Ω → X} {πk : Ω → Y} {τ : Ω → ℝ≥0} (hπj : Measurable πj) (hπk : Measurable πk)
    (hτ : Measurable τ) {live : ℝ≥0 → Y → Prop} (hlive : MeasurableSet {q : ℝ≥0 × Y | live q.1 q.2})
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {Wk : ℝ≥0 → Y → ℝ} {ζk : Y → ℝ≥0∞}
    (hlk : ∀ s y, live s y → (s : ℝ≥0∞) < ζk y)
    (hjc : ∀ x, ContinuousOn (Wj · x) {t | (t : ℝ≥0∞) < ζj x}) (hj0 : ∀ x, Wj 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk · y) {t | (t : ℝ≥0∞) < ζk y}) (hk0 : ∀ y, Wk 0 y = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk) :
    CanonHyp {ω | live (τ ω) (πk ω)} (fun ω t => Wj t (πj ω)) (fun ω => ζj (πj ω)) (fun ω t => Wk t (πk ω))
      (fun ω => ζk (πk ω)) τ where
  meas := hlive.preimage (hτ.prodMk hπk)
  life ω h := hlk _ _ h
  contj ω := hjc (πj ω)
  zeroj ω := hj0 (πj ω)
  contk ω := hkc (πk ω)
  zerok ω := hk0 (πk ω)
  measj t := (hjm t).comp hπj
  measζj := hζj.comp hπj
  measτ := hτ
  hitj q K hK hKH := (measurableSet_hit_stop hjc hjm hζj hK hKH).preimage (measurable_const.prodMk hπj)
  hitk K hK hKH := by
    have h := (measurableSet_hit_stop hkc hkm hζk hK hKH).preimage (hτ.prodMk hπk)
    have e : {ω | ω ∈ {ω | live (τ ω) (πk ω)} ∧
        (K ∩ fwdHull (Strip.extPath ((fun ω t => Wk t (πk ω)) ω)) (τ ω)).Nonempty} =
        {ω | live (τ ω) (πk ω)} ∩ ((fun ω => (τ ω, πk ω)) ⁻¹' {q : ℝ≥0 × Y | (q.1 : ℝ≥0∞) < ζk q.2 ∧
          (K ∩ fwdHull (Strip.extPath (Wk · q.2)) q.1).Nonempty}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
      exact ⟨fun h => ⟨h.1, hlk _ _ h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [e]
    exact (hlive.preimage (hτ.prodMk hπk)).inter h

end Paths

section Rect

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **(m3)–(m4), image curve on `X`, conditioning curve on `Y`**: for drivers continuous before their lifetimes and
started at `0` at every sample, with measurable evaluations and lifetimes, and a jointly measurable live event on
which the stop precedes the conditioning curve's lifetime. -/
theorem measurable_rDrv_rLife {live : ℝ≥0 → Y → Prop} (hlive : MeasurableSet {q : ℝ≥0 × Y | live q.1 q.2})
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {Wk : ℝ≥0 → Y → ℝ} {ζk : Y → ℝ≥0∞}
    (hlk : ∀ s y, live s y → (s : ℝ≥0∞) < ζk y)
    (hjc : ∀ x, ContinuousOn (Wj · x) {t | (t : ℝ≥0∞) < ζj x}) (hj0 : ∀ x, Wj 0 x = 0)
    (hkc : ∀ y, ContinuousOn (Wk · y) {t | (t : ℝ≥0∞) < ζk y}) (hk0 : ∀ y, Wk 0 y = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    (xj xk : ℝ) :
    (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
      Measurable fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2 := by
  have hC := canonHyp_of_paths (Ω := ℝ≥0 × (X × Y)) (πj := fun p => p.2.1) (πk := fun p => p.2.2)
    (τ := Prod.fst) measurable_snd.fst measurable_snd.snd measurable_fst hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
  refine ⟨fun t => ?_, ?_⟩
  · have h := hC.measurable_canonImgDrv xj xk t
    convert h using 1
    funext p
    by_cases hp : live p.1 p.2.2
    · rw [indicator_of_mem (show p ∈ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.2} from hp)]
      simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, hp, ↓reduceIte]
    · rw [indicator_of_notMem (show p ∉ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.2} from hp)]
      simp only [rDrv, cImgDrvM, hp, ↓reduceIte]
  · have h := hC.measurable_canonImgLife xj xk
    convert h using 1
    funext p
    by_cases hp : live p.1 p.2.2
    · rw [indicator_of_mem (show p ∈ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.2} from hp)]
      simp only [rLife, cImgLifeM, cImgLife, hp, ↓reduceIte]
    · rw [indicator_of_notMem (show p ∉ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.2} from hp)]
      simp only [rLife, cImgLifeM, hp, ↓reduceIte]

/-- **(m3)–(m4), image curve on `Y`, conditioning curve on `X`** (the mirror). -/
theorem measurable_rDrvFst_rLifeFst {live : ℝ≥0 → X → Prop} (hlive : MeasurableSet {q : ℝ≥0 × X | live q.1 q.2})
    {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {Wk : ℝ≥0 → X → ℝ} {ζk : X → ℝ≥0∞}
    (hlk : ∀ s x, live s x → (s : ℝ≥0∞) < ζk x)
    (hjc : ∀ y, ContinuousOn (Wj · y) {t | (t : ℝ≥0∞) < ζj y}) (hj0 : ∀ y, Wj 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk · x) {t | (t : ℝ≥0∞) < ζk x}) (hk0 : ∀ x, Wk 0 x = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    (xj xk : ℝ) :
    (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
      Measurable fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2 := by
  have hC := canonHyp_of_paths (Ω := ℝ≥0 × (X × Y)) (πj := fun p => p.2.2) (πk := fun p => p.2.1)
    (τ := Prod.fst) measurable_snd.snd measurable_snd.fst measurable_fst hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
  refine ⟨fun t => ?_, ?_⟩
  · have h := hC.measurable_canonImgDrv xj xk t
    convert h using 1
    funext p
    by_cases hp : live p.1 p.2.1
    · rw [indicator_of_mem (show p ∈ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.1} from hp)]
      simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, hp, ↓reduceIte]
    · rw [indicator_of_notMem (show p ∉ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.1} from hp)]
      simp only [rDrvFst, cImgDrvM, hp, ↓reduceIte]
  · have h := hC.measurable_canonImgLife xj xk
    convert h using 1
    funext p
    by_cases hp : live p.1 p.2.1
    · rw [indicator_of_mem (show p ∈ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.1} from hp)]
      simp only [rLifeFst, cImgLifeM, cImgLife, hp, ↓reduceIte]
    · rw [indicator_of_notMem (show p ∉ {ω : ℝ≥0 × (X × Y) | live ω.1 ω.2.1} from hp)]
      simp only [rLifeFst, cImgLifeM, hp, ↓reduceIte]

end Rect

end InteractingSLE.ZhanGT4.A1Marg
