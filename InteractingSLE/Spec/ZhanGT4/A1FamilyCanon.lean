/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FamilyRect
import InteractingSLE.Spec.ZhanGT4.DualSeedEndCanonical
import InteractingSLE.Spec.ZhanGT4.A1MargClock

/-!
# A.1's seeded frozen-sample families, IV: the canonical image is the seeded capacity image

Packet PROVE-A1-FAMILY (R76). A22's `seedCapacityDriver_eq_canonical` identifies the seeded capacity-time driver
with the canonical image driver `A1Ref.imgDrv` in the frame of the image curve (started at `0`). This file
translates it (A1-MARG's `imgClk_sub`, `isGoodTime_sub`, `isImgDrvOn_add`) to an arbitrary start `xj` and restates it
for the masked canonical image of the families at a deterministic frozen time `σ` on a live frozen sample, which
discharges the driver and lifetime premises of `isSeedSampleLaw_of_seed`:

* **`seedCapacityHorizon_le_imgLife`**: the capacity horizon of seeded data whose own horizon is a good (pre-contact)
  time is at most the canonical image lifetime;
* **`imgDrv_sub_eq_seedCapacityDriver`**: up to the capacity horizon, the centred canonical image driver of the image
  curve started at `xj` is the seeded capacity driver (seeded data in the image curve's frame);
* **`rDrv_eq_seedCapacityDriver`**, **`rLife_ge_seedCapacityHorizon`** (image curve on `X`, conditioning sample `y`
  live at `σ`) and the mirrors **`rDrvFst_eq_seedCapacityDriver`**, **`rLifeFst_ge_seedCapacityHorizon`** (image
  curve on `Y`): up to the capacity horizon the masked canonical image driver is the seeded capacity driver, and the
  horizon precedes the masked canonical lifetime;
* `isStronglyProgressive_stopped_sub`, **`isStronglyProgressive_seedDriver`**, `isStronglyProgressive_seedForce`: the
  progressive own-time coordinates required by `isSeedSampleLaw_of_seed`, from continuity and adaptedness.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Family

open A1Canon A1Ref A1Core A1Frozen

section Canon

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}

/-- **The capacity horizon precedes the canonical image lifetime** (any image start `xj`; the seeded data live in the
frame of the image curve, where the conditioning curve starts at `xk − xj`) when the own horizon is a good time. -/
theorem seedCapacityHorizon_le_imgLife {xj xk : ℝ} {ζ : Ω → ℝ≥0∞} {wk : ℝ → ℝ} {τ : ℝ} {ω : Ω}
    (hown : OwnData (d ω).W (A2X.physHull (xk - xj) wk τ) (A2X.physMap (xk - xj) wk τ) (S ω) (d ω).a (d ω).W')
    (hgood : A1Ref.IsGoodTime 0 (d ω).W (ζ ω) (xk - xj) wk τ (S ω)) :
    (seedCapacityHorizon d S ω : ℝ≥0∞) ≤ A1Ref.imgLife xj (d ω).W (ζ ω) xk wk τ := by
  have hEq := (isImgDrvOn_of_ownData hown).2 ⟨(S ω).coe_nonneg, le_rfl⟩
  rw [A1Marg.imgLife_sub]
  unfold seedCapacityHorizon A1Ref.imgLife
  refine le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : (s : ℝ≥0∞) < A2X.contactTime 0 (d ω).W (ζ ω) (xk - xj) wk τ) =>
    ENNReal.ofReal (A1Ref.imgClk 0 (d ω).W (xk - xj) wk τ s)) (S ω) ?_ ?_
  · have h := hgood.2
    rwa [ENNReal.ofReal_coe_nnreal] at h
  · rw [hEq]
    rfl

/-- **The centred canonical image driver is the seeded capacity driver up to the capacity horizon** (any image start
`xj`: the canonical image of the image curve started at `xj` is the translate of the one in its own frame, whose image
driver is the seeded data's `W'`). -/
theorem imgDrv_sub_eq_seedCapacityDriver {xj xk : ℝ} {ζ : Ω → ℝ≥0∞} {wk : ℝ → ℝ} {τ : ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A2X.physHull (xk - xj) wk τ) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hφ : ∀ ω, (d ω).φ = A2X.physMap (xk - xj) wk τ)
    (hj : ∀ ω T, ENNReal.ofReal T < ζ ω → ContinuousOn (d ω).W (Icc 0 T))
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hgood : ∀ ω, A1Ref.IsGoodTime 0 (d ω).W (ζ ω) (xk - xj) wk τ (S ω))
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r) (ω : Ω) {u : ℝ≥0}
    (hu : u ≤ seedCapacityHorizon d S ω) :
    A1Ref.imgDrv xj (d ω).W (ζ ω) xk wk τ u - A1Ref.imgDrv xj (d ω).W (ζ ω) xk wk τ 0 =
      seedCapacityDriver d S u ω := by
  have hown' : OwnData (d ω).W (A2X.physHull (xk - xj) wk τ) (A2X.physMap (xk - xj) wk τ) (S ω) (d ω).a
      (d ω).W' := by
    rw [← hφ ω]
    exact hown ω
  have hS0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn ⟨le_rfl, (hown ω).pos.le⟩ ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  have hua : (u : ℝ) ≤ (d ω).a (S ω) := by
    have h : (u : ℝ) ≤ (seedCapacityHorizon d S ω : ℝ) := hu
    rwa [seedCapacityHorizon, Real.coe_toNNReal _ hS0] at h
  obtain ⟨hW', hEq⟩ := isImgDrvOn_of_ownData hown'
  have hcl : A1Ref.imgClk xj (d ω).W xk wk τ (S ω) = (d ω).a (S ω) := by
    rw [A1Marg.imgClk_sub, ← hEq ⟨(S ω).coe_nonneg, le_rfl⟩]
  have heq := A1Ref.imgDrv_eqOn (hj ω) (hown ω).zero hk hk0 hτ (A1Marg.isGoodTime_sub.2 (hgood ω))
    (A1Marg.isImgDrvOn_add hW')
  rw [hcl] at heq
  rw [heq ⟨u.coe_nonneg, hua⟩, heq ⟨le_rfl, hS0⟩, seedCapacityDriver_eq_canonical (ζ := ζ)
    (xk := fun _ => xk - xj) (wk := fun _ => wk) (τ := fun _ => τ) hown hφ hj (fun _ => hk) (fun _ => hk0)
    (fun _ => hτ) hgood hCc hCs hc hClb ω u, min_eq_left hua]
  have h0 := A1Ref.imgDrv_eqOn_of_ownData (hj ω) (hown ω).zero hk hk0 hτ (hgood ω) hown'
  rw [h0 ⟨u.coe_nonneg, hua⟩, h0 ⟨le_rfl, hS0⟩]
  ring

variable {X Y : Type*}

/-- **The masked canonical image driver is the seeded capacity driver up to the capacity horizon** (image curve on
`X` started at `xj`, conditioning sample `y` live at the frozen time `σ`; seeded data in the frame of the image
curve). -/
theorem rDrv_eq_seedCapacityDriver {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {σ : ℝ≥0} {y : Y} (hlive : live σ y) {d : X → SeedData n} {S : X → ℝ≥0}
    (hW : ∀ x, (d x).W = Strip.extPath (Wj · x))
    (hown : ∀ x, OwnData (d x).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · y)) σ) (d x).φ (S x) (d x).a
      (d x).W')
    (hφ : ∀ x, (d x).φ = A2X.physMap (xk - xj) (Strip.extPath (Wk · y)) σ)
    (hj : ∀ x T, ENNReal.ofReal T < ζj x → ContinuousOn (d x).W (Icc 0 T))
    (hk : ∃ τ', (σ : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · y)) (Icc 0 τ')) (hk0 : Wk 0 y = 0)
    (hgood : ∀ x, A1Ref.IsGoodTime 0 (d x).W (ζj x) (xk - xj) (Strip.extPath (Wk · y)) σ (S x))
    (hCc : ∀ x, Continuous (seedQuadClock (seedCapacityCoeff d S) x))
    (hCs : ∀ x, StrictMono (seedQuadClock (seedCapacityCoeff d S) x)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ x r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) x r) (x : X) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon d S x) :
    rDrv live xj Wj ζj xk Wk (fun _ => σ) t (x, y) = seedCapacityDriver d S t x := by
  rw [← imgDrv_sub_eq_seedCapacityDriver hown hφ hj hk (extPath_zero_of hk0) σ.coe_nonneg hgood hCc hCs hc hClb x
    ht]
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive, hW]

/-- **The capacity horizon precedes the masked canonical image lifetime** (image curve on `X` started at `xj`,
conditioning sample `y` live at `σ`). -/
theorem rLife_ge_seedCapacityHorizon {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {σ : ℝ≥0} {y : Y} (hlive : live σ y) {d : X → SeedData n} {S : X → ℝ≥0}
    (hW : ∀ x, (d x).W = Strip.extPath (Wj · x))
    (hown : ∀ x, OwnData (d x).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · y)) σ)
      (A2X.physMap (xk - xj) (Strip.extPath (Wk · y)) σ) (S x) (d x).a (d x).W')
    (hgood : ∀ x, A1Ref.IsGoodTime 0 (d x).W (ζj x) (xk - xj) (Strip.extPath (Wk · y)) σ (S x)) (x : X) :
    (seedCapacityHorizon d S x : ℝ≥0∞) ≤ rLife live xj Wj ζj xk Wk (fun _ => σ) (x, y) := by
  have h := seedCapacityHorizon_le_imgLife (ζ := ζj) (hown x) (hgood x)
  simp only [rLife, cImgLifeM, cImgLife, ite_eq_left hlive]
  rwa [hW] at h

/-- **The masked canonical image driver is the seeded capacity driver up to the capacity horizon** (mirror: image
curve on `Y` started at `xj`, conditioning sample `x` live at `σ`). -/
theorem rDrvFst_eq_seedCapacityDriver {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {σ : ℝ≥0} {x : X} (hlive : live σ x) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · x)) σ) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = A2X.physMap (xk - xj) (Strip.extPath (Wk · x)) σ)
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hk : ∃ τ', (σ : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ')) (hk0 : Wk 0 x = 0)
    (hgood : ∀ y, A1Ref.IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (Wk · x)) σ (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon d S y) :
    rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t (x, y) = seedCapacityDriver d S t y := by
  rw [← imgDrv_sub_eq_seedCapacityDriver hown hφ hj hk (extPath_zero_of hk0) σ.coe_nonneg hgood hCc hCs hc hClb y
    ht]
  simp only [rDrvFst, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive, hW]

/-- **The capacity horizon precedes the masked canonical image lifetime** (mirror). -/
theorem rLifeFst_ge_seedCapacityHorizon {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {σ : ℝ≥0} {x : X} (hlive : live σ x) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (A2X.physHull (xk - xj) (Strip.extPath (Wk · x)) σ)
      (A2X.physMap (xk - xj) (Strip.extPath (Wk · x)) σ) (S y) (d y).a (d y).W')
    (hgood : ∀ y, A1Ref.IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (Wk · x)) σ (S y)) (y : Y) :
    (seedCapacityHorizon d S y : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk (fun _ => σ) (x, y) := by
  have h := seedCapacityHorizon_le_imgLife (ζ := ζj) (hown y) (hgood y)
  simp only [rLifeFst, cImgLifeM, cImgLife, ite_eq_left hlive]
  rwa [hW] at h

end Canon

/-! ### Progressive own-time image coordinates -/

section Progressive

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {d : Ω → SeedData n}
  {S : Ω → ℝ≥0}

/-- A continuous `𝓕`-adapted own-time coordinate stopped at the own horizon and centred at its start is progressive
(the form of the premises `hWp`, `hVp` of `isSeedSampleLaw_of_seed`). -/
theorem isStronglyProgressive_stopped_sub {f : Ω → ℝ → ℝ} (hc : ∀ ω, ContinuousOn (f ω) (Icc 0 (S ω)))
    (ha : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => f ω ((min u (S ω) : ℝ≥0) : ℝ)) (g : Ω → ℝ)
    (hg : Measurable[𝓕 0] g) :
    IsStronglyProgressive 𝓕 fun u ω => f ω ((min u (S ω) : ℝ≥0) : ℝ) - g ω := by
  refine StronglyAdapted.isStronglyProgressive_of_continuous (fun u => ?_) fun ω => ?_
  · exact ((ha u).sub (hg.mono (𝓕.mono zero_le) le_rfl)).stronglyMeasurable
  · have ht : Continuous (fun u : ℝ≥0 => ((min u (S ω) : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    have hm : ∀ u : ℝ≥0, ((min u (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
      fun u => ⟨(min u (S ω)).coe_nonneg, min_le_right _ _⟩
    exact ((hc ω).comp_continuous ht hm).sub continuous_const

/-- **The own-time image driver premise `hWp` of `isSeedSampleLaw_of_seed`** from `OwnData` (continuity) and the
adaptedness of the stopped driver. -/
theorem isStronglyProgressive_seedDriver {A : Ω → Set ℂ}
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (ha : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ)) :
    IsStronglyProgressive 𝓕 fun u ω => (d ω).A 0 ((min u (S ω) : ℝ≥0) : ℝ) - (d ω).A 0 0 := by
  have h0 : (fun ω => (d ω).A 0 0) = fun ω => (d ω).A 0 ((min 0 (S ω) : ℝ≥0) : ℝ) := by
    funext ω
    simp only [zero_min, NNReal.coe_zero]
  refine isStronglyProgressive_stopped_sub (f := fun ω => (d ω).A 0) (fun ω => (hown ω).continuousOn_frzA 0) ha _ ?_
  rw [h0]
  exact ha 0

/-- **The own-time image force premise `hVp` of `isSeedSampleLaw_of_seed`** from the continuity of the image force
on the own interval and the adaptedness of the stopped force and of the starting driver value. -/
theorem isStronglyProgressive_seedForce (i : Fin (n + 1))
    (hc : ∀ ω, ContinuousOn (fun t => (d ω).imageForce t i) (Icc 0 (S ω)))
    (ha : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => (d ω).imageForce ((min u (S ω) : ℝ≥0) : ℝ) i)
    (h0 : Measurable[𝓕 0] fun ω => (d ω).A 0 0) :
    IsStronglyProgressive 𝓕 fun u ω => (d ω).imageForce ((min u (S ω) : ℝ≥0) : ℝ) i - (d ω).A 0 0 :=
  isStronglyProgressive_stopped_sub (f := fun ω t => (d ω).imageForce t i) hc ha _ h0

end Progressive

end InteractingSLE.ZhanGT4.A1Family
