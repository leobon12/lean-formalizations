/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomFamily

/-!
# Zhan's A.1 (R80): seeded data with several marks fixed in the frozen chart

Packet PROVE-A1-MULTIMARK. A22's `SeedData` carries exactly one real point of the frozen chart, the other tip `ζ₀`;
its image force is `A20 = frzImg W' a ζ₀` and every other image force is the image `B0 = F_t(V^m_t)` of an own-chart
mark. In the large-curve direction of A.1 (image curve: the large curve, conditioning curve: the small curve stopped
at `τ`) every image mark is a real point of the frozen chart: the image of `x`, the two sides `y^±` of the small
curve's seed and its tip (`A1SeedGeom` handoff, "What remains" (a)). Here the seeded image calculus is extended to any
finite family of frozen-chart marks, and to image forces given by any own-time processes:

* `withTip s ζ`: `s` with its frozen-chart mark replaced by `ζ`; every capacity-time quantity of A22 that does not
  read the mark is unchanged (`seedCapacityDriver_withTip`, by `rfl`), so A22's other-tip results apply to each mark;
* `ownImageEq_frozen`, `continuousOn_frzImg`, `frzImg_zero`, `frzImg_lt_A0`, `A0_lt_frzImg`: the own-time image
  equation, continuity, initial value and positive-time side of a frozen-chart mark;
* `capForce d S X`: the capacity coordinate of an own-time image force `X` (A22's `seedCapacityForce` is the case
  `X = imageForce · k`, `seedCapacityForce_eq_capForce`); `capForce_integrated`, `continuous_capForce`,
  `capForce_lt_driver`, `driver_lt_capForce`;
* **`seedImageGeometry_capForce`**: `SeedImageGeometry` of the seeded capacity driver and the capacity coordinates of
  any families of own-time image forces (left and right), for an admissible initial word;
* **`seedImageGeometry_frozenLeft`**: the case of a word made of frozen-chart marks left of the image start only (the
  large-curve direction of A.1), from the forward solutions and protected gaps of the marks.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1MultiMark

open A1SeedGeom Sec2

/-! ### One frozen-chart mark at a time -/

section Own

variable {n : ℕ} (s : SeedData n) {T : ℝ}

/-- The seeded data `s` with its frozen-chart mark (the other tip `ζ₀`) replaced by the real point `ζ` of the frozen
chart. Only `A20`, `A21` and the densities read the mark. -/
def withTip (ζ : ℝ) : SeedData n := { s with ζ₀ := ζ }

theorem withTip_A20 (ζ t : ℝ) : (withTip s ζ).A20 t = frzImg s.W' s.a ζ t := rfl

theorem withTip_A (ζ : ℝ) (k : ℕ) (t : ℝ) : (withTip s ζ).A k t = s.A k t := rfl

/-- **The own-time image equation of a frozen-chart mark** `ζ` from its forward solution up to `a(T)` and its
protected gap (A22's `SeedData.integrated_other_tip` for `withTip s ζ`). -/
theorem ownImageEq_frozen {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {ζ : ℝ} {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol s.W' ζ (s.a T) v) (hne : ∀ u ∈ Icc (0 : ℝ) T, frzImg s.W' s.a ζ u ≠ s.A 0 u) :
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (frzImg s.W' s.a ζ u - s.A 0 u)) volume 0 t ∧
        frzImg s.W' s.a ζ t = frzImg s.W' s.a ζ 0 +
          ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (frzImg s.W' s.a ζ u - s.A 0 u) :=
  fun _ ht => (withTip s ζ).integrated_other_tip h hv hne ht

/-- A frozen-chart mark with a forward solution up to `a(T)` has a continuous image on `[0, T]`. -/
theorem continuousOn_frzImg {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {ζ : ℝ} {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol s.W' ζ (s.a T) v) : ContinuousOn (frzImg s.W' s.a ζ) (Icc 0 T) :=
  fun _ hu => (h.hasDerivWithinAt_frzImg hv hu).continuousWithinAt

/-- The image driver starts at `W'(0)`: `A₀(0) = W'(0)`. -/
theorem A_zero_zero {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') : s.A 0 0 = s.W' 0 := by
  have h0 := h.frzA_zero ⟨le_rfl, h.pos.le⟩
  rw [h.a0] at h0
  exact h0

/-- **The initial image of a frozen-chart mark is the mark** (`a(0) = 0`, `g̃₀(ζ) = ζ − W'(0)`). -/
theorem frzImg_zero {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {ζ : ℝ} (hζ : ζ ≠ s.W' 0) :
    frzImg s.W' s.a ζ 0 = ζ := by
  have hz : (ζ : ℂ) ≠ (s.W' 0 : ℂ) := fun he => hζ (Complex.ofReal_injective he)
  simp only [frzImg, h.a0, QuantumZipper.B5.fwdMap_zero_time s.W' hz, Complex.sub_re, Complex.ofReal_re,
    sub_add_cancel]

/-- **A frozen-chart mark initially left of the image driver stays left of it** on `[0, T]` (A22's other-tip side
argument, `A20_lt_A0`, for `withTip s ζ`). -/
theorem frzImg_lt_A0 {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {ζ : ℝ} {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol s.W' ζ (s.a T) v) (hne : ∀ u ∈ Icc (0 : ℝ) T, frzImg s.W' s.a ζ u ≠ s.A 0 u)
    (hζ : ζ < s.W' 0) : ∀ t ∈ Icc (0 : ℝ) T, frzImg s.W' s.a ζ t < s.A 0 t := by
  have h0 : (withTip s ζ).A20 0 < (withTip s ζ).A 0 0 := by
    rw [withTip_A20, withTip_A, frzImg_zero s h hζ.ne, A_zero_zero s h]
    exact hζ
  exact A20_lt_A0 (withTip s ζ) h (continuousOn_frzImg s h hv) (fun u hu => (hne u hu).symm) h0

/-- The mirror of `frzImg_lt_A0`: a frozen-chart mark initially right of the image driver stays right of it. -/
theorem A0_lt_frzImg {A : Set ℂ} (h : OwnData s.W A s.φ T s.a s.W') {ζ : ℝ} {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol s.W' ζ (s.a T) v) (hne : ∀ u ∈ Icc (0 : ℝ) T, frzImg s.W' s.a ζ u ≠ s.A 0 u)
    (hζ : s.W' 0 < ζ) : ∀ t ∈ Icc (0 : ℝ) T, s.A 0 t < frzImg s.W' s.a ζ t := by
  have h0 : (withTip s ζ).A 0 0 < (withTip s ζ).A20 0 := by
    rw [withTip_A20, withTip_A, frzImg_zero s h hζ.ne', A_zero_zero s h]
    exact hζ
  exact A0_lt_A20 (withTip s ζ) h (continuousOn_frzImg s h hv) (fun u hu => (hne u hu).symm) h0

end Own

/-! ### Capacity coordinates of arbitrary own-time image forces -/

section Capacity

variable {Ω : Type*} {n : ℕ}

/-- **The capacity coordinate of an own-time image force** `X` (read at the inverse capacity clock, centred at the
image start). A22's `seedCapacityForce d S k` is the case `X ω t = (d ω).imageForce t k`. -/
def capForce (d : Ω → SeedData n) (S : Ω → ℝ≥0) (X : Ω → ℝ → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  X ω (seedCapacityTime d S u ω) - (d ω).A 0 0

theorem seedCapacityForce_eq_capForce (d : Ω → SeedData n) (S : Ω → ℝ≥0) (k : Fin (n + 1)) (u : ℝ≥0) (ω : Ω) :
    seedCapacityForce d S k u ω = capForce d S (fun ω t => (d ω).imageForce t k) u ω := rfl

/-- Replacing the frozen-chart mark does not change the capacity clock, driver, time or horizon. -/
theorem seedCapacityDriver_withTip (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ζ : Ω → ℝ) :
    seedCapacityDriver (fun ω => withTip (d ω) (ζ ω)) S = seedCapacityDriver d S := rfl

theorem seedCapacityHorizon_withTip (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ζ : Ω → ℝ) :
    seedCapacityHorizon (fun ω => withTip (d ω) (ζ ω)) S = seedCapacityHorizon d S := rfl

/-- The capacity coordinate of a frozen-chart mark is the other-tip capacity force of `withTip`. -/
theorem capForce_frzImg_eq (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ζ : Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    capForce d S (fun ω => frzImg (d ω).W' (d ω).a (ζ ω)) u ω =
      seedCapacityForce (fun ω => withTip (d ω) (ζ ω)) S 0 u ω := rfl

variable {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {c : ℝ}
  (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
  (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
  (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hown hCc hCs hc hlb

/-- At the capacity of an own time `r ≤ S`, the capacity coordinate reads the own-time force at `r`. -/
theorem capForce_at_capacity (X : Ω → ℝ → ℝ) (ω : Ω) {r : ℝ≥0} (hr : r ≤ S ω) :
    capForce d S X ((d ω).a r).toNNReal ω = X ω r - (d ω).A 0 0 := by
  rw [capForce, seedCapacityTime_at_capacity hown hCc hCs hc hlb ω hr]

/-- The initial capacity coordinate is the centred initial own-time force. -/
theorem capForce_zero (X : Ω → ℝ → ℝ) (ω : Ω) : capForce d S X 0 ω = X ω 0 - (d ω).A 0 0 := by
  have hh := capForce_at_capacity hown hCc hCs hc hlb X ω (zero_le (a := S ω))
  simpa only [NNReal.coe_zero, (hown ω).a0, Real.toNNReal_zero] using hh

/-- **The capacity force equation of an own-time image force up to the horizon**, from its own-time image equation
on `[0, S]` (capacity substitution, `OwnData.capacity_force_equation`). -/
theorem capForce_integrated (X : Ω → ℝ → ℝ) (ω : Ω)
    (himg : ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / (X ω u - (d ω).A 0 u)) volume 0 t ∧
        X ω t = X ω 0 + ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / (X ω u - (d ω).A 0 u))
    {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :
    IntervalIntegrable (fun t : ℝ => (seedCapacityDriver d S t.toNNReal ω - capForce d S X t.toNNReal ω)⁻¹)
        volume 0 u ∧
      capForce d S X u ω = capForce d S X 0 ω +
        ∫ t in (0 : ℝ)..u, 2 / (capForce d S X t.toNNReal ω - seedCapacityDriver d S t.toNNReal ω) := by
  have hle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) : t.toNNReal ≤ S ω := by
    simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.2
  have hW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      seedCapacityDriver d S ((d ω).a t).toNNReal ω = (d ω).A 0 t - (d ω).A 0 0 := by
    simpa only [Real.coe_toNNReal _ ht.1] using seedCapacityDriver_at_capacity hown hCc hCs hc hlb ω (hle t ht)
  have hV (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (S ω)) :
      capForce d S X ((d ω).a t).toNNReal ω = X ω t - (d ω).A 0 0 := by
    simpa only [Real.coe_toNNReal _ ht.1] using capForce_at_capacity hown hCc hCs hc hlb X ω (hle t ht)
  obtain ⟨ht, hat⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have htm : ((seedCapacityTime d S u ω : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨NNReal.coe_nonneg _, ht⟩
  have hh := (hown ω).capacity_force_equation htm (w := fun t : ℝ => seedCapacityDriver d S t.toNNReal ω)
    (v := fun t : ℝ => capForce d S X t.toNNReal ω) hW hV (himg _ htm).1 (himg _ htm).2
  simpa only [hat, Real.toNNReal_coe, Real.toNNReal_zero] using hh

omit hown in
/-- The capacity coordinate is continuous when the own-time force is continuous on `[0, S]`. -/
theorem continuous_capForce (X : Ω → ℝ → ℝ) (ω : Ω) (hX : ContinuousOn (X ω) (Icc 0 (S ω))) :
    Continuous (capForce d S X · ω) := by
  refine Continuous.sub ?_ continuous_const
  apply hX.comp_continuous (continuous_subtype_val.comp (continuous_seedCapacityTime hCc hCs hc hlb ω))
  intro u
  exact ⟨(seedCapacityTime d S u ω).coe_nonneg, min_le_right _ _⟩

/-- A positive-time own side left of the image driver transfers to the capacity coordinates. -/
theorem capForce_lt_driver (X : Ω → ℝ → ℝ) (ω : Ω) (hlt : ∀ t ∈ Ioc (0 : ℝ) (S ω), X ω t < (d ω).A 0 t)
    {u : ℝ≥0} (hu0 : 0 < u) (hu : u ≤ seedCapacityHorizon d S ω) :
    capForce d S X u ω < seedCapacityDriver d S u ω := by
  have hp := seedCapacityTime_pos hown hCc hCs hc hlb ω hu0 hu
  have hle := (seedCapacityTime_spec hown hCc hCs hc hlb ω hu).1
  have h := hlt _ ⟨by exact_mod_cast hp, by exact_mod_cast hle⟩
  exact sub_lt_sub_right h _

/-- A positive-time own side right of the image driver transfers to the capacity coordinates. -/
theorem driver_lt_capForce (X : Ω → ℝ → ℝ) (ω : Ω) (hgt : ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).A 0 t < X ω t)
    {u : ℝ≥0} (hu0 : 0 < u) (hu : u ≤ seedCapacityHorizon d S ω) :
    seedCapacityDriver d S u ω < capForce d S X u ω := by
  have hp := seedCapacityTime_pos hown hCc hCs hc hlb ω hu0 hu
  have hle := (seedCapacityTime_spec hown hCc hCs hc hlb ω hu).1
  have h := hgt _ ⟨by exact_mod_cast hp, by exact_mod_cast hle⟩
  exact sub_lt_sub_right h _

/-- **`SeedImageGeometry` of the seeded capacity driver and the capacity coordinates of any families of own-time image
forces** `XL` (left) and `XR` (right), for an admissible initial word `(xL, xR)`: from continuity and the own-time
image equation of each force on `[0, S]`, the positive-time sides, and the centred initial values. -/
theorem seedImageGeometry_capForce {nL nR : ℕ} (XL : Fin nL → Ω → ℝ → ℝ) (XR : Fin nR → Ω → ℝ → ℝ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hword : IsSeedWord xL xR ρL ρR) (ω : Ω)
    (hcL : ∀ i, ContinuousOn (XL i ω) (Icc 0 (S ω))) (hcR : ∀ j, ContinuousOn (XR j ω) (Icc 0 (S ω)))
    (himgL : ∀ i, ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / (XL i ω u - (d ω).A 0 u)) volume 0 t ∧
        XL i ω t = XL i ω 0 + ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / (XL i ω u - (d ω).A 0 u))
    (himgR : ∀ j, ∀ t ∈ Icc (0 : ℝ) (S ω),
      IntervalIntegrable (fun u => 2 * (d ω).A 1 u ^ 2 / (XR j ω u - (d ω).A 0 u)) volume 0 t ∧
        XR j ω t = XR j ω 0 + ∫ u in (0 : ℝ)..t, 2 * (d ω).A 1 u ^ 2 / (XR j ω u - (d ω).A 0 u))
    (hltL : ∀ i, ∀ t ∈ Ioc (0 : ℝ) (S ω), XL i ω t < (d ω).A 0 t)
    (hgtR : ∀ j, ∀ t ∈ Ioc (0 : ℝ) (S ω), (d ω).A 0 t < XR j ω t)
    (hx0L : ∀ i, XL i ω 0 - (d ω).A 0 0 = xL i) (hx0R : ∀ j, XR j ω 0 - (d ω).A 0 0 = xR j) :
    SeedImageGeometry xL xR ρL ρR (seedCapacityDriver d S · ω) (fun i u => capForce d S (XL i) u ω)
      (fun j u => capForce d S (XR j) u ω) (seedCapacityHorizon d S ω) := by
  have hintL (i) {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :=
    capForce_integrated hown hCc hCs hc hlb (XL i) ω (himgL i) hu
  have hintR (j) {u : ℝ≥0} (hu : u ≤ seedCapacityHorizon d S ω) :=
    capForce_integrated hown hCc hCs hc hlb (XR j) ω (himgR j) hu
  have h0L (i) : capForce d S (XL i) 0 ω = xL i := by rw [capForce_zero hown hCc hCs hc hlb, hx0L]
  have h0R (j) : capForce d S (XR j) 0 ω = xR j := by rw [capForce_zero hown hCc hCs hc hlb, hx0R]
  refine seedImageGeometry_of_isSeedWord hword (seedCapacityDriver_zero hown hCc hCs hc hlb ω) h0L h0R
    (continuous_seedCapacityDriver hown hCc hCs hc hlb ω)
    (fun i => continuous_capForce hCc hCs hc hlb _ ω (hcL i))
    (fun j => continuous_capForce hCc hCs hc hlb _ ω (hcR j))
    (fun t ht i => (hintL i ht).1) (fun t ht j => (hintR j ht).1) (fun t ht i => ?_) (fun t ht j => ?_)
    (fun t hp ht i => capForce_lt_driver hown hCc hCs hc hlb _ ω (hltL i) hp ht)
    (fun t hp ht j => driver_lt_capForce hown hCc hCs hc hlb _ ω (hgtR j) hp ht)
  · rw [(hintL i ht).2, h0L]
  · rw [(hintR j ht).2, h0R]

/-- **`SeedImageGeometry` for a word of frozen-chart marks left of the image start** (the large-curve direction of
A.1): marks `ζ i` with forward solutions up to `a(S)` and protected gaps on `[0, S]`, strictly left of the image start
`W'(0)`, forming the admissible word `xL i = ζ i − W'(0)` (no right marks). The seeded capacity driver and the
capacity coordinates of the marks have the geometry up to the horizon. -/
theorem seedImageGeometry_frozenLeft {nL : ℕ} (ζ : Fin nL → Ω → ℝ) {xL : Fin nL → ℝ} {ρL : Fin nL → ℝ}
    (hword : IsSeedWord xL (![] : Fin 0 → ℝ) ρL ![]) (ω : Ω)
    (hv : ∀ i, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (d ω).W' (ζ i ω) ((d ω).a (S ω)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S ω), frzImg (d ω).W' (d ω).a (ζ i ω) u ≠ (d ω).A 0 u)
    (hside : ∀ i, ζ i ω < (d ω).W' 0) (hx0 : ∀ i, ζ i ω - (d ω).W' 0 = xL i) :
    SeedImageGeometry xL ![] ρL ![] (seedCapacityDriver d S · ω)
      (fun i u => capForce d S (fun ω => frzImg (d ω).W' (d ω).a (ζ i ω)) u ω) (fun j => Fin.elim0 j)
      (seedCapacityHorizon d S ω) := by
  have h := seedImageGeometry_capForce hown hCc hCs hc hlb (fun i ω => frzImg (d ω).W' (d ω).a (ζ i ω))
    (fun j => Fin.elim0 j) hword ω
    (fun i => (hv i).elim fun _ hvi => continuousOn_frzImg (d ω) (hown ω) hvi) (fun j => Fin.elim0 j)
    (fun i => (hv i).elim fun _ hvi => ownImageEq_frozen (d ω) (hown ω) hvi (hne i)) (fun j => Fin.elim0 j)
    (fun i t ht => (hv i).elim fun _ hvi =>
      frzImg_lt_A0 (d ω) (hown ω) hvi (hne i) (hside i) t ⟨ht.1.le, ht.2⟩) (fun j => Fin.elim0 j)
    (fun i => by
      show frzImg (d ω).W' (d ω).a (ζ i ω) 0 - (d ω).A 0 0 = xL i
      rw [frzImg_zero (d ω) (hown ω) (hside i).ne, A_zero_zero (d ω) (hown ω), hx0])
    (fun j => Fin.elim0 j)
  convert h using 2

end Capacity

end InteractingSLE.ZhanGT4.A1MultiMark
