/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkCap

/-!
# Zhan's A.1 (R80): the large-curve direction with its frozen-chart marks

Packet PROVE-A1-MULTIMARK. In the large-curve direction of A.1 (`A1DualCoupling{G3,Eight}PatchStatement`, second law
part: image curve the large curve `SLE_κ` started at `0`, conditioning curve the small curve `SLE_κ̂` started at `xk`
and stopped at `σ`) the image word is made of frozen-chart marks only. In the frame of the image curve the frozen
chart is `φ = physMap xk (extPath W₁) σ` and the marks are

* G3 (`xk = y`): `xk + VR₁ 1 σ` (the image of `x`), `xk + VR₁ 0 σ` (the side `y⁺`), `xk + W₁ σ` (the tip) and
  `xk + VL₁ 0 σ` (the side `y⁻`);
* Eight (`xk = x`): `xk + VR₁ 0 σ` (`x⁺`), `xk + W₁ σ` (the tip) and `xk + VL₁ 0 σ` (`x⁻`);

while the image curve starts at the boundary value `xk + VR₁ last σ` of `φ` at the large curve's start (the small
curve's outermost right mark, which never meets the small driver: A1-SEEDGEOM's `vR_last_ne_of_path`).

## Main results

* `W'_zero_eq_of_force`, `W'_zero_eq_of_path`: **the image start of any `OwnData` against the frozen chart is the
  boundary value `xk + v(σ)` of `φ` at a force mark separated from the driver up to `σ`**;
* `largeG3_marks_lt`, `largeEight_marks_lt`: every mark is strictly left of the image start;
* **`seedImageGeometry_largeG3`**, **`seedImageGeometry_largeEight`**: `SeedImageGeometry` of the seeded capacity
  driver and the capacity coordinates of the frozen-chart marks, with the image word of A.1 as initial word, from the
  marks' forward solutions and protected gaps;
* `seedImageGeometry_rDrvFst_of`: A1-SEEDGEOM's `seedImageGeometry_rDrvFst` for arbitrary capacity forces;
* **`seedImageGeometry_rDrvFst_largeG3`**, **`seedImageGeometry_rDrvFst_largeEight`**: A1-FAMILY's premise `hgeom`
  of `FamilyRectFst.ofRect` for the large-curve direction, sample by sample.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1MultiMark

open A1SeedGeom A1Ref A1Core A1Family Sec2 A2X

/-! ### The image start -/

section Start

/-- **The image start is the frozen chart's boundary value at a separated force mark**: if `v` is a force process of
the conditioning driver `w` from `p`, separated from `w` up to `σ < ζ`, and the image curve starts at the physical
mark (`x + p = 0`), then every `OwnData` of the image curve against the frozen chart `physMap x (extPath w) σ` has
`W'(0) = x + v(σ)`. -/
theorem W'_zero_eq_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ σ, v r ≠ w r) {x : ℝ} (hxp : x + p = 0)
    {wj : ℝ → ℝ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData wj (A2X.physHull x (Strip.extPath w) σ) (A2X.physMap x (Strip.extPath w) σ) T a W') :
    W' 0 = x + v σ := by
  have h1 := (isImgDrvOn_of_ownData h).1.2.1
  have h2 := tendsto_physMap_of_force hw hw0 hv hveq hσ hsep x
  rw [hxp] at h2
  have : (𝓝[QuantumZipper.H] ((0 : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  exact_mod_cast tendsto_nhds_unique h1 h2

/-- **The image start from a pathwise integrated conditioning evolution**: the boundary value of the frozen chart at a
right mark `j` separated from the driver up to `σ`, when the image curve starts at that mark (`x + xR j = 0`). -/
theorem W'_zero_eq_of_path {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (j : Fin nR) {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ)
    (hsep : ∀ r ≤ σ, vR j r ≠ w r) {x : ℝ} (hx : x + xR j = 0) {wj : ℝ → ℝ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData wj (A2X.physHull x (Strip.extPath w) σ) (A2X.physMap x (Strip.extPath w) σ) T a W') :
    W' 0 = x + vR j σ := by
  obtain ⟨hw0, -, -, hcw, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := id hP
  exact W'_zero_eq_of_force hcw hw0 (hcR j) (hReq · · j) hσ hsep hx h

end Start

/-! ### The large-curve words: every mark is left of the image start -/

section Words

variable {κ x : ℝ} {W : ℝ≥0 → ℝ} {VL : Fin 1 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {τ : ℝ≥0}

/-- The G3 frozen-chart marks of the large-curve direction (offset `x₀ = xk − xj`): the images of `x`, `y⁺`, the tip
and `y⁻`. -/
def largeG3Marks (x₀ : ℝ) (W : ℝ≥0 → ℝ) (VL : Fin 1 → ℝ≥0 → ℝ) (VR : Fin 3 → ℝ≥0 → ℝ) (τ : ℝ≥0) : Fin 4 → ℝ :=
  ![x₀ + VR 1 τ, x₀ + VR 0 τ, x₀ + W τ, x₀ + VL 0 τ]

/-- The Eight frozen-chart marks of the large-curve direction: the images of `x⁺`, the tip and `x⁻`. -/
def largeEightMarks (x₀ : ℝ) (W : ℝ≥0 → ℝ) (VL : Fin 1 → ℝ≥0 → ℝ) (VR : Fin 2 → ℝ≥0 → ℝ) (τ : ℝ≥0) : Fin 3 → ℝ :=
  ![x₀ + VR 0 τ, x₀ + W τ, x₀ + VL 0 τ]

/-- **G3: the small curve's outermost right mark never meets its driver, and every large-curve mark is strictly left
of it.** -/
theorem largeG3_marks_lt {y : ℝ} (hx : x < 0) {VR : Fin 3 → ℝ≥0 → ℝ}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) W VL VR B ζ)
    (hτ : (τ : ℝ≥0∞) < ζ) :
    (∀ r ≤ τ, VR 2 r ≠ W r) ∧ ∀ (x₀ : ℝ) (i : Fin 4), largeG3Marks x₀ W VL VR τ i < x₀ + VR 2 τ := by
  have hsum : ∑ j, smallG3RhoR κ j ≤ -2 := by
    rw [Fin.sum_univ_three]
    simp only [smallG3RhoR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linarith
  have hlast : ∀ j : Fin 3, j ≤ 2 := fun j => by fin_cases j <;> decide
  have hle {r : ℝ≥0} (hr : r ≤ τ) : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hτ
  have hsep : ∀ r ≤ τ, VR 2 r ≠ W r := fun r hr => vR_last_ne_of_path hP hsum hlast (hle hr)
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, hmono, -⟩ := id hP
  have hW2' : W τ < VR 2 τ := lt_of_le_of_ne (hwR τ hτ 2) (hsep τ le_rfl).symm
  have h12 : VR 1 τ < VR 2 τ := by
    refine vR_lt_vR_of_path hP (j := 1) (j' := 2) (by simp; linarith) hτ fun r _ hrτ hm => ?_
    rw [hm]; exact vR_last_ne_of_path hP hsum hlast (hle hrτ)
  have h01 : VR 0 τ ≤ VR 1 τ := hmono τ hτ (by decide)
  have hw0 : W τ ≤ VR 0 τ := hwR τ hτ 0
  have hL : VL 0 τ ≤ W τ := hLw τ hτ 0
  refine ⟨hsep, fun x₀ i => ?_⟩
  fin_cases i <;> simp [largeG3Marks] <;> linarith

/-- **Eight: the small curve's outermost right mark never meets its driver, and every large-curve mark is strictly
left of it.** -/
theorem largeEight_marks_lt (hx : x < 0) {VR : Fin 2 → ℝ≥0 → ℝ}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) W VL VR B ζ)
    (hτ : (τ : ℝ≥0∞) < ζ) :
    (∀ r ≤ τ, VR 1 r ≠ W r) ∧ ∀ (x₀ : ℝ) (i : Fin 3), largeEightMarks x₀ W VL VR τ i < x₀ + VR 1 τ := by
  have hsum : ∑ j, smallEightRhoR κ j ≤ -2 := by
    rw [Fin.sum_univ_two]
    simp only [smallEightRhoR, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  have hlast : ∀ j : Fin 2, j ≤ 1 := fun j => by fin_cases j <;> decide
  have hle {r : ℝ≥0} (hr : r ≤ τ) : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hτ
  have hsep : ∀ r ≤ τ, VR 1 r ≠ W r := fun r hr => vR_last_ne_of_path hP hsum hlast (hle hr)
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, -⟩ := id hP
  have hW1' : W τ < VR 1 τ := lt_of_le_of_ne (hwR τ hτ 1) (hsep τ le_rfl).symm
  have h01 : VR 0 τ < VR 1 τ := by
    refine vR_lt_vR_of_path hP (j := 0) (j' := 1) (by simp; linarith) hτ fun r _ hrτ hm => ?_
    rw [hm]; exact vR_last_ne_of_path hP hsum hlast (hle hrτ)
  have hw0 : W τ ≤ VR 0 τ := hwR τ hτ 0
  have hL : VL 0 τ ≤ W τ := hLw τ hτ 0
  refine ⟨hsep, fun x₀ i => ?_⟩
  fin_cases i <;> simp [largeEightMarks] <;> linarith

end Words

/-! ### The seeded capacity geometry of the large-curve direction -/

section Geometry

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {c : ℝ}
  (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
  (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
  (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)

include hCc hCs hc hlb

/-- **G3, large-curve direction: the seeded capacity geometry of the frozen-chart marks.** The image curve's seeded
own-time data `d` live against the frozen chart of the small curve (pathwise integrated, word `![0]`, `![0, x − y, −y]`)
stopped at `σ` before its lifetime, in the frame where the image curve starts at the small curve's mark `−y`
(`x₀ − y = 0`). If the four marks `largeG3Marks` have forward solutions up to `a(S)` and protected gaps on `[0, S]`,
the seeded capacity driver and the capacity coordinates of the marks have the geometry with A.1's large image word
`![VR 1 σ − VR 2 σ, VR 0 σ − VR 2 σ, W σ − VR 2 σ, VL 0 σ − VR 2 σ]`. -/
theorem seedImageGeometry_largeG3 {κ x y : ℝ} (hx : x < 0) {W₁ : ℝ≥0 → ℝ} {VL₁ : Fin 1 → ℝ≥0 → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → ℝ} {B₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) W₁ VL₁ VR₁ B₁ ζ₁)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ₁) {x₀ : ℝ} (hx₀ : x₀ - y = 0)
    (hown : ∀ ω, OwnData (d ω).W (physHull x₀ (Strip.extPath W₁) σ) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hφ : ∀ ω, (d ω).φ = physMap x₀ (Strip.extPath W₁) σ) (ω : Ω)
    (hv : ∀ i, ∃ v : ℝ → ℂ,
      QuantumZipper.IsForwardSol (d ω).W' (largeG3Marks x₀ W₁ VL₁ VR₁ σ i) ((d ω).a (S ω)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S ω),
      frzImg (d ω).W' (d ω).a (largeG3Marks x₀ W₁ VL₁ VR₁ σ i) u ≠ (d ω).A 0 u) :
    SeedImageGeometry ![VR₁ 1 σ - VR₁ 2 σ, VR₁ 0 σ - VR₁ 2 σ, W₁ σ - VR₁ 2 σ, VL₁ 0 σ - VR₁ 2 σ] ![]
      (largeG3ImgRhoL κ) ![] (seedCapacityDriver d S · ω)
      (fun i u => capForce d S (fun ω => frzImg (d ω).W' (d ω).a (largeG3Marks x₀ W₁ VL₁ VR₁ σ i)) u ω)
      (fun j => Fin.elim0 j) (seedCapacityHorizon d S ω) := by
  obtain ⟨hsep, hlt⟩ := largeG3_marks_lt hx hP hσ
  have h0 : (d ω).W' 0 = x₀ + VR₁ 2 σ := by
    have h := hown ω
    rw [hφ ω] at h
    exact W'_zero_eq_of_path hP 2 hσ hsep (by simp; linarith) h
  exact seedImageGeometry_frozenLeft hown hCc hCs hc hlb (fun i _ => largeG3Marks x₀ W₁ VL₁ VR₁ σ i)
    (largeG3_isSeedWord hx hP hσ) ω hv hne (fun i => by rw [h0]; exact hlt x₀ i)
    (fun i => by rw [h0]; fin_cases i <;> simp [largeG3Marks])

/-- **Eight, large-curve direction: the seeded capacity geometry of the frozen-chart marks** (small curve word `![0]`,
`![0, −x]`, frame `x₀ − x = 0`; marks `largeEightMarks`; A.1's large image word
`![VR 0 σ − VR 1 σ, W σ − VR 1 σ, VL 0 σ − VR 1 σ]`). -/
theorem seedImageGeometry_largeEight {κ x : ℝ} (hx : x < 0) {W₁ : ℝ≥0 → ℝ} {VL₁ : Fin 1 → ℝ≥0 → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → ℝ} {B₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) W₁ VL₁ VR₁ B₁ ζ₁)
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ₁) {x₀ : ℝ} (hx₀ : x₀ - x = 0)
    (hown : ∀ ω, OwnData (d ω).W (physHull x₀ (Strip.extPath W₁) σ) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hφ : ∀ ω, (d ω).φ = physMap x₀ (Strip.extPath W₁) σ) (ω : Ω)
    (hv : ∀ i, ∃ v : ℝ → ℂ,
      QuantumZipper.IsForwardSol (d ω).W' (largeEightMarks x₀ W₁ VL₁ VR₁ σ i) ((d ω).a (S ω)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S ω),
      frzImg (d ω).W' (d ω).a (largeEightMarks x₀ W₁ VL₁ VR₁ σ i) u ≠ (d ω).A 0 u) :
    SeedImageGeometry ![VR₁ 0 σ - VR₁ 1 σ, W₁ σ - VR₁ 1 σ, VL₁ 0 σ - VR₁ 1 σ] ![]
      (largeEightImgRhoL κ) ![] (seedCapacityDriver d S · ω)
      (fun i u => capForce d S (fun ω => frzImg (d ω).W' (d ω).a (largeEightMarks x₀ W₁ VL₁ VR₁ σ i)) u ω)
      (fun j => Fin.elim0 j) (seedCapacityHorizon d S ω) := by
  obtain ⟨hsep, hlt⟩ := largeEight_marks_lt hx hP hσ
  have h0 : (d ω).W' 0 = x₀ + VR₁ 1 σ := by
    have h := hown ω
    rw [hφ ω] at h
    exact W'_zero_eq_of_path hP 1 hσ hsep (by simp; linarith) h
  exact seedImageGeometry_frozenLeft hown hCc hCs hc hlb (fun i _ => largeEightMarks x₀ W₁ VL₁ VR₁ σ i)
    (largeEight_isSeedWord hx hP hσ) ω hv hne (fun i => by rw [h0]; exact hlt x₀ i)
    (fun i => by rw [h0]; fin_cases i <;> simp [largeEightMarks])

end Geometry

/-! ### A1-FAMILY's `hgeom` for the large-curve direction -/

section Family

variable {X Y : Type*} {n : ℕ}

/-- **`hgeom` from any seeded capacity geometry** (image curve on `Y`, conditioning sample `x` live at its stop): A1-
SEEDGEOM's `seedImageGeometry_rDrvFst` with arbitrary capacity force points `vL`, `vR` in place of A22's
`seedCapacityForce` (for instance the capacity coordinates of frozen-chart marks, `capForce`). -/
theorem seedImageGeometry_rDrvFst_of {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {x : X} (hlive : live (τ x) x) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - xj) (Strip.extPath (Wk · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - xj) (Strip.extPath (Wk · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ')) (hk0 : Wk 0 x = 0)
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (Wk · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hgeo : SeedImageGeometry xL xR ρL ρR (seedCapacityDriver d S · y) vL vR (seedCapacityHorizon d S y))
    {VL : Fin nL → ℝ≥0 → ℝ} {VR : Fin nR → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y)
    (hVL : ∀ i, ∀ t ≤ cap, VL i t = vL i t) (hVR : ∀ j, ∀ t ≤ cap, VR j t = vR j t) :
    SeedImageGeometry xL xR ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ (min t cap) (x, y))
      (fun i t => VL i (min t cap)) (fun j t => VR j (min t cap)) cap :=
  (hgeo.mono hcap).stop_of_eqOn (fun t ht => by
    show rDrvFst live xj Wj ζj xk Wk (fun _ => τ x) t (x, y) = _
    exact rDrvFst_eq_seedCapacityDriver hlive hW hown hφ hj hk hk0 hgood hCc hCs hc hClb y (ht.trans hcap))
    hVL hVR

/-- **A1-FAMILY's `hgeom`, G3 large-curve direction, at one live sample** `z = (x, y)`: the conditioning curve is the
small curve (`IsIntegratedSLEPath (kh κ) ![0] ![0, x' − y', −y']` at the sample `x`), alive at its stop `τ x`; the image
curve (on `Y`, started at `xj`, conditioning start `xk`, `xk − xj = y'`) has seeded data `d` against the frozen chart;
the four frozen-chart marks have forward solutions up to `a(S)` and protected gaps; the family's left force points agree
with their capacity coordinates up to the cap `≤ horizon`. Then the masked canonical image driver and the family's
force points, stopped at the cap, have the geometry with A.1's large image word. -/
theorem seedImageGeometry_rDrvFst_largeG3 {κ x' y' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x' - y', -y'] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (B₁ · x) (ζ₁ x))
    {live : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {τ : X → ℝ≥0}
    (hlive : live (τ x) x) (hτ : (τ x : ℝ≥0∞) < ζ₁ x) (hxk : xk - xj - y' = 0) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - xj) (Strip.extPath (W₁ · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - xj) (Strip.extPath (W₁ · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (W₁ · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y)
    (hv : ∀ i, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (d y).W'
      (largeG3Marks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) ((d y).a (S y)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S y), frzImg (d y).W' (d y).a
      (largeG3Marks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) u ≠ (d y).A 0 u)
    {VL : Fin 4 → ℝ≥0 → ℝ} {VR : Fin 0 → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y)
    (hVL : ∀ i, ∀ t ≤ cap, VL i t = capForce d S (fun y => frzImg (d y).W' (d y).a
      (largeG3Marks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i)) t y) :
    SeedImageGeometry ![VR₁ 1 (τ x) x - VR₁ 2 (τ x) x, VR₁ 0 (τ x) x - VR₁ 2 (τ x) x, W₁ (τ x) x - VR₁ 2 (τ x) x,
        VL₁ 0 (τ x) x - VR₁ 2 (τ x) x] ![] (largeG3ImgRhoL κ) ![]
      (fun t => rDrvFst live xj Wj ζj xk W₁ τ (min t cap) (x, y)) (fun i t => VL i (min t cap))
      (fun j t => VR j (min t cap)) cap := by
  have hk0 : W₁ 0 x = 0 := hP.1
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  have hgeo := seedImageGeometry_largeG3 hCc hCs hc hClb hx' hP hτ hxk hown hφ y hv hne
  exact seedImageGeometry_rDrvFst_of hlive hW hown hφ hj hk hk0 hgood hCc hCs hc hClb y hgeo hcap hVL
    (fun j => Fin.elim0 j)

/-- **A1-FAMILY's `hgeom`, Eight large-curve direction, at one live sample** (small curve word `![0]`, `![0, −x']`,
`xk − xj = x'`; marks `largeEightMarks`). -/
theorem seedImageGeometry_rDrvFst_largeEight {κ x' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x'] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (B₁ · x) (ζ₁ x))
    {live : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {τ : X → ℝ≥0}
    (hlive : live (τ x) x) (hτ : (τ x : ℝ≥0∞) < ζ₁ x) (hxk : xk - xj - x' = 0) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - xj) (Strip.extPath (W₁ · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - xj) (Strip.extPath (W₁ · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - xj) (Strip.extPath (W₁ · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y)
    (hv : ∀ i, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (d y).W'
      (largeEightMarks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) ((d y).a (S y)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S y), frzImg (d y).W' (d y).a
      (largeEightMarks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) u ≠ (d y).A 0 u)
    {VL : Fin 3 → ℝ≥0 → ℝ} {VR : Fin 0 → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y)
    (hVL : ∀ i, ∀ t ≤ cap, VL i t = capForce d S (fun y => frzImg (d y).W' (d y).a
      (largeEightMarks (xk - xj) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i)) t y) :
    SeedImageGeometry ![VR₁ 0 (τ x) x - VR₁ 1 (τ x) x, W₁ (τ x) x - VR₁ 1 (τ x) x, VL₁ 0 (τ x) x - VR₁ 1 (τ x) x] ![]
      (largeEightImgRhoL κ) ![] (fun t => rDrvFst live xj Wj ζj xk W₁ τ (min t cap) (x, y))
      (fun i t => VL i (min t cap)) (fun j t => VR j (min t cap)) cap := by
  have hk0 : W₁ 0 x = 0 := hP.1
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  have hgeo := seedImageGeometry_largeEight hCc hCs hc hClb hx' hP hτ hxk hown hφ y hv hne
  exact seedImageGeometry_rDrvFst_of hlive hW hown hφ hj hk hk0 hgood hCc hCs hc hClb y hgeo hcap hVL
    (fun j => Fin.elim0 j)

end Family

end InteractingSLE.ZhanGT4.A1MultiMark
