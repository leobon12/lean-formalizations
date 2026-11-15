/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkLarge

/-!
# Zhan's A.1 (R80): the canonical image forces of frozen-chart marks

Packet PROVE-A1-MULTIMARK. A1-FROZEN's families need image force points that are chosen once for all rectangles (the
field `VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ` of `FrozenFamily(Fst)` does not depend on the rectangle `m`), while A22's
seeded capacity coordinates depend on the own horizon `S` of each rectangle. Here the canonical choice is made for
frozen-chart marks, exactly as A1REF's canonical image driver:

* `imgForce xj wj ζj xk wk τ p u`: the image chain `g̃_u(p) + W̃_u` at the absolute frozen-chart point `p`, driven by
  the canonical image driver `imgDrv`, centred at the image start;
* `rFrzFst live xj Wj ζj xk Wk τ p`: the same on `X × Y` (conditioning curve on `X`, image curve on `Y`), masked by the
  live event like `A1Core.rDrvFst`, for a mark `p x` read from the conditioning sample;
* **`imgForce_eq_capForce`**, **`rFrzFst_eq_capForce`**: up to the capacity horizon of any seeded data of the image
  curve (frame `0`), the canonical force is the capacity coordinate of the mark (`capForce`), whatever the horizon `S`;
* **`seedImageGeometry_rDrvFst_largeG3_canon`**, **`seedImageGeometry_rDrvFst_largeEight_canon`**: A1-FAMILY's
  `hgeom` for the large-curve direction with the canonical forces (no agreement hypothesis left).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1MultiMark

open A1SeedGeom A1Ref A1Core A1Family Sec2 A2X
open QuantumZipper (fwdMap)

/-! ### The canonical image force of a frozen-chart point -/

/-- **The canonical image force** of the absolute frozen-chart point `p` at image time `u`: `g̃_u(p) + W̃_u`, centred
at the image start `W̃_0`, for the canonical image driver `W̃ = imgDrv xj wj ζj xk wk τ`. -/
def imgForce (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ p u : ℝ) : ℝ :=
  (fwdMap (imgDrv xj wj ζj xk wk τ) u p).re + imgDrv xj wj ζj xk wk τ u - imgDrv xj wj ζj xk wk τ 0

section Ident

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {c : ℝ}

/-- **The canonical image force is the capacity coordinate of the mark** up to the capacity horizon of any seeded
data of the image curve in its own frame (image start `0`, conditioning start `xk`): the canonical image driver agrees
with the seeded image driver `W'` up to `a(S)` (A1REF's `imgDrv_eqOn_of_ownData`), and `g̃` only reads the driver up to
the current image time. -/
theorem imgForce_eq_capForce {wk : ℝ → ℝ} {xk τ : ℝ} {ζj : Ω → ℝ≥0∞}
    (hown : ∀ ω, OwnData (d ω).W (physHull xk wk τ) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hφ : ∀ ω, (d ω).φ = physMap xk wk τ)
    (hj : ∀ ω T, ENNReal.ofReal T < ζj ω → ContinuousOn (d ω).W (Icc 0 T))
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hgood : ∀ ω, IsGoodTime 0 (d ω).W (ζj ω) xk wk τ (S ω))
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
    (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r) (p : ℝ) (ω : Ω) {u : ℝ≥0}
    (hu : u ≤ seedCapacityHorizon d S ω) :
    imgForce 0 (d ω).W (ζj ω) xk wk τ p u = capForce d S (fun ω => frzImg (d ω).W' (d ω).a p) u ω := by
  have h := hown ω
  have h' : OwnData (d ω).W (physHull xk wk τ) (physMap xk wk τ) (S ω) (d ω).a (d ω).W' := by
    rw [← hφ ω]; exact h
  have hEq := imgDrv_eqOn_of_ownData (hj ω) h.zero hk hk0 hτ (hgood ω) h'
  obtain ⟨hS, hat⟩ := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
  have huS : (u : ℝ) ≤ (d ω).a (S ω) := by
    rw [← hat]
    exact h.mono.monotoneOn ⟨(seedCapacityTime d S u ω).coe_nonneg, hS⟩ ⟨(S ω).coe_nonneg, le_rfl⟩ hS
  have haS : 0 ≤ (d ω).a (S ω) := (u.coe_nonneg).trans huS
  simp only [imgForce, capForce, frzImg, hat, A_zero_zero (d ω) h]
  rw [Ito.fwdMap_congr_of_eqOn_of_le hEq huS, hEq ⟨u.coe_nonneg, huS⟩, hEq ⟨le_rfl, haS⟩]

end Ident

/-! ### The masked canonical force on `X × Y` -/

section Masked

variable {X Y : Type*} {n : ℕ}

open scoped Classical in
/-- **The canonical image force of a frozen-chart mark, masked by the live event** (conditioning curve on `X`, image
curve on `Y`; the mark `p x` is read from the conditioning sample): the mirror of `A1Core.rDrvFst` for force points. -/
def rFrzFst (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (τ : X → ℝ≥0) (p : X → ℝ) : ℝ≥0 → X × Y → ℝ :=
  fun t z => if live (τ z.1) z.1 then
    imgForce xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (p z.1) t else 0

/-- **The masked canonical force is the capacity coordinate of the mark** at a live sample, up to the capacity horizon
of any seeded data of the image curve (frame `0`, as in the large-curve direction of A.1). -/
theorem rFrzFst_eq_capForce {live : ℝ≥0 → X → Prop} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {p : X → ℝ} {x : X} (hlive : live (τ x) x) {d : Y → SeedData n}
    {S : Y → ℝ≥0} (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - 0) (Strip.extPath (Wk · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - 0) (Strip.extPath (Wk · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ')) (hk0 : Wk 0 x = 0)
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - 0) (Strip.extPath (Wk · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon d S y) :
    rFrzFst live 0 Wj ζj xk Wk τ p t (x, y) = capForce d S (fun y => frzImg (d y).W' (d y).a (p x)) t y := by
  simp only [sub_zero] at hown hφ hgood
  have hk0' : Strip.extPath (Wk · x) 0 = 0 := by simp [Strip.extPath, hk0]
  have e := imgForce_eq_capForce hown hφ hj hk hk0' (τ x).coe_nonneg hgood hCc hCs hc hClb (p x) y ht
  simp only [rFrzFst, hlive, ↓reduceIte]
  rw [← e, hW y]

/-- **A1-FAMILY's `hgeom`, G3 large-curve direction, with the canonical forces**: `seedImageGeometry_rDrvFst_largeG3`
for the family force points `rFrzFst … (largeG3Marks …)` (no agreement hypothesis). -/
theorem seedImageGeometry_rDrvFst_largeG3_canon {κ x' y' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x' - y', -y'] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (B₁ · x) (ζ₁ x))
    {live : ℝ≥0 → X → Prop} {xk : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {τ : X → ℝ≥0}
    (hlive : live (τ x) x) (hτ : (τ x : ℝ≥0∞) < ζ₁ x) (hxk : xk - 0 - y' = 0) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - 0) (Strip.extPath (W₁ · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - 0) (Strip.extPath (W₁ · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - 0) (Strip.extPath (W₁ · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y)
    (hv : ∀ i, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (d y).W'
      (largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) ((d y).a (S y)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S y), frzImg (d y).W' (d y).a
      (largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) u ≠ (d y).A 0 u)
    {VR : Fin 0 → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y) :
    SeedImageGeometry ![VR₁ 1 (τ x) x - VR₁ 2 (τ x) x, VR₁ 0 (τ x) x - VR₁ 2 (τ x) x, W₁ (τ x) x - VR₁ 2 (τ x) x,
        VL₁ 0 (τ x) x - VR₁ 2 (τ x) x] ![] (largeG3ImgRhoL κ) ![]
      (fun t => rDrvFst live 0 Wj ζj xk W₁ τ (min t cap) (x, y))
      (fun i t => rFrzFst live 0 Wj ζj xk W₁ τ (fun x => largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x)
        (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y))
      (fun j t => VR j (min t cap)) cap := by
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  exact seedImageGeometry_rDrvFst_largeG3 (VL := fun i t => rFrzFst live 0 Wj ζj xk W₁ τ
      (fun x => largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) t (x, y))
    hx' hP hlive hτ hxk hW hown hφ hj hgood hCc hCs hc hClb y hv hne hcap fun i t ht => rFrzFst_eq_capForce
      (p := fun x => largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i)
      hlive hW hown hφ hj hk hP.1 hgood hCc hCs hc hClb y
      (ht.trans hcap)

/-- **A1-FAMILY's `hgeom`, Eight large-curve direction, with the canonical forces.** -/
theorem seedImageGeometry_rDrvFst_largeEight_canon {κ x' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x'] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (B₁ · x) (ζ₁ x))
    {live : ℝ≥0 → X → Prop} {xk : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {τ : X → ℝ≥0}
    (hlive : live (τ x) x) (hτ : (τ x : ℝ≥0∞) < ζ₁ x) (hxk : xk - 0 - x' = 0) {d : Y → SeedData n} {S : Y → ℝ≥0}
    (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - 0) (Strip.extPath (W₁ · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - 0) (Strip.extPath (W₁ · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - 0) (Strip.extPath (W₁ · x)) (τ x) (S y))
    (hCc : ∀ y, Continuous (seedQuadClock (seedCapacityCoeff d S) y))
    (hCs : ∀ y, StrictMono (seedQuadClock (seedCapacityCoeff d S) y)) {c : ℝ} (hc : 0 < c)
    (hClb : ∀ y r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) y r) (y : Y)
    (hv : ∀ i, ∃ v : ℝ → ℂ, QuantumZipper.IsForwardSol (d y).W'
      (largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) ((d y).a (S y)) v)
    (hne : ∀ i, ∀ u ∈ Icc (0 : ℝ) (S y), frzImg (d y).W' (d y).a
      (largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) u ≠ (d y).A 0 u)
    {VR : Fin 0 → ℝ≥0 → ℝ} {cap : ℝ≥0} (hcap : cap ≤ seedCapacityHorizon d S y) :
    SeedImageGeometry ![VR₁ 0 (τ x) x - VR₁ 1 (τ x) x, W₁ (τ x) x - VR₁ 1 (τ x) x, VL₁ 0 (τ x) x - VR₁ 1 (τ x) x] ![]
      (largeEightImgRhoL κ) ![] (fun t => rDrvFst live 0 Wj ζj xk W₁ τ (min t cap) (x, y))
      (fun i t => rFrzFst live 0 Wj ζj xk W₁ τ (fun x => largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x)
        (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y))
      (fun j t => VR j (min t cap)) cap := by
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  exact seedImageGeometry_rDrvFst_largeEight (VL := fun i t => rFrzFst live 0 Wj ζj xk W₁ τ
      (fun x => largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) t (x, y))
    hx' hP hlive hτ hxk hW hown hφ hj hgood hCc hCs hc hClb y hv hne hcap fun i t ht => rFrzFst_eq_capForce
      (p := fun x => largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i)
      hlive hW hown hφ hj hk hP.1 hgood hCc hCs hc hClb y
      (ht.trans hcap)

end Masked

end InteractingSLE.ZhanGT4.A1MultiMark
