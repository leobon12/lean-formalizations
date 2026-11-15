/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesLim
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomLocal

/-!
# Zhan's A.1 (R80): the family's force points in the large-curve direction (`measurable_VL`, `hgVL`, `hgeom`)

Packet PROVE-A1-FORCES. In the large-curve direction of A.1 the conditioning (small) curve lives on `X`, the image
(large) curve on `Y`, and the image word consists of frozen-chart marks only (PROVE-A1-MULTIMARK: `largeG3Marks`,
`largeEightMarks`). Here the family's force points are the measurable canonical forces `rForceFst` (A1Forces'
`canonForce` read on `X × Y`):

* **`measurable_rForceFst`**: jointly measurable in the frozen time and the sample (`FrozenFamilyFst.measurable_VL`),
  for marks jointly measurable in the frozen time and the conditioning sample;
* **`rForceFst_eq_rFrzFst_of_seed`**: up to the capacity horizon of any seeded data of the image curve, at a live
  sample and an alive mark, they are A1-MULTIMARK's canonical forces `rFrzFst` (hence the capacity coordinates);
* **`seedImageGeometry_rDrvFst_largeG3_force`**, **`…largeEight_force`**: A1-FAMILY's premise `hgeom` with these
  force points;
* **`exists_measurable_rForceFst_of_stopped`**: A1-FAMILY's premise `hgVL` (`hgVR`): before the cap, the force
  points agree with a function measurable for the two stopped records, from replacement drivers measurable for the
  records (A1-SEEDGEOM's form for the driver, `exists_measurable_rDrvFst_of_stopped`) and a record-measurable mark.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Forces

open QuantumZipper (H IsForwardSol fwdMap)
open A2X A1Ref A1Core A1Marg A1MultiMark A1SeedGeom A1Family Sec2

/-! ### The clock at a good horizon stays below the lifetime -/

/-- **The clock at a good horizon is strictly below the canonical image lifetime.** -/
theorem ofReal_imgClk_lt_imgLife {xj xk τ : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ) {S : ℝ}
    (hS : IsGoodTime xj wj ζj xk wk τ S) :
    ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ S) < imgLife xj wj ζj xk wk τ := by
  obtain ⟨T, hT, hST⟩ := exists_isGoodTime hS.1.le hS.2
  obtain ⟨-, hmono, -⟩ := exists_isImgDrvOn hj hj0 hk hk0 hτ hT
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.1.le⟩
  have hSI : S ∈ Icc 0 T := ⟨hS.1.le, hST.le⟩
  have hlt := hmono hSI ⟨hT.1.le, le_rfl⟩ hST
  have hnn : 0 ≤ A1Ref.imgClk xj wj xk wk τ S := by
    rw [← imgClk_zero (xj := xj) (wj := wj) (xk := xk) (wk := wk) (τ := τ)]
    exact hmono.monotoneOn h0 hSI hS.1.le
  have hle : ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ T) ≤ imgLife xj wj ζj xk wk τ :=
    le_iSup₂_of_le (f := fun (r : ℝ≥0) (_ : (r : ℝ≥0∞) < contactTime xj wj ζj xk wk τ) =>
      ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ r)) (Real.toNNReal T)
      (by rw [← ENNReal.ofReal]; exact hT.2) (by rw [Real.coe_toNNReal _ hT.1.le])
  exact ((ENNReal.ofReal_lt_ofReal_iff (hnn.trans_lt hlt)).2 hlt).trans_le hle

/-! ### The force points on `X × Y` -/

section Fst

variable {X Y : Type*}

/-- **The family's force point of the mark `p`** (conditioning curve on `X`, image curve on `Y`, stop `τ`): the
masked canonical force `canonForce` read on `X × Y`, the mark `p x` read from the conditioning sample. -/
abbrev rForceFst (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (τ : X → ℝ≥0) (p : X → ℝ) : ℝ≥0 → X × Y → ℝ :=
  canonForce {z : X × Y | live (τ z.1) z.1} xj xk (fun z t => Wj t z.2) (fun z => ζj z.2) (fun z t => Wk t z.1)
    (fun z => τ z.1) (fun z => p z.1)

/-- On the fibre over `x` only the frozen time `τ x` and the mark at `τ x` are read (`FrozenFamilyFst.VLat`). -/
theorem rForceFst_at (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (τ : X → ℝ≥0) (p : ℝ≥0 → X → ℝ) (t : ℝ≥0) (z : X × Y) :
    rForceFst live xj Wj ζj xk Wk (fun _ => τ z.1) (p (τ z.1)) t z =
      rForceFst live xj Wj ζj xk Wk τ (fun x => p (τ x) x) t z := rfl

/-- **`FrozenFamilyFst.measurable_VL`**: the force points at the deterministic frozen time `σ`, with marks `p σ`, are
jointly measurable in `(σ, z)` (A1-MARG's standing hypotheses on the two drivers). -/
theorem measurable_rForceFst [MeasurableSpace X] [MeasurableSpace Y] {live : ℝ≥0 → X → Prop}
    (hlive : MeasurableSet {q : ℝ≥0 × X | live q.1 q.2}) {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    {Wk : ℝ≥0 → X → ℝ} {ζk : X → ℝ≥0∞} (hlk : ∀ s x, live s x → (s : ℝ≥0∞) < ζk x)
    (hjc : ∀ y, ContinuousOn (Wj · y) {t | (t : ℝ≥0∞) < ζj y}) (hj0 : ∀ y, Wj 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk · x) {t | (t : ℝ≥0∞) < ζk x}) (hk0 : ∀ x, Wk 0 x = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    (xj xk : ℝ) {p : ℝ≥0 → X → ℝ} (hp : Measurable fun q : ℝ≥0 × X => p q.1 q.2) (t : ℝ≥0) :
    Measurable fun q : ℝ≥0 × (X × Y) => rForceFst live xj Wj ζj xk Wk (fun _ => q.1) (p q.1) t q.2 := by
  have hC := canonHyp_of_paths (Ω := ℝ≥0 × (X × Y)) (πj := fun q => q.2.2) (πk := fun q => q.2.1)
    (τ := Prod.fst) measurable_snd.snd measurable_snd.fst measurable_fst hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
  exact hC.measurable_canonForce xj xk (p := fun q => p q.1 q.2.1) (hp.comp (measurable_fst.prodMk
    measurable_snd.fst)) t

/-- **The force point is A1-MULTIMARK's canonical force `rFrzFst`** at a live sample, before the image lifetime, when
the mark is alive under the canonical driver. -/
theorem rForceFst_eq_rFrzFst {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
    {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {p : X → ℝ} {t : ℝ≥0} {x : X} {y : Y} (hlive : live (τ x) x)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj y → ContinuousOn (Strip.extPath (Wj · y)) (Icc 0 T))
    (hj0 : Strip.extPath (Wj · y) 0 = 0)
    (hk : ∃ τ' : ℝ, (τ x : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ'))
    (hk0 : Strip.extPath (Wk · x) 0 = 0)
    (ht : ENNReal.ofReal t < imgLife xj (Strip.extPath (Wj · y)) (ζj y) xk (Strip.extPath (Wk · x)) (τ x))
    {v : ℝ → ℂ} (hv : IsForwardSol (imgDrv xj (Strip.extPath (Wj · y)) (ζj y) xk (Strip.extPath (Wk · x)) (τ x))
      (p x : ℂ) t v) :
    rForceFst live xj Wj ζj xk Wk τ p t (x, y) = rFrzFst live xj Wj ζj xk Wk τ p t (x, y) := by
  have e := canonForce_eq_imgForce (L := {z : X × Y | live (τ z.1) z.1}) (xj := xj) (xk := xk)
    (wj := fun z t => Wj t z.2) (ζj := fun z => ζj z.2) (wk := fun z t => Wk t z.1) (τ := fun z => τ z.1)
    (p := fun z => p z.1) (t := t) (ω := (x, y)) hlive hj hj0 hk hk0 ht hv
  rw [rForceFst, e]
  simp only [rFrzFst, hlive, ↓reduceIte]

/-- **Up to the capacity horizon of seeded data of the image curve** (frame `0`), at a live sample, the force point
of a mark alive under the seeded image driver up to the horizon is A1-MULTIMARK's `rFrzFst`. -/
theorem rForceFst_eq_rFrzFst_of_seed {n : ℕ} {live : ℝ≥0 → X → Prop} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {p : X → ℝ} {x : X} (hlive : live (τ x) x) {d : Y → SeedData n}
    {S : Y → ℝ≥0} (hW : ∀ y, (d y).W = Strip.extPath (Wj · y))
    (hown : ∀ y, OwnData (d y).W (physHull (xk - 0) (Strip.extPath (Wk · x)) (τ x)) (d y).φ (S y) (d y).a
      (d y).W')
    (hφ : ∀ y, (d y).φ = physMap (xk - 0) (Strip.extPath (Wk · x)) (τ x))
    (hj : ∀ y T, ENNReal.ofReal T < ζj y → ContinuousOn (d y).W (Icc 0 T))
    (hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · x)) (Icc 0 τ')) (hk0 : Wk 0 x = 0)
    (hgood : ∀ y, IsGoodTime 0 (d y).W (ζj y) (xk - 0) (Strip.extPath (Wk · x)) (τ x) (S y)) (y : Y)
    (hv : ∃ v : ℝ → ℂ, IsForwardSol (d y).W' (p x : ℂ) ((d y).a (S y)) v) {t : ℝ≥0}
    (ht : t ≤ seedCapacityHorizon d S y) :
    rForceFst live 0 Wj ζj xk Wk τ p t (x, y) = rFrzFst live 0 Wj ζj xk Wk τ p t (x, y) := by
  simp only [sub_zero] at hown hφ hgood
  have h := hown y
  have h' : OwnData (d y).W (physHull xk (Strip.extPath (Wk · x)) (τ x)) (physMap xk (Strip.extPath (Wk · x)) (τ x))
      (S y) (d y).a (d y).W' := by rw [← hφ y]; exact h
  have hk0' : Strip.extPath (Wk · x) 0 = 0 := by simp [Strip.extPath, hk0]
  have hEq := imgDrv_eqOn_of_ownData (hj y) h.zero hk hk0' (τ x).coe_nonneg (hgood y) h'
  have haS0 : 0 ≤ (d y).a (S y) := by
    rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ ⟨(S y).coe_nonneg, le_rfl⟩ (S y).coe_nonneg
  have htS : (t : ℝ) ≤ (d y).a (S y) := by
    have := NNReal.coe_le_coe.2 ht
    rwa [seedCapacityHorizon, Real.coe_toNNReal _ haS0] at this
  have hclk : (d y).a (S y) = A1Ref.imgClk 0 (d y).W xk (Strip.extPath (Wk · x)) (τ x) (S y) :=
    (isImgDrvOn_of_ownData h').2 ⟨(S y).coe_nonneg, le_rfl⟩
  have hlife : ENNReal.ofReal t < imgLife 0 (d y).W (ζj y) xk (Strip.extPath (Wk · x)) (τ x) :=
    (ENNReal.ofReal_le_ofReal htS).trans_lt (hclk ▸ ofReal_imgClk_lt_imgLife (hj y) h.zero hk hk0'
      (τ x).coe_nonneg (hgood y))
  obtain ⟨v, hv⟩ := hv
  have hv' : IsForwardSol (imgDrv 0 (d y).W (ζj y) xk (Strip.extPath (Wk · x)) (τ x)) (p x : ℂ) t v :=
    QuantumZipper.isForwardSol_congr_drive (fun r hr => (hEq ⟨hr.1, hr.2.trans htS⟩).symm)
      (QuantumZipper.isForwardSol_restrict hv t.coe_nonneg htS)
  rw [hW y] at hlife hv'
  have hjy : ∀ T : ℝ, ENNReal.ofReal T < ζj y → ContinuousOn (Strip.extPath (Wj · y)) (Icc 0 T) := by
    rw [← hW y]; exact hj y
  exact rForceFst_eq_rFrzFst hlive hjy (by rw [← hW y]; exact h.zero) hk hk0' hlife hv'

/-! ### The large-curve direction: marks, geometry -/

/-- The G3 large-direction marks are jointly measurable in the frozen time and the conditioning sample. -/
theorem measurable_largeG3Marks [MeasurableSpace X] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} (hW : Measurable fun q : ℝ≥0 × X => W₁ q.1 q.2)
    (hL : ∀ i, Measurable fun q : ℝ≥0 × X => VL₁ i q.1 q.2) (hR : ∀ j, Measurable fun q : ℝ≥0 × X => VR₁ j q.1 q.2)
    (x₀ : ℝ) (i : Fin 4) :
    Measurable fun q : ℝ≥0 × X => largeG3Marks x₀ (W₁ · q.2) (fun i t => VL₁ i t q.2) (fun j t => VR₁ j t q.2)
      q.1 i := by
  fin_cases i
  · exact measurable_const.add (hR 1)
  · exact measurable_const.add (hR 0)
  · exact measurable_const.add hW
  · exact measurable_const.add (hL 0)

/-- The Eight large-direction marks are jointly measurable in the frozen time and the conditioning sample. -/
theorem measurable_largeEightMarks [MeasurableSpace X] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} (hW : Measurable fun q : ℝ≥0 × X => W₁ q.1 q.2)
    (hL : ∀ i, Measurable fun q : ℝ≥0 × X => VL₁ i q.1 q.2) (hR : ∀ j, Measurable fun q : ℝ≥0 × X => VR₁ j q.1 q.2)
    (x₀ : ℝ) (i : Fin 3) :
    Measurable fun q : ℝ≥0 × X => largeEightMarks x₀ (W₁ · q.2) (fun i t => VL₁ i t q.2) (fun j t => VR₁ j t q.2)
      q.1 i := by
  fin_cases i
  · exact measurable_const.add (hR 0)
  · exact measurable_const.add hW
  · exact measurable_const.add (hL 0)

/-- **A1-FAMILY's `hgeom`, G3 large-curve direction, with the measurable force points `rForceFst`.** -/
theorem seedImageGeometry_rDrvFst_largeG3_force {κ x' y' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X} {n : ℕ}
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
      (fun i t => rForceFst live 0 Wj ζj xk W₁ τ (fun x => largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x)
        (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y))
      (fun j t => VR j (min t cap)) cap := by
  have h := seedImageGeometry_rDrvFst_largeG3_canon (VR := VR) hx' hP hlive hτ hxk hW hown hφ hj hgood hCc hCs hc
    hClb y hv hne hcap
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  have e : (fun (i : Fin 4) (t : ℝ≥0) => rForceFst live 0 Wj ζj xk W₁ τ (fun x => largeG3Marks (xk - 0) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y)) =
      fun i t => rFrzFst live 0 Wj ζj xk W₁ τ (fun x => largeG3Marks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x)
        (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y) := by
    funext i t
    exact rForceFst_eq_rFrzFst_of_seed hlive hW hown hφ hj hk hP.1 hgood y (hv i)
      ((min_le_right t cap).trans hcap)
  rw [e]
  exact h

/-- **A1-FAMILY's `hgeom`, Eight large-curve direction, with the measurable force points `rForceFst`.** -/
theorem seedImageGeometry_rDrvFst_largeEight_force {κ x' : ℝ} (hx' : x' < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {x : X} {n : ℕ}
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
      (fun i t => rForceFst live 0 Wj ζj xk W₁ τ (fun x => largeEightMarks (xk - 0) (W₁ · x)
        (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y))
      (fun j t => VR j (min t cap)) cap := by
  have h := seedImageGeometry_rDrvFst_largeEight_canon (VR := VR) hx' hP hlive hτ hxk hW hown hφ hj hgood hCc hCs
    hc hClb y hv hne hcap
  have hk : ∃ τ', ((τ x : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · x)) (Icc 0 τ') :=
    exists_continuousOn_extPath_beyond hP.2.2.2.1 hτ
  have e : (fun (i : Fin 3) (t : ℝ≥0) => rForceFst live 0 Wj ζj xk W₁ τ (fun x => largeEightMarks (xk - 0) (W₁ · x)
      (fun i t => VL₁ i t x) (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y)) =
      fun i t => rFrzFst live 0 Wj ζj xk W₁ τ (fun x => largeEightMarks (xk - 0) (W₁ · x) (fun i t => VL₁ i t x)
        (fun j t => VR₁ j t x) (τ x) i) (min t cap) (x, y) := by
    funext i t
    exact rForceFst_eq_rFrzFst_of_seed hlive hW hown hφ hj hk hP.1 hgood y (hv i)
      ((min_le_right t cap).trans hcap)
  rw [e]
  exact h

/-! ### Before the cap: record measurability (`hgVL`) -/

/-- **Locality of the force point**: at a live sample (for both live events), if the image curve's drivers agree up
to a horizon `T` good for both and the conditioning curve's drivers agree up to the stop, then at image times up to the
clock of `T` the two force points of marks agreeing at the sample coincide. -/
theorem rForceFst_congr {live live' : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → Y → ℝ} {ζj ζj' : Y → ℝ≥0∞}
    {Wk Wk' : ℝ≥0 → X → ℝ} {τ : X → ℝ≥0} {p p' : X → ℝ} {z : X × Y} {T : ℝ} (hlive : live (τ z.1) z.1)
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
    (hjeq : ∀ t : ℝ≥0, (t : ℝ) ≤ T → Wj' t z.2 = Wj t z.2) (hkeq : ∀ t ≤ τ z.1, Wk' t z.1 = Wk t z.1)
    (hp : p' z.1 = p z.1) {r : ℝ≥0}
    (hr : (r : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) T) :
    rForceFst live' xj Wj' ζj' xk Wk' τ p' r z = rForceFst live xj Wj ζj xk Wk τ p r z := by
  have hjE : EqOn (Strip.extPath (Wj · z.2)) (Strip.extPath (Wj' · z.2)) (Icc 0 T) := fun s hs => by
    simp only [Strip.extPath]
    rw [hjeq _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)]
  have hkE : EqOn (Strip.extPath (Wk · z.1)) (Strip.extPath (Wk' · z.1)) (Icc 0 (τ z.1)) := fun s hs => by
    simp only [Strip.extPath]
    rw [hkeq _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hj00 : Strip.extPath (Wj · z.2) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hj0]
  have hj00' : Strip.extPath (Wj' · z.2) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hj0']
  have hk00 : Strip.extPath (Wk · z.1) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hk0]
  have hk00' : Strip.extPath (Wk' · z.1) 0 = 0 := by simp only [Strip.extPath, Real.toNNReal_zero, hk0']
  have hE := imgDrv_congr hj hj00 hj' hj00' hk hk00 hk' hk00' (τ z.1).coe_nonneg hT hT' hjE hkE
  -- the clocks at `T` agree
  obtain ⟨T₁, hT₁, hc₁⟩ := exists_continuousOn_beyond_of_isGoodTime hj hT
  obtain ⟨T₂, hT₂, hc₂⟩ := exists_continuousOn_beyond_of_isGoodTime hj' hT'
  have hclk : A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) T =
      A1Ref.imgClk xj (Strip.extPath (Wj' · z.2)) xk (Strip.extPath (Wk' · z.1)) (τ z.1) T :=
    imgClk_congr (τ z.1).coe_nonneg hkE (hc₁.mono (Icc_subset_Icc_right (min_le_left T₁ T₂)))
      (hc₂.mono (Icc_subset_Icc_right (min_le_right T₁ T₂))) (lt_min hT₁ hT₂) hjE
  have hlife : ENNReal.ofReal r < imgLife xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1))
      (τ z.1) :=
    (ENNReal.ofReal_le_ofReal hr).trans_lt (ofReal_imgClk_lt_imgLife hj hj00 hk hk00 (τ z.1).coe_nonneg hT)
  have hlife' : ENNReal.ofReal r < imgLife xj (Strip.extPath (Wj' · z.2)) (ζj' z.2) xk (Strip.extPath (Wk' · z.1))
      (τ z.1) :=
    (ENNReal.ofReal_le_ofReal (hr.trans hclk.le)).trans_lt
      (ofReal_imgClk_lt_imgLife hj' hj00' hk' hk00' (τ z.1).coe_nonneg hT')
  have h0 : (0 : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) T :=
    r.coe_nonneg.trans hr
  have hstop : stopDrv (imgDrv xj (Strip.extPath (Wj' · z.2)) (ζj' z.2) xk (Strip.extPath (Wk' · z.1)) (τ z.1)) r =
      stopDrv (imgDrv xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1)) r := by
    funext s
    simp only [stopDrv]
    exact (hE ⟨le_max_left _ _, max_le h0 ((min_le_right _ _).trans hr)⟩).symm
  show canonForce _ xj xk _ _ _ _ _ r z = canonForce _ xj xk _ _ _ _ _ r z
  rw [canonForce, canonForce, ite_eq_left (show z ∈ {z : X × Y | live' (τ z.1) z.1} ∧ _ from ⟨hlive', hlife'⟩),
    ite_eq_left (show z ∈ {z : X × Y | live (τ z.1) z.1} ∧ _ from ⟨hlive, hlife⟩)]
  rw [hstop, hp, ← hE ⟨r.coe_nonneg, hr⟩, ← hE ⟨le_rfl, h0⟩]

/-- **`hgVL` (`hgVR`) of `FamilyRectFst.ofRect` from stopped versions measurable for the records** (the mirror of
A1-SEEDGEOM's `exists_measurable_rDrvFst_of_stopped` for the force points): with `𝓐` on `X` and `𝓑` on `Y` the records
as measurable structures, replacement data `(Wj', ζj')`, `(Wk', ζk')`, `live'` satisfying A1-MARG's (m3) hypotheses
for them, `τ` record-measurable and a record-measurable replacement mark `p'`, if on `{r < cap}` the replacements agree
with the original data up to a horizon `T z` good for both whose clock reaches `cap z` (A1-SEEDGEOM's `hloc`,
verbatim) and the marks agree, then the force point at `r` agrees on `{r < cap}` with a record-measurable function. -/
theorem exists_measurable_rForceFst_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y]
    {live live' : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj Wj' : ℝ≥0 → Y → ℝ} {ζj ζj' : Y → ℝ≥0∞} {Wk Wk' : ℝ≥0 → X → ℝ}
    {ζk' : X → ℝ≥0∞} {τ : X → ℝ≥0} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × X | live' q.1 q.2}) (hlk : ∀ s x, live' s x → (s : ℝ≥0∞) < ζk' x)
    (hjc : ∀ y, ContinuousOn (Wj' · y) {t | (t : ℝ≥0∞) < ζj' y}) (hj0' : ∀ y, Wj' 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk' · x) {t | (t : ℝ≥0∞) < ζk' x}) (hk0' : ∀ x, Wk' 0 x = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    {p p' : X → ℝ} (hp' : Measurable p') {cap : X × Y → ℝ≥0} {T : X × Y → ℝ} (r : ℝ≥0)
    (hloc : ∀ z : X × Y, r < cap z →
      live (τ z.1) z.1 ∧ live' (τ z.1) z.1 ∧
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T)) ∧ Wj 0 z.2 = 0 ∧
      (∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ')) ∧ Wk 0 z.1 = 0 ∧
      IsGoodTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z) ∧
      IsGoodTime xj (Strip.extPath (Wj' · z.2)) (ζj' z.2) xk (Strip.extPath (Wk' · z.1)) (τ z.1) (T z) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T z → Wj' t z.2 = Wj t z.2) ∧ (∀ t ≤ τ z.1, Wk' t z.1 = Wk t z.1) ∧
      (cap z : ℝ) ≤ A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z))
    (hp : ∀ z : X × Y, r < cap z → p' z.1 = p z.1) :
    ∃ f : X × Y → ℝ, Measurable f ∧ ∀ z, r < cap z → rForceFst live xj Wj ζj xk Wk τ p r z = f z := by
  have hC := canonHyp_of_paths (Ω := X × Y) (πj := Prod.snd) (πk := Prod.fst) (τ := fun z => τ z.1)
    measurable_snd measurable_fst (hτ.comp measurable_fst) hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk
  refine ⟨rForceFst live' xj Wj' ζj' xk Wk' τ p' r,
    hC.measurable_canonForce xj xk (p := fun z => p' z.1) (hp'.comp measurable_fst) r, fun z hz => ?_⟩
  obtain ⟨hl, hl', hj, hj0, hk, hk0, hT, hT', hjeq, hkeq, hcap⟩ := hloc z hz
  have hk' : ∃ τ', ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk' · z.1)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (hkc z.1) (hlk _ _ hl')
  have hj' : ∀ T : ℝ, ENNReal.ofReal T < ζj' z.2 → ContinuousOn (Strip.extPath (Wj' · z.2)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (hjc z.2) hT
  exact (rForceFst_congr hl hl' hj hj0 hj' (hj0' z.2) hk hk0 hk' (hk0' z.1) hT hT' hjeq hkeq (hp z hz)
    ((NNReal.coe_le_coe.2 hz.le).trans hcap)).symm

end Fst

end InteractingSLE.ZhanGT4.A1Forces
