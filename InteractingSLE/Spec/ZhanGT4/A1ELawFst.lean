/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawEightRect
import InteractingSLE.Spec.ZhanGT4.A1LargeDensEncl
import InteractingSLE.Spec.ZhanGT4.A1G3RowEight
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldPath

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the per-sample frozen law

Packet PROVE-A1-EIGHTLAW (R83). The image curve is the large curve (on `Y`, ordinary `SLE_κ`: its only mark has weight
`0`), the conditioning curve the small curve (on `X`), frozen at the own time `s`. A1-LARGEDENS proved the one-sample
law from enclosure data in its own frame (`isSeedSampleLaw_largeEight_of_encl`: large curve started at `0`, small
physical driver `W₁ − p` started at `x = −p`), and A1-G3ROW identified the patch density with its Girsanov density
(`seedHeightField_eightRec_eq_girsDensity`, `isSeedSampleLaw_eightRec_of_girs`). This file supplies every enclosure,
frame and mark input of these theorems from the patched Eight marginals and A1-COMMON's cofinal rectangles:

* the frame translation: `disjoint_ball_transl`, `sep_transl`, `mem_closure_transl`;
* `drive_eq_extPath_largeEight`: the large driver is `√κ B` before its lifetime (weight-`0` mark);
* **`eightFst_frame`**: the hulls of both curves lie in the translated cofinal enclosures;
* **`exists_ownData_eightFst`**: an image chain of the large curve against the frozen small hull exists at every
  large sample, up to the rectangle exit;
* **`eightFst_isSeedSampleLaw`**: at every small sample `x₀` and own time `s ∈ (0, S₁ᵐ(x₀)]`, under the rectangle
  density `P₂.withDensity (y ↦ M(s, S₂ᵐ(y)))` (A1-RECTLAW2's large-direction family density at `σ` with
  `σ ∧ S₁ᵐ(x₀) = s`), every image datum equal up to the cap to the seeded capacity coordinates of seeded data carrying
  the chain (driver, the three frozen-chart forces `x⁺`, the small tip, `x⁻`, the residual as the noise, the cap the
  capacity horizon, the other caps image capacities at own-time stopping times) satisfies `IsSeedSampleLaw`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ELaw

open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1RLaw A1LargeDens A1G3Row A1MultiMark

/-! ### Translating the enclosure data -/

section Transl

/-- A ball disjoint from a set stays disjoint after a real translation of both. -/
theorem disjoint_ball_transl {E : Set ℂ} {q r : ℝ} (h : Disjoint (ball (q : ℂ) r) E) (c : ℝ) :
    Disjoint (ball ((q + c : ℝ) : ℂ) r) (transl c E) := by
  refine Set.disjoint_left.2 fun w hw hwE => ?_
  rw [mem_transl_iff] at hwE
  refine Set.disjoint_left.1 h ?_ hwE
  rw [mem_ball, dist_eq_norm] at hw ⊢
  have e : w - (c : ℂ) - (q : ℂ) = w - ((q + c : ℝ) : ℂ) := by push_cast; ring
  rwa [e]

/-- The separation of two enclosures survives a common real translation (roles swapped). -/
theorem sep_transl {H₁ H₂ : Set ℂ} {δ : ℝ} (h : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) (c : ℝ) :
    ∀ a ∈ transl c H₁, ∀ z ∈ transl c H₂, 2 * δ ≤ ‖a - z‖ := by
  intro a ha z hz
  rw [mem_transl_iff] at ha hz
  have hb := h _ hz _ ha
  have e : z - (c : ℂ) - (a - (c : ℂ)) = -(a - z) := by ring
  rwa [e, norm_neg] at hb

/-- A point of the closure moves into the closure of the translate. -/
theorem mem_closure_transl {E : Set ℂ} {w : ℂ} (h : w ∈ closure E) (c : ℝ) :
    w + (c : ℂ) ∈ closure (transl c E) :=
  image_closure_subset_closure_image (continuous_id.add continuous_const) (mem_image_of_mem _ h)

end Transl

/-! ### The large curve's driver -/

/-- **The large Eight driver is `√κ B` before its lifetime** (its only mark has weight `0`). -/
theorem drive_eq_extPath_largeEight {κ x : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 0 → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hP : IsIntegratedSLEPath κ ![x] ![] ![0] ![] w vL vR b ζ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) : ∀ u ∈ Icc (0 : ℝ) T, (Real.sqrt κ * b u.toNNReal) = Strip.extPath w u := by
  intro u hu
  have hle : u.toNNReal ≤ T := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1]; exact hu.2
  have h := driver_eq_of_path hP (t := u.toNNReal) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hle) hT)
  simp only [Strip.extPath, h, Fin.sum_univ_one, Fin.sum_univ_zero, Matrix.cons_val_zero, neg_zero, zero_div,
    zero_mul, add_zero]

section Frame

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The frame facts of the large direction** at a small sample `x₀` and own time `s ≤ S₁ᵐ(x₀)`: the large
drivers `√κ B₂` are continuous, start at `0`, the rectangle exits are positive, the frozen physical small driver
`W₁ − p` (stopped at the exit, `p = −x`) is continuous, the translated enclosures are separated and contain the hulls
of the large curve up to its exit and of the frozen small curve up to `s`. -/
theorem eightFst_frame {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {s : ℝ} (hsS : s ≤ eightS₁ x W₁ ζ₁ m x₀) :
    (∀ y, Continuous (drive κ B₂ y)) ∧ (∀ y, drive κ B₂ y 0 = 0) ∧ (∀ y, 0 < (eightS₂ x W₂ ζ₂ m y : ℝ)) ∧
      Continuous (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) ∧
      (∀ a ∈ transl (-(-x)) (cofH₁ (-x) ![] m), ∀ z ∈ transl (-(-x)) (cofH₂ (-x) ![] m),
        2 * cofδ (-x) ![] m ≤ ‖a - z‖) ∧
      (∀ y, ∀ u ∈ Icc (0 : ℝ) (eightS₂ x W₂ ζ₂ m y), drive κ B₂ y u = Strip.extPath (W₂ · y) u) ∧
      (∀ y, fwdHull (drive κ B₂ y) (eightS₂ x W₂ ζ₂ m y) ⊆ transl (-(-x)) (cofH₂ (-x) ![] m)) ∧
      fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s ⊆ transl (-(-x)) (cofH₁ (-x) ![] m) := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, -, hc₂, -, hgood₂, hS₂pos, hlt₂⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hpp := hF.pp m
  have hdc : ∀ y, Continuous (drive κ B₂ y) := fun y =>
    continuous_const.mul ((hB₂ y).comp continuous_real_toNNReal)
  have hdrive : ∀ y, ∀ u ∈ Icc (0 : ℝ) (eightS₂ x W₂ ζ₂ m y), drive κ B₂ y u = Strip.extPath (W₂ · y) u :=
    fun y u hu => drive_eq_extPath_largeEight (h₂.path y) (hlt₂ m y) u hu
  have hd0 : ∀ y, drive κ B₂ y 0 = 0 := fun y => by
    rw [hdrive y 0 ⟨le_rfl, NNReal.coe_nonneg _⟩]
    simp only [Strip.extPath, Real.toNNReal_zero]
    exact (h₂.path y).1
  have hWc : Continuous (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 (hgood₁ m x₀).1
  have hK₁ : ∀ y, fwdHull (drive κ B₂ y) (eightS₂ x W₂ ζ₂ m y) ⊆ transl (-(-x)) (cofH₂ (-x) ![] m) := by
    intro y
    set T := (eightS₂ x W₂ ζ₂ m y : ℝ) with hT
    have hsc : Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y)) T) :=
      A1Ref.continuous_stopDrv (hc₂ m y) (NNReal.coe_nonneg _)
    have heq : fwdHull (drive κ B₂ y) T = fwdHull (fun u => frzPath W₂ (-x) T y u - -x) T := by
      have e : (fun u => frzPath W₂ (-x) T y u - -x) = A1Ref.stopDrv (Strip.extPath (W₂ · y)) T := by
        funext u; simp only [frzPath, add_sub_cancel_right]
      rw [e]
      refine LocalExt.fwdHull_congr_of_continuousOn (hdc y).continuousOn hsc.continuousOn
        (NNReal.coe_nonneg _) (lt_add_one T) fun u hu => ?_
      rw [hdrive y u hu, A1Ref.stopDrv_eqOn _ _ hu]
    rw [heq, fwdHull_sub_const]
    exact image_mono (hgood₂ m y).2
  have hK₂ : fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s ⊆
      transl (-(-x)) (cofH₁ (-x) ![] m) := by
    rw [fwdHull_sub_const]
    exact image_mono ((QuantumZipper.fwdHull_mono.1 hsS).trans (hgood₁ m x₀).2.2.2)
  exact ⟨hdc, hd0, hS₂pos m, hWc.sub continuous_const, sep_transl hpp.sep _, hdrive, hK₁, hK₂⟩

/-- **An image chain of the large curve against the frozen small hull exists at every large sample**, up to the
rectangle exit (A1-EIGHTSEED's `exists_ownData_of_encl` with the translated enclosures). -/
theorem exists_ownData_eightFst {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {s : ℝ} (hs : 0 < s) (hsS : s ≤ eightS₁ x W₁ ζ₁ m x₀) :
    ∃ a W' : Y → ℝ → ℝ, ∀ y, OwnData (drive κ B₂ y)
      (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y) := by
  obtain ⟨hdc, hd0, hSpos, hWc, hsep, -, hK₁, hK₂⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hsS
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hpp := (isEnclFamily_cof hne).pp m
  have h : ∀ y, ∃ a W', OwnData (drive κ B₂ y)
      (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s) (eightS₂ x W₂ ζ₂ m y) a W' := fun y =>
    exists_ownData_of_encl (hdc y) (hd0 y) (hSpos y) hWc hs.le hpp.sep_pos hsep (hK₁ y) hK₂
  choose a W' haW using h
  exact ⟨a, W', haW⟩

/-- **The per-sample frozen law of the large image curve** ((Eight), large-curve direction) at every small sample
`x₀` and own time `s ∈ (0, S₁ᵐ(x₀)]`: under the rectangle density `P₂.withDensity (y ↦ M(s, S₂ᵐ(y)))`, for every image
chain `(a, W')` of the large curve against the frozen small hull up to the rectangle exit (`exists_ownData_eightFst`)
and seeded data `d` carrying it, image data equal up to the cap to the seeded capacity coordinates (driver, the
frozen-chart forces of `x⁺`, the small tip and `x⁻` in the physical frame, the residual as the noise, the cap the
capacity horizon, the other caps image capacities at own-time stopping times) satisfy `IsSeedSampleLaw`. -/
theorem eightFst_isSeedSampleLaw {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {s : ℝ} (hs : 0 < s) (hsS : s ≤ eightS₁ x W₁ ζ₁ m x₀) {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y, OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y))
    {n' : ℕ} {d : Y → SeedData n'} {A' : Y → Set ℂ}
    (hown : ∀ y, OwnData (d y).W (A' y) (d y).φ (eightS₂ x W₂ ζ₂ m y) (d y).a (d y).W')
    (hda : ∀ y, (d y).a = a y) (hdW' : ∀ y, (d y).W' = W' y)
    {Wi : ℝ≥0 → Y → ℝ} {ζi : Y → ℝ≥0∞} {VL : Fin 3 → ℝ≥0 → Y → ℝ} {VR : Fin 0 → ℝ≥0 → Y → ℝ}
    {N : ℝ≥0 → Y → ℝ} {Scap : ℕ → Y → ℝ≥0} {m' : ℕ}
    (hSm : ∀ y, Scap m' y = seedCapacityHorizon d (eightS₂ x W₂ ζ₂ m) y)
    (hW : ∀ y t, t ≤ Scap m' y → Wi t y = seedCapacityDriver d (eightS₂ x W₂ ζ₂ m) t y)
    (hVL : ∀ y i t, t ≤ Scap m' y → VL i t y = capForce d (eightS₂ x W₂ ζ₂ m)
      (fun y => frzImg (d y).W' (d y).a (![Strip.extPath (VR₁ 0 · x₀) s - -x,
        eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ s - -x, Strip.extPath (VL₁ 0 · x₀) s - -x] i)) t y)
    (hN : ∀ y t, t ≤ Scap m' y → N t y = seedCapacityNoise κ (largeEightImgRhoL κ) ![] (Wi · y)
      (fun i t => VL i t y) (fun j t => VR j t y) t)
    (hζ : ∀ y, (Scap m' y : ℝ≥0∞) ≤ ζi y)
    (Tk : ℕ → Y → ℝ≥0) (hTk : ∀ k, IsStoppingTime 𝓖₂ fun y => (Tk k y : WithTop ℝ≥0))
    (hcap₁ : ∀ k y, Tk k y ≤ eightS₂ x W₂ ζ₂ m y → (Scap k y : ℝ) = (d y).a (Tk k y))
    (hcap₂ : ∀ k y, eightS₂ x W₂ ζ₂ m y ≤ Tk k y → Scap m' y ≤ Scap k y) :
    IsSeedSampleLaw (P₂.withDensity fun y =>
        ENNReal.ofReal (eightM κ x W₁ VL₁ VR₁ ζ₁ W₂ m (x₀, y) s (eightS₂ x W₂ ζ₂ m y)))
      Wi ζi VL VR N Scap m' := by
  have hκ : 0 < κ := by linarith
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, -⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hpp := hF.pp m
  obtain ⟨-, -, -, hWsc, hsep, hdrive, hK₁, hK₂⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hsS
  have hS₂ : IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0) :=
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) m
  -- the frozen small curve at `s`: driver, seeds and the protected point
  set S₁ := eightS₁ x W₁ ζ₁ with hS₁def
  have hlt₁ : (S₁ m x₀ : ℝ≥0∞) < ζ₁ x₀ := (hgood₁ m x₀).1
  have hWc : Continuous (eightDrv W₁ S₁ m x₀) := continuous_eightDrv (h₁.path x₀).2.2.2.1 hlt₁
  have hW0 : eightDrv W₁ S₁ m x₀ 0 = 0 := eightDrv_zero (h₁.path x₀).1
  have hne' : ∀ t : ℝ≥0, 0 < t → t ≤ S₁ m x₀ → VL₁ 0 t x₀ ≠ W₁ t x₀ ∧ VR₁ 0 t x₀ ≠ W₁ t x₀ := fun t ht htS =>
    hsep₁ x₀ t ht (lt_of_le_of_lt (ENNReal.coe_le_coe.2 htS) hlt₁)
  have hhi : IsSeedCoordinate (eightDrv W₁ S₁ m x₀) (Strip.extPath (VR₁ 0 · x₀)) (S₁ m x₀) :=
    isSeedCoordinate_vR_of_path (h₁.path x₀) 0 rfl hlt₁ (fun t ht htS => (hne' t ht htS).2)
      (eightDrv_eqOn W₁ S₁ m x₀)
  have hq2 : Disjoint (ball (cofq (-x) ![] m : ℂ) (2 * cofd (-x) ![] m)) (fwdHull (eightDrv W₁ S₁ m x₀) (S₁ m x₀)) :=
    hpp.prot.mono_right ((hgood₁ m x₀).2.2.2.trans subset_union_left)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball hWc hW0 hpp.prot_pos.ne' (NNReal.coe_nonneg _)
    (by have := hpp.rad_pos; positivity) hq2
  have hsI : s ∈ Icc (0 : ℝ) (S₁ m x₀) := ⟨hs.le, hsS⟩
  have hgq : fwdMap (eightDrv W₁ S₁ m x₀) s (cofq (-x) ![] m : ℂ) = u s := fwdMap_eq_of_isForwardSol hWc hu hsI
  have hRq : Strip.extPath (VR₁ 0 · x₀) s < (u s).re + eightDrv W₁ S₁ m x₀ s :=
    hhi.lt_gmap hWc (by rw [hW0]; exact hpp.prot_pos) hu hsI
  -- the order of the seeds and the driver at `s`
  have hsN : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ₁ x₀ := by
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hlt₁
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.le]; exact hsS
  obtain ⟨hLW, hWR⟩ := hg₁ x₀ s.toNNReal hsN hsζ
  have hWs : eightDrv W₁ S₁ m x₀ s = W₁ s.toNNReal x₀ := eightDrv_eqOn W₁ S₁ m x₀ hsI
  have h1 : Strip.extPath (VL₁ 0 · x₀) s < eightDrv W₁ S₁ m x₀ s := by rw [hWs]; exact hLW
  have h2 : eightDrv W₁ S₁ m x₀ s < Strip.extPath (VR₁ 0 · x₀) s := by rw [hWs]; exact hWR
  set vr := Strip.extPath (VR₁ 0 · x₀) s with hvr
  set vl := Strip.extPath (VL₁ 0 · x₀) s with hvl
  set wv := eightDrv W₁ S₁ m x₀ s with hwv
  -- the marks in A1-LARGEDENS's frame
  have hgqx : (fwdMap (fun u => eightDrv W₁ S₁ m x₀ u - -x) s ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ)).re =
      (u s).re := by
    rw [fwdMap_sub_const]
    have e : (((cofq (-x) ![] m + -(-x) : ℝ) : ℂ) + ((-x : ℝ) : ℂ)) = (cofq (-x) ![] m : ℂ) := by push_cast; ring
    rw [e, hgq]
  set ν := min (min (vr - wv) (wv - vl)) (vr - vl) with hν
  have hνpos : 0 < ν := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hν1 : ν ≤ vr - wv := (min_le_left _ _).trans (min_le_left _ _)
  have hν2 : ν ≤ wv - vl := (min_le_left _ _).trans (min_le_right _ _)
  have hν3 : ν ≤ vr - vl := min_le_right _ _
  have hζq : ∀ k, ![vr - -x, vl - -x] k <
      (fwdMap (fun u => eightDrv W₁ S₁ m x₀ u - -x) s ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ)).re +
        (fun u => eightDrv W₁ S₁ m x₀ u - -x) s := by
    intro k
    rw [hgqx]
    fin_cases k
    · show vr - -x < (u s).re + (wv - -x)
      linarith
    · show vl - -x < (u s).re + (wv - -x)
      linarith
  have hζM : ∀ k, |![vr - -x, vl - -x] k| ≤ |vr - -x| + |vl - -x| := by
    intro k
    fin_cases k
    · show |vr - -x| ≤ _
      linarith [abs_nonneg (vl - -x)]
    · show |vl - -x| ≤ _
      linarith [abs_nonneg (vr - -x)]
  have hζν : ∀ k, ν ≤ |![vr - -x, vl - -x] k - (fun u => eightDrv W₁ S₁ m x₀ u - -x) s| := by
    intro k
    fin_cases k
    · show ν ≤ |vr - -x - (wv - -x)|
      rw [abs_of_pos (by linarith)]; linarith
    · show ν ≤ |vl - -x - (wv - -x)|
      rw [abs_of_neg (by linarith)]; linarith
  have hζνmk : ∀ k l, k ≠ l → ν ≤ |![vr - -x, vl - -x] k - ![vr - -x, vl - -x] l| := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · show ν ≤ |vr - -x - (vl - -x)|
      rw [abs_of_pos (by linarith)]; linarith
    · show ν ≤ |vl - -x - (vr - -x)|
      rw [abs_of_neg (by linarith)]; linarith
    · exact absurd rfl hkl
  have hqneg : cofq (-x) ![] m + -(-x) < 0 := by linarith [hpp.prot_lt]
  have hqH := disjoint_ball_transl hpp.prot (-(-x))
  have hqH' : Disjoint (ball ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ) (2 * cofd (-x) ![] m))
      (transl (-(-x)) (cofH₂ (-x) ![] m) ∪ transl (-(-x)) (cofH₁ (-x) ![] m)) := by
    have e : transl (-(-x)) (cofH₂ (-x) ![] m) ∪ transl (-(-x)) (cofH₁ (-x) ![] m) =
        transl (-(-x)) (cofH₁ (-x) ![] m ∪ cofH₂ (-x) ![] m) := by
      unfold transl; rw [image_union, union_comm]
    rw [e]; exact hqH
  have hW₂H : (((fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 : ℝ) : ℂ) ∈ closure (transl (-(-x)) (cofH₁ (-x) ![] m)) := by
    have h0 := mem_closure_transl (hF.zero_mem_closure₁ m) (-(-x))
    have e : (((fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 : ℝ) : ℂ) = 0 + ((-(-x) : ℝ) : ℂ) := by
      simp only [hW0]; push_cast; ring
    rw [e]; exact h0
  have hqW : (fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 < cofq (-x) ![] m + -(-x) := by
    simp only [hW0]; linarith [hpp.prot_pos]
  have hlaw := isSeedSampleLaw_largeEight_of_encl (hF.hull₂ m) (isHPHull_transl hpp.hull₁ _) hpp.sep_pos hsep
    hpp.rad_pos hqneg hqH' hνpos hκ h₂.evol.1 hB₂ hS₂ (T := fun y => (eightS₂ x W₂ ζ₂ m y : ℝ)) hown₁
    (fun y => le_rfl) (fun y => (hgood₂ m y).1) hK₁ hWsc hW₂H hqW hs (hsS.trans (hgood₁ m x₀).2.2.1) hK₂ hζq hζM
    hζν hζνmk hown hda hdW' hSm hW hVL hN hζ Tk hTk hcap₁ hcap₂
  refine isSeedSampleLaw_eightRec_of_girs hlaw (Eventually.of_forall fun y => ?_)
  exact seedHeightField_eightRec_eq_girsDensity hκ hpp (h₁.path x₀) rfl rfl (hgood₁ m x₀) (hsep₁ x₀) (hc₂ m y)
    (h0₂ y) (hgood₂ m y) (hS₂pos m y) (hdrive y) ⟨hs, hsS⟩ (hown₁ y) le_rfl

end Frame

end InteractingSLE.ZhanGT4.A1ELaw
