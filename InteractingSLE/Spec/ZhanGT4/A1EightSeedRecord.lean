/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightSeedCongr
import InteractingSLE.Spec.ZhanGT4.A1EightSeedGlue
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldPath
import InteractingSLE.Spec.ZhanGT4.DualMarg0
import InteractingSLE.Spec.ZhanGT4.DualForceLawD9

/-!
# Zhan's A.1 (R80): the concrete rectangle-wise seeded records

Packet PROVE-A1-EIGHTSEED. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407)
and follow-up 4 §2.5 (L739–L788).

The seeded record of rectangle `m` at frozen height `t` is A22's `SeedData.fromSource` built from

* the growing driver stopped at the rectangle's own exit (`A1Ref.stopDrv`, globally continuous);
* the frozen path stopped at the height `t` (`frzPath`) and its chart `frzChart`;
* an image chain of the growing driver against the frozen hull, chosen when one exists (`imgChain`).

## Main results

* `imgChain`, `ownData_imgChain`; **`exists_ownData_of_encl`**: an image chain exists when the two hulls lie in
  separated enclosures;
* `srcRec`: the source record; **`normEll_srcRec_congr`** and **`recCompat_srcRec`**: records of two rectangles whose
  drivers agree up to the smaller exit have the same seeded logarithm on the common rectangle (`RecCompat`, through
  `normEll_fromSource_congr`);
* `SeedData.normEll_eq_zero_of_identityLog` (A22's `normEll_eq_zero_of_identity` with `log A21 = 0` in place of
  `A21 = 1`) and **`normEll_srcRec_zero_height`**: at frozen height zero the record's seeded logarithm vanishes on its
  horizon (identity chart; no positivity of `g_t'(p)` is needed);
* the Eight records `eightRec` (marks the two seeds `x⁻`, `x⁺` of the small curve, charges `ρ/κ̂`) and
  **`isSourceRecord_eightRec`**: an Eight record is a source record (`IsSourceRecord`) at every sample where the
  small curve is alive up to the exit with its seeds off the driver at positive times, the frozen large curve is
  continuous up to the height, and both hulls lie in their protected enclosures.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EightSeed

open QuantumZipper (H fwdMap fwdHull)
open A1SeedField A2X

/-! ### The chosen image chain and the source record -/

section Chain

open Classical in
/-- An image chain (clock, image driver) of the growing driver `W` against the frozen hull `A` with chart `φ` up to `T`,
chosen when one exists (`OwnData`), and `(0, 0)` otherwise. -/
def imgChain (W : ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T : ℝ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  if h : ∃ a W', OwnData W A φ T a W' then (h.choose, h.choose_spec.choose) else (fun _ => 0, fun _ => 0)

theorem ownData_imgChain {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} (h : ∃ a W', OwnData W A φ T a W') :
    OwnData W A φ T (imgChain W A φ T).1 (imgChain W A φ T).2 := by
  classical
  unfold imgChain
  simp only [h, ↓reduceDIte]
  exact h.choose_spec.choose_spec

/-- **An image chain exists when the two hulls lie in separated enclosures** (`exists_ownData`). -/
theorem exists_ownData_of_encl {W Wf : ℝ → ℝ} {T t δ : ℝ} {H₁ H₂ : Set ℂ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hT : 0 < T) (hWf : Continuous Wf) (ht : 0 ≤ t) (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    (hK₁ : fwdHull W T ⊆ H₁) (hK₂ : fwdHull Wf t ⊆ H₂) :
    ∃ a W', OwnData W (fwdHull Wf t) (frzChart Wf t) T a W' :=
  exists_ownData hW hW0 hT (isHPHull_fwdHull hWf ht) (isMapOut_fwdMap_gen hWf ht)
    ((disjoint_closure_of_le_norm_sub hδ hsep).mono (closure_mono hK₁) (closure_mono hK₂)).symm

variable {n : ℕ}

/-- **The source record** of the growing driver `W` up to its horizon `T` against the frozen path `Wf` at height `t`
(other source `p`, charges `rr`, marks `V`): `SeedData.fromSource` with the chosen image chain. -/
def srcRec (W : ℝ → ℝ) (T : ℝ) (Wf : ℝ → ℝ) (t κ : ℝ) (rr : Fin n → ℝ) (p : ℝ) (V : Fin n → ℝ → ℝ) : SeedData n :=
  SeedData.fromSource W (imgChain W (fwdHull Wf t) (frzChart Wf t) T).2 (imgChain W (fwdHull Wf t) (frzChart Wf t) T).1
    (frzChart Wf t) κ rr (Wf t) p V

/-- **Two source records whose drivers agree up to `U` have the same seeded logarithm** at every `u` below both
horizons and `U`. -/
theorem normEll_srcRec_congr {W₁ W₂ Wf : ℝ → ℝ} {T₁ T₂ U t κ p : ℝ} {rr : Fin n → ℝ} {V₁ V₂ : Fin n → ℝ → ℝ}
    (h₁ : ∃ a W', OwnData W₁ (fwdHull Wf t) (frzChart Wf t) T₁ a W')
    (h₂ : ∃ a W', OwnData W₂ (fwdHull Wf t) (frzChart Wf t) T₂ a W')
    (hW : EqOn W₁ W₂ (Icc 0 U)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (min (min T₁ T₂) U)) (hV : ∀ m, V₁ m u = V₂ m u) :
    (srcRec W₁ T₁ Wf t κ rr p V₁).normEll u = (srcRec W₂ T₂ Wf t κ rr p V₂).normEll u :=
  normEll_fromSource_congr (ownData_imgChain h₁) (ownData_imgChain h₂) hW κ rr (Wf t) p hu hV

/-- **Rectangle-wise source records are compatible** (`RecCompat`) when an image chain exists on every rectangle and
the drivers of two rectangles agree up to the smaller exit. -/
theorem recCompat_srcRec {X Y : Type*} {W : ℕ → X → ℝ → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
    {Wf : ℝ → Y → ℝ → ℝ} {κ p : ℝ} {rr : Fin n → ℝ} {V : X → Fin n → ℝ → ℝ}
    (hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y →
      ∃ a W', OwnData (W m x) (fwdHull (Wf t y) t) (frzChart (Wf t y) t) (S₁ m x) a W')
    (hagree : ∀ m m' x, EqOn (W m x) (W m' x) (Icc 0 (min (S₁ m x : ℝ) (S₁ m' x)))) :
    RecCompat (fun m t ω => srcRec (W m ω.1) (S₁ m ω.1) (Wf t ω.2) t κ rr p (V ω.1)) S₁ S₂ := by
  intro m m' x y s t hs hsm hsm' ht htm htm'
  exact normEll_srcRec_congr (hex m x y t ht htm) (hex m' x y t ht htm') (hagree m m' x)
    ⟨hs, le_min (le_min hsm hsm') (le_min hsm hsm')⟩ fun _ => rfl

/-- Two drivers stopped at `T₁` and `T₂` agree up to `min T₁ T₂`. -/
theorem eqOn_stopDrv (w : ℝ → ℝ) (T₁ T₂ : ℝ) :
    EqOn (A1Ref.stopDrv w T₁) (A1Ref.stopDrv w T₂) (Icc 0 (min T₁ T₂)) := fun s hs => by
  rw [A1Ref.stopDrv_eqOn w T₁ ⟨hs.1, hs.2.trans (min_le_left _ _)⟩,
    A1Ref.stopDrv_eqOn w T₂ ⟨hs.1, hs.2.trans (min_le_right _ _)⟩]

end Chain

/-! ### Frozen height zero: the identity chart -/

section Identity

variable {n : ℕ}

/-- A22's `normEll_eq_zero_of_identity` with `log A21 = 0` in place of `A21 = 1`. -/
theorem _root_.InteractingSLE.ZhanGT4.SeedData.normEll_eq_zero_of_identityLog (d : SeedData n) (t : ℝ)
    (hf : d.F 0 t = id) (hA : d.A 1 t = 1)
    (h21 : Real.log (d.A21 t) = 0) (hB : ∀ m, d.B1 t m = 1) (h20 : d.A20 t = d.V₀ t) (hL : d.L t = 0) :
    d.normEll t = 0 := by
  have h0 : d.A 0 t = d.W t := by
    rw [← d.F_driver 0 t, hf]
    rfl
  have hB0 (m : Fin n) : d.B0 t m = d.V m t := by
    change d.F 0 t (d.V m t) = _
    rw [hf]
    rfl
  have hds (x y : ℝ) : dslope (id : ℝ → ℝ) x y = 1 := by
    by_cases hxy : y = x
    · subst y
      rw [dslope_same]
      exact deriv_id x
    · rw [dslope_of_ne _ hxy, slope_def_field]
      exact div_self (sub_ne_zero.2 hxy)
  simp only [SeedData.normEll, hA, h21, hB, h20, hL, h0, hB0, hf, hds,
    Real.log_one, Real.log_div_self, mul_zero, zero_sub, neg_zero,
    add_zero, Finset.sum_const_zero, pairSum]

end Identity

section Zero

variable {n : ℕ}

/-- The iterated derivatives of the identity of `ℂ` of order at least two vanish. -/
theorem iterate_deriv_id_two_add (k : ℕ) : deriv^[k + 2] (id : ℂ → ℂ) = 0 := by
  induction k with
  | zero =>
    funext z
    simp only [zero_add, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, deriv_id', deriv_const,
      Pi.zero_apply, id]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Function.iterate_succ', Function.comp_apply, ih]
    funext z
    simp only [Pi.zero_apply]
    exact deriv_const z (0 : ℂ)

/-- **The seeded logarithm of a record with the identity chart vanishes**: an image chain against the empty hull with
the identity chart, and the frozen tip at the other source, give `normEll s = 0` on the horizon. -/
theorem normEll_fromSource_empty_eq_zero {W c J : ℝ → ℝ} {T : ℝ} (h : OwnData W ∅ id T c J) (κ : ℝ)
    (rr : Fin n → ℝ) (p : ℝ) (V : Fin n → ℝ → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    (SeedData.fromSource W J c id κ rr p p V).normEll s = 0 := by
  have hext : ∀ v ∈ Icc (0 : ℝ) T, ownExt W J c id v = id := fun v hv => h.ownExt_eq_of_empty hv
  have hclk : c s = s := h.clock_eq_of_empty hs
  have himg : fwdMap J (c s) = fwdMap W s := by
    funext z
    rw [hclk]
    exact Ito.fwdMap_congr_of_eqOn fun v hv => h.W'_eq_of_empty ⟨hv.1, hv.2.trans hs.2⟩
  have hdrv : J (c s) = W s := by rw [hclk]; exact h.W'_eq_of_empty hs
  refine SeedData.normEll_eq_zero_of_identityLog _ s ?_ ?_ ?_ ?_ ?_ ?_
  · funext x
    change (deriv^[0] (ownExt W J c id s) x).re = x
    rw [hext s hs]
    simp
  · exact h.frzA_one_eq_of_empty hs
  · change Real.log ((deriv (fwdMap J (c s)) p).re / (deriv (fwdMap W s) p).re) = 0
    rw [himg, Real.log_div_self]
  · intro m
    change (deriv^[1] (ownExt W J c id s) (V m s)).re = 1
    rw [hext s hs, Function.iterate_one, deriv_id']
    simp
  · change (fwdMap J (c s) p).re + J (c s) = (fwdMap W s p).re + W s
    rw [himg, hdrv]
  · change frzLogF W J c id s = 0
    unfold frzLogF
    have e : ∀ v ∈ uIcc (0 : ℝ) s, frzRate W J c id v = 0 := fun v hv => by
      rw [uIcc_of_le hs.1] at hv
      have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hs.2⟩
      unfold frzRate frzA
      rw [hext v hvT, show (2 : ℕ) = 0 + 2 from rfl, iterate_deriv_id_two_add 0,
        show (3 : ℕ) = 1 + 2 from rfl, iterate_deriv_id_two_add 1]
      simp
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_zero]

/-- **At frozen height zero the source record's seeded logarithm vanishes on its horizon**: the frozen hull at height
`0` is empty and the frozen chart is the identity (`frzChart_zero_eq_id`). -/
theorem normEll_srcRec_zero_height {W Wf : ℝ → ℝ} {T κ p : ℝ} {rr : Fin n → ℝ} {V : Fin n → ℝ → ℝ}
    (hWf : Continuous Wf) (hWf0 : Wf 0 = p) (hex : ∃ a W', OwnData W (fwdHull Wf 0) (frzChart Wf 0) T a W') {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) : (srcRec W T Wf 0 κ rr p V).normEll s = 0 := by
  have hown := ownData_imgChain hex
  have hK : fwdHull Wf 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hWf
  have hφ : frzChart Wf 0 = id := frzChart_zero_eq_id Wf
  unfold srcRec
  rw [hK, hφ] at hown ⊢
  rw [hWf0]
  exact normEll_fromSource_empty_eq_zero hown κ rr p V hs

end Zero

/-! ### The Eight records -/

section Eight

variable {X Y : Type*}

/-- The frozen path of the large curve at height `t` in the small curve's frame: its driver stopped at `t`, shifted by
the source `p`. -/
def frzPath (W₂ : ℝ≥0 → Y → ℝ) (p t : ℝ) (y : Y) : ℝ → ℝ := fun u => A1Ref.stopDrv (Strip.extPath (W₂ · y)) t u + p

/-- The reduced charges `ρ/κ̂` of the small curve's two seeds `x⁻`, `x⁺`. -/
def eightRR (κ : ℝ) : Fin 2 → ℝ := ![smallEightRhoL κ 0 / kh κ, smallEightRhoR κ 0 / kh κ]

/-- The seed marks `x⁻`, `x⁺` of the small curve. -/
def eightMarks (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ) (x : X) : Fin 2 → ℝ → ℝ :=
  ![Strip.extPath (VL₁ 0 · x), Strip.extPath (VR₁ 0 · x)]

/-- The growing driver of rectangle `m`: the small curve's driver stopped at the rectangle's exit. -/
def eightDrv (W₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) : ℝ → ℝ :=
  A1Ref.stopDrv (Strip.extPath (W₁ · x)) (S₁ m x)

/-- **The Eight seeded record** of rectangle `m` at frozen height `t` (other source `p = −x`, small parameter
`κ̂ = kh κ`). -/
def eightRec (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (W₂ : ℝ≥0 → Y → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (t : ℝ) (ω : X × Y) : SeedData 2 :=
  srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (frzPath W₂ p t ω.2) t (kh κ) (eightRR κ) p (eightMarks VL₁ VR₁ ω.1)

theorem continuous_frzPath {W₂ : ℝ≥0 → Y → ℝ} {p t : ℝ} {y : Y} (hc : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t))
    (ht : 0 ≤ t) : Continuous (frzPath W₂ p t y) :=
  (A1Ref.continuous_stopDrv hc ht).add continuous_const

theorem frzPath_zero {W₂ : ℝ≥0 → Y → ℝ} {p t : ℝ} {y : Y} (h0 : W₂ 0 y = 0) (ht : 0 ≤ t) :
    frzPath W₂ p t y 0 = p := by
  simp only [frzPath, A1Ref.stopDrv, min_eq_left ht, max_self, Strip.extPath, Real.toNNReal_zero, h0, zero_add]

theorem continuous_eightDrv {W₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X}
    (hc : ContinuousOn (W₁ · x) {t | (t : ℝ≥0∞) < ζ₁ x}) (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x) :
    Continuous (eightDrv W₁ S₁ m x) :=
  A1Ref.continuous_stopDrv (A1Ref.continuousOn_extPath_Icc hc (by rwa [ENNReal.ofReal_coe_nnreal]))
    (S₁ m x).coe_nonneg

theorem eightDrv_zero {W₁ : ℝ≥0 → X → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} (h0 : W₁ 0 x = 0) :
    eightDrv W₁ S₁ m x 0 = 0 := by
  simp only [eightDrv, A1Ref.stopDrv, min_eq_left (S₁ m x).coe_nonneg, max_self, Strip.extPath, Real.toNNReal_zero, h0]

theorem eightDrv_eqOn (W₁ : ℝ≥0 → X → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) :
    EqOn (eightDrv W₁ S₁ m x) (Strip.extPath (W₁ · x)) (Icc 0 (S₁ m x)) :=
  A1Ref.stopDrv_eqOn _ _

/-- **The Eight records are compatible across rectangles** whenever an image chain exists on every rectangle. -/
theorem recCompat_eightRec {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
    (hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y →
      ∃ a W', OwnData (eightDrv W₁ S₁ m x) (fwdHull (frzPath W₂ p t y) t) (frzChart (frzPath W₂ p t y) t)
        (S₁ m x) a W') :
    RecCompat (eightRec κ p W₁ VL₁ VR₁ W₂ S₁) S₁ S₂ :=
  recCompat_srcRec (W := eightDrv W₁ S₁) (Wf := fun t y => frzPath W₂ p t y) (V := eightMarks VL₁ VR₁) hex
    fun _ _ _ => eqOn_stopDrv _ _ _

/-- **At frozen height zero the Eight record's seeded logarithm is constant on the rectangle** (the identity chart). -/
theorem normEll_eightRec_zero {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y}
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 0)) (h0₂ : W₂ 0 y = 0)
    (hex : ∃ a W', OwnData (eightDrv W₁ S₁ m x) (fwdHull (frzPath W₂ p 0 y) 0) (frzChart (frzPath W₂ p 0 y) 0)
      (S₁ m x) a W') {s : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S₁ m x) :
    (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m 0 (x, y)).normEll s = (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m 0 (x, y)).normEll 0 := by
  have hWf := continuous_frzPath (p := p) hc₂ le_rfl
  have hWf0 := frzPath_zero (p := p) h0₂ le_rfl
  rw [eightRec, normEll_srcRec_zero_height hWf hWf0 hex ⟨hs, hsS⟩,
    normEll_srcRec_zero_height hWf hWf0 hex ⟨le_rfl, (S₁ m x).coe_nonneg⟩]

/-- **An Eight record is a source record** (`IsSourceRecord`) at a sample where the small curve's path relation holds
with seeds at `0`, the small curve is alive up to the rectangle's positive exit `S₁ m x` with its seeds off the driver
at positive times, the large curve starts at `0` and is continuous up to the height `0 < t`, both hulls lie in
`2δ`-separated enclosures, and the exit and the height are bounded by `Tm`. -/
theorem isSourceRecord_eightRec {κ p a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ}
    {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
    {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y} {t Tm δ : ℝ} {H₁ H₂ : Set ℂ}
    (hP : IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x) (hTpos : 0 < (S₁ m x : ℝ))
    (hneL : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VR₁ 0 s x ≠ W₁ s x)
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t)) (h0₂ : W₂ 0 y = 0) (ht : 0 < t) (htm : t ≤ Tm)
    (hTm : (S₁ m x : ℝ) ≤ Tm) (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    (hK₁ : fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁) (hK₂ : fwdHull (frzPath W₂ p t y) t ⊆ H₂) :
    IsSourceRecord H₁ H₂ p Tm (kh κ) (eightRR κ) (frzPath W₂ p t y) t (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y))
      (Strip.extPath (VL₁ 0 · x)) (Strip.extPath (VR₁ 0 · x)) (S₁ m x) := by
  have hWc := continuous_eightDrv (S₁ := S₁) (m := m) hP.2.2.2.1 hT
  have hW0 := eightDrv_zero (S₁ := S₁) (m := m) hP.1
  have hWf := continuous_frzPath (p := p) hc₂ ht.le
  have hex := exists_ownData_of_encl hWc hW0 hTpos hWf ht.le hδ hsep hK₁ hK₂
  have hEq := eightDrv_eqOn W₁ S₁ m x
  have hlo : IsSeedCoordinate (eightDrv W₁ S₁ m x) (Strip.extPath (VL₁ 0 · x)) (S₁ m x) :=
    isSeedCoordinate_vL_of_path hP 0 hxL hT hneL hEq
  have hhi : IsSeedCoordinate (eightDrv W₁ S₁ m x) (Strip.extPath (VR₁ 0 · x)) (S₁ m x) :=
    isSeedCoordinate_vR_of_path hP 0 hxR hT hneR hEq
  exact
    { source := rfl
      own := ownData_imgChain hex
      contW₂ := hWf
      zeroW₂ := frzPath_zero h0₂ ht.le
      pos₂ := ht
      le₂ := htm
      le₁ := hTm
      sub₁ := hK₁
      sub₂ := hK₂
      lo := hlo
      hi := hhi
      drv := seedPair_between hP 0 0 hT hEq
      marks := fun s _ k => seedPair_marks _ _ s k
      seed := fun k => by
        fin_cases k
        · exact hlo
        · exact hhi
      inj := seedPair_injective hP 0 0 hT hneL hneR }

end Eight

end InteractingSLE.ZhanGT4.A1EightSeed
