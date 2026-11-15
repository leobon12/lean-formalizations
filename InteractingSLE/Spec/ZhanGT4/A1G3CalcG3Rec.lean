/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcRecord
import InteractingSLE.Spec.ZhanGT4.A1EightSeedRecord

/-!
# Zhan's A.1, G3: the concrete mixed-mark seeded records

Packet PROVE-A1-G3CALC (R48, R80). Source: Astra, *Follow-up proofs*, §A.1 (`ig1_followup_proofs.txt` L190–L203,
L426–L500) and follow-up 4 §2.5. In the G3 configuration the growing (small) curve of parameter `κ̂ = 16/κ` starts at
`0` (physically `y`) with the left seed `y⁻` (weight `3κ̂/2 − 4`), the right seed `y⁺` (weight `2 − κ̂/2`), the ordinary
right mark `x` at `x − y > 0` (weight `κ̂ − 4`), and the other source `p = −y` (weight `−κ̂/2`).

The G3 record of rectangle `m` at frozen height `t` is A1-EIGHTSEED's source record `srcRec` (the small driver stopped
at the rectangle's exit, `eightDrv`; the frozen large path `frzPath`) with the three marks `y⁻`, `y⁺`, `x` and their
reduced charges. Its seeds are integrated seed coordinates (A1-SEEDFIELD), its ordinary mark is the real flow of
`x − y` (`fwdMap_add_eq_force`), and all three lie in the extended interval `[V_lo, g_t(q) + W_t]` for a protected
point `q ≥ x − y`.

## Main results

* `IsMarkCoordinate.congr`, `isForwardSol_of_force`, **`isMarkCoordinate_of_force`**: a force process from a real
  point, separated from the driver, is a mark coordinate;
* `vL_le_of_path`, `le_vR_of_path`, `vR_le_vR_of_path`: the side order of an integrated path, read on `ℝ`;
* `g3RR`, `g3Marks`, **`g3Rec`**; **`recCompat_g3Rec`**, **`normEll_g3Rec_zero`**;
* **`isSourceRecordG_g3Rec`**: a G3 record is a mixed source record (`IsSourceRecordG`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

open InteractingSLE.ZhanGT4 A1SeedField A1EightSeed A2X

/-! ### Mark coordinates of force processes -/

/-- Mark coordinates transfer along functions agreeing on `[0, T]`. -/
theorem IsMarkCoordinate.congr {W V V' : ℝ → ℝ} {T : ℝ} (h : IsMarkCoordinate W V T) (he : EqOn V V' (Icc 0 T)) :
    IsMarkCoordinate W V' T where
  cont := h.cont.congr fun _ hs => (he hs).symm
  ne := fun s hs => by
    rw [← he (Ioc_subset_Icc_self hs)]
    exact h.ne s hs
  deriv := fun s hs => by
    have hd := h.deriv s hs
    rw [he (Ioc_subset_Icc_self hs)] at hd
    exact hd.congr (fun _ hu => (he (Ioc_subset_Icc_self hu)).symm) (he (Ioc_subset_Icc_self hs)).symm

/-- **A force process from a real point, separated from the driver, is a forward solution**: for a driver `W` agreeing
with `extPath w` on `[0, T]` (`T` before the lifetime), `s ↦ extPath v s − W s` solves the centered forward flow from
`p` (A1-SEEDFIELD's construction in `fwdMap_add_eq_force`). -/
theorem isForwardSol_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ T, v r ≠ w r) {W : ℝ → ℝ} (hWc : ContinuousOn W (Icc 0 T))
    (hW : EqOn W (Strip.extPath w) (Icc 0 T)) :
    IsForwardSol W (p : ℂ) T fun s => ((Strip.extPath v s - W s : ℝ) : ℂ) := by
  have hWt : ∀ s ∈ Icc (0 : ℝ) T, W s = w s.toNNReal := fun s hs => hW hs
  have hvc : ContinuousOn (Strip.extPath v) (Icc 0 (T : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hv (by rw [ENNReal.ofReal_coe_nnreal]; exact hT)
  refine ⟨continuous_ofReal.comp_continuousOn (hvc.sub hWc), fun s hs => ⟨?_, ?_⟩⟩
  · simp only [ne_eq, ofReal_eq_zero, hWt s hs, sub_eq_zero, Strip.extPath]
    exact hsep _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  · have hint : ∫ r in (0 : ℝ)..s, (2 : ℂ) / ((Strip.extPath v r - W r : ℝ) : ℂ) =
        ((∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hWt r ⟨hr.1, hr.2.trans hs.2⟩, Strip.extPath]
      push_cast
      rfl
    have hve := hveq s.toNNReal (toNNReal_lt_of_mem_Icc hT hs)
    rw [Real.coe_toNNReal s hs.1] at hve
    rw [hint]
    simp only [hWt s hs, Strip.extPath]
    rw [hve]
    push_cast
    ring

/-- **A force process from a real point, separated from the driver on `[0, T]`, is a mark coordinate** of every
continuous driver agreeing with `extPath w` on `[0, T]`. -/
theorem isMarkCoordinate_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ T, v r ≠ w r) {W : ℝ → ℝ} (hWc : Continuous W)
    (hW : EqOn W (Strip.extPath w) (Icc 0 T)) : IsMarkCoordinate W (Strip.extPath v) T :=
  (isMarkCoordinate_of_forwardSol hWc (isForwardSol_of_force hv hveq hT hsep hWc.continuousOn hW)).congr
    fun _ ht => fwdMap_add_eq_force hv hveq hT hsep hWc.continuousOn hW ht

/-! ### The side order of an integrated path, read on `ℝ` -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A left force point lies left of the driver up to `T` before the lifetime. -/
theorem vL_le_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, Strip.extPath (vL i) t ≤ W t := by
  obtain ⟨-, -, -, -, -, -, -, hLw, -⟩ := hP
  intro t ht
  rw [hW ht]
  exact hLw _ (toNNReal_lt_of_mem_Icc hT ht) i

/-- A right force point lies right of the driver up to `T` before the lifetime. -/
theorem le_vR_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (j : Fin nR) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) {W : ℝ → ℝ} (hW : EqOn W (Strip.extPath w) (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, W t ≤ Strip.extPath (vR j) t := by
  obtain ⟨-, -, -, -, -, -, -, -, hwR, -⟩ := hP
  intro t ht
  rw [hW ht]
  exact hwR _ (toNNReal_lt_of_mem_Icc hT ht) j

/-- The right force points keep their order up to `T` before the lifetime. -/
theorem vR_le_vR_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {j k : Fin nR} (hjk : j ≤ k)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) : ∀ t ∈ Icc (0 : ℝ) T, Strip.extPath (vR j) t ≤ Strip.extPath (vR k) t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hmR, -⟩ := hP
  intro t ht
  exact hmR _ (toNNReal_lt_of_mem_Icc hT ht) hjk

end Path

/-- A real-valued function on `Fin 3` that increases strictly is injective. -/
theorem injective_fin3_of_lt {f : Fin 3 → ℝ} (h01 : f 0 < f 1) (h12 : f 1 < f 2) : Function.Injective f := by
  refine (Fin.strictMono_iff_lt_succ.2 fun i => ?_).injective
  fin_cases i
  · exact h01
  · exact h12

/-! ### The G3 records -/

section G3

variable {X Y : Type*}

/-- The reduced charges `ρ/κ̂` of the G3 small curve's marks: the seeds `y⁻`, `y⁺` and the ordinary mark `x`. -/
def g3RR (κ : ℝ) : Fin 3 → ℝ := ![smallG3RhoL κ 0 / kh κ, smallG3RhoR κ 0 / kh κ, smallG3RhoR κ 1 / kh κ]

/-- The marks of the G3 small curve: the seeds `y⁻`, `y⁺` and the ordinary mark `x`. -/
def g3Marks (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ) (x : X) : Fin 3 → ℝ → ℝ :=
  ![Strip.extPath (VL₁ 0 · x), Strip.extPath (VR₁ 0 · x), Strip.extPath (VR₁ 1 · x)]

/-- **The G3 seeded record** of rectangle `m` at frozen height `t` (other source `p = −y`, small parameter
`κ̂ = kh κ`): A1-EIGHTSEED's source record with the G3 marks and charges. -/
def g3Rec (κ p : ℝ) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 3 → ℝ≥0 → X → ℝ)
    (W₂ : ℝ≥0 → Y → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (t : ℝ) (ω : X × Y) : SeedData 3 :=
  srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (frzPath W₂ p t ω.2) t (kh κ) (g3RR κ) p (g3Marks VL₁ VR₁ ω.1)

/-- **The G3 records are compatible across rectangles** whenever an image chain exists on every rectangle. -/
theorem recCompat_g3Rec {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
    (hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y →
      ∃ a W', OwnData (eightDrv W₁ S₁ m x) (fwdHull (frzPath W₂ p t y) t) (frzChart (frzPath W₂ p t y) t)
        (S₁ m x) a W') :
    RecCompat (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁) S₁ S₂ :=
  recCompat_srcRec (W := eightDrv W₁ S₁) (Wf := fun t y => frzPath W₂ p t y) (V := g3Marks VL₁ VR₁) hex
    fun _ _ _ => eqOn_stopDrv _ _ _

/-- **At frozen height zero the G3 record's seeded logarithm is constant on the rectangle** (the identity chart). -/
theorem normEll_g3Rec_zero {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y}
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 0)) (h0₂ : W₂ 0 y = 0)
    (hex : ∃ a W', OwnData (eightDrv W₁ S₁ m x) (fwdHull (frzPath W₂ p 0 y) 0) (frzChart (frzPath W₂ p 0 y) 0)
      (S₁ m x) a W') {s : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S₁ m x) :
    (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m 0 (x, y)).normEll s = (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m 0 (x, y)).normEll 0 := by
  have hWf := continuous_frzPath (p := p) hc₂ le_rfl
  have hWf0 := frzPath_zero (p := p) h0₂ le_rfl
  rw [g3Rec, normEll_srcRec_zero_height hWf hWf0 hex ⟨hs, hsS⟩,
    normEll_srcRec_zero_height hWf hWf0 hex ⟨le_rfl, (S₁ m x).coe_nonneg⟩]

/-- **A G3 record is a mixed source record** (`IsSourceRecordG`) at a sample where the small curve's path relation
holds with its seeds at `0` and its ordinary mark at `0 < x_R(1) ≤ q`, the small curve is alive up to the rectangle's
positive exit with its seeds off the driver at positive times and its ordinary mark off the driver, the protected point
`q` is clear of `H₁`, the large curve starts at `0` and is continuous up to the height `0 < t`, both hulls lie in
`2δ`-separated enclosures, and the exit and the height are bounded by `Tm`. -/
theorem isSourceRecordG_g3Rec {κ p q a ρq : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 3 → ℝ} {ρL : Fin 1 → ℝ}
    {ρR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y}
    {t Tm δ : ℝ} {H₁ H₂ : Set ℂ}
    (hP : IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxO : 0 < xR 1) (hxOq : xR 1 ≤ q)
    (hT : (S₁ m x : ℝ≥0∞) < ζ₁ x) (hTpos : 0 < (S₁ m x : ℝ))
    (hneL : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x)
    (hneR : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VR₁ 0 s x ≠ W₁ s x)
    (hneO : ∀ s : ℝ≥0, s ≤ S₁ m x → VR₁ 1 s x ≠ W₁ s x)
    (hρq : 0 < ρq) (hqH₁ : Disjoint (ball (q : ℂ) ρq) H₁)
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 t)) (h0₂ : W₂ 0 y = 0) (ht : 0 < t) (htm : t ≤ Tm)
    (hTm : (S₁ m x : ℝ) ≤ Tm) (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    (hK₁ : fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁) (hK₂ : fwdHull (frzPath W₂ p t y) t ⊆ H₂) :
    IsSourceRecordG H₁ H₂ p q Tm (kh κ) (g3RR κ) (frzPath W₂ p t y) t (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y))
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
  obtain ⟨-, -, -, -, -, hcR, -, -, -, -, -, -, -, -, hReq, -⟩ := id hP
  have hOeq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ x →
      VR₁ 1 s x = xR 1 + ∫ r in (0 : ℝ)..s, 2 / (VR₁ 1 r.toNNReal x - W₁ r.toNNReal x) :=
    fun s hs => hReq s hs 1
  have hOc : ContinuousOn (VR₁ 1 · x) {s | (s : ℝ≥0∞) < ζ₁ x} := hcR 1
  have hOmark : IsMarkCoordinate (eightDrv W₁ S₁ m x) (Strip.extPath (VR₁ 1 · x)) (S₁ m x) :=
    isMarkCoordinate_of_force hOc hOeq hT hneO hWc hEq
  have huO := isForwardSol_of_force hOc hOeq hT hneO hWc.continuousOn hEq
  have hOform : ∀ s ∈ Icc (0 : ℝ) (S₁ m x),
      (fwdMap (eightDrv W₁ S₁ m x) s (xR 1)).re + eightDrv W₁ S₁ m x s = Strip.extPath (VR₁ 1 · x) s :=
    fun s hs => fwdMap_add_eq_force hOc hOeq hT hneO hWc.continuousOn hEq hs
  have hq0 : eightDrv W₁ S₁ m x 0 < q := by rw [hW0]; exact hxO.trans_le hxOq
  have hO0 : eightDrv W₁ S₁ m x 0 < xR 1 := by rw [hW0]; exact hxO
  obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen hWc hq0.ne' (S₁ m x).coe_nonneg hρq
    (hqH₁.mono_right hK₁)
  -- the order on `[0, S₁]`: `V_lo ≤ W ≤ V_hi ≤ V_x ≤ g(q) + W`
  have hloW := vL_le_of_path hP 0 hT hEq
  have hWhi := le_vR_of_path hP 0 hT hEq
  have hhiO := vR_le_vR_of_path hP (show (0 : Fin 3) ≤ 1 by decide) hT
  have hOq : ∀ s ∈ Icc (0 : ℝ) (S₁ m x),
      Strip.extPath (VR₁ 1 · x) s ≤ (fwdMap (eightDrv W₁ S₁ m x) s q).re + eightDrv W₁ S₁ m x s := by
    intro s hs
    rw [← hOform s hs]
    rcases hxOq.eq_or_lt with he | hlt
    · rw [he]
    · rw [fwdMap_eq_of_isForwardSol hWc huO hs, fwdMap_eq_of_isForwardSol hWc huq hs]
      have hord := QuantumZipper.F1.isForwardSol_lt_of_lt (S₁ m x).coe_nonneg hlt huO huq s hs
      simp only [ofReal_re] at hord ⊢
      linarith
  have hmem : ∀ s ∈ Icc (0 : ℝ) (S₁ m x), ∀ z, Strip.extPath (VL₁ 0 · x) s ≤ z →
      z ≤ (fwdMap (eightDrv W₁ S₁ m x) s q).re + eightDrv W₁ S₁ m x s →
      z ∈ uIcc (Strip.extPath (VL₁ 0 · x) s) ((fwdMap (eightDrv W₁ S₁ m x) s q).re + eightDrv W₁ S₁ m x s) :=
    fun _ _ z h1 h2 => Icc_subset_uIcc ⟨h1, h2⟩
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
      drv := fun s hs => hmem s hs _ (hloW s hs) (((hWhi s hs).trans (hhiO s hs)).trans (hOq s hs))
      marks := fun s hs k => by
        fin_cases k
        · exact left_mem_uIcc
        · exact hmem s hs _ ((hloW s hs).trans (hWhi s hs)) ((hhiO s hs).trans (hOq s hs))
        · exact hmem s hs _ (((hloW s hs).trans (hWhi s hs)).trans (hhiO s hs)) (hOq s hs)
      mark := fun k => by
        fin_cases k
        · exact isMarkCoordinate_of_seed hlo hWc
        · exact isMarkCoordinate_of_seed hhi hWc
        · exact hOmark
      inj := fun s hs => by
        have hsI := Ioc_subset_Icc_self hs
        have h1 : Strip.extPath (VL₁ 0 · x) s < eightDrv W₁ S₁ m x s :=
          lt_of_le_of_ne (hloW s hsI) (hlo.ne s hs)
        have h2 : eightDrv W₁ S₁ m x s < Strip.extPath (VR₁ 0 · x) s :=
          lt_of_le_of_ne (hWhi s hsI) (hhi.ne s hs).symm
        have h3 : Strip.extPath (VR₁ 0 · x) s < Strip.extPath (VR₁ 1 · x) s := by
          have hl := hhi.lt_gmap hWc hO0 huO hsI
          rw [← fwdMap_eq_of_isForwardSol hWc huO hsI, hOform s hsI] at hl
          exact hl
        exact injective_fin3_of_lt (f := fun k => g3Marks VL₁ VR₁ x k s) (h1.trans h2) h3 }

end G3

end InteractingSLE.ZhanGT4.A1G3Calc
