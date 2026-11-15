/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RowCongr
import InteractingSLE.Spec.ZhanGT4.A1EightFinAssembly
import InteractingSLE.Spec.ZhanGT4.A1LargeDensEncl

/-!
# Zhan's A.1 (Eight): the patch density is the large direction's Girsanov density (`hrowIdent`)

Packet PROVE-A1-G3ROW. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425: the
rectangle density `M(S₁ᵐ, S₂ᵐ)` is, row by row, the frozen-curve density (D6) of the large curve "with the conformal
map of `K₁(I)` frozen"); follow-up 4 §2.5 (L739–L788).

For the large-curve direction (`FrozenFamilyFst`, conditioning curve the small one) A1-FAMILY needs the one-sample law
under `P₂.withDensity (D σ m (x, ·))`, where `D σ m (x, y) = M(σ ∧ S₁ᵐ(x), S₂ᵐ(y))` is the patch density.
A1-LARGEDENS proved the one-sample law under the Girsanov measure `(M̃_S/M̃_0)·P₂` of the frozen data `frzDataOf`
(large Brownian driver, image chain `OwnData`, marks `x⁺, x⁻` with `largeEightRR`), and reduced the rest to
`D σ m (x, ·) = M̃_S/M̃_0` `P₂`-a.e. This file proves that identity at every sample where the rectangle data hold:

* `eightRR_dual`: the Eight charges in the two views (`−(κ̂/4)·eightRR = largeEightRR ∘ swap`);
* `frzChart_sub_const_eq_physMap`, `fwdHull_sub_const_eq_physHull`: the frozen chart and hull of the translated small
  driver are A2X's `physMap`, `physHull` (the frame of the family's canonical image chain);
* **`normEll_srcRec_sub_eq_frzDataOf`**: A1-EIGHTFIN's row identity
  (`normEll_srcRec_sub_eq_eView`) with the opposite view replaced by A1-LARGEDENS's `frzDataOf` of any Brownian path
  whose driver is the large curve up to the height, with any image chain (`FrzData.ell_congr_of_ownData`);
* **`exp_normEll_eq_girsDensity`**: the same at a stop `S₂`, as A1-LARGEDENS's `girsDensity`;
* **`seedHeightField_eightRec_eq_girsDensity`**: for A1-EIGHTSEED's concrete records `eightRec` (the hypotheses of
  `eight_rows` at one rectangle and one pair of samples), the patch density `seedHeightField … (x, y) s (S₂ m y)` is
  the Girsanov density of `frzDataOf` at `y`;
* **`isSeedSampleLaw_eightRec_of_girs`**: hence A1-LARGEDENS's one-sample law transfers to the patch density
  `P₂.withDensity (fun y => ofReal (seedHeightField … (x, y) s (S₂ m y)))` once the rectangle data hold `P₂`-a.e.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Row

open QuantumZipper (H fwdMap fwdHull drive)
open A1SeedField A1EightSeed A1EightFin A2X A1LargeDens A1Family

/-- **The Eight charges in the two views**: the opposite view's reduced charges `−(κ̂/4)·eightRR κ` are A.1's large
image charges `largeEightRR κ` in the other order (`x⁻, x⁺` versus `x⁺, x⁻`). -/
theorem eightRR_dual {κ : ℝ} (hκ : κ ≠ 0) (m : Fin 2) :
    largeEightRR κ m = -(kh κ / 4) * eightRR κ (Equiv.swap 0 1 m) := by
  fin_cases m
  · simp only [largeEightRR, eightRR, smallEightRhoL, smallEightRhoR, kh, Fin.zero_eta, Fin.isValue,
      Equiv.swap_apply_left, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · simp only [largeEightRR, eightRR, smallEightRhoL, smallEightRhoR, kh, Fin.mk_one, Fin.isValue,
      Equiv.swap_apply_right, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring

/-! ### The frozen chart in A2X's physical frame -/

/-- **The frozen chart of a translated driver is A2X's physical map**: `frzChart (w − c) σ = physMap (−c) w σ` (the
small curve started at `−c`, e.g. `−c = x` for the Eight source separation `p = −x`). -/
theorem frzChart_sub_const_eq_physMap (w : ℝ → ℝ) (c σ : ℝ) :
    frzChart (fun u => w u - c) σ = physMap (-c) w σ := by
  funext z
  simp only [frzChart, physMap, fwdMap_sub_const]
  push_cast
  ring_nf

/-- **The hull of a translated driver is A2X's physical hull**: `fwdHull (w − c) t = physHull (−c) w t`. -/
theorem fwdHull_sub_const_eq_physHull (w : ℝ → ℝ) (c t : ℝ) :
    fwdHull (fun u => w u - c) t = physHull (-c) w t :=
  fwdHull_sub_const w c t

section View

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}
  {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} {W' a : Ω → ℝ → ℝ} {T s : ℝ}

/-- **The row identity in A1-LARGEDENS's frame**: for the Eight charges, at a positive own time `s ≤ S` of the small
curve and a height `t ≤ Y`, the normalized row increment of A1-EIGHTSEED's source records is the increment of the
logarithm `ℓ` of `frzDataOf κ B W' a φ (largeEightRR κ) (W₁ s − p) ![Vhi s − p, Vlo s − p]` (frozen chart
`φ = frzChart (W₁ − p) s`), along the driver, for every Brownian path `B` whose driver `√κ B` is the large curve
`V₂ − p` up to `Y`, with any image chain `(a, W')` up to `T ≥ Y`. -/
theorem normEll_srcRec_sub_eq_frzDataOf (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi)
    (hκ : 0 < κ) (hs : s ∈ Ioc (0 : ℝ) S)
    (hown : OwnData (drive κ B ω) (fwdHull (fun u => W₁ u - p) s) (frzChart (fun u => W₁ u - p) s) T (a ω) (W' ω))
    (hYT : Y ≤ T) (hB : ∀ u ∈ Icc (0 : ℝ) Y, drive κ B ω u = V₂ u - p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) :
    (srcRec W₁ S V₂ t (kh κ) (eightRR κ) p ![Vlo, Vhi]).normEll s -
        (srcRec W₁ S V₂ t (kh κ) (eightRR κ) p ![Vlo, Vhi]).normEll 0 =
      (frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeEightRR κ) (W₁ s - p)
          ![Vhi s - p, Vlo s - p] ω).ell t (drive κ B ω t) -
        (frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeEightRR κ) (W₁ s - p)
          ![Vhi s - p, Vlo s - p] ω).ell 0 (drive κ B ω 0) := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hk : kh κ ≠ 0 := by unfold kh; positivity
  have hVs : ∀ m, IsSeedCoordinate W₁ (![Vlo, Vhi] m) S := fun m => by
    fin_cases m
    · exact h.lo
    · exact h.hi
  rw [h.normEll_srcRec_sub_eq_eView hk (eightRR_fused hκ) hVs (fun u _ m => seedPair_marks Vlo Vhi u m)
    (fun u hu => pair_injective (h.inj u hu)) hs ht]
  -- the opposite view and the Brownian frozen data have the same logarithm up to `Y`
  set e := eView (kh κ) (eightRR κ) W₁ V₂ S Y ![Vlo, Vhi] s with he
  set f := frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeEightRR κ) (W₁ s - p)
    ![Vhi s - p, Vlo s - p] ω with hf
  have hz : V₂ 0 = p := h.zero₂
  have hsI : s ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self hs
  have h₁ := (h.tOwn hsI).1
  have hA : fwdHull (fun u => W₁ u - V₂ 0) s = fwdHull (fun u => W₁ u - p) s := by rw [hz]
  have hφ : frzChart (fun u => W₁ u - V₂ 0) s = frzChart (fun u => W₁ u - p) s := by rw [hz]
  rw [hA, hφ] at h₁
  have hWe : EqOn e.W f.W (Icc 0 Y) := fun u hu => by
    change V₂ u - V₂ 0 = drive κ B ω u
    rw [hB u hu, hz]
  have hcongr : ∀ v ∈ Icc (0 : ℝ) Y, ∀ x, e.ell v x = f.ell v x := fun v hv x =>
    FrzData.ell_congr_of_ownData (d₁ := e) (d₂ := f) h₁ hown (by change frzChart _ s = _; rw [hφ]) rfl hWe
      (sixteen_div_kh hκ0) (Equiv.swap 0 1) (fun m => eightRR_dual hκ0 m) (by change W₁ s - V₂ 0 = W₁ s - p; rw [hz])
      (fun m => by
        fin_cases m
        · change Vhi s - p = Vhi s - V₂ 0
          rw [hz]
        · change Vlo s - p = Vlo s - V₂ 0
          rw [hz])
      ⟨hv.1, le_min (le_min hv.2 (hv.2.trans hYT)) hv.2⟩ x
  have h0Y : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, h.pos₂.le⟩
  rw [hcongr t ht, hcongr 0 h0Y]
  have hdt : V₂ t - V₂ 0 = drive κ B ω t := by rw [hB t ht, hz]
  have hd0 : V₂ 0 - V₂ 0 = drive κ B ω 0 := by rw [hB 0 h0Y, hz]
  rw [hdt, hd0]

/-- **The row identity as A1-LARGEDENS's Girsanov density** at a stop `S₂ ≤ T` with `S₂ = Y`: the exponential of the
normalized row increment of the source records at height `S₂` is `girsDensity (√κ) B S₂ ℓ ω` for the logarithm `ℓ` of
`frzDataOf`. -/
theorem exp_normEll_eq_girsDensity {S₂ : Ω → ℝ≥0}
    (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S (S₂ ω) Vlo Vhi) (hκ : 0 < κ) (hs : s ∈ Ioc (0 : ℝ) S)
    (hown : OwnData (drive κ B ω) (fwdHull (fun u => W₁ u - p) s) (frzChart (fun u => W₁ u - p) s) T (a ω) (W' ω))
    (hYT : (S₂ ω : ℝ) ≤ T) (hB : ∀ u ∈ Icc (0 : ℝ) (S₂ ω), drive κ B ω u = V₂ u - p) :
    Real.exp ((srcRec W₁ S V₂ (S₂ ω) (kh κ) (eightRR κ) p ![Vlo, Vhi]).normEll s -
        (srcRec W₁ S V₂ (S₂ ω) (kh κ) (eightRR κ) p ![Vlo, Vhi]).normEll 0) =
      girsDensity (Real.sqrt κ) B S₂ (fun ω' => (frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s)
        (largeEightRR κ) (W₁ s - p) ![Vhi s - p, Vlo s - p] ω').ell) ω := by
  rw [normEll_srcRec_sub_eq_frzDataOf h hκ hs hown hYT hB ⟨(S₂ ω).coe_nonneg, le_rfl⟩, girsDensity]
  simp only [drive, Real.toNNReal_coe, Real.toNNReal_zero]

end View

/-! ### The concrete Eight records -/

section Records

variable {X Y : Type*}

/-- **`hrowIdent` for A1-EIGHTSEED's concrete Eight records**: with the hypotheses of `eight_rows` at one rectangle `m`
and one pair of samples `(x, y)`, a Brownian path `B₂` whose driver `√κ B₂` is the large driver up to the exit
`S₂ m y`, and an image chain `(a, W')` of `√κ B₂` against the small hull frozen at `s ∈ (0, S₁ m x]` (A1-LARGEDENS's
`hown₁`), the patch density at the rectangle corner `(s, S₂ m y)` is the Girsanov density of the frozen data
`frzDataOf κ B₂ W' a (frzChart Wₛ s) (largeEightRR κ) (Wₛ s) ![pp, pm]`, `Wₛ = eightDrv W₁ S₁ m x − p` the physical
small driver and `pp`, `pm` the physical seeds `x⁺`, `x⁻` at `s`. -/
theorem seedHeightField_eightRec_eq_girsDensity {κ p a₀ : ℝ} (hκ : 0 < κ) {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
    {H₁ H₂ : Set ℂ} {δ q dd Tm : ℝ} {m : ℕ} {x : X} {y : Y} (hpp : IsProtectedPair H₁ H₂ δ p q dd)
    (hP : IsIntegratedSLEPath a₀ xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x) (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hgood₁ : (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁)
    (hsep₁ : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y))) (h0₂ : W₂ 0 y = 0)
    (hgood₂ : (S₂ m y : ℝ) ≤ Tm ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂) (hS₂pos : 0 < (S₂ m y : ℝ))
    {B₂ : ℝ≥0 → Y → ℝ} (hB₂ : ∀ u ∈ Icc (0 : ℝ) (S₂ m y), drive κ B₂ y u = Strip.extPath (W₂ · y) u)
    {s T : ℝ} (hs : s ∈ Ioc (0 : ℝ) (S₁ m x)) {W' a : Y → ℝ → ℝ}
    (hown : OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ S₁ m x u - p) s)
      (frzChart (fun u => eightDrv W₁ S₁ m x u - p) s) T (a y) (W' y)) (hYT : (S₂ m y : ℝ) ≤ T) :
    seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (S₂ m y) =
      girsDensity (Real.sqrt κ) B₂ (S₂ m) (fun y' => (frzDataOf κ B₂ W' a
        (frzChart (fun u => eightDrv W₁ S₁ m x u - p) s) (largeEightRR κ) (eightDrv W₁ S₁ m x s - p)
        ![Strip.extPath (VR₁ 0 · x) s - p, Strip.extPath (VL₁ 0 · x) s - p] y').ell) y := by
  have hne : ∀ s : ℝ≥0, 0 < s → s ≤ S₁ m x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x := fun s hs hsS =>
    hsep₁ s hs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsS) hgood₁.1)
  have hrec := isSourceRecord_eightRec hP hxL hxR hgood₁.1 hgood₁.2.1 (fun s hs hsS => (hne s hs hsS).1)
    (fun s hs hsS => (hne s hs hsS).2) hc₂ h0₂ hS₂pos hgood₂.1 hgood₁.2.2.1 hpp.sep_pos hpp.sep hgood₁.2.2.2
    hgood₂.2 (κ := κ)
  have hset := viewSetup_of_isSourceRecord hpp hrec rfl
  have hB : ∀ u ∈ Icc (0 : ℝ) (S₂ m y), drive κ B₂ y u = frzPath W₂ p (S₂ m y) y u - p := fun u hu => by
    simp only [frzPath, A1Ref.stopDrv_eqOn _ _ hu, add_sub_cancel_right, hB₂ u hu]
  rw [seedHeightField, eightRec_eq_srcRec hc₂ (S₂ m y).coe_nonneg le_rfl]
  exact exp_normEll_eq_girsDensity (S₂ := S₂ m) hset hκ hs hown hYT hB

/-- **The large direction's one-sample law under the Eight patch density**: if, for `P₂`-almost every `y`, the
rectangle data of `seedHeightField_eightRec_eq_girsDensity` hold, then A1-LARGEDENS's one-sample law under the
Girsanov measure of `frzDataOf` (`isSeedSampleLaw_largeEight_of_encl`) holds under
`P₂.withDensity (fun y => ofReal (seedHeightField (eightRec …) (x, y) s (S₂ m y)))` — the form `FrozenFamilyFst`
asks for (A1-LARGEDENS "What remains" 1, `hrowIdent`). -/
theorem isSeedSampleLaw_eightRec_of_girs [MeasurableSpace Y] {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0} {m : ℕ} {x : X}
    {s : ℝ} {P₂ : Measure Y} {B₂ : ℝ≥0 → Y → ℝ} {ℓ : Y → ℝ → ℝ → ℝ} {nL nR : ℕ} {Wi : ℝ≥0 → Y → ℝ}
    {ζi : Y → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Y → ℝ} {VR : Fin nR → ℝ≥0 → Y → ℝ} {N : ℝ≥0 → Y → ℝ}
    {Scap : ℕ → Y → ℝ≥0} {m' : ℕ}
    (hlaw : IsSeedSampleLaw (girsMeasure P₂ (Real.sqrt κ) B₂ (S₂ m) ℓ) Wi ζi VL VR N Scap m')
    (hid : ∀ᵐ y ∂P₂, seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (S₂ m y) =
      girsDensity (Real.sqrt κ) B₂ (S₂ m) ℓ y) :
    IsSeedSampleLaw (P₂.withDensity fun y =>
        ENNReal.ofReal (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (S₂ m y)))
      Wi ζi VL VR N Scap m' :=
  isSeedSampleLaw_withDensity_of_ae_eq hlaw (hid.mono fun y hy => by simp only [hy])

end Records

end InteractingSLE.ZhanGT4.A1G3Row
