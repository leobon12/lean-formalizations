/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRD9
import InteractingSLE.Spec.ZhanGT4.A1G3IdRow
import InteractingSLE.Spec.ZhanGT4.A1AsmRow

/-!
# Zhan's A.1 (G3): the row identity at every height

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407: the
rectangle density is, row by row, the frozen-curve density of the large curve "with the conformal map of `K₁` frozen",
relative to the large curve's own law).

PROVE-A1-G3ROW2 proved the (G3) row identity at the corner of a rectangle (`seedHeightField_g3Rec_eq`): the patch
density is the frozen-curve density times the inverse `SLE_κ(κ − 4, −4)` martingale ratio. Its two ingredients
(`normEll_srcRec_eq_eView_sub`, `normEll_srcRec_g3_own_zero_eq`) hold at **every** height `u ≤ S₂`. Written with the
opposite view `e = eView … s` (A1-EIGHTFIN) and the logarithm `ℓ = G3Field.ell` of the inverse martingale
(PROVE-A1-G3ROW2), at every height `u ≤ S₂`:

`seedHeightField (g3Rec …) (ω₁, ω₂) s u = exp((e.ell u (W u) + ℓ(u, W u)) − (e.ell 0 (W 0) + ℓ(0, W 0)))`.

* `g3Rec_eq_srcRec`: a record at height `t ≤ T` reads the large path stopped at `T`;
* `pathOn_mono`: the large path facts restrict to earlier stops;
* **`seedHeightField_g3Rec_row_eq`**: the identity above (deterministic, every sample).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3RR

open QuantumZipper (IsForwardSol fwdMap fwdHull)
open A2X A1SeedField A1EightSeed A1EightFin A1G3Calc A1G3Id G3Field

variable {X Y : Type*}

/-- **A G3 record at height `t ≤ T` reads the large path stopped at `T`.** -/
theorem g3Rec_eq_srcRec {κ p : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {x : X} {y : Y} {t T : ℝ}
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T)) (ht : 0 ≤ t) (htT : t ≤ T) :
    g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y) = srcRec (eightDrv W₁ S₁ m x) (S₁ m x) (frzPath W₂ p T y) t (kh κ)
      (g3RR κ) p (g3Marks VL₁ VR₁ x) := by
  rcases htT.eq_or_lt with rfl | hlt
  · rfl
  · refine srcRec_congr_frozen (continuous_frzPath (hc₂.mono (Icc_subset_Icc_right hlt.le)) ht).continuousOn
      (continuous_frzPath hc₂ (ht.trans hlt.le)).continuousOn ht hlt fun s hs => ?_
    simp only [frzPath, A1Ref.stopDrv_eqOn _ t hs, A1Ref.stopDrv_eqOn _ T ⟨hs.1, hs.2.trans hlt.le⟩]

/-- The large path facts on `[0, S]` restrict to `[0, u]`, `u ≤ S`. -/
theorem pathOn_mono {Ω : Type*} {κ : ℝ} {xL : Fin 2 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {S u : ℝ≥0}
    {δ : ℝ} (h : PathOn κ xL xR ρR W VL VR B ζ ω S δ) (hu : u ≤ S) : PathOn κ xL xR ρR W VL VR B ζ ω u δ :=
  ⟨h.path, lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) h.lt, h.pos, fun r hr i => h.gap r (hr.trans hu) i⟩

/-- **The (G3) row identity at every height.** For A1-G3CALC's records `g3Rec` (other source `p`), at a rectangle
`m` and a pair of samples `(ω₁, ω₂)` with the enclosure data `G3Setup` of the rectangle `[0, S₁] × [0, S₂]`, a large
`SLE_κ(κ − 4, −4)` path whose force points start at the images `V₂(0) − p` of the ordinary mark and `−p` of the small
source, with gaps at least `δ₂` up to `S₂`: at every own time `s ∈ (0, S₁]` and every height `u ≤ S₂`,
`seedHeightField (g3Rec …) (ω₁, ω₂) s u = exp((e.ell u (W u) + ℓ(u, W u)) − (e.ell 0 (W 0) + ℓ(0, W 0)))`, with
`e = eView … s` the opposite view, `ℓ = G3Field.ell` and `W = G3Field.w W₂ ω₂` the large driver. -/
theorem seedHeightField_g3Rec_row_eq {κ p : ℝ} (hκ : 0 < κ) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0} {H₁ H₂ : Set ℂ}
    {δ q dd Tm : ℝ} {m : ℕ} {ω₁ : X} {ω₂ : Y}
    (hset : G3Setup H₁ H₂ δ p q dd Tm (eightDrv W₁ S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₁ m ω₁) (S₂ m ω₂)
      (Strip.extPath (VL₁ 0 · ω₁)) (Strip.extPath (VR₁ 0 · ω₁)) (g3Marks VL₁ VR₁ ω₁))
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · ω₂)) (Icc 0 (S₂ m ω₂))) (h0₂ : W₂ 0 ω₂ = 0)
    (hV2 : g3Marks VL₁ VR₁ ω₁ 2 0 ≠ 0) (hV2p : g3Marks VL₁ VR₁ ω₁ 2 0 ≠ p)
    {xL₂ : Fin 2 → ℝ} {xR₂ ρR₂ : Fin 0 → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
    {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {δ₂ : ℝ} (hp₂ : PathOn κ xL₂ xR₂ ρR₂ W₂ VL₂ VR₂ B₂ ζ₂ ω₂ (S₂ m ω₂) δ₂)
    (hx₂ : xL₂ 0 = g3Marks VL₁ VR₁ ω₁ 2 0 - p) (hy₂ : xL₂ 1 = -p) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (S₁ m ω₁))
    {u : ℝ≥0} (hu : u ≤ S₂ m ω₂) :
    seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, ω₂) s u =
      Real.exp (((eView (kh κ) (g3RR κ) (eightDrv W₁ S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₁ m ω₁) (S₂ m ω₂)
          (g3Marks VL₁ VR₁ ω₁) s).ell u (w W₂ ω₂ u) + ell κ W₂ VL₂ ω₂ u (w W₂ ω₂ u)) -
        ((eView (kh κ) (g3RR κ) (eightDrv W₁ S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₁ m ω₁) (S₂ m ω₂)
          (g3Marks VL₁ VR₁ ω₁) s).ell 0 (w W₂ ω₂ 0) + ell κ W₂ VL₂ ω₂ 0 (w W₂ ω₂ 0))) := by
  have hv := hset.view
  have hk : kh κ ≠ 0 := by unfold kh; positivity
  have huI : (u : ℝ) ∈ Icc (0 : ℝ) (S₂ m ω₂) := ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  -- the record at height `u` reads the large path stopped at `S₂`
  rw [seedHeightField, g3Rec_eq_srcRec hc₂ huI.1 huI.2]
  set V₂ := frzPath W₂ p (S₂ m ω₂) ω₂ with hV₂def
  set e := eView (kh κ) (g3RR κ) (eightDrv W₁ S₁ m ω₁) V₂ (S₁ m ω₁) (S₂ m ω₂) (g3Marks VL₁ VR₁ ω₁) s with he
  -- the opposite view's driver is the large driver on `[0, S₂]`
  have hV₂ : (fun u => V₂ u - V₂ 0) = A1Ref.stopDrv (Strip.extPath (W₂ · ω₂)) (S₂ m ω₂) :=
    A1Asm.frzPath_sub_zero_eq h0₂ p (S₂ m ω₂) (S₂ m ω₂).coe_nonneg
  have hWw : ∀ r : ℝ, r ∈ Icc (0 : ℝ) (S₂ m ω₂) → V₂ r - V₂ 0 = w W₂ ω₂ r := fun r hr => by
    rw [show V₂ r - V₂ 0 = A1Ref.stopDrv (Strip.extPath (W₂ · ω₂)) (S₂ m ω₂) r from congrFun hV₂ r,
      A1Ref.stopDrv_eqOn _ _ hr]
    rfl
  have hn1 := normEll_srcRec_eq_eView_sub hset hk (g3RR κ) hs huI
  rw [hWw u huI, hWw 0 ⟨le_rfl, (S₂ m ω₂).coe_nonneg⟩] at hn1
  -- the own-time-`0` value
  obtain ⟨-, -, -, hcw₂, hcL₂, -, -, -, -, -, -, -, -, hLeq₂, -⟩ := id hp₂.path
  have hne : ∀ r ≤ S₂ m ω₂, ∀ i, VL₂ i r ω₂ ≠ W₂ r ω₂ := fun r hr i he' => by
    have := hp₂.gap r hr i
    rw [he', sub_self, abs_zero] at this
    linarith [hp₂.pos]
  have hode := sub_eq_mul_exp_of_force hcw₂ (hcL₂ 0) (hcL₂ 1) (fun t ht => hLeq₂ t ht 0) (fun t ht => hLeq₂ t ht 1)
    hp₂.lt (fun r hr => hne r hr 0) (fun r hr => hne r hr 1) hu
  have hxy₂ : xL₂ 0 ≠ xL₂ 1 := by
    rw [hx₂, hy₂]
    intro h'
    exact hV2 (by linarith)
  have hxy : VL₂ 0 u ω₂ ≠ VL₂ 1 u ω₂ := by
    intro h'
    have h0 := hode
    simp only at h0
    rw [h', sub_self] at h0
    exact (mul_ne_zero (sub_ne_zero.2 hxy₂) (Real.exp_pos _).ne') h0.symm
  have hV0 : g3Marks VL₁ VR₁ ω₁ 0 0 = eightDrv W₁ S₁ m ω₁ 0 := hv.lo.zero
  have hV1 : g3Marks VL₁ VR₁ ω₁ 1 0 = eightDrv W₁ S₁ m ω₁ 0 := hv.hi.zero
  have hV2' : g3Marks VL₁ VR₁ ω₁ 2 0 ≠ eightDrv W₁ S₁ m ω₁ 0 := by rw [hv.zero₁]; exact hV2
  have hvx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ ω₂ → VL₂ 0 t ω₂ = (g3Marks VL₁ VR₁ ω₁ 2 0 - p) +
      ∫ r in (0 : ℝ)..t, 2 / (VL₂ 0 r.toNNReal ω₂ - W₂ r.toNNReal ω₂) := fun t ht => by
    rw [← hx₂]; exact hLeq₂ t ht 0
  have hvy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ ω₂ → VL₂ 1 t ω₂ = -p +
      ∫ r in (0 : ℝ)..t, 2 / (VL₂ 1 r.toNNReal ω₂ - W₂ r.toNNReal ω₂) := fun t ht => by
    rw [← hy₂]; exact hLeq₂ t ht 1
  have hn0 := normEll_srcRec_g3_own_zero_eq hset hκ hV0 hV1 hV2' hV2p (w := (W₂ · ω₂)) (vx := (VL₂ 0 · ω₂))
    (vy := (VL₂ 1 · ω₂)) (ζ := ζ₂ ω₂) (Sl := S₂ m ω₂) rfl hV₂ hcw₂ (hcL₂ 0) (hcL₂ 1) hvx hvy hp₂.lt
    (fun r hr => hne r hr 0) (fun r hr => hne r hr 1) hu hxy
  -- the inverse martingale's logarithm
  have hl := ell_sub_eq_neg_g3LogMart (S := fun _ : Y => u) (pathOn_mono hp₂ hu) hxy₂
  rw [hn1, hn0]
  congr 1
  linarith

end InteractingSLE.ZhanGT4.A1G3RR
