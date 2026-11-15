/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdAxis
import InteractingSLE.Spec.ZhanGT4.A1G3RowEight
import InteractingSLE.Spec.ZhanGT4.A1AsmG0

/-!
# Zhan's A.1 (G3): the patch density is the Girsanov density times the inverse `SLE_κ(κ − 4, −4)` martingale ratio

Packet PROVE-A1-G3ROW2. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425: the
rectangle density is, row by row, the frozen-curve density (D6) of the large curve with the small hull frozen), and the
specification's force-point martingale (proof of Theorem 2.2, L488).

In (G3) the large curve is `SLE_κ(κ − 4, −4)` with force points `x` (weight `κ − 4`) and `y` (weight `−4`). Relative
to ordinary `SLE_κ` its density is `M_t/M_0` with
`log M_t = log g_t'(y) − (4/κ) log|V_y − W| + ((κ − 4)/κ) log|W − V_x| + (8/κ − 2) log|V_x − V_y|`
(`g3LogMart`; `log g_t'(y) = −∫₀ᵗ 2/(V_y − W)²`). This file proves, deterministically:

* `g3RR_dual`: the G3 charges in the two views (`−(κ̂/4)·g3RR = largeG3RR ∘ swap 0 2`);
* `eView_zero_frzImg`, `eView_zero_frzImgD`: the opposite view frozen at own time `0` reads the large curve's own
  Loewner flow (no small hull);
* **`normEll_srcRec_g3_eq_frzDataOf`**: at a positive own time, the column record's normalized logarithm is the
  increment of A1-LARGEDENS's `frzDataOf` logarithm (marks `x`, `y⁺`, `y⁻`, charges `largeG3RR`) along any Brownian
  path whose driver is the large curve;
* **`normEll_srcRec_g3_own_zero_eq`**: the own-time-`0` value is the increment of `g3LogMart` of the large path;
* **`seedHeightField_g3Rec_eq`**: for the concrete records `g3Rec`, the patch density at the corner of a rectangle is
  `girsDensity · exp(−(log M_{S₂} − log M_0))`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)
open A1SeedField A1EightSeed A1EightFin A1G3Calc A2X A1LargeDens A1G3Row

/-! ### The charges and the large martingale -/

/-- **The G3 charges in the two views**: the opposite view's reduced charges `−(κ̂/4)·g3RR κ` (marks `y⁻`, `y⁺`, `x`)
are A.1's large image charges `largeG3RR κ` (marks `x`, `y⁺`, `y⁻`) after the swap `0 ↔ 2`. -/
theorem g3RR_dual {κ : ℝ} (hκ : κ ≠ 0) (m : Fin 3) :
    largeG3RR κ m = -(kh κ / 4) * g3RR κ (Equiv.swap 0 2 m) := by
  have e1 : Equiv.swap (0 : Fin 3) 2 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  rw [g3RR_eq]
  fin_cases m
  · rw [show ((⟨0, by decide⟩ : Fin 3)) = 0 from rfl, Equiv.swap_apply_left]
    simp only [largeG3RR, kh, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    ring
  · rw [show ((⟨1, by decide⟩ : Fin 3)) = 1 from rfl, e1]
    simp only [largeG3RR, kh, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    ring
  · rw [show ((⟨2, by decide⟩ : Fin 3)) = 2 from rfl, Equiv.swap_apply_right]
    simp only [largeG3RR, kh, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    field_simp
    ring

/-- **The logarithm of the `SLE_κ(κ − 4, −4)` martingale relative to `SLE_κ`** along a driver `w` with force points
`vx` (weight `κ − 4`) and `vy` (weight `−4`): `−∫₀ᵗ 2/(vy − w)² − (4/κ) log(vy − w) + ((κ − 4)/κ) log(w − vx)
+ (8/κ − 2) log(vx − vy)` (`Real.log` is `log |·|`). -/
def g3LogMart (κ : ℝ) (w vx vy : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  -(∫ s in (0 : ℝ)..t, 2 / (vy s.toNNReal - w s.toNNReal) ^ 2) + -(4 / κ) * Real.log (vy t - w t) +
    (κ - 4) / κ * Real.log (w t - vx t) + (8 / κ - 2) * Real.log (vx t - vy t)

/-! ### One rectangle: the opposite view at own time `0` and the transfer to `frzDataOf` -/

section View

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}

/-- The opposite image chain at own time `0` (no small hull) is the large driver itself: clock `id`, image driver
`V₂ − V₂ 0`, on `[0, Y]`. -/
theorem tSel_zero (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) :
    tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0 t = t ∧
      tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0 t = V₂ t - V₂ 0 := by
  have hown := (h.tOwn (⟨le_rfl, h.pos₁.le⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) S)).1
  have hc : Continuous fun s => W₁ s - V₂ 0 := h.cont₁.sub continuous_const
  rw [QuantumZipper.RS.fwdHull_zero_eq_empty hc, frzChart_zero_eq_id] at hown
  exact ⟨hown.clock_eq_of_empty ht, hown.W'_eq_of_empty ht⟩

/-- **The opposite view frozen at own time `0` reads the large curve's own flow**: `frzImg` of its image chain at a
real point `z` is `Re g_t(z) + W_t` for the large driver `V₂ − V₂ 0`. -/
theorem eView_zero_frzImg (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y)
    (z : ℝ) :
    frzImg (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0)
        (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) z t =
      (fwdMap (fun u => V₂ u - V₂ 0) t z).re + (V₂ t - V₂ 0) := by
  obtain ⟨ha, hW⟩ := tSel_zero h ht
  have hmap : fwdMap (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) t =
      fwdMap (fun u => V₂ u - V₂ 0) t := by
    funext w
    exact Ito.fwdMap_congr_of_eqOn fun v hv => (tSel_zero h ⟨hv.1, hv.2.trans ht.2⟩).2
  rw [frzImg, ha, hmap, hW]

/-- The derivative companion of `eView_zero_frzImg`. -/
theorem eView_zero_frzImgD (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y)
    (z : ℝ) :
    frzImgD (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0)
        (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) z t =
      (deriv (fwdMap (fun u => V₂ u - V₂ 0) t) z).re := by
  obtain ⟨ha, -⟩ := tSel_zero h ht
  have hmap : fwdMap (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) t =
      fwdMap (fun u => V₂ u - V₂ 0) t := by
    funext w
    exact Ito.fwdMap_congr_of_eqOn fun v hv => (tSel_zero h ⟨hv.1, hv.2.trans ht.2⟩).2
  rw [frzImgD, ha, hmap]

/-- **The G3 row in A1-LARGEDENS's frame**: at a positive own time `s ≤ S` and a height `t ≤ Y`, the column record's
normalized logarithm at `s` is the increment of the logarithm of
`frzDataOf κ B W' a (frzChart (W₁ − p) s) (largeG3RR κ) (W₁ s − p) ![V₂ₛ − p, V₁ₛ − p, V₀ₛ − p]` (marks: the ordinary
mark, then the seeds `y⁺`, `y⁻`) along the driver, for every Brownian path `B` whose driver `√κ B` is the large curve
`V₂ − p` up to `Y`, with any image chain `(a, W')` up to `T ≥ Y`. -/
theorem normEll_srcRec_g3_eq_frzDataOf {V : Fin 3 → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V)
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} {W' a : Ω → ℝ → ℝ} {T s : ℝ} (hκ : 0 < κ)
    (hs : s ∈ Ioc (0 : ℝ) S)
    (hown : OwnData (drive κ B ω) (fwdHull (fun u => W₁ u - p) s) (frzChart (fun u => W₁ u - p) s) T (a ω) (W' ω))
    (hYT : Y ≤ T) (hB : ∀ u ∈ Icc (0 : ℝ) Y, drive κ B ω u = V₂ u - p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) :
    (srcRec W₁ S V₂ t (kh κ) (g3RR κ) p V).normEll s =
      (frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeG3RR κ) (W₁ s - p)
          ![V 2 s - p, V 1 s - p, V 0 s - p] ω).ell t (drive κ B ω t) -
        (frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeG3RR κ) (W₁ s - p)
          ![V 2 s - p, V 1 s - p, V 0 s - p] ω).ell 0 (drive κ B ω 0) := by
  have hv := h.view
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hk : kh κ ≠ 0 := by unfold kh; positivity
  rw [normEll_srcRec_eq_eView_sub h hk (g3RR κ) hs ht]
  set e := eView (kh κ) (g3RR κ) W₁ V₂ S Y V s with he
  set f := frzDataOf κ B W' a (frzChart (fun u => W₁ u - p) s) (largeG3RR κ) (W₁ s - p)
    ![V 2 s - p, V 1 s - p, V 0 s - p] ω with hf
  have hz : V₂ 0 = p := hv.zero₂
  have hsI : s ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self hs
  have h₁ := (hv.tOwn hsI).1
  have hA : fwdHull (fun u => W₁ u - V₂ 0) s = fwdHull (fun u => W₁ u - p) s := by rw [hz]
  have hφ : frzChart (fun u => W₁ u - V₂ 0) s = frzChart (fun u => W₁ u - p) s := by rw [hz]
  rw [hA, hφ] at h₁
  have hWe : EqOn e.W f.W (Icc 0 Y) := fun u hu => by
    change V₂ u - V₂ 0 = drive κ B ω u
    rw [hB u hu, hz]
  have hcongr : ∀ v ∈ Icc (0 : ℝ) Y, ∀ x, e.ell v x = f.ell v x := fun v hv' x =>
    FrzData.ell_congr_of_ownData (d₁ := e) (d₂ := f) h₁ hown (by change frzChart _ s = _; rw [hφ]) rfl hWe
      (sixteen_div_kh hκ0) (Equiv.swap 0 2) (fun m => g3RR_dual hκ0 m)
      (by change W₁ s - V₂ 0 = W₁ s - p; rw [hz])
      (fun m => by
        fin_cases m
        · change V 2 s - p = V 2 s - V₂ 0
          rw [hz]
        · change V 1 s - p = V (Equiv.swap (0 : Fin 3) 2 1) s - V₂ 0
          rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), hz]
        · change V 0 s - p = V 0 s - V₂ 0
          rw [hz])
      ⟨hv'.1, le_min (le_min hv'.2 (hv'.2.trans hYT)) hv'.2⟩ x
  have h0Y : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, hv.pos₂.le⟩
  rw [hcongr t ht, hcongr 0 h0Y]
  have hdt : V₂ t - V₂ 0 = drive κ B ω t := by rw [hB t ht, hz]
  have hd0 : V₂ 0 - V₂ 0 = drive κ B ω 0 := by rw [hB 0 h0Y, hz]
  rw [hdt, hd0]

/-- **The own-time-`0` value of the G3 record is the increment of the large martingale's logarithm.** For a
`G3Setup` with the G3 charges whose seeds start at the driver and whose ordinary mark starts at `x₀ ∉ {0, p}`, when the
large driver `V₂ − p` is the driver `w` stopped at `Sl = Y`, and `vx`, `vy` are the large curve's force points started
at `x₀ − p` and `−p` (the images of the ordinary mark and of the small source), off the driver up to `Sl < ζ`: at every
height `u ≤ Sl` where `vx u ≠ vy u`,
`d_u.normEll 0 = g3LogMart κ w vx vy u − g3LogMart κ w vx vy 0`. -/
theorem normEll_srcRec_g3_own_zero_eq {V : Fin 3 → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V)
    {κ : ℝ} (hκ : 0 < κ) (hV0 : V 0 0 = W₁ 0) (hV1 : V 1 0 = W₁ 0) (hV2 : V 2 0 ≠ W₁ 0) (hV2p : V 2 0 ≠ p)
    {w vx vy : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {Sl : ℝ≥0} (hY : Y = Sl)
    (hV₂ : (fun u => V₂ u - V₂ 0) = A1Ref.stopDrv (Strip.extPath w) Sl)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvxc : ContinuousOn vx {t | (t : ℝ≥0∞) < ζ})
    (hvyc : ContinuousOn vy {t | (t : ℝ≥0∞) < ζ})
    (hvx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vx t = (V 2 0 - p) + ∫ s in (0 : ℝ)..t, 2 / (vx s.toNNReal - w s.toNNReal))
    (hvy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vy t = -p + ∫ s in (0 : ℝ)..t, 2 / (vy s.toNNReal - w s.toNNReal))
    (hSl : (Sl : ℝ≥0∞) < ζ) (hsx : ∀ r ≤ Sl, vx r ≠ w r) (hsy : ∀ r ≤ Sl, vy r ≠ w r) {u : ℝ≥0} (hu : u ≤ Sl)
    (hxy : vx u ≠ vy u) :
    (srcRec W₁ S V₂ u (kh κ) (g3RR κ) p V).normEll 0 = g3LogMart κ w vx vy u - g3LogMart κ w vx vy 0 := by
  have hv := h.view
  have hz₁ : W₁ 0 = 0 := hv.zero₁
  have hz₂ : V₂ 0 = p := hv.zero₂
  have hp : 0 < p := hv.pp.prot_pos.trans hv.pp.prot_lt
  have hk : kh κ ≠ 0 := by unfold kh; positivity
  have huY : (u : ℝ) ∈ Icc (0 : ℝ) Y := by rw [hY]; exact ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩
  have hvy' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      vy t = (W₁ 0 - V₂ 0) + ∫ s in (0 : ℝ)..t, 2 / (vy s.toNNReal - w s.toNNReal) := fun t ht => by
    rw [hz₁, hz₂, zero_sub]; exact hvy t ht
  have hvx' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      vx t = (V 2 0 - V₂ 0) + ∫ s in (0 : ℝ)..t, 2 / (vx s.toNNReal - w s.toNNReal) := fun t ht => by
    rw [hz₂]; exact hvx t ht
  have he20 : (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A20 u = vy u := by
    change frzImg (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0)
      (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) (W₁ 0 - V₂ 0) u = vy u
    rw [eView_zero_frzImg hv huY, show V₂ u - V₂ 0 = A1Ref.stopDrv (Strip.extPath w) Sl u from congrFun hV₂ u, hV₂]
    exact A1Common.fwdMap_stopDrv_add_eq hwc hvyc hvy' hSl hsy hu
  have he21 : (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A21 u =
      Real.exp (-∫ s in (0 : ℝ)..u, 2 / (vy s.toNNReal - w s.toNNReal) ^ 2) := by
    change frzImgD (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0)
      (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) (W₁ 0 - V₂ 0) u = _
    rw [eView_zero_frzImgD hv huY, hV₂]
    exact A1Asm.re_deriv_fwdMap_stopDrv_eq hwc hvyc hvy' hSl hsy hu
  have heB0 : (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).B0 u 2 = vx u := by
    change frzImg (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0)
      (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) 0) (V 2 0 - V₂ 0) u = vx u
    rw [eView_zero_frzImg hv huY, show V₂ u - V₂ 0 = A1Ref.stopDrv (Strip.extPath w) Sl u from congrFun hV₂ u, hV₂]
    exact A1Common.fwdMap_stopDrv_add_eq hwc hvxc hvx' hSl hsx hu
  have hstop : ∀ r : ℝ≥0, r ≤ Sl → A1Ref.stopDrv (Strip.extPath w) Sl r = w r := fun r hr => by
    rw [A1Ref.stopDrv_eqOn _ _ ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr⟩, Strip.extPath, Real.toNNReal_coe]
  have hV₂u : V₂ u = w u + p := by
    have := congrFun hV₂ u
    rw [hstop u hu, hz₂] at this
    linarith
  have hw0 : w 0 = 0 := by
    have h0 := congrFun hV₂ 0
    have h1 := hstop 0 bot_le
    rw [NNReal.coe_zero] at h1
    rw [h1, sub_self] at h0
    exact h0.symm
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) hSl
  have hvy0 : vy 0 = -p := by rw [hvy 0 hζ0]; simp
  have hvx0 : vx 0 = V 2 0 - p := by rw [hvx 0 hζ0]; simp
  have htip : (eView (kh κ) (g3RR κ) W₁ V₂ S Y V 0).A20 u + p ≠ V₂ u := by
    rw [he20, hV₂u]
    intro h'
    exact hsy u hu (by linarith)
  rw [normEll_srcRec_g3_own_zero hk h hV0 hV1 hV2 huY htip, he20, he21, heB0, hV₂u, Real.log_exp]
  have e1 : (vy u + p - (w u + p)) / -p = (vy u - w u) / -p := by ring
  have e2 : (w u + p - (vx u + p)) / (p - V 2 0) = (w u - vx u) / (p - V 2 0) := by ring
  have hyw : vy u - w u ≠ 0 := sub_ne_zero.2 (hsy u hu)
  have hwx : w u - vx u ≠ 0 := sub_ne_zero.2 (hsx u hu).symm
  have hyx : vy u - vx u ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hpm : -p ≠ 0 := neg_ne_zero.2 hp.ne'
  have hpV : p - V 2 0 ≠ 0 := sub_ne_zero.2 (Ne.symm hV2p)
  have hV20 : -V 2 0 ≠ 0 := neg_ne_zero.2 (by rw [hz₁] at hV2; exact hV2)
  rw [e1, e2, Real.log_div hyw hpm, Real.log_div hwx hpV, Real.log_div hyx hV20]
  have l1 : Real.log (vy u - vx u) = Real.log (vx u - vy u) := by rw [← neg_sub, Real.log_neg_eq_log]
  have l2 : Real.log (-V 2 0) = Real.log (V 2 0) := Real.log_neg_eq_log _
  rw [l1, l2]
  unfold g3LogMart
  rw [hw0, hvy0, hvx0]
  have h0x : (0 : ℝ) - (V 2 0 - p) = p - V 2 0 := by ring
  have h0xy : V 2 0 - p - -p = V 2 0 := by ring
  rw [h0x, h0xy, sub_zero]
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, neg_zero, zero_add, kh]
  field_simp
  ring

end View

/-! ### The concrete G3 records -/

section Records

variable {X Y : Type*}

/-- **A G3 mixed source record gives a `G3Setup`**, once its driver lies between its two seeds (the first two marks). -/
theorem g3Setup_of_isSourceRecordG {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin 3 → ℝ} {W₂ : ℝ → ℝ} {t₂ : ℝ}
    {s : SeedData 3} {Vlo Vhi : ℝ → ℝ} {T : ℝ} (hpp : IsProtectedPairG H₁ H₂ δ p q dd)
    (hrec : IsSourceRecordG H₁ H₂ p q Tm κ rr W₂ t₂ s Vlo Vhi T) (hV0 : s.V 0 = Vlo) (hV1 : s.V 1 = Vhi)
    (hdrv : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ uIcc (Vlo t) (Vhi t)) :
    G3Setup H₁ H₂ δ p q dd Tm s.W W₂ T t₂ Vlo Vhi s.V where
  view :=
    { pp := hpp.pair
      cont₁ := hrec.own.cont
      zero₁ := hrec.own.zero
      pos₁ := hrec.own.pos
      le₁ := hrec.le₁
      K₁ := hrec.sub₁
      cont₂ := hrec.contW₂
      zero₂ := hrec.zeroW₂
      pos₂ := hrec.pos₂
      le₂ := hrec.le₂
      K₂ := hrec.sub₂
      lo := hrec.lo
      hi := hrec.hi
      drv := hdrv
      inj := fun u hu he =>
        absurd (hrec.inj u hu (show s.V 0 u = s.V 1 u by rw [hV0, hV1]; exact he)) (by decide) }
  seg := hpp.seg
  drvE := hrec.drv
  marks := hrec.marks
  mark := hrec.mark
  inj := hrec.inj

/-- **The G3 row identity at the corner of a rectangle (deterministic).** For A1-G3CALC's concrete records `g3Rec`
(other source `p`), at one rectangle `m` and one pair of samples `(ω₁, ω₂)` where the rectangle data of
`isSourceRecordG_g3Rec` hold, the large path is an integrated path whose force points start at the images `xR 1 − p`
of the ordinary mark and `−p` of the small source and stay off the driver up to the exit `S₂ m ω₂ < ζ₂`, and `√κ B₂`
is the large driver up to the exit, with any image chain `(a, W')` of `√κ B₂` against the small hull frozen at
`s ∈ (0, S₁ m ω₁]`: the patch density at the corner `(s, S₂ m ω₂)` is
`girsDensity (√κ) B₂ (S₂ m) ℓ ω₂ · exp(−(g3LogMart S₂ − g3LogMart 0))`, `ℓ` the logarithm of A1-LARGEDENS's
`frzDataOf` with the G3 large charges and the marks `x`, `y⁺`, `y⁻` (physical, at `s`). -/
theorem seedHeightField_g3Rec_eq {κ p a₀ : ℝ} (hκ : 0 < κ) {xL : Fin 1 → ℝ} {xR : Fin 3 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0}
    {H₁ H₂ : Set ℂ} {δ q dd Tm : ℝ} {m : ℕ} {ω₁ : X} {ω₂ : Y} (hpp : IsProtectedPairG H₁ H₂ δ p q dd)
    (hP : IsIntegratedSLEPath a₀ xL xR ρL ρR (W₁ · ω₁) (fun i s => VL₁ i s ω₁) (fun i s => VR₁ i s ω₁) (B₁ · ω₁)
      (ζ₁ ω₁))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxO : 0 < xR 1) (hxOq : xR 1 ≤ q)
    (hgood₁ : (S₁ m ω₁ : ℝ≥0∞) < ζ₁ ω₁ ∧ 0 < (S₁ m ω₁ : ℝ) ∧ (S₁ m ω₁ : ℝ) ≤ Tm ∧
      fwdHull (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) ⊆ H₁)
    (hsep₁ : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < ζ₁ ω₁ → VL₁ 0 s ω₁ ≠ W₁ s ω₁ ∧ VR₁ 0 s ω₁ ≠ W₁ s ω₁)
    (hsepO : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω₁ → VR₁ 1 s ω₁ ≠ W₁ s ω₁)
    (hc₂ : ContinuousOn (Strip.extPath (W₂ · ω₂)) (Icc 0 (S₂ m ω₂))) (h0₂ : W₂ 0 ω₂ = 0)
    (hgood₂ : (S₂ m ω₂ : ℝ) ≤ Tm ∧ fwdHull (frzPath W₂ p (S₂ m ω₂) ω₂) (S₂ m ω₂) ⊆ H₂)
    (hS₂pos : 0 < (S₂ m ω₂ : ℝ)) {a₂ : ℝ} {xL₂ : Fin 2 → ℝ} {nR₂ : ℕ} {xR₂ : Fin nR₂ → ℝ} {ρL₂ : Fin 2 → ℝ}
    {ρR₂ : Fin nR₂ → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin nR₂ → ℝ≥0 → Y → ℝ} {b₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (hP₂ : IsIntegratedSLEPath a₂ xL₂ xR₂ ρL₂ ρR₂ (W₂ · ω₂) (fun i s => VL₂ i s ω₂) (fun j s => VR₂ j s ω₂)
      (b₂ · ω₂) (ζ₂ ω₂))
    (hx₂ : xL₂ 0 = xR 1 - p) (hy₂ : xL₂ 1 = -p) (hS₂ζ : (S₂ m ω₂ : ℝ≥0∞) < ζ₂ ω₂)
    (hsx : ∀ r ≤ S₂ m ω₂, VL₂ 0 r ω₂ ≠ W₂ r ω₂) (hsy : ∀ r ≤ S₂ m ω₂, VL₂ 1 r ω₂ ≠ W₂ r ω₂)
    (hxy : VL₂ 0 (S₂ m ω₂) ω₂ ≠ VL₂ 1 (S₂ m ω₂) ω₂)
    {B₂ : ℝ≥0 → Y → ℝ} (hB₂ : ∀ u ∈ Icc (0 : ℝ) (S₂ m ω₂), drive κ B₂ ω₂ u = Strip.extPath (W₂ · ω₂) u)
    {s T : ℝ} (hs : s ∈ Ioc (0 : ℝ) (S₁ m ω₁)) {W' a : Y → ℝ → ℝ}
    (hown : OwnData (drive κ B₂ ω₂) (fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - p) s)
      (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) T (a ω₂) (W' ω₂)) (hYT : (S₂ m ω₂ : ℝ) ≤ T) :
    seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, ω₂) s (S₂ m ω₂) =
      girsDensity (Real.sqrt κ) B₂ (S₂ m) (fun ω' => (frzDataOf κ B₂ W' a
          (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (largeG3RR κ) (eightDrv W₁ S₁ m ω₁ s - p)
          ![Strip.extPath (VR₁ 1 · ω₁) s - p, Strip.extPath (VR₁ 0 · ω₁) s - p,
            Strip.extPath (VL₁ 0 · ω₁) s - p] ω').ell) ω₂ *
        Real.exp (-(g3LogMart κ (W₂ · ω₂) (VL₂ 0 · ω₂) (VL₂ 1 · ω₂) (S₂ m ω₂) -
          g3LogMart κ (W₂ · ω₂) (VL₂ 0 · ω₂) (VL₂ 1 · ω₂) 0)) := by
  have hprot := hpp.pair.prot
  have hne : ∀ r : ℝ≥0, 0 < r → r ≤ S₁ m ω₁ → VL₁ 0 r ω₁ ≠ W₁ r ω₁ ∧ VR₁ 0 r ω₁ ≠ W₁ r ω₁ := fun r hr hrS =>
    hsep₁ r hr (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrS) hgood₁.1)
  have hrec := isSourceRecordG_g3Rec (κ := κ) (p := p) (m := m) hP hxL hxR hxO hxOq hgood₁.1 hgood₁.2.1
    (fun r hr hrS => (hne r hr hrS).1) (fun r hr hrS => (hne r hr hrS).2)
    (fun r hrS => hsepO r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrS) hgood₁.1))
    (by have := hpp.pair.rad_pos; positivity) (hprot.mono_right subset_union_left) hc₂ h0₂ hS₂pos hgood₂.1
    hgood₁.2.2.1 hpp.pair.sep_pos hpp.pair.sep hgood₁.2.2.2 hgood₂.2
  have hEq := eightDrv_eqOn W₁ S₁ m ω₁
  have hloW := vL_le_of_path hP 0 hgood₁.1 hEq
  have hWhi := le_vR_of_path hP 0 hgood₁.1 hEq
  have hset := g3Setup_of_isSourceRecordG hpp hrec rfl rfl
    (fun t ht => Icc_subset_uIcc ⟨hloW t ht, hWhi t ht⟩)
  have hB : ∀ u ∈ Icc (0 : ℝ) (S₂ m ω₂), drive κ B₂ ω₂ u = frzPath W₂ p (S₂ m ω₂) ω₂ u - p := fun u hu => by
    simp only [frzPath, A1Ref.stopDrv_eqOn _ _ hu, add_sub_cancel_right, hB₂ u hu]
  have hS₂I : ((S₂ m ω₂ : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S₂ m ω₂) := ⟨(S₂ m ω₂).coe_nonneg, le_rfl⟩
  have hnorm : (srcRec (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₂ m ω₂) (kh κ) (g3RR κ) p
      (g3Marks VL₁ VR₁ ω₁)).normEll s =
      (frzDataOf κ B₂ W' a (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (largeG3RR κ)
          (eightDrv W₁ S₁ m ω₁ s - p) ![Strip.extPath (VR₁ 1 · ω₁) s - p, Strip.extPath (VR₁ 0 · ω₁) s - p,
            Strip.extPath (VL₁ 0 · ω₁) s - p] ω₂).ell (S₂ m ω₂) (drive κ B₂ ω₂ (S₂ m ω₂)) -
        (frzDataOf κ B₂ W' a (frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (largeG3RR κ)
          (eightDrv W₁ S₁ m ω₁ s - p) ![Strip.extPath (VR₁ 1 · ω₁) s - p, Strip.extPath (VR₁ 0 · ω₁) s - p,
            Strip.extPath (VL₁ 0 · ω₁) s - p] ω₂).ell 0 (drive κ B₂ ω₂ 0) :=
    normEll_srcRec_g3_eq_frzDataOf hset hκ hs hown hYT hB hS₂I
  -- the own-time-`0` value
  obtain ⟨-, hvL0, hvR0, -⟩ := id hP
  obtain ⟨-, -, -, hcw₂, hcL₂, -, -, -, -, -, -, -, -, hLeq₂, -⟩ := id hP₂
  have hV0 : g3Marks VL₁ VR₁ ω₁ 0 0 = eightDrv W₁ S₁ m ω₁ 0 := hrec.lo.zero
  have hV1 : g3Marks VL₁ VR₁ ω₁ 1 0 = eightDrv W₁ S₁ m ω₁ 0 := hrec.hi.zero
  have hV2v : g3Marks VL₁ VR₁ ω₁ 2 0 = xR 1 := by
    change Strip.extPath (VR₁ 1 · ω₁) 0 = xR 1
    simp only [Strip.extPath, Real.toNNReal_zero]
    exact hvR0 1
  have hW0 : eightDrv W₁ S₁ m ω₁ 0 = 0 := hset.view.zero₁
  have hpq : xR 1 < p := hxOq.trans_lt hpp.pair.prot_lt
  have hV2 : g3Marks VL₁ VR₁ ω₁ 2 0 ≠ eightDrv W₁ S₁ m ω₁ 0 := by rw [hV2v, hW0]; exact hxO.ne'
  have hV2p : g3Marks VL₁ VR₁ ω₁ 2 0 ≠ p := by rw [hV2v]; exact hpq.ne
  have hV₂ : (fun u => frzPath W₂ p (S₂ m ω₂) ω₂ u - frzPath W₂ p (S₂ m ω₂) ω₂ 0) =
      A1Ref.stopDrv (Strip.extPath (W₂ · ω₂)) (S₂ m ω₂) := by
    funext u
    rw [frzPath_zero h0₂ (S₂ m ω₂).coe_nonneg]
    simp only [frzPath, add_sub_cancel_right]
  have hvx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ ω₂ → VL₂ 0 t ω₂ = (g3Marks VL₁ VR₁ ω₁ 2 0 - p) +
      ∫ r in (0 : ℝ)..t, 2 / (VL₂ 0 r.toNNReal ω₂ - W₂ r.toNNReal ω₂) := fun t ht => by
    rw [hV2v, ← hx₂]; exact hLeq₂ t ht 0
  have hvy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ ω₂ → VL₂ 1 t ω₂ = -p +
      ∫ r in (0 : ℝ)..t, 2 / (VL₂ 1 r.toNNReal ω₂ - W₂ r.toNNReal ω₂) := fun t ht => by
    rw [← hy₂]; exact hLeq₂ t ht 1
  have hzero : (srcRec (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₂ m ω₂) (kh κ) (g3RR κ) p
      (g3Marks VL₁ VR₁ ω₁)).normEll 0 = g3LogMart κ (W₂ · ω₂) (VL₂ 0 · ω₂) (VL₂ 1 · ω₂) (S₂ m ω₂) -
        g3LogMart κ (W₂ · ω₂) (VL₂ 0 · ω₂) (VL₂ 1 · ω₂) 0 :=
    normEll_srcRec_g3_own_zero_eq hset hκ hV0 hV1 hV2 hV2p (w := (W₂ · ω₂)) (vx := (VL₂ 0 · ω₂))
      (vy := (VL₂ 1 · ω₂)) (ζ := ζ₂ ω₂) (Sl := S₂ m ω₂) rfl hV₂ hcw₂ (hcL₂ 0) (hcL₂ 1) hvx hvy hS₂ζ hsx hsy le_rfl
      hxy
  rw [seedHeightField]
  change Real.exp ((srcRec (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂) (S₂ m ω₂) (kh κ) (g3RR κ) p
      (g3Marks VL₁ VR₁ ω₁)).normEll s - (srcRec (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) (frzPath W₂ p (S₂ m ω₂) ω₂)
      (S₂ m ω₂) (kh κ) (g3RR κ) p (g3Marks VL₁ VR₁ ω₁)).normEll 0) = _
  rw [hnorm, hzero, girsDensity, ← Real.exp_add]
  congr 1
  simp only [drive, Real.toNNReal_coe, Real.toNNReal_zero]
  ring

end Records

end InteractingSLE.ZhanGT4.A1G3Id
