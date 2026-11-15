/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aPathSample
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd
import InteractingSLE.Spec.Supplement.GB11RelParam
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Scale
import InteractingSLE.Spec.ZhanGT4.A1RefBridge
import InteractingSLE.Spec.Supplement.RLCG8DetRelBoundary
import InteractingSLE.Spec.Restart.FCAux79MeanFlow
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# BR4a's relative chain: the relative driver of one sample

Packet PROVE-T14-BR4A2 (supplement p. 610, Corollary BR4a: "the original and transformed stopped histories recover
each other, every force label, and both half-plane-capacity clocks"). The target change `w ↦ mob v w = w/(vw + 1)`
of BR4a (pole `−1/v`) is Zhan's explicit retargeting (`Zhan.Retarget`, PROVE-SEC7-C8/C10), applied to the original
driver oriented so that the pole is on the right (`oDrv`: `w` for `v < 0`, `−w` for `v > 0`), with target `a = |v|⁻¹`,
then scaled (`mob v = a ψ_a` for `v < 0`, `ψ_a(z) = z/(a − z)`) and reflected back (`mob v = R ∘ mob (−v) ∘ R` for
`v > 0`, `R z = −z̄`).

* `pullData_of_notMem`: a right target outside the closed hulls before `T₀` gives Zhan's pull-back data (the target
  is alive, its real flow solves the Loewner equation);
* `sclDrv`, `fwdHull_sclDrv_eq`, `hcapSet_image`: the scaled driver and its hull and capacity identities;
* `relDrv` (**the relative driver**), `relClk`, `mob_eq_of_neg`, `mob_eq_of_pos`, `fwdHull_relDrv_eq`,
  `clock_eq_relClk`: the hull identity `K^{rel}_{clock v w t} = mob v (K_t)` and `clock v w t = relClk v w t`;
* `exists_firstTipTime_notMem`: the pole avoids the closed hulls before the first visit;
* **`relDrv_spec`**: for one sample whose clock is unbounded before the first visit, the relative driver is
  continuous everywhere, starts at `0`, Zhan's new horizon is infinite, and the hull identity holds before the visit.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aChain

open Zhan.Retarget MartChar.RealFlow

/-- A right target `a > 0` outside the closed hulls before `T₀` gives the pull-back data. -/
theorem pullData_of_notMem {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {a : ℝ} (ha : 0 < a)
    {T₀ : ℝ≥0∞} (hsep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (a : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t)) :
    PullData w (fun t => rightImg (fun s : ℝ => w s.toNNReal) a t) a T₀ := by
  set wr : ℝ → ℝ := fun s => w s.toNNReal with hwr
  have hwc : Continuous wr := hw.comp continuous_real_toNNReal
  have hwr0 : wr 0 = 0 := by simp [hwr, hw0]
  -- alive before `T₀`
  have halive : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → ∃ X, IsPosSol wr a t X := by
    intro t ht
    obtain ⟨u, hu⟩ := RLC.G8Det.alive_of_notMem_closure hwc (by rw [hwr0]; exact ha.ne') t.coe_nonneg
      (hsep t ht)
    exact ⟨_, WangWu.isPosSol_of_isForwardSol hwc hwr0 ha hu⟩
  have hgap : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → ∀ s ∈ Icc (0 : ℝ) t,
      rightImg wr a s = wr s + cflow wr a s ∧ 0 < cflow wr a s ∧
        cflow wr a s = a - wr s + ∫ r in (0 : ℝ)..s, 2 / cflow wr a r := by
    intro t ht s hs
    obtain ⟨X, hX⟩ := halive t ht
    have hA : Alive wr a s := ⟨X, hX.mono hs.2⟩
    have hc : ∀ r ∈ Icc (0 : ℝ) s, cflow wr a r = X r := fun r hr =>
      cflow_eq_of_isPosSol hwc hX ⟨hr.1, hr.2.trans hs.2⟩
    refine ⟨rightImg_eq_gImg hwc hs.1 hA, ?_, ?_⟩
    · rw [hc s ⟨hs.1, le_rfl⟩]; exact (hX.2 s hs).1
    · rw [hc s ⟨hs.1, le_rfl⟩, (hX.2 s hs).2]
      congr 1
      exact intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le hs.1] at hr
        simp only [hc r hr]
  refine ⟨ha, hw0, ?_, ?_⟩
  · intro S hS0 hST
    refine ⟨hS0, hwc.continuousOn, ?_, ?_⟩
    · refine ((continuousOn_rightImg hwc a).mono fun s hs => (show (0:ℝ) ≤ s from hs.1)).congr fun s hs => ?_
      simp only [Real.coe_toNNReal _ hs.1]
    · intro s hs
      have hsT : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T₀ :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hs.2)) hST
      obtain ⟨h1, h2, -⟩ := hgap _ hsT s.toNNReal ⟨NNReal.coe_nonneg _, le_rfl⟩
      simp only [gap, Real.coe_toNNReal _ hs.1] at h1 h2 ⊢
      rw [h1]
      show 0 < wr s + cflow wr a s - w s.toNNReal
      simp only [hwr] at h2 ⊢
      linarith
  · intro t ht
    obtain ⟨h1, -, h3⟩ := hgap t ht t ⟨t.coe_nonneg, le_rfl⟩
    show rightImg wr a t = a + ∫ s in (0 : ℝ)..t, 2 / (rightImg wr a s.toNNReal - w s.toNNReal)
    rw [h1, h3]
    have : ∫ r in (0 : ℝ)..t, 2 / cflow wr a r =
        ∫ s in (0 : ℝ)..t, 2 / (rightImg wr a s.toNNReal - w s.toNNReal) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le t.coe_nonneg] at hr
      have hr' : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
      obtain ⟨g1, -, -⟩ := hgap t ht r hr
      show 2 / cflow wr a r = 2 / (rightImg wr a (r.toNNReal : ℝ) - wr r)
      rw [hr', g1]
      ring
    rw [this]
    simp only [hwr]
    ring


/-! ### The scaled retargeted driver -/

/-- **The scaled retargeted driver** `r ↦ a · W̃(r / a²)` (Zhan's new driver `W̃ = newDrv`, for the map
`z ↦ a ψ_a(z)`, `ψ_a(z) = z/(a − z)`). -/
def sclDrv (a : ℝ) (w vk : ℝ≥0 → ℝ) (r : ℝ≥0) : ℝ := a * newDrv a w vk ((r : ℝ) / a ^ 2).toNNReal

theorem toNNReal_div_sq {a : ℝ} (ha : 0 < a) (s : ℝ) :
    ((((a ^ 2 * s).toNNReal : ℝ≥0) : ℝ) / a ^ 2).toNNReal = s.toNNReal := by
  have ha2 : 0 < a ^ 2 := by positivity
  rcases le_or_gt 0 s with hs | hs
  · rw [Real.coe_toNNReal _ (by positivity), mul_div_cancel_left₀ _ ha2.ne']
  · have h1 : a ^ 2 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha2.le hs.le
    rw [Real.toNNReal_of_nonpos h1, NNReal.coe_zero, zero_div, Real.toNNReal_zero, Real.toNNReal_of_nonpos hs.le]

theorem sclDrv_scale {a : ℝ} (ha : 0 < a) (w vk : ℝ≥0 → ℝ) :
    (fun s : ℝ => sclDrv a w vk (a ^ 2 * s).toNNReal / a) = fun s : ℝ => newDrv a w vk s.toNNReal := by
  funext s
  simp only [sclDrv, toNNReal_div_sq ha s]
  field_simp

variable {w vk : ℝ≥0 → ℝ} {a : ℝ} {T : ℝ≥0∞}

/-- **The hull identity for the scaled driver**: `K^{sclDrv}_{a² C(t)} = a ψ_a(K_t)` before `T`. -/
theorem fwdHull_sclDrv_eq (hd : PullData w vk a T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    fwdHull (fun r : ℝ => sclDrv a w vk r.toNNReal) (a ^ 2 * clk (rate a w vk) t) =
      (fun z => (a : ℂ) * Sec7.targetChange a z) '' fwdHull (fun s : ℝ => w s.toNNReal) t := by
  have hR := hd.isRate ht
  have h0 : 0 ≤ clk (rate a w vk) t := hR.clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
  rw [ZhanGT4.A34.fwdHull_eq_image_of_scale hd.pos h0]
  have he : (fun s : ℝ => (fun r : ℝ => sclDrv a w vk r.toNNReal) (a ^ 2 * s) / a) =
      fun s : ℝ => newDrv a w vk s.toNNReal := sclDrv_scale hd.pos w vk
  rw [he, hd.fwdHull_newDrv_eq ht, image_image]
  rfl

/-- The scaled driver agrees on `[0, a² C(S)]` with a continuous driver. -/
theorem exists_continuous_sclDrv (hd : PullData w vk a T) {S : ℝ≥0} (hST : (S : ℝ≥0∞) < T) :
    ∃ D : ℝ → ℝ, Continuous D ∧ ∀ r ∈ Icc (0 : ℝ) (a ^ 2 * clk (rate a w vk) S), D r = sclDrv a w vk r.toNNReal := by
  obtain ⟨-, Wn', -, hWn, -, -, -, hWn'eq, -⟩ := hd.local_hull hST
  have ha := hd.pos
  have ha2 : 0 < a ^ 2 := by positivity
  refine ⟨fun r => a * Wn' (r / a ^ 2), continuous_const.mul (hWn.comp (continuous_id.div_const _)), ?_⟩
  intro r hr
  have hr' : r / a ^ 2 ∈ Icc (0 : ℝ) (clk (rate a w vk) S) :=
    ⟨div_nonneg hr.1 ha2.le, (div_le_iff₀ ha2).2 (by linarith [hr.2])⟩
  simp only [sclDrv, Real.coe_toNNReal _ hr.1, hWn'eq _ hr']

/-- **The capacity of the scaled hulls**: `hcap(a ψ_a(K_t)) = 2 a² C(t)` before `T`. -/
theorem hcapSet_image (hd : PullData w vk a T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ConformalImage.hcapSet ((fun z => (a : ℂ) * Sec7.targetChange a z) '' fwdHull (fun s : ℝ => w s.toNNReal) t) =
      2 * (a ^ 2 * clk (rate a w vk) t) := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  obtain ⟨D, hD, hDeq⟩ := exists_continuous_sclDrv hd hST
  have hR := hd.isRate hST
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast htS'.le⟩
  have hlt : clk (rate a w vk) t < clk (rate a w vk) S :=
    hR.clk_lt htI ⟨S.coe_nonneg, le_rfl⟩ (by exact_mod_cast htS')
  have h0 : 0 ≤ clk (rate a w vk) t := hR.clk_nonneg htI
  have ha2 : 0 < a ^ 2 := by have := hd.pos; positivity
  rw [← fwdHull_sclDrv_eq hd ht, ← fwdHull_eq_of_eqOn (W := D) (by positivity)
    (mul_lt_mul_of_pos_left hlt ha2) hDeq]
  exact ZhanGT4.A1Ref.hcapSet_fwdHull hD (by positivity)


/-! ### The relative driver of the target change to `v` -/

open BR4aPath

/-- The orientation of the target change: `1` when the pole `−1/v` is on the right (`v < 0`), `−1` otherwise. -/
def sgn (v : ℝ) : ℝ := if v < 0 then 1 else -1

/-- The distance `|v|⁻¹` of the pole `−1/v` to `0`. -/
def scl (v : ℝ) : ℝ := |v|⁻¹

/-- The original driver in the orientation where the pole is on the right. -/
def oDrv (v : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => sgn v * w t

/-- The pole, flowed by the oriented driver (Zhan's target process). -/
def tgt (v : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => rightImg (fun s : ℝ => oDrv v w s.toNNReal) (scl v) t

/-- **The relative driver of the target change `w ↦ w/(v w + 1)`**: Zhan's explicit retargeted driver of the
oriented driver, scaled by `|v|⁻¹` and oriented back. -/
def relDrv (v : ℝ) (w : ℝ≥0 → ℝ) (q : ℝ≥0) : ℝ := sgn v * sclDrv (scl v) (oDrv v w) (tgt v w) q

/-- **The relative clock** in Zhan's form: `|v|⁻² C(t)`. -/
def relClk (v : ℝ) (w : ℝ≥0 → ℝ) (t : ℝ) : ℝ := scl v ^ 2 * clk (rate (scl v) (oDrv v w) (tgt v w)) t

theorem scl_pos {v : ℝ} (hv : v ≠ 0) : 0 < scl v := inv_pos.2 (abs_pos.2 hv)

theorem pole_eq_scl_of_neg {v : ℝ} (hv : v < 0) : pole v = scl v := by
  simp only [pole, scl, abs_of_neg hv, inv_neg]

theorem pole_eq_neg_scl_of_pos {v : ℝ} (hv : 0 < v) : pole v = -scl v := by
  simp only [pole, scl, abs_of_pos hv]

/-- `w ↦ w/(vw + 1)` is `a ψ_a` for `v = −1/a < 0`. -/
theorem mob_eq_of_neg {v : ℝ} (hv : v < 0) (z : ℂ) :
    BR4aPath.mob v z = (scl v : ℂ) * Sec7.targetChange (scl v) z := by
  have ha : (scl v : ℂ) ≠ 0 := by exact_mod_cast (scl_pos hv.ne).ne'
  have hv0 : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne
  have hva : (v : ℂ) * (scl v : ℂ) = -1 := by
    simp only [scl, abs_of_neg hv]; push_cast; rw [inv_neg, mul_neg, mul_inv_cancel₀ hv0]
  rw [BR4aPath.mob_apply, Sec7.targetChange]
  by_cases hz : (scl v : ℂ) - z = 0
  · have h2 : (v : ℂ) * z + 1 = 0 := by
      rw [show z = (scl v : ℂ) by linear_combination -hz, hva]; ring
    rw [hz, h2]
    simp
  · have h2 : (v : ℂ) * z + 1 ≠ 0 := by
      intro h; apply hz
      linear_combination (scl v : ℂ) * h - z * hva
    rw [mul_div_assoc', div_eq_div_iff h2 hz]
    linear_combination (-z ^ 2) * hva

/-- For `v > 0` the target change is the reflection of the one for `−v`. -/
theorem mob_eq_of_pos {v : ℝ} (hv : 0 < v) (z : ℂ) :
    BR4aPath.mob v z = LP.reflectC ((scl v : ℂ) * Sec7.targetChange (scl v) (LP.reflectC z)) := by
  have hv' : -v < 0 := neg_neg_of_pos hv
  have hs : scl (-v) = scl v := by simp only [scl, abs_neg]
  rw [← hs, ← mob_eq_of_neg hv', BR4aPath.mob_apply, BR4aPath.mob_apply]
  simp only [LP.reflectC, map_div₀, map_add, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal, map_one]
  push_cast
  rw [neg_div, neg_neg]
  congr 1
  ring


theorem sgn_of_neg {v : ℝ} (hv : v < 0) : sgn v = 1 := by simp [sgn, hv]

theorem sgn_of_pos {v : ℝ} (hv : 0 < v) : sgn v = -1 := by simp [sgn, not_lt.2 hv.le]

theorem continuous_oDrv {w : ℝ≥0 → ℝ} (hw : Continuous w) (v : ℝ) : Continuous (oDrv v w) :=
  continuous_const.mul hw

theorem oDrv_zero {w : ℝ≥0 → ℝ} (hw0 : w 0 = 0) (v : ℝ) : oDrv v w 0 = 0 := by simp [oDrv, hw0]

/-- The oriented hulls: the original ones for `v < 0`, their reflections for `v > 0`. -/
theorem fwdHull_oDrv_of_pos {w : ℝ≥0 → ℝ} {v : ℝ} (hv : 0 < v) (t : ℝ) :
    fwdHull (fun s : ℝ => oDrv v w s.toNNReal) t = LP.reflectC '' fwdHull (fun s : ℝ => w s.toNNReal) t := by
  rw [← LP.fwdHull_neg]
  congr 1
  funext s
  simp [oDrv, sgn_of_pos hv]

theorem fwdHull_oDrv_of_neg {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v < 0) (t : ℝ) :
    fwdHull (fun s : ℝ => oDrv v w s.toNNReal) t = fwdHull (fun s : ℝ => w s.toNNReal) t := by
  congr 1
  funext s
  simp [oDrv, sgn_of_neg hv]

/-- **The pole avoids the oriented closed hull** when it avoids the original one. -/
theorem scl_notMem_closure {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v ≠ 0) {t : ℝ}
    (hp : (pole v : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t)) :
    (scl v : ℂ) ∉ closure (fwdHull (fun s : ℝ => oDrv v w s.toNNReal) t) := by
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · rwa [fwdHull_oDrv_of_neg hneg, ← pole_eq_scl_of_neg hneg]
  · rw [fwdHull_oDrv_of_pos hpos, LP.closure_image_reflectC]
    rintro ⟨y, hy, hye⟩
    apply hp
    have : y = LP.reflectC (scl v : ℂ) := by rw [← hye, LP.reflectC_reflectC]
    rw [this, LP.reflectC_ofReal, ← pole_eq_neg_scl_of_pos hpos] at hy
    exact hy

/-- **Zhan's pull-back data for the target change to `v`** before a time `T₀` at which the pole avoids the closed
hulls. -/
theorem pullData_rel {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {v : ℝ} (hv : v ≠ 0) {T₀ : ℝ≥0∞}
    (hsep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (pole v : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t)) :
    PullData (oDrv v w) (tgt v w) (scl v) T₀ :=
  pullData_of_notMem (continuous_oDrv hw v) (oDrv_zero hw0 v) (scl_pos hv) fun t ht =>
    scl_notMem_closure hv (hsep t ht)

/-- **The hull identity of the relative driver** before `T₀`: `K^{rel}_{relClk(t)} = mob v (K_t)`. -/
theorem fwdHull_relDrv_eq {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v ≠ 0) {T₀ : ℝ≥0∞}
    (hd : PullData (oDrv v w) (tgt v w) (scl v) T₀) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T₀) :
    fwdHull (fun s : ℝ => relDrv v w s.toNNReal) (relClk v w t) =
      BR4aPath.mob v '' fwdHull (fun s : ℝ => w s.toNNReal) t := by
  have h := fwdHull_sclDrv_eq hd ht
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · have he : (fun s : ℝ => relDrv v w s.toNNReal) = fun s : ℝ => sclDrv (scl v) (oDrv v w) (tgt v w) s.toNNReal := by
      funext s; simp [relDrv, sgn_of_neg hneg]
    rw [he, relClk, h, fwdHull_oDrv_of_neg hneg]
    exact image_congr fun z _ => (mob_eq_of_neg hneg z).symm
  · have he : (fun s : ℝ => relDrv v w s.toNNReal) = -fun s : ℝ => sclDrv (scl v) (oDrv v w) (tgt v w) s.toNNReal := by
      funext s; simp [relDrv, sgn_of_pos hpos]
    rw [he, LP.fwdHull_neg, relClk, h, fwdHull_oDrv_of_pos hpos, image_image, image_image]
    exact image_congr fun z _ => (mob_eq_of_pos hpos z).symm

/-- The relative driver agrees on `[0, relClk S]` with a continuous driver. -/
theorem exists_continuous_relDrv {w : ℝ≥0 → ℝ} {v : ℝ} {T₀ : ℝ≥0∞}
    (hd : PullData (oDrv v w) (tgt v w) (scl v) T₀) {S : ℝ≥0} (hST : (S : ℝ≥0∞) < T₀) :
    ∃ D : ℝ → ℝ, Continuous D ∧ ∀ r ∈ Icc (0 : ℝ) (relClk v w S), D r = relDrv v w r.toNNReal := by
  obtain ⟨D, hD, hDeq⟩ := exists_continuous_sclDrv hd hST
  exact ⟨fun r => sgn v * D r, continuous_const.mul hD, fun r hr => by simp only [relDrv, hDeq r hr]⟩

/-- **The relative clock is the half-plane capacity clock** before `T₀`. -/
theorem clock_eq_relClk {w : ℝ≥0 → ℝ} {v : ℝ} (hv : v ≠ 0) {T₀ : ℝ≥0∞}
    (hd : PullData (oDrv v w) (tgt v w) (scl v) T₀) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T₀) :
    clock v (fun s : ℝ => w s.toNNReal) t = relClk v w t := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  obtain ⟨D, hD, hDeq⟩ := exists_continuous_relDrv hd hST
  have hR := hd.isRate hST
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast htS'.le⟩
  have hlt : clk (rate (scl v) (oDrv v w) (tgt v w)) t < clk (rate (scl v) (oDrv v w) (tgt v w)) S :=
    hR.clk_lt htI ⟨S.coe_nonneg, le_rfl⟩ (by exact_mod_cast htS')
  have h0 : 0 ≤ clk (rate (scl v) (oDrv v w) (tgt v w)) t := hR.clk_nonneg htI
  have ha2 : 0 < scl v ^ 2 := by have := hd.pos; positivity
  have h0' : 0 ≤ relClk v w t := by unfold relClk; positivity
  rw [clock, ← fwdHull_relDrv_eq hv hd ht, ← fwdHull_eq_of_eqOn (W := D) h0'
    (mul_lt_mul_of_pos_left hlt ha2) hDeq, ZhanGT4.A1Ref.hcapSet_fwdHull hD h0']
  ring


/-! ### One sample: the relative driver through the first visit -/

/-- **The pole avoids the closed hulls before the first visit** of `v` (a later trace point outside the earlier trace
is not in the earlier closed hull, `GW4Reg.notMem_closure_fwdHull_of_lt`). -/
theorem exists_firstTipTime_notMem {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hγ : IsGeneratingTrace w ⊤ γ) {v : ℝ} (hv : v ≠ 0) (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤) :
    ∃ T₀ : ℝ≥0, firstTipTime infinitySourceChart w {(v : ℂ)} = T₀ ∧ 0 < T₀ ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} →
        (pole v : ℂ) ∉ closure (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨T₀, hT, hγT, hT0, hbef⟩ := exists_firstTipTime_eq hγ hw hw0 hv hvis
  refine ⟨T₀, hT, hT0, fun t ht => ?_⟩
  rw [hT, ENNReal.coe_lt_coe] at ht
  have h := Theorem14.GW4Reg.notMem_closure_fwdHull_of_lt hw hw0 hγ ht (s := T₀) (by
    rintro ⟨s, hs, hγs⟩
    exact hbef s (lt_of_le_of_lt hs.2 ht) (hγs.trans hγT))
  rwa [hγT] at h

/-- **The relative driver of one sample** (deterministic). For a continuous driver from `0` with a complete
generating trace that visits `v ≠ 0` through `∞`, and whose capacity clock `clock v` is unbounded before the first
visit `T_v`: the relative driver is continuous everywhere and starts at `0`, Zhan's new horizon is infinite, and for
`t < T_v` it generates `mob v (K_t)` at the relative time `clock v w t`, which is Zhan's scaled clock. -/
theorem relDrv_spec {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hγ : IsGeneratingTrace w ⊤ γ) {v : ℝ} (hv : v ≠ 0) (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤)
    (hclk : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => w s.toNNReal) t) :
    PullData (oDrv v w) (tgt v w) (scl v) (firstTipTime infinitySourceChart w {(v : ℂ)}) ∧
      newHorizon (scl v) (oDrv v w) (tgt v w) (firstTipTime infinitySourceChart w {(v : ℂ)}) = ⊤ ∧
      Continuous (relDrv v w) ∧ relDrv v w 0 = 0 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} →
        fwdHull (fun s : ℝ => relDrv v w s.toNNReal) (clock v (fun s : ℝ => w s.toNNReal) t) =
            BR4aPath.mob v '' fwdHull (fun s : ℝ => w s.toNNReal) t ∧
          clock v (fun s : ℝ => w s.toNNReal) t = relClk v w t := by
  obtain ⟨T₀, hT, hT0, hsep⟩ := exists_firstTipTime_notMem hw hw0 hγ hv hvis
  have hd := pullData_rel hw hw0 hv hsep
  have ha := scl_pos hv
  have ha2 : 0 < scl v ^ 2 := by positivity
  have hclkeq := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)}) =>
    clock_eq_relClk hv hd ht
  have hN : newHorizon (scl v) (oDrv v w) (tgt v w) (firstTipTime infinitySourceChart w {(v : ℂ)}) = ⊤ := by
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨t, ht, hM⟩ := hclk (scl v ^ 2 * r)
    rw [hclkeq t ht, relClk] at hM
    have hle : (r : ℝ) ≤ clk (rate (scl v) (oDrv v w) (tgt v w)) t := le_of_mul_le_mul_left hM ha2
    refine le_trans ?_ (le_iSup₂_of_le t ht le_rfl)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hle
  have hcont : Continuous (newDrv (scl v) (oDrv v w) (tgt v w)) := by
    have h := hd.continuousOn_newDrv
    rw [hN] at h
    simpa only [ENNReal.coe_lt_top, ofPred_true, continuousOn_univ] using h
  refine ⟨hd, hN, ?_, ?_, fun t ht => ?_⟩
  · exact continuous_const.mul (continuous_const.mul (hcont.comp
      (continuous_real_toNNReal.comp (NNReal.continuous_coe.div_const _))))
  · have h0 : (0 : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} := by
      rw [hT]; exact_mod_cast hT0
    simp only [relDrv, sclDrv, NNReal.coe_zero, zero_div, Real.toNNReal_zero, hd.newDrv_zero h0, mul_zero]
  · rw [hclkeq t ht]
    exact ⟨fwdHull_relDrv_eq hv hd ht, rfl⟩

end InteractingSLE.Theorem14.BR4aChain
