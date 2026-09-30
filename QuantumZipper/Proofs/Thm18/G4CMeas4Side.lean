import QuantumZipper.Proofs.Thm18.G4CMeas4Drv
import QuantumZipper.Proofs.Loewner.CoreArc1
import QuantumZipper.Proofs.Loewner.ForwardHolo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JOINT-LEN-READER, part D3: the side images, jointly in time

* `exists_isForwardSol_gt`: a forward solution on `[0,S]` extends beyond `S`
  (`CoreArc.exists_isForwardSol_beyond`, `exists_isForwardSol_small`).
* `tendsto_fwdMap_qj`: for a continuous driver, `z ∈ ℍ` and `t ≥ 0`, the forward map at the dyadic
  times `qj j t ↓ t` converges to the forward map at `t` (alive: continuity of the solution; not
  alive beyond `t`: all values are the junk `0`).
* `FR a t z`: the right limit along `qj`; jointly measurable (`measurable_FR`), equal to
  `fwdMap (wg a) t z` (`FR_eq`).
* `sideR a t`: the side-image reader; `measurable_sideR` and `sideImages_eq_sideR` on good data.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- **Forward solutions extend.** -/
theorem exists_isForwardSol_gt {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {S : ℝ}
    (hS : 0 ≤ S) {u : ℝ → ℂ} (hu : IsForwardSol W z S u) : ∃ S' > S, ∃ v, IsForwardSol W z S' v := by
  rcases hS.eq_or_lt with h0 | hpos
  · obtain ⟨T, hT, v, hv⟩ := exists_isForwardSol_small hW hz
    exact ⟨T, h0 ▸ hT, v, hv⟩
  · obtain ⟨m, hm, hmle⟩ : ∃ m > 0, ∀ s ∈ Icc (0 : ℝ) S, m ≤ ‖u s‖ := by
      obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_isMinOn
        (nonempty_Icc.2 hS) (hu.1.norm)
      exact ⟨‖u s₀‖, norm_pos_iff.2 (hu.2 s₀ hs₀).1, fun s hs => hmin hs⟩
    refine CoreArc.exists_isForwardSol_beyond hW hz hpos hm
      (fun s hs => ⟨u, isForwardSol_restrict hu hs.1 hs.2.le⟩) fun s hs => ?_
    rw [fwdMap_eq hW hz hu ⟨hs.1, hs.2.le⟩]
    exact hmle s ⟨hs.1, hs.2.le⟩

/-- The dyadic time `⌈2ʲ t⌉ / 2ʲ ≥ t`. -/
def qj (j : ℕ) (t : ℝ) : ℝ := (⌈(2 : ℝ) ^ j * t⌉₊ : ℝ) / 2 ^ j

theorem le_qj (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : t ≤ qj j t := by
  unfold qj
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Nat.le_ceil _

theorem qj_lt (j : ℕ) {t : ℝ} (ht : 0 ≤ t) : qj j t < t + 1 / 2 ^ j := by
  unfold qj
  rw [div_lt_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity), mul_comm]
  exact Nat.ceil_lt_add_one (by positivity)

theorem tendsto_qj {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun j => qj j t) atTop (𝓝 t) := by
  have h2 : Tendsto (fun j : ℕ => t + 1 / (2 : ℝ) ^ j) atTop (𝓝 t) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_add t
    simpa [one_div, inv_pow] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun j => le_qj j ht)
    fun j => (qj_lt j ht).le

/-- **Right limit of the forward map along the dyadic times.** -/
theorem tendsto_fwdMap_qj {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) {t : ℝ}
    (ht : 0 ≤ t) : Tendsto (fun j => fwdMap W (qj j t) z) atTop (𝓝 (fwdMap W t z)) := by
  by_cases hA : ∃ T' > t, ∃ u, IsForwardSol W z T' u
  · obtain ⟨T', hT', u, hu⟩ := hA
    have hev : ∀ᶠ j in atTop, qj j t ∈ Icc (0 : ℝ) T' :=
      ((tendsto_qj ht).eventually (Iio_mem_nhds hT')).mono fun j hj =>
        ⟨ht.trans (le_qj j ht), hj.le⟩
    have hc : Tendsto u (𝓝[Icc (0 : ℝ) T'] t) (𝓝 (u t)) :=
      hu.1 t ⟨ht, hT'.le⟩
    rw [fwdMap_eq hW hz hu ⟨ht, hT'.le⟩]
    refine (hc.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_qj ht, hev⟩)).congr' ?_
    filter_upwards [hev] with j hj
    exact (fwdMap_eq hW hz hu hj).symm
  · push_neg at hA
    have h0 : ∀ s, t ≤ s → fwdMap W s z = 0 := by
      intro s hs
      unfold fwdMap
      rw [dif_neg]
      rintro ⟨u, hu⟩
      rcases hs.eq_or_lt with rfl | hlt
      · obtain ⟨S', hS', v, hv⟩ := exists_isForwardSol_gt hW hz ht hu
        exact hA S' hS' v hv
      · exact hA s hlt u hu
    rw [h0 t le_rfl]
    exact tendsto_const_nhds.congr fun j => (h0 _ (le_qj j ht)).symm

/-- **The forward map at time `t`, read as a right limit along the dyadic times.** -/
def FR (a : ℕ → ℝ) (t : ℝ) (z : ℂ) : ℂ := limUnder atTop fun j => fwdMap (wg a) (qj j t) z

theorem FR_eq (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 < z.im) :
    FR a t z = fwdMap (wg a) t z :=
  (tendsto_fwdMap_qj (continuous_wg a) hz ht).limUnder_eq

theorem measurable_fwdMap_wg_apply {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : 0 < z.im) :
    Measurable fun a : ℕ → ℝ => fwdMap (wg a) s z := by
  have e : (fun a : ℕ → ℝ => fwdMap (wg a) s z) =
      (fun f => fwdMap (CharFun.Wof 1 s hs f) s z) ∘ fPath s := by
    funext a
    refine ESM.fwdMap_congr_drive_ext hs (fun r hr => ?_) z
    simp only [Function.comp, CharFun.Wof, fPath, ContinuousMap.coe_mk, Real.sqrt_one, one_mul,
      projIcc_of_mem hs hr]
  rw [e]
  exact (ESM.measurable_fwdMap_Wof 1 s hs hz).comp (measurable_fPath s)

theorem measurable_FR {z : ℂ} (hz : 0 < z.im) :
    Measurable fun q : (ℕ → ℝ) × ℝ => FR q.1 q.2 z := by
  refine (StronglyMeasurable.limUnder fun j => ?_).measurable
  have hG : Measurable fun p : (ℕ → ℝ) × ℕ =>
      fwdMap (wg p.1) ((p.2 : ℝ) / 2 ^ j) z :=
    measurable_from_prod_countable_left fun N =>
      measurable_fwdMap_wg_apply (s := (N : ℝ) / 2 ^ j) (by positivity) hz
  have hN : Measurable fun q : (ℕ → ℝ) × ℝ => (q.1, ⌈(2 : ℝ) ^ j * q.2⌉₊) :=
    measurable_fst.prodMk (Nat.measurable_ceil.comp (measurable_snd.const_mul _))
  exact (hG.comp hN).stronglyMeasurable

/-- **The side-image reader on the code.** -/
def sideR (a : ℕ → ℝ) (t : ℝ) : ℝ × ℝ :=
  (liminf (fun n : ℕ => liminf (fun m : ℕ => (FR a t (ESM.sidePtL n m)).re) atTop) atTop,
   limsup (fun n : ℕ => limsup (fun m : ℕ => (FR a t (ESM.sidePtR n m)).re) atTop) atTop)

theorem measurable_sideR : Measurable fun q : (ℕ → ℝ) × ℝ => sideR q.1 q.2 := by
  refine Measurable.prodMk ?_ ?_
  · exact Measurable.liminf fun n => Measurable.liminf fun m =>
      Complex.measurable_re.comp (measurable_FR (ESM.sidePtL_im_pos n m))
  · exact Measurable.limsup fun n => Measurable.limsup fun m =>
      Complex.measurable_re.comp (measurable_FR (ESM.sidePtR_im_pos n m))

/-- **On good data at `t ≥ 0`, the side images are read by `sideR`.** -/
theorem sideImages_eq_sideR {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t) :
    sideImages (F1.readDrv d.2) t = sideR (lcode d).2 t := by
  set a := (lcode d).2 with ha
  have hW : ∀ r ∈ Icc (0 : ℝ) t, F1.readDrv d.2 r = CharFun.Wof 1 t ht (fPath t a) r := by
    intro r hr
    simp only [CharFun.Wof, fPath, ContinuousMap.coe_mk, Real.sqrt_one, one_mul,
      projIcc_of_mem ht hr, ha, wg_lcode hp]
  rw [ESM.sideImages_congr_drive ht hW]
  rw [ESM.sideImages_Wof_eq_sideReader 1 t ht (fPath t a) fun x hx => ?_]
  · unfold ESM.sideReader sideR
    have hL : ∀ n m, fwdMap (CharFun.Wof 1 t ht (fPath t a)) t (ESM.sidePtL n m) =
        FR a t (ESM.sidePtL n m) := fun n m => by
      rw [FR_eq a ht (ESM.sidePtL_im_pos n m)]
      refine ESM.fwdMap_congr_drive_ext ht (fun r hr => ?_) _
      simp only [CharFun.Wof, fPath, ContinuousMap.coe_mk, Real.sqrt_one, one_mul,
        projIcc_of_mem ht hr]
    have hR : ∀ n m, fwdMap (CharFun.Wof 1 t ht (fPath t a)) t (ESM.sidePtR n m) =
        FR a t (ESM.sidePtR n m) := fun n m => by
      rw [FR_eq a ht (ESM.sidePtR_im_pos n m)]
      refine ESM.fwdMap_congr_drive_ext ht (fun r hr => ?_) _
      simp only [CharFun.Wof, fPath, ContinuousMap.coe_mk, Real.sqrt_one, one_mul,
        projIcc_of_mem ht hr]
    simp only [hL, hR]
  · obtain ⟨u, hu⟩ := hp.2.2 x hx t ht
    exact ⟨u, isForwardSol_congr_drive hW hu⟩

end G4Core
end Thm18Asm
end QuantumZipper
