import QuantumZipper.Proofs.Zipper.SWCoreNA2InstBase
import QuantumZipper.Proofs.Zipper.SWCoreA6Flow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A7-FAM: the Loewner flow maps as a Lipschitz 5-parameter family

The family `a7Map W T S q` (time `q 0`, real shift `q 1`, clamped) together with clamped centres
`a7Cen` and radius factors `a7Rad` satisfies `SwcNA2Unif` on any rectangle
`[x₁,x₂] × [y₁,y₂] ⊂ ℍ` (`a7_unif`), and at `q 0 = t`, `q 1 = W t` it is `fwdMapInv W t`
(`a7Map_diag`).

In uncentred coordinates `a7Map W T S q z = f_{t}(z + u)` with `f_t = RS.fwdMapInvUnc W t`
(Kemppainen's `g_t⁻¹`), so no increment of `W` appears. Time-Lipschitz bound: as in the proof of
A. Kemppainen, *Schramm–Loewner Evolution* (SpringerBriefs 2017), Lemma 6.7, pp. 110–111, in the
project form of `RS.kd_time_step`: `f̂_{t+s} = f̂_t ∘ φ` (`RS.fwdMapInv_add_shift`) with `φ` a
reverse flow of duration `s`, `‖φ(w') − w‖ ≤ 2s / Im w` (`RS.norm_revMap_sub_self_add_le`),
`Im φ(w') ≥ Im w`; then (own elementary step, replacing the Koebe chain since `s` need not be
small) the mean value inequality with a uniform bound of `‖f̂_t'‖` on a compact rectangle, from
the joint continuity `RegUnif.continuousOn_log_deriv_fwdMapInv_joint`. Class membership:
`flow_mem_areaClass` on a larger rational rectangle plus translation.
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace SWCore

open RS UnzipInvariance

/-- `max lo (min x hi)`. -/
def clampI (lo hi x : ℝ) : ℝ := max lo (min x hi)

/-- The 5-parameter flow family: `q 0` time, `q 1` real shift (stands for `W t`), `q 2, q 3`
centre, `q 4` radius factor. -/
def a7Map (W : ℝ → ℝ) (T S : ℝ) (q : Fin 5 → ℝ) (z : ℂ) : ℂ :=
  fwdMapInv W (clampI 0 T (q 0))
    (z + ((clampI (-S) S (q 1) : ℝ) : ℂ) - ((W (clampI 0 T (q 0)) : ℝ) : ℂ))

def a7Cen (x₁ x₂ y₁ y₂ : ℝ) (q : Fin 5 → ℝ) : ℂ := ⟨clampI x₁ x₂ (q 2), clampI y₁ y₂ (q 3)⟩

def a7Rad (q : Fin 5 → ℝ) : ℝ := clampI 1 2 (q 4)

theorem clampI_mem {lo hi : ℝ} (h : lo ≤ hi) (x : ℝ) : clampI lo hi x ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

theorem clampI_eq {lo hi x : ℝ} (hx : x ∈ Icc lo hi) : clampI lo hi x = x := by
  unfold clampI; rw [min_eq_left hx.2, max_eq_right hx.1]

theorem clampI_lip (lo hi x y : ℝ) : |clampI lo hi x - clampI lo hi y| ≤ |x - y| := by
  unfold clampI
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero]
  refine max_le (abs_nonneg _) ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
  rw [sub_self, abs_zero]
  exact max_le le_rfl (abs_nonneg _)

theorem a7_coord_le (q q' : Fin 5 → ℝ) (i : Fin 5) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

theorem a7Map_eq_unc (W : ℝ → ℝ) (T S : ℝ) (q : Fin 5 → ℝ) (z : ℂ) :
    a7Map W T S q z = fwdMapInvUnc W (clampI 0 T (q 0)) (z + ((clampI (-S) S (q 1) : ℝ) : ℂ)) :=
  rfl

theorem a7Map_diag {W : ℝ → ℝ} {T S t : ℝ} {q : Fin 5 → ℝ} (ht : t ∈ Icc 0 T)
    (hS : |W t| ≤ S) (h0 : q 0 = t) (h1 : q 1 = W t) : a7Map W T S q = fwdMapInv W t := by
  funext z
  unfold a7Map
  rw [h0, h1, clampI_eq ht, clampI_eq (abs_le.1 hS), add_sub_cancel_right]

/-! ## The flow step and the uniform Lipschitz bound -/

/-- Flow step (as in the proof of `RS.kd_time_step`): `f_{t+s}(ζ) = f̂_t(p)` with
`‖p − (ζ − W_t)‖ ≤ 2s / Im ζ` and `Im p ≥ Im ζ`. -/
theorem a7_flow_step {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) {ζ : ℂ} (hζ : 0 < ζ.im) :
    ∃ p : ℂ, fwdMapInvUnc W (t + s) ζ = fwdMapInv W t p ∧
      ‖p - (ζ - ((W t : ℝ) : ℂ))‖ ≤ 2 * s / ζ.im ∧ ζ.im ≤ p.im := by
  set w' : ℂ := ζ - ((W (t + s) : ℝ) : ℂ) with hw'
  have hw'im : w'.im = ζ.im := by simp [hw']
  have hw'H : w' ∈ H := show 0 < w'.im by rw [hw'im]; exact hζ
  set Ws := shiftDrive W t with hWs
  have hWsc : Continuous Ws := continuous_shiftDrive hW t
  have hWs0 : Ws 0 = 0 := shiftDrive_zero W t
  set V : ℝ → ℝ := fun r => Ws (s - r) - Ws s with hV
  have hVc : Continuous V := by rw [hV]; fun_prop
  set φ := fwdMapInv Ws s with hφ
  have hφw' : φ w' = revMap V s w' := fwdMapInv_eq_revMap_timeRev Ws hWsc hWs0 hs hw'H
  have hVs : V s = -(W (t + s) - W t) := by simp [hV, hWs, shiftDrive]
  refine ⟨φ w', fwdMapInv_add_shift hW hW0 ht hs hw'H, ?_, ?_⟩
  · have h := norm_revMap_sub_self_add_le hVc hs hw'H
    rw [hVs, hw'im, ← hφw'] at h
    have e : φ w' - w' + ((-(W (t + s) - W t) : ℝ) : ℂ) = φ w' - (ζ - ((W t : ℝ) : ℂ)) := by
      rw [hw']; push_cast; ring
    rwa [e] at h
  · rw [hφw', ← hw'im]; exact im_le_im_revMap V hVc w' hw'H hs

/-- Uniform Lipschitz bound of `f̂_t`, `t ∈ [0,T]`, on a rectangle in `ℍ` (mean value inequality
with the joint continuity of `log ‖f̂_t'‖`). -/
theorem a7_deriv_lip {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ)
    {X₁ X₂ Y₁ Y₂ : ℝ} (hY : 0 < Y₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ rectC X₁ X₂ Y₁ Y₂, ∀ b ∈ rectC X₁ X₂ Y₁ Y₂,
      ‖fwdMapInv W t a - fwdMapInv W t b‖ ≤ B * ‖a - b‖ := by
  have hKH : rectC X₁ X₂ Y₁ Y₂ ⊆ H := fun z hz => show 0 < z.im from lt_of_lt_of_le hY hz.2.1
  have hg := (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).mono
    (prod_mono (subset_refl (Icc (0 : ℝ) T)) hKH)
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_Icc.prod (swA6_isCompact_rectC X₁ X₂ Y₁ Y₂)).exists_bound_of_continuousOn hg
  refine ⟨Real.exp B₀, (Real.exp_pos _).le, fun t ht a ha b hb => ?_⟩
  have hd : ∀ z ∈ rectC X₁ X₂ Y₁ Y₂, ‖deriv (fwdMapInv W t) z‖ ≤ Real.exp B₀ := by
    intro z hz
    have hb := hB₀ (t, z) ⟨ht, hz⟩
    rw [Real.norm_eq_abs, abs_le] at hb
    rcases (norm_nonneg (deriv (fwdMapInv W t) z)).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · calc ‖deriv (fwdMapInv W t) z‖ = Real.exp (Real.log ‖deriv (fwdMapInv W t) z‖) :=
            (Real.exp_log hpos).symm
        _ ≤ Real.exp B₀ := Real.exp_le_exp.2 hb.2
  exact (swcVA_convex_rectC X₁ X₂ Y₁ Y₂).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => differentiableAt_fwdMapInv hW hW0 ht.1 (hKH hz)) hd hb ha

theorem a7_mem_big {W : ℝ → ℝ} {T S X₁ X₂ Y₁ Y₂ : ℝ} (hT : 0 ≤ T) (hY : 0 < Y₁)
    (hS : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ S) {ζ : ℂ} (hζ : ζ ∈ rectC X₁ X₂ Y₁ Y₂) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ζ - ((W t : ℝ) : ℂ) ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁) := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hζ
  have hWt := abs_le.1 (hS t ht)
  have hT' : 0 ≤ 2 * T / Y₁ := by positivity
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith

/-- Time-Lipschitz bound of the uncentred maps, `t ≤ t'`. -/
theorem a7_time_lip_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T S X₁ X₂ Y₁ Y₂ B : ℝ}
    (hT : 0 ≤ T) (hS : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ S) (hY : 0 < Y₁) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ a ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁),
      ∀ b ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁),
      ‖fwdMapInv W t a - fwdMapInv W t b‖ ≤ B * ‖a - b‖)
    {ζ : ℂ} (hζ : ζ ∈ rectC X₁ X₂ Y₁ Y₂) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ht' : t' ∈ Icc (0 : ℝ) T) (htt : t ≤ t') :
    ‖fwdMapInvUnc W t' ζ - fwdMapInvUnc W t ζ‖ ≤ B * (2 / Y₁) * (t' - t) := by
  have hmb := a7_mem_big hT hY hS hζ ht
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hζ
  have hζim : 0 < ζ.im := lt_of_lt_of_le hY hi1
  obtain ⟨p, hp, hpd, hpim⟩ := a7_flow_step hW hW0 ht.1 (sub_nonneg.2 htt) hζim
  have e : t + (t' - t) = t' := by ring
  rw [e] at hp
  have hq : 2 * (t' - t) / ζ.im ≤ 2 * (t' - t) / Y₁ :=
    div_le_div_of_nonneg_left (by linarith) hY hi1
  have hq2 : 2 * (t' - t) / Y₁ ≤ 2 * T / Y₁ :=
    div_le_div_of_nonneg_right (by linarith [ht.1, ht'.2]) hY.le
  have hWt := abs_le.1 (hS t ht)
  have hre := Complex.abs_re_le_norm (p - (ζ - ((W t : ℝ) : ℂ)))
  have him := Complex.abs_im_le_norm (p - (ζ - ((W t : ℝ) : ℂ)))
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero] at hre him
  rw [abs_le] at hre him
  have hma : p ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  calc ‖fwdMapInvUnc W t' ζ - fwdMapInvUnc W t ζ‖
        = ‖fwdMapInv W t p - fwdMapInv W t (ζ - ((W t : ℝ) : ℂ))‖ := by rw [hp]; rfl
    _ ≤ B * ‖p - (ζ - ((W t : ℝ) : ℂ))‖ := hB t ht p hma _ hmb
    _ ≤ B * (2 * (t' - t) / Y₁) := mul_le_mul_of_nonneg_left (hpd.trans hq) hB0
    _ = B * (2 / Y₁) * (t' - t) := by ring

theorem a7_time_lip {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T S X₁ X₂ Y₁ Y₂ B : ℝ}
    (hT : 0 ≤ T) (hS : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ S) (hY : 0 < Y₁) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ a ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁),
      ∀ b ∈ rectC (X₁ - S - 2 * T / Y₁) (X₂ + S + 2 * T / Y₁) Y₁ (Y₂ + 2 * T / Y₁),
      ‖fwdMapInv W t a - fwdMapInv W t b‖ ≤ B * ‖a - b‖)
    {ζ : ℂ} (hζ : ζ ∈ rectC X₁ X₂ Y₁ Y₂) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ht' : t' ∈ Icc (0 : ℝ) T) :
    ‖fwdMapInvUnc W t ζ - fwdMapInvUnc W t' ζ‖ ≤ B * (2 / Y₁) * |t - t'| := by
  rcases le_total t t' with h | h
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
    exact a7_time_lip_le hW hW0 hT hS hY hB0 hB hζ ht ht' h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact a7_time_lip_le hW hW0 hT hS hY hB0 hB hζ ht' ht h

/-! ## Class membership by translation -/

theorem a7_areaClass_translate {f : ℂ → ℂ} {a b c d ρ₀ M m x₁ x₂ y₁ y₂ ρ κ : ℝ}
    (hf : f ∈ AreaClass a b c d ρ₀ M m) (hρ : ρ ≤ ρ₀)
    (hK : ∀ z ∈ rectC x₁ x₂ y₁ y₂, z + (κ : ℂ) ∈ rectC a b c d) :
    (fun z => f (z + (κ : ℂ))) ∈ AreaClass x₁ x₂ y₁ y₂ ρ M m := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hT : ∀ w ∈ thickening ρ (rectC x₁ x₂ y₁ y₂), w + (κ : ℂ) ∈ thickening ρ₀ (rectC a b c d) := by
    intro w hw
    obtain ⟨z, hz, hdz⟩ := mem_thickening_iff.1 hw
    exact mem_thickening_iff.2 ⟨z + κ, hK z hz, by rw [dist_add_right]; linarith⟩
  refine ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, fun w hw => ⟨(h3 _ (hT w hw)).1, hρ.trans (h3 _ (hT w hw)).2⟩,
    fun z hz => ?_⟩
  · exact ((h1.differentiableAt (isOpen_thickening.mem_nhds (hT w hw))).comp w
      (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact add_right_cancel (h2 (hT w₁ hw₁) (hT w₂ hw₂) h)
  · rw [deriv_comp_add_const]; exact h4 _ (hK z hz)

theorem a7_mem_mid {x₁ x₂ y₁ y₂ ρ S v : ℝ} {w : ℂ} (hw : w ∈ thickening ρ (rectC x₁ x₂ y₁ y₂))
    (hρ1 : ρ ≤ 1) (hρy : ρ ≤ y₁ / 2) (hv : v ∈ Icc (-S) S) :
    w + (v : ℂ) ∈ rectC (x₁ - 1 - S) (x₂ + 1 + S) (y₁ / 2) (y₂ + 1) := by
  obtain ⟨z, ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩, hdz⟩ := mem_thickening_iff.1 hw
  have h1 := Complex.abs_re_le_norm (w - z)
  have h2 := Complex.abs_im_le_norm (w - z)
  rw [← dist_eq_norm, Complex.sub_re, abs_le] at h1
  rw [← dist_eq_norm, Complex.sub_im, abs_le] at h2
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith

/-! ## The uniform family -/

theorem a7_unif {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy0 : 0 < y₁) (hy : y₁ ≤ y₂) :
    ∃ S ρ M m H : ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, |W t| ≤ S) ∧
      SwcNA2Unif (a7Map W T S) (a7Cen x₁ x₂ y₁ y₂) a7Rad x₁ x₂ y₁ y₂ ρ M m H := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW.continuousOn (s := Icc (0 : ℝ) T))
  set S := max C 0 with hSdef
  have hS : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ S := fun t ht =>
    (show |W t| ≤ C by simpa [Real.norm_eq_abs] using hC t ht).trans (le_max_left _ _)
  have hS0 : 0 ≤ S := le_max_right _ _
  obtain ⟨a, ha⟩ := exists_rat_lt (x₁ - 2 * S - 1)
  obtain ⟨b, hb⟩ := exists_rat_gt (x₂ + 2 * S + 1)
  obtain ⟨c, hc0, hc⟩ := exists_rat_btwn hy0
  obtain ⟨d, hd⟩ := exists_rat_gt y₂
  obtain ⟨ρ₀, M, m, hρ₀, hm, hcls⟩ :=
    flow_mem_areaClass hW hW0 hT (a := a) (b := b) (c := c) (d := d) hc0
  have hY : 0 < y₁ / 2 := by positivity
  obtain ⟨B, hB0, hB⟩ := a7_deriv_lip hW hW0 T (X₁ := x₁ - 1 - S - S - 2 * T / (y₁ / 2))
    (X₂ := x₂ + 1 + S + S + 2 * T / (y₁ / 2)) (Y₂ := y₂ + 1 + 2 * T / (y₁ / 2)) hY
  set ρ := min (min (ρ₀ : ℝ) 1) (y₁ / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₀ one_pos) hY
  have hρρ₀ : ρ ≤ ρ₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hρy : ρ ≤ y₁ / 2 := min_le_right _ _
  have hB2 : 0 ≤ B * (2 / (y₁ / 2)) := by positivity
  have hSS : -S ≤ S := by linarith
  refine ⟨S, ρ, M, m, 2 + B + B * (2 / (y₁ / 2)), hS, ⟨hy0, hρ0, hm, by positivity, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · intro q
    have ht := clampI_mem hT (q 0)
    have hu := clampI_mem hSS (q 1)
    have hWt := abs_le.1 (hS _ ht)
    have e : a7Map W T S q = fun z => fwdMapInv W (clampI 0 T (q 0))
        (z + ((clampI (-S) S (q 1) - W (clampI 0 T (q 0)) : ℝ) : ℂ)) := by
      funext z; unfold a7Map; congr 1; push_cast; ring
    rw [e]
    refine a7_areaClass_translate (hcls _ ht) hρρ₀ fun z hz => ?_
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    obtain ⟨hu1, hu2⟩ := hu
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  · intro q; exact ⟨clampI_mem hx _, clampI_mem hy _⟩
  · intro q; exact (clampI_mem (by norm_num : (1 : ℝ) ≤ 2) _).1
  · intro q; exact (clampI_mem (by norm_num : (1 : ℝ) ≤ 2) _).2
  · intro q q'
    have h2 := (clampI_lip x₁ x₂ (q 2) (q' 2)).trans (a7_coord_le q q' 2)
    have h3 := (clampI_lip y₁ y₂ (q 3) (q' 3)).trans (a7_coord_le q q' 3)
    have hn := norm_nonneg (q - q')
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [a7Cen, Complex.sub_re, Complex.sub_im]
    nlinarith
  · intro q q'
    have h4 := (clampI_lip 1 2 (q 4) (q' 4)).trans (a7_coord_le q q' 4)
    have hn := norm_nonneg (q - q')
    simp only [a7Rad]
    nlinarith
  · intro q q' w hw
    have ht := clampI_mem hT (q 0)
    have ht' := clampI_mem hT (q' 0)
    have hu := clampI_mem hSS (q 1)
    have hu' := clampI_mem hSS (q' 1)
    have hζ := a7_mem_mid hw hρ1 hρy hu
    have hζ' := a7_mem_mid hw hρ1 hρy hu'
    have h0 := (clampI_lip 0 T (q 0) (q' 0)).trans (a7_coord_le q q' 0)
    have h1 := (clampI_lip (-S) S (q 1) (q' 1)).trans (a7_coord_le q q' 1)
    have hn := norm_nonneg (q - q')
    rw [a7Map_eq_unc, a7Map_eq_unc]
    set t := clampI 0 T (q 0)
    set t' := clampI 0 T (q' 0)
    set u := clampI (-S) S (q 1)
    set u' := clampI (-S) S (q' 1)
    have hsh : ‖fwdMapInvUnc W t (w + (u : ℂ)) - fwdMapInvUnc W t (w + (u' : ℂ))‖ ≤
        B * |u - u'| := by
      have := hB t ht _ (a7_mem_big hT hY hS hζ ht) _ (a7_mem_big hT hY hS hζ' ht)
      have e : w + (u : ℂ) - ((W t : ℝ) : ℂ) - (w + (u' : ℂ) - ((W t : ℝ) : ℂ)) =
          ((u - u' : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have htm := a7_time_lip hW hW0 hT hS hY hB0 hB hζ' ht ht'
    calc ‖fwdMapInvUnc W t (w + (u : ℂ)) - fwdMapInvUnc W t' (w + (u' : ℂ))‖
        ≤ ‖fwdMapInvUnc W t (w + (u : ℂ)) - fwdMapInvUnc W t (w + (u' : ℂ))‖ +
          ‖fwdMapInvUnc W t (w + (u' : ℂ)) - fwdMapInvUnc W t' (w + (u' : ℂ))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ B * ‖q - q'‖ + B * (2 / (y₁ / 2)) * ‖q - q'‖ :=
          add_le_add (hsh.trans (mul_le_mul_of_nonneg_left h1 hB0))
            (htm.trans (mul_le_mul_of_nonneg_left h0 hB2))
      _ ≤ (2 + B + B * (2 / (y₁ / 2))) * ‖q - q'‖ := by nlinarith

end SWCore
end QuantumZipper
