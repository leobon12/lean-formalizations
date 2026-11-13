import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.RS.TraceRadial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Hull

/-!
# The reverse flow of the SLE₈ note (§2.2: (2.5)–(2.7) and Lemma 2.2)

SLE₈ note `source/sle8-continuity.pdf`, §2.2, pp. 3–4 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-2.2`, `lem-2.2-proof`).

Fix a continuous driver `W` with `W 0 = 0` and a terminal time `T`. The note's reverse flow (2.5) is
driven by `V_s = W_{T-s} - W_T` (`revDriver W T`):
`∂_s h_s(z) = -2/(h_s(z) - V_s)`, `h_0(z) = z`, and (2.6) writes
`Z_s(z) = h_s(z) - V_s = X_s(z) + i Y_s(z)`, `Φ_s(z) = |h_s'(z)|`.

## Carriers

QuantumZipper's centred reverse flow `revMap V s z` solves `u_s = z - V_s - ∫_0^s 2/u_r dr`, so it *is*
the note's `Z_s(z)` (no derivative of `V` is needed). The uncentred flow `h_s(z)` is `revFlow V s z :=
revMap V s z + V s`; `hasDerivWithinAt_revFlow` and `revFlow_zero` show that it solves (2.5).
Since `h_s` and `Z_s` differ by a constant, `Φ_s(z) = ‖deriv (revMap V s) z‖ = ‖deriv (revFlow V s) z‖`
(`deriv_revFlow`). The centred inverse maps `F_t` of (1.2) are `QuantumZipper.fwdMapInv W t`.

## Main results

* `revFlow_bounds` — **Lemma 2.2**: `y ≤ Y_s ≤ √(y² + 4s)`, `Φ_s ≤ Y_s / y`, and `Re h_s(z)` lies in
  the convex hull of `{x} ∪ {V_v : 0 ≤ v ≤ s}`;
* `abs_re_revMap_mul_I_le_two_mul_sSup` — **(2.9)**: `|X_s(iy)| ≤ 2 sup_{0 ≤ v ≤ s} |V_v|`;
* `fwdMapInv_eq_fwdMapInv_revMap`, `norm_deriv_fwdMapInv_eq_mul` — **(2.7)**:
  `F_T = F_{T-s} ∘ Z_s` and `|F_T'(z)| = Φ_s(z) |F'_{T-s}(Z_s(z))|`, with the case `s = T`
  (`fwdMapInv_eq_revMap_revDriver`, `norm_deriv_fwdMapInv_eq_norm_deriv_revMap`) and the identity
  `Z_s(z) = g_{T-s}(F_T(z)) - W_{T-s}` (`revMap_revDriver_eq_fwdMap_fwdMapInv`).

The height and derivative bounds are QuantumZipper's `im_le_im_revMap`, `TwoPoint.im_revMap_sq_le`
and `TwoPoint.norm_deriv_revMap_le`; the convex-hull bound is proved here by the scalar comparison
principle (`le_of_hasDerivWithinAt_neg_of_lt`, from Mathlib's
`image_le_of_deriv_right_lt_deriv_boundary'`).
-/

noncomputable section

open Set Filter Complex
open scoped Topology

namespace InteractingSLE.SLE8

open QuantumZipper

/-! ## The reversed driver and the uncentred reverse flow -/

/-- The time-reversed driver of the SLE₈ note's (2.5): `V_s = W_{T-s} - W_T`. -/
def revDriver (W : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := fun s => W (T - s) - W T

@[simp] theorem revDriver_apply (W : ℝ → ℝ) (T s : ℝ) : revDriver W T s = W (T - s) - W T := rfl

theorem revDriver_zero (W : ℝ → ℝ) (T : ℝ) : revDriver W T 0 = 0 := by simp

theorem continuous_revDriver {W : ℝ → ℝ} (hW : Continuous W) (T : ℝ) :
    Continuous (revDriver W T) := by
  unfold revDriver; fun_prop

/-- The uncentred reverse Loewner flow `h_s(z)` of the SLE₈ note's (2.5), driven by `V`:
`h_s(z) = Z_s(z) + V_s`, where `Z_s = revMap V s` is QuantumZipper's centred reverse flow. -/
def revFlow (V : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ := revMap V s z + V s

theorem revFlow_def (V : ℝ → ℝ) (s : ℝ) (z : ℂ) : revFlow V s z = revMap V s z + V s := rfl

/-- `Z_s(z) = h_s(z) - V_s` (2.6). -/
theorem revMap_eq_revFlow_sub (V : ℝ → ℝ) (s : ℝ) (z : ℂ) : revMap V s z = revFlow V s z - V s := by
  rw [revFlow_def]; ring

/-- The value of a reverse-flow solution at time `0`. -/
theorem revMap_zero {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) :
    revMap V 0 z = z - V 0 := by
  obtain ⟨u, hu⟩ := exists_isReverseSol V hV z hz 0 le_rfl
  rw [revMap_eq V hV z le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2]
  simp

/-- The initial condition `h_0(z) = z` of (2.5). -/
theorem revFlow_zero {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) : revFlow V 0 z = z := by
  rw [revFlow_def, revMap_zero hV hz]; ring

/-- The differential equation `∂_s h_s(z) = -2/(h_s(z) - V_s)` of (2.5), on every `[0, S]`. -/
theorem hasDerivWithinAt_revFlow {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {S s : ℝ}
    (hS : 0 ≤ S) (hs : s ∈ Icc 0 S) :
    HasDerivWithinAt (fun r => revFlow V r z) (-2 / (revFlow V s z - V s)) (Icc 0 S) s := by
  obtain ⟨u, hu⟩ := exists_isReverseSol V hV z hz S hS
  have hval : ∀ r ∈ Icc 0 S, revMap V r z = u r := fun r hr => revMap_eq V hV z hr.1 hr.2 hu
  have h := isReverseSol_hasDerivWithinAt V z S hu hs
  rw [← revMap_eq_revFlow_sub, hval s hs]
  exact h.congr_of_mem (fun r hr => by rw [revFlow_def, hval r hr]) hs

/-- `Φ_s(z) = |h_s'(z)| = |Z_s'(z)|`: `h_s` and `Z_s` differ by the constant `V_s`. -/
theorem deriv_revFlow (V : ℝ → ℝ) (s : ℝ) (z : ℂ) :
    deriv (revFlow V s) z = deriv (revMap V s) z :=
  deriv_add_const (f := revMap V s) (V s)

theorem im_revFlow (V : ℝ → ℝ) (s : ℝ) (z : ℂ) : (revFlow V s z).im = (revMap V s z).im := by
  simp [revFlow_def]

theorem re_revFlow (V : ℝ → ℝ) (s : ℝ) (z : ℂ) : (revFlow V s z).re = (revMap V s z).re + V s := by
  simp [revFlow_def]


/-! ## The scalar comparison principle -/

/-- **Scalar comparison principle.** A function continuous on `[0, S]`, with right derivatives on
`[0, S)`, that starts at most `m` and is strictly decreasing wherever it exceeds `m`, stays at most `m`
on `[0, S]`. -/
theorem le_of_hasDerivWithinAt_neg_of_lt {f f' : ℝ → ℝ} {S m : ℝ}
    (hf : ContinuousOn f (Icc 0 S)) (hf' : ∀ r ∈ Ico 0 S, HasDerivWithinAt f (f' r) (Ici r) r)
    (h0 : f 0 ≤ m) (hneg : ∀ r ∈ Ico 0 S, m < f r → f' r < 0) :
    ∀ r ∈ Icc 0 S, f r ≤ m := by
  intro r hr
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact image_le_of_deriv_right_lt_deriv_boundary' hf hf' (B := fun _ => m + ε) (B' := fun _ => 0)
    (by linarith) continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hfx => hneg x hx (by rw [hfx]; linarith)) hr

/-! ## Lemma 2.2 -/

/-- `Re(-2/u) = -2 Re u / |u|²`. -/
theorem re_neg_two_div (u : ℂ) : (-2 / u).re = -2 * u.re / normSq u := by
  rw [Complex.div_re]; simp

/-- **Lemma 2.2, the real part.** `Re h_s(z)` belongs to the convex hull of
`{Re z} ∪ {V_v : 0 ≤ v ≤ s}`: the real part of `h_s` moves toward `V_s`. -/
theorem re_revFlow_mem_convexHull {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ}
    (hs : 0 ≤ s) : (revFlow V s z).re ∈ convexHull ℝ (insert z.re (V '' Icc 0 s)) := by
  set K := insert z.re (V '' Icc 0 s)
  have hKc : IsCompact K := (isCompact_Icc.image hV).insert z.re
  have hKne : K.Nonempty := ⟨z.re, mem_insert _ _⟩
  have hVK : ∀ r ∈ Icc 0 s, V r ∈ K := fun r hr => mem_insert_of_mem _ (mem_image_of_mem V hr)
  obtain ⟨u, hu⟩ := exists_isReverseSol V hV z hz s hs
  have hval : ∀ r ∈ Icc 0 s, revMap V r z = u r := fun r hr => revMap_eq V hV z hr.1 hr.2 hu
  set f : ℝ → ℝ := fun r => (u r).re + V r with hfdef
  have hfs : (revFlow V s z).re = f s := by
    rw [re_revFlow, hval s ⟨hs, le_rfl⟩]
  have hf0 : f 0 = z.re := by
    have h := (hu.2 0 ⟨le_rfl, hs⟩).2
    simp only [hfdef, h, intervalIntegral.integral_same, sub_zero, sub_re, ofReal_re]
    ring
  have hfc : ContinuousOn f (Icc 0 s) :=
    (Complex.continuous_re.comp_continuousOn hu.1).add hV.continuousOn
  have hderiv : ∀ r ∈ Ico 0 s, HasDerivWithinAt f ((-2 / u r).re) (Ici r) r := by
    intro r hr
    have h1 := isReverseSol_hasDerivWithinAt V z s hu (Ico_subset_Icc_self hr)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt r h1
    have e : (⇑Complex.reCLM ∘ fun s => u s + (V s : ℂ)) = f := by
      funext x; simp [hfdef]
    have h3 : HasDerivWithinAt f ((-2 / u r).re) (Icc 0 s) r := by
      rw [e, Complex.reCLM_apply] at h2; exact h2
    exact h3.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hr)
  have hnsq : ∀ r ∈ Ico 0 s, 0 < normSq (u r) := by
    intro r hr
    refine normSq_pos.2 fun h0 => ?_
    have := (hu.2 r (Ico_subset_Icc_self hr)).1
    rw [h0] at this
    simp at this
  -- the upper bound `f ≤ sup K`
  have hup : f s ≤ sSup K := by
    refine le_of_hasDerivWithinAt_neg_of_lt hfc hderiv ?_ (fun r hr hgt => ?_) s ⟨hs, le_rfl⟩
    · rw [hf0]; exact le_csSup hKc.bddAbove (mem_insert _ _)
    · have hVr : V r ≤ sSup K := le_csSup hKc.bddAbove (hVK r (Ico_subset_Icc_self hr))
      have hre : 0 < (u r).re := by
        have : f r = (u r).re + V r := rfl
        linarith
      rw [re_neg_two_div]
      exact div_neg_of_neg_of_pos (by linarith) (hnsq r hr)
  -- the lower bound `inf K ≤ f`, by the same principle for `-f`
  have hlo : sInf K ≤ f s := by
    have h := le_of_hasDerivWithinAt_neg_of_lt (f := fun r => -f r) (f' := fun r => -(-2 / u r).re)
      (m := -sInf K) hfc.neg (fun r hr => (hderiv r hr).neg) ?_ (fun r hr hgt => ?_) s ⟨hs, le_rfl⟩
    · linarith
    · show -f 0 ≤ -sInf K
      rw [hf0, neg_le_neg_iff]; exact csInf_le hKc.bddBelow (mem_insert _ _)
    · have hVr : sInf K ≤ V r := csInf_le hKc.bddBelow (hVK r (Ico_subset_Icc_self hr))
      have hre : (u r).re < 0 := by
        have : f r = (u r).re + V r := rfl
        linarith
      rw [re_neg_two_div, neg_neg_iff_pos]
      exact div_pos (by linarith) (hnsq r hr)
  rw [hfs]
  refine segment_subset_convexHull (hKc.sInf_mem hKne) (hKc.sSup_mem hKne) ?_
  rw [segment_eq_Icc (csInf_le_csSup hKne hKc.bddBelow hKc.bddAbove)]
  exact ⟨hlo, hup⟩

/-- **Lemma 2.2, (2.8): the height.** `y ≤ Y_s(z) ≤ √(y² + 4s)`. -/
theorem im_revMap_mem_Icc {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ}
    (hs : 0 ≤ s) : (revMap V s z).im ∈ Icc z.im (Real.sqrt (z.im ^ 2 + 4 * s)) :=
  ⟨im_le_im_revMap V hV z hz hs, Real.le_sqrt_of_sq_le (TwoPoint.im_revMap_sq_le hV hz hs)⟩

/-- **Lemma 2.2, (2.8): the derivative.** `Φ_s(z) ≤ Y_s(z)/y`. -/
theorem norm_deriv_revFlow_le {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ}
    (hs : 0 ≤ s) : ‖deriv (revFlow V s) z‖ ≤ (revMap V s z).im / z.im := by
  rw [deriv_revFlow]; exact TwoPoint.norm_deriv_revMap_le hV hz hs

/-- **Lemma 2.2** (SLE₈ note, p. 3), for the reverse flow (2.5) driven by a continuous `V`, with
initial point `z = x + iy ∈ ℍ` and time `s ≥ 0`: `y ≤ Y_s(z) ≤ √(y² + 4s)`, `Φ_s(z) ≤ Y_s(z)/y`, and
`Re h_s(z)` belongs to the convex hull of `{x} ∪ {V_v : 0 ≤ v ≤ s}`. Here `Y_s(z) = Im Z_s(z)`,
`Z_s = revMap V s`, `h_s = revFlow V s`, `Φ_s(z) = ‖deriv (revFlow V s) z‖`. -/
theorem revFlow_bounds {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ} (hs : 0 ≤ s) :
    z.im ≤ (revMap V s z).im ∧ (revMap V s z).im ≤ Real.sqrt (z.im ^ 2 + 4 * s) ∧
      ‖deriv (revFlow V s) z‖ ≤ (revMap V s z).im / z.im ∧
      (revFlow V s z).re ∈ convexHull ℝ (insert z.re (V '' Icc 0 s)) :=
  ⟨(im_revMap_mem_Icc hV hz hs).1, (im_revMap_mem_Icc hV hz hs).2, norm_deriv_revFlow_le hV hz hs,
    re_revFlow_mem_convexHull hV hz hs⟩

/-- **Lemma 2.2 for the note's driver** `V = revDriver W T` and `s ∈ [0, T]`, exactly as stated. -/
theorem revFlow_revDriver_bounds {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} {z : ℂ} (hz : z ∈ H)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    z.im ≤ (revMap (revDriver W T) s z).im ∧
      (revMap (revDriver W T) s z).im ≤ Real.sqrt (z.im ^ 2 + 4 * s) ∧
      ‖deriv (revFlow (revDriver W T) s) z‖ ≤ (revMap (revDriver W T) s z).im / z.im ∧
      (revFlow (revDriver W T) s z).re ∈
        convexHull ℝ (insert z.re (revDriver W T '' Icc 0 s)) :=
  revFlow_bounds (continuous_revDriver hW T) hz hs.1

/-- The convex-hull bound in absolute value: if `|V_v| ≤ m` on `[0, s]`, then
`|Re h_s(z)| ≤ max |x| m`. -/
theorem abs_re_revFlow_le {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ}
    (hs : 0 ≤ s) {m : ℝ} (hm : ∀ v ∈ Icc 0 s, |V v| ≤ m) : |(revFlow V s z).re| ≤ max |z.re| m := by
  have hsub : insert z.re (V '' Icc 0 s) ⊆ Icc (-max |z.re| m) (max |z.re| m) := by
    rintro a (rfl | ⟨v, hv, rfl⟩)
    · exact abs_le.1 (le_max_left _ _)
    · exact abs_le.1 ((hm v hv).trans (le_max_right _ _))
  exact abs_le.2 (convexHull_min hsub (convex_Icc _ _) (re_revFlow_mem_convexHull hV hz hs))

/-- `|X_s(z)| ≤ max |x| m + m` when `|V_v| ≤ m` on `[0, s]`. -/
theorem abs_re_revMap_le {V : ℝ → ℝ} (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {s : ℝ}
    (hs : 0 ≤ s) {m : ℝ} (hm : ∀ v ∈ Icc 0 s, |V v| ≤ m) :
    |(revMap V s z).re| ≤ max |z.re| m + m := by
  have h1 := abs_re_revFlow_le hV hz hs hm
  have h2 := hm s ⟨hs, le_rfl⟩
  have he : (revMap V s z).re = (revFlow V s z).re - V s := by rw [re_revFlow]; ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- **(2.9)**, bound form: if `|V_v| ≤ m` on `[0, s]`, then `|X_s(iy)| ≤ 2m`. -/
theorem abs_re_revMap_mul_I_le {V : ℝ → ℝ} (hV : Continuous V) {y : ℝ} (hy : 0 < y) {s : ℝ}
    (hs : 0 ≤ s) {m : ℝ} (hm : ∀ v ∈ Icc 0 s, |V v| ≤ m) :
    |(revMap V s ((y : ℂ) * I)).re| ≤ 2 * m := by
  have hz : (y : ℂ) * I ∈ H := by show 0 < ((y : ℂ) * I).im; simpa using hy
  have h := abs_re_revMap_le hV hz hs hm
  have hm0 : 0 ≤ m := (abs_nonneg _).trans (hm 0 ⟨le_rfl, hs⟩)
  simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, abs_zero,
    max_eq_right hm0] at h
  linarith

/-- **(2.9)** (SLE₈ note, p. 3): `|X_s(iy)| ≤ 2 sup_{0 ≤ v ≤ s} |V_v|`. -/
theorem abs_re_revMap_mul_I_le_two_mul_sSup {V : ℝ → ℝ} (hV : Continuous V) {y : ℝ} (hy : 0 < y)
    {s : ℝ} (hs : 0 ≤ s) :
    |(revMap V s ((y : ℂ) * I)).re| ≤ 2 * sSup ((fun v => |V v|) '' Icc 0 s) := by
  have hbdd : BddAbove ((fun v => |V v|) '' Icc 0 s) :=
    (isCompact_Icc.image (continuous_abs.comp hV)).bddAbove
  exact abs_re_revMap_mul_I_le hV hy hs fun v hv => le_csSup hbdd (mem_image_of_mem _ hv)

/-! ## (2.7): the reverse flow and the centred inverse maps -/

/-- The driver of the reverse flow `fwdMapInv (shiftDrive W (T - s)) s` is the note's `V = revDriver W T`. -/
theorem shiftDrive_timeRev_eq_revDriver (W : ℝ → ℝ) (T s : ℝ) :
    (fun r => RS.shiftDrive W (T - s) (s - r) - RS.shiftDrive W (T - s) s) = revDriver W T := by
  funext r
  simp only [RS.shiftDrive, revDriver_apply, sub_add_sub_cancel, sub_add_cancel]
  ring

theorem revMap_revDriver_mem_H {W : ℝ → ℝ} (hW : Continuous W) {T s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H) : revMap (revDriver W T) s z ∈ H :=
  TwoPoint.im_revMap_pos (continuous_revDriver hW T) hz hs

/-- **(2.7)** (SLE₈ note, p. 3): `F_T(z) = F_{T-s}(Z_s(z))` for `z ∈ ℍ` and `0 ≤ s ≤ T`, where
`F_t = fwdMapInv W t` and `Z_s = revMap (revDriver W T) s`. -/
theorem fwdMapInv_eq_fwdMapInv_revMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W T z = fwdMapInv W (T - s) (revMap (revDriver W T) s z) := by
  have h := RS.fwdMapInv_add_shift hW hW0 (sub_nonneg.2 hsT) hs hz
  rw [sub_add_cancel] at h
  rw [h, UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ (RS.continuous_shiftDrive hW _)
    (RS.shiftDrive_zero W _) hs hz, shiftDrive_timeRev_eq_revDriver]

/-- **(2.7)**, complex-derivative form: `F_T'(z) = F'_{T-s}(Z_s(z)) Z_s'(z)`. -/
theorem deriv_fwdMapInv_eq_mul {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    deriv (fwdMapInv W T) z =
      deriv (fwdMapInv W (T - s)) (revMap (revDriver W T) s z) *
        deriv (revMap (revDriver W T) s) z := by
  have hev : fwdMapInv W T =ᶠ[𝓝 z] fun w => fwdMapInv W (T - s) (revMap (revDriver W T) s w) :=
    eventually_of_mem (isOpen_H.mem_nhds hz) fun w hw =>
      fwdMapInv_eq_fwdMapInv_revMap hW hW0 hs hsT hw
  rw [hev.deriv_eq]
  exact deriv_comp (h₂ := fwdMapInv W (T - s)) (h := revMap (revDriver W T) s) z
    (RS.differentiableAt_fwdMapInv hW hW0 (sub_nonneg.2 hsT) (revMap_revDriver_mem_H hW hs hz))
    (hasDerivAt_revMap _ (continuous_revDriver hW T) hs hz).differentiableAt

/-- **(2.7)** (SLE₈ note, p. 3): `|F_T'(z)| = Φ_s(z) |F'_{T-s}(Z_s(z))|` for `z ∈ ℍ`, `0 ≤ s ≤ T`. -/
theorem norm_deriv_fwdMapInv_eq_mul {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    ‖deriv (fwdMapInv W T) z‖ =
      ‖deriv (revFlow (revDriver W T) s) z‖ *
        ‖deriv (fwdMapInv W (T - s)) (revMap (revDriver W T) s z)‖ := by
  rw [deriv_fwdMapInv_eq_mul hW hW0 hs hsT hz, norm_mul, mul_comm, deriv_revFlow]

/-- The case `s = T` of (2.7): `F_T(z) = Z_T(z)` (`F_0` is the identity on `ℍ`). -/
theorem fwdMapInv_eq_revMap_revDriver {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) : fwdMapInv W T z = revMap (revDriver W T) T z :=
  UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 hT hz

/-- The case `s = T` of (2.7): `Φ_T(z) = |F_T'(z)|`. -/
theorem norm_deriv_fwdMapInv_eq_norm_deriv_revFlow {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) :
    ‖deriv (fwdMapInv W T) z‖ = ‖deriv (revFlow (revDriver W T) T) z‖ := by
  have hev : fwdMapInv W T =ᶠ[𝓝 z] revMap (revDriver W T) T :=
    eventually_of_mem (isOpen_H.mem_nhds hz) fun w hw => fwdMapInv_eq_revMap_revDriver hW hW0 hT hw
  rw [hev.deriv_eq, deriv_revFlow]

/-- The identification behind (2.7): `Z_s(z) = f_{T-s}(F_T(z))`, with QuantumZipper's centred
forward map `f_t = g_t - W_t` (`fwdMap W t`). -/
theorem revMap_revDriver_eq_fwdMap_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    revMap (revDriver W T) s z = fwdMap W (T - s) (fwdMapInv W T z) := by
  rw [fwdMapInv_eq_fwdMapInv_revMap hW hW0 hs hsT hz,
    RS.fwdMap_fwdMapInv hW hW0 (sub_nonneg.2 hsT) (revMap_revDriver_mem_H hW hs hz)]

/-- The note's identification `h_s(z) = g_{T-s}(F_T(z)) - W_T`, with `g_t = f_t + W_t`. -/
theorem revFlow_revDriver_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    revFlow (revDriver W T) s z = fwdMap W (T - s) (fwdMapInv W T z) + W (T - s) - W T := by
  rw [revFlow_def, revMap_revDriver_eq_fwdMap_fwdMapInv hW hW0 hs hsT hz, revDriver_apply]
  push_cast; ring

end InteractingSLE.SLE8
