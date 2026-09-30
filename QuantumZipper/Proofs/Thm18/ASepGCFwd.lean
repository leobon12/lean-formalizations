import QuantumZipper.Proofs.Thm18.ASepGCPsi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 4: the unzipping map `f_τ⁻¹` of `pathDrive κ x` read from the path code

The driver `W = pathDrive κ x` of a continuous path need not start at `0`. The centered forward
flow only sees `z − W t`, so translating the driver and the starting point by the same real
constant `c` does not change the flow (`isForwardSol_sub_const`); hence
`f_τ⁻¹[W] = f_τ⁻¹[W − c] + c` on `ℍ` (`fwdMapInv_eq_add_const`). With `W − W 0 = wg (kcode κ …)`
(`GC.wg_kcode`) and `G4Core.fwdMapInv_eq_psiR`:

* **`fwdMapInv_pathDrive_eq`**: for continuous `x`, `τ ≥ 0`, `w ∈ ℍ`,
  `fwdMapInv (pathDrive κ x) τ w = fC κ (codeP x, τ) w`, where
  `fC κ (c, τ) w = psiR (kcode κ c) τ w + √κ c(m0)` is jointly Borel (`measurable_fC`).

Own elementary argument (translation invariance of the Loewner equation, Lawler,
*Conformally invariant processes in the plane*, §4.1).
-/

noncomputable section

open MeasureTheory Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

theorem isForwardSol_sub_const (W : ℝ → ℝ) (c : ℝ) (z : ℂ) (T : ℝ) :
    IsForwardSol (fun s => W s - c) (z - c) T = IsForwardSol W z T := by
  funext u
  unfold IsForwardSol
  have e : ∀ t, z - (c : ℂ) - (((W t - c : ℝ)) : ℂ) = z - (W t : ℂ) := fun t => by
    push_cast; ring
  simp only [e]

theorem fwdMap_sub_const (W : ℝ → ℝ) (c : ℝ) (z : ℂ) (T : ℝ) :
    fwdMap (fun s => W s - c) T (z - c) = fwdMap W T z := by
  unfold fwdMap
  rw [isForwardSol_sub_const]

theorem mem_fwdHull_sub_const (W : ℝ → ℝ) (c : ℝ) (z : ℂ) (T : ℝ) :
    z - c ∈ fwdHull (fun s => W s - c) T ↔ z ∈ fwdHull W T := by
  have hs : swallowTime (fun s => W s - c) (z - c) = swallowTime W z := by
    unfold swallowTime
    simp only [isForwardSol_sub_const]
  have hH : (z - c ∈ H) ↔ z ∈ H := by
    show 0 < (z - (c : ℂ)).im ↔ 0 < z.im
    simp
  simp only [fwdHull, mem_ofPred_eq, hs, hH]

theorem fwdMapInv_eq_of {W : ℝ → ℝ} {T : ℝ} {w z : ℂ}
    (hex : ∃! z', z' ∈ H \ fwdHull W T ∧ fwdMap W T z' = w)
    (hz : z ∈ H \ fwdHull W T ∧ fwdMap W T z = w) : fwdMapInv W T w = z := by
  unfold fwdMapInv
  rw [dif_pos hex]
  exact hex.unique hex.choose_spec.1 hz

/-- The inverse forward map is uniquely defined on `ℍ` (driver starting at `0`). -/
theorem existsUnique_fwdMapInv {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    ∃! z', z' ∈ H \ fwdHull V t ∧ fwdMap V t z' = w := by
  set V' : ℝ → ℝ := fun s => V (t - s) - V t with hV'def
  have hV' : Continuous V' := (hV.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hV'0 : V' 0 = 0 := by simp [hV'def]
  have hVV : (fun s => V' (t - s) - V' t) = V := by
    funext s; simp only [hV'def, sub_sub_cancel, sub_self, hV0]; ring
  obtain ⟨h1, h2⟩ := UnzipInvariance.fwdMap_revMap_timeRev_of_nonneg V' hV' hV'0 ht hw
  rw [hVV] at h1 h2
  have hmem : revMap V' t w ∈ H \ fwdHull V t :=
    ⟨lt_of_lt_of_le hw (im_le_im_revMap V' hV' w hw ht), h1⟩
  exact ⟨revMap V' t w, ⟨hmem, h2⟩, fun y hy =>
    FwdHolo.injOn_fwdMap hV ht hy.1 hmem (hy.2.trans h2.symm)⟩

/-- **Translation of the driver**: `f_T⁻¹[W] = f_T⁻¹[W − c] + c` on `ℍ` when `W − c` starts at
`0`. -/
theorem fwdMapInv_eq_add_const {W : ℝ → ℝ} {c : ℝ} (hW : Continuous W) (hW0 : W 0 = c) {T : ℝ}
    (hT : 0 ≤ T) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W T w = fwdMapInv (fun s => W s - c) T w + c := by
  have hV : Continuous fun s => W s - c := hW.sub continuous_const
  have hex := existsUnique_fwdMapInv hV (by simp [hW0]) hT hw
  obtain ⟨z0, hz0⟩ := hex.exists
  have h0 : fwdMapInv (fun s => W s - c) T w = z0 := fwdMapInv_eq_of hex hz0
  have hmem : ∀ y : ℂ, y ∈ H \ fwdHull W T ↔ y - c ∈ H \ fwdHull (fun s => W s - c) T := by
    intro y
    have hH : (y - c ∈ H) ↔ y ∈ H := by
      show 0 < (y - (c : ℂ)).im ↔ 0 < y.im
      simp
    simp only [mem_sdiff, hH, mem_fwdHull_sub_const]
  have hz0' : z0 + c ∈ H \ fwdHull W T ∧ fwdMap W T (z0 + c) = w := by
    refine ⟨(hmem _).2 (by simpa using hz0.1), ?_⟩
    rw [← fwdMap_sub_const W c, add_sub_cancel_right]
    exact hz0.2
  have hexW : ∃! z', z' ∈ H \ fwdHull W T ∧ fwdMap W T z' = w := by
    refine ⟨z0 + c, hz0', fun y hy => ?_⟩
    have hy' : y - c ∈ H \ fwdHull (fun s => W s - c) T ∧
        fwdMap (fun s => W s - c) T (y - c) = w :=
      ⟨(hmem y).1 hy.1, by rw [fwdMap_sub_const]; exact hy.2⟩
    have := hex.unique hy' hz0
    rw [← this]; ring
  rw [fwdMapInv_eq_of hexW hz0', h0]

/-- The code unzipping map. -/
def fC (κ : ℝ) (q : (ℕ → ℝ) × ℝ) (w : ℂ) : ℂ :=
  psiR (kcode κ q.1) q.2 w + ((Real.sqrt κ * q.1 m0 : ℝ) : ℂ)

theorem measurable_fC (κ : ℝ) :
    Measurable fun s : ((ℕ → ℝ) × ℝ) × ℂ => fC κ s.1 (selC s.2) := by
  have h1 : Measurable fun s : ((ℕ → ℝ) × ℝ) × ℂ => ((kcode κ s.1.1, s.1.2), s.2) :=
    (((measurable_kcode κ).comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk
      measurable_snd
  have h2 := measurable_Psi.comp h1
  refine h2.add (Complex.measurable_ofReal.comp (measurable_const.mul
    ((measurable_pi_apply m0).comp measurable_fst.fst)))

/-- **The unzipping map of a continuous path read from its code.** -/
theorem fwdMapInv_pathDrive_eq (κ : ℝ) {x : ℝ≥0 → ℝ} (hx : Continuous x) {τ : ℝ} (hτ : 0 ≤ τ)
    {w : ℂ} (hw : w ∈ H) : fwdMapInv (pathDrive κ x) τ w = fC κ (codeP x, τ) w := by
  have hW : Continuous (pathDrive κ x) :=
    continuous_const.mul (hx.comp continuous_real_toNNReal)
  have hc : pathDrive κ x 0 = Real.sqrt κ * codeP x m0 := by
    simp only [pathDrive, codeP, qs_m0, Real.toNNReal_zero]
  rw [fwdMapInv_eq_add_const hW rfl hτ hw, ← wg_kcode hx, fwdMapInv_eq_psiR _ hτ hw, fC, hc]

end GC
end ASep
end QuantumZipper
