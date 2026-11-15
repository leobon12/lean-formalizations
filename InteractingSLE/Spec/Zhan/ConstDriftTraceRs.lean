/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# The trace of a restarted strip path, from the original trace

Packet PROVE-ZHAN-A6. PROVE-ZHAN-A4's assembly of the strip endpoint theorem applies the constant-drift endpoint
theorem to the restart of a strip path at an integer strip time `n` (`rsW`, `rsV`, `rsZ`: the chordal path after the
chordal time `a = t⁻¹(n)`, mapped out and rescaled by the gap `g = w_a − v_a`). Its trace clause there is not needed
as an input: the restart has a continuous generating trace on its strip life as soon as the original path has one.

By [Yua22] Corollary 1.3 before a finite horizon (`IsLoewnerTraceLT.isLoewnerTraceLT_shift`, PROVE-YUAN-M1), the
tips `γ_a(u) = F̄^{(a)}_u(0)` of the chain of the shifted driver `w(a + ·) − w(a)` (`shiftTip`) generate that chain
before every horizon at which the original trace generates its chain (`isGeneratingTrace_shiftTip`). The restarted
driver is the dilation `r ↦ g⁻¹(w(a + g² r) − w(a))` of the shifted one, so the dilated tips generate it
(`IsGeneratingTrace.dilate`).

## Main results

* `shiftTip`, `isGeneratingTrace_shiftTip`;
* `IsStripPath.isGeneratingTrace_rs` (**the restarted trace**): if `η` generates the chain of `w` on every strip-life
  interval, then `r ↦ g⁻¹ γ_a(g² r)` generates the chain of the restarted driver on every strip-life interval of the
  restart.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Zhan

open Strip

/-! ### The tips of the shifted chain -/

/-- The tip `γ_a(u) = F̄^{(a)}_u(0)` of the chain of the shifted driver `w(a + ·) − w(a)`. -/
def shiftTip (w : ℝ≥0 → ℝ) (a : ℝ≥0) (u : ℝ≥0) : ℂ :=
  loewnerTip (fun s : ℝ => Sec7.shiftNN w a s.toNNReal) u

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

theorem shiftDrive_frozenDrive_eq {t₂ : ℝ} {a : ℝ≥0} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) (t₂ - a)) :
    shiftDrive (frozenDrive w t₂) a r = Sec7.shiftNN w a r.toNNReal := by
  have h1 : (a : ℝ) + r ≤ t₂ := by linarith [hr.2]
  have h2 : (a : ℝ) ≤ t₂ := by linarith [hr.1]
  have e1 : ((a : ℝ) + r).toNNReal = a + r.toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith [hr.1, a.coe_nonneg]), Real.coe_toNNReal _ hr.1]
  simp only [shiftDrive, frozenDrive, Sec7.shiftNN, min_eq_left h1, min_eq_left h2, e1, Real.toNNReal_coe]

/-- **[Yua22] Corollary 1.3 for the frozen generating trace before a finite horizon**: if `η` generates the chain of
`w` before `T` and `a + u < T`, the shifted tips generate the chain of `w(a + ·) − w(a)` on `[0, u]`. -/
theorem isGeneratingTrace_shiftTip (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {a u : ℝ≥0} (hau : ((a + u : ℝ≥0) : ℝ≥0∞) < T) :
    IsGeneratingTrace (Sec7.shiftNN w a) u (shiftTip w a) := by
  obtain ⟨t₂, hut₂, ht₂T⟩ := exists_real_btwn_of_lt hau
  have hau' : (a : ℝ) + u < t₂ := by simpa using hut₂
  have ht₂ : 0 ≤ t₂ := by linarith [a.coe_nonneg, u.coe_nonneg]
  have hL := hη.isLoewnerTraceLT ht₂T
  have hWc := continuous_frozenDrive_of_lt hw ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  obtain ⟨hγ, -⟩ := hL.isLoewnerTraceLT_shift hWc hW0 a.coe_nonneg
  set γ := loewnerTip (shiftDrive (frozenDrive w t₂) a) with hγdef
  have hagree : ∀ r ∈ Icc (0 : ℝ) (t₂ - a),
      shiftDrive (frozenDrive w t₂) a r = (fun s : ℝ => Sec7.shiftNN w a s.toNNReal) r :=
    fun r hr => shiftDrive_frozenDrive_eq hr
  have htip : ∀ t : ℝ≥0, (t : ℝ) ≤ u → shiftTip w a t = γ t := by
    intro t ht
    simp only [shiftTip, hγdef, loewnerTip]
    rw [fwdMapInv_eq_of_eqOn t.coe_nonneg (by linarith) hagree]
  have hmapsto : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ u → (t : ℝ) ∈ Ico (0 : ℝ) (t₂ - a) := fun t ht =>
    ⟨t.coe_nonneg, by have : (t : ℝ) ≤ u := by exact_mod_cast ht
                      linarith⟩
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · rw [htip 0 u.coe_nonneg]
    exact hγ.1
  · refine ((hγ.2.1.comp NNReal.continuous_coe.continuousOn fun t ht => hmapsto t ht)).congr
      fun t ht => ?_
    exact htip t (by exact_mod_cast (show (t : ℝ≥0∞) ≤ u from ht))
  · have htu : (t : ℝ) < u := by exact_mod_cast ht
    have htT : (t : ℝ) < t₂ - a := by linarith
    have hfill := hγ.2.2 t t.coe_nonneg htT
    have himg : shiftTip w a '' Icc 0 t = γ '' Icc 0 (t : ℝ) := by
      ext z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr.2⟩,
          (htip r (le_trans (NNReal.coe_le_coe.2 hr.2) htu.le)).symm⟩
      · rintro ⟨r, hr, rfl⟩
        refine ⟨r.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩, ?_⟩
        rw [htip _ (by rw [Real.coe_toNNReal _ hr.1]; linarith [hr.2]), Real.coe_toNNReal _ hr.1]
    have hK : fwdHull (fun s : ℝ => Sec7.shiftNN w a s.toNNReal) t =
        fwdHull (shiftDrive (frozenDrive w t₂) a) t :=
      (fwdHull_eq_of_eqOn t.coe_nonneg htT hagree).symm
    have hA : IsCompact (γ '' Icc 0 (t : ℝ)) :=
      isCompact_Icc.image_of_continuousOn (hγ.2.1.mono fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 htT⟩)
    rw [himg, hK]
    exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).2 hfill

/-! ### The restarted trace -/

variable {v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The restarted driver is the dilation of the shifted one by the gap: `ŵ(r) = g⁻¹(w(a + g² r) − w(a))`. -/
theorem IsStripPath.dilPath_shiftNN_eq_rsW (h : IsStripPath w v ζ) (n : ℝ≥0) :
    Sec7.Dilation.dilPath (rsScale w v n) (Sec7.shiftNN w (chordT w v n)) = rsW w v n := by
  have hg : 0 < rsGap w v n := h.rsGap_pos n
  have hsq : √((rsScale w v n : ℝ≥0) : ℝ) = rsGap w v n := by
    rw [coe_rsScale, Real.sqrt_sq hg.le]
  funext r
  simp only [Sec7.Dilation.dilPath, Sec7.shiftNN, rsW, hsq]
  field_simp

/-- **The restarted trace.** If `η` generates the chain of `w` on every strip-life interval, then
`r ↦ g⁻¹ γ_a(g² r)` generates the chain of the restarted driver on every strip-life interval of the restart. -/
theorem IsStripPath.isGeneratingTrace_rs (h : IsStripPath w v ζ)
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) (n : ℝ≥0) {r : ℝ≥0}
    (hr : IsStripLife (rsW w v n) (rsV w v n) (rsZ w v ζ n) r) :
    IsGeneratingTrace (rsW w v n) r fun r =>
      (((√((rsScale w v n : ℝ≥0) : ℝ))⁻¹ : ℝ) : ℂ) * shiftTip w (chordT w v n) (rsScale w v n * r) := by
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  have hc : 0 < c := h.rsScale_pos n
  have hs := (h.isStripLife_rs_iff n r).1 hr
  obtain ⟨s', hss', hs'⟩ := h.exists_gt hs
  have hT := isGeneratingTrace_shiftTip (hη s' hs') (h.continuousOn_lt hs') h.1 (a := a) (u := c * r)
    (ENNReal.coe_lt_coe.2 hss')
  have hd := IsGeneratingTrace.dilate hc.ne' hT
  have hT' : (((c * r : ℝ≥0) : ℝ≥0∞)) / (c : ℝ≥0∞) = (r : ℝ≥0∞) := by
    rw [ENNReal.coe_mul, mul_comm, ENNReal.mul_div_cancel_right (ENNReal.coe_ne_zero.2 hc.ne')
      ENNReal.coe_ne_top]
  rw [hT', h.dilPath_shiftNN_eq_rsW n] at hd
  exact hd

end Zhan

end InteractingSLE
