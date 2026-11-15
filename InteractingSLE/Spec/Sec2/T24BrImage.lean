import InteractingSLE.WangWu.ReverseContactBdryChart
import InteractingSLE.Spec.Sec7.PocketTraversalCoords

/-!
# Theorem 2.4: geometric force-point image bridges

The formulas are stated explicitly so that they can be used with the audited force-image
definitions without importing the statement candidates. Positive real solutions and reflection
are reused from the landed Wang–Wu and Loewner APIs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol fwdMap)

namespace InteractingSLE.Sec2.T24Bridge

open InteractingSLE.MartChar.RealFlow

/-- Existence of a complex flow from a positive real point is exactly positive real survival. -/
theorem exists_isForwardSol_iff_alive {w : ℝ → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) {y t : ℝ} (hy : 0 < y) :
    (∃ u : ℝ → ℂ, IsForwardSol w (y : ℂ) t u) ↔ Alive w y t := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨_, WangWu.isPosSol_of_isForwardSol hw hw0 hy hu⟩
  · intro hy
    exact ⟨_, WangWu.isForwardSol_of_alive hw hy⟩

/-- On a surviving real point, the complex centred map is the landed real flow. -/
theorem re_fwdMap_eq_cflow {w : ℝ → ℝ} (hw : Continuous w) {y t : ℝ}
    (ht : 0 ≤ t) (hy : Alive w y t) :
    (fwdMap w t (y : ℂ)).re = cflow w y t := by
  rw [fwdMap_eq_of_isForwardSol hw (WangWu.isForwardSol_of_alive hw hy)
    ⟨ht, le_rfl⟩, Complex.ofReal_re]

/-- The source's right-force image formula equals the landed uncentred real image. -/
theorem right_force_image_eq {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    w t + sInf {v : ℝ | ∃ y : ℝ, x < y ∧
      (∃ u : ℝ → ℂ, IsForwardSol w (y : ℂ) t u) ∧
      v = (fwdMap w t (y : ℂ)).re} = rightImg w x t := by
  let S : Set ℝ := {v | ∃ y : ℝ, x < y ∧
    (∃ u : ℝ → ℂ, IsForwardSol w (y : ℂ) t u) ∧
    v = (fwdMap w t (y : ℂ)).re}
  have hmem : ∀ v, v ∈ S ↔ ∃ y, x < y ∧ Alive w y t ∧ v = cflow w y t := by
    intro v
    constructor
    · rintro ⟨y, hxy, hu, rfl⟩
      have hy := (exists_isForwardSol_iff_alive hw hw0 (hx.trans_lt hxy)).1 hu
      exact ⟨y, hxy, hy, re_fwdMap_eq_cflow hw ht hy⟩
    · rintro ⟨y, hxy, hy, rfl⟩
      exact ⟨y, hxy, ⟨_, WangWu.isForwardSol_of_alive hw hy⟩,
        (re_fwdMap_eq_cflow hw ht hy).symm⟩
  have hSne : S.Nonempty := by
    obtain ⟨g, y, hxy, hy, rfl⟩ := imgSet_nonempty hw x ht
    exact ⟨_, (hmem _).2 ⟨y, hxy, hy, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, fun v hv => ?_⟩
    obtain ⟨y, -, hy, rfl⟩ := (hmem v).1 hv
    exact (hy.cflow_pos hw ⟨ht, le_rfl⟩).le
  change w t + sInf S = rightImg w x t
  apply le_antisymm
  · refine le_csInf (imgSet_nonempty hw x ht) ?_
    rintro g ⟨y, hxy, hy, rfl⟩
    exact add_le_add_right (csInf_le hSbdd ((hmem _).2 ⟨y, hxy, hy, rfl⟩)) (w t)
  · have hle : rightImg w x t - w t ≤ sInf S := by
      refine le_csInf hSne ?_
      intro v hv
      obtain ⟨y, hxy, hy, rfl⟩ := (hmem v).1 hv
      exact sub_le_iff_le_add.2 (by
        simpa only [gImg, add_comm] using rightImg_le_gImg hw ht hxy hy)
    exact (sub_le_iff_le_add.1 hle).trans_eq (add_comm _ _)

/-- The left-force formula equals the reflected landed real image. -/
theorem left_force_image_eq {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {x t : ℝ} (hx : x ≤ 0) (ht : 0 ≤ t) :
    w t + sSup {v : ℝ | ∃ y : ℝ, y < x ∧
      (∃ u : ℝ → ℂ, IsForwardSol w (y : ℂ) t u) ∧
      v = (fwdMap w t (y : ℂ)).re} = -rightImg (fun s => -w s) (-x) t := by
  let S : Set ℝ := {v | ∃ y : ℝ, -x < y ∧
    (∃ u : ℝ → ℂ, IsForwardSol (fun s => -w s) (y : ℂ) t u) ∧
    v = (fwdMap (fun s => -w s) t (y : ℂ)).re}
  have hset : {v : ℝ | ∃ y : ℝ, y < x ∧
      (∃ u : ℝ → ℂ, IsForwardSol w (y : ℂ) t u) ∧
      v = (fwdMap w t (y : ℂ)).re} = -S := by
    ext v
    change _ ↔ -v ∈ S
    constructor
    · rintro ⟨y, hy, ⟨u, hu⟩, rfl⟩
      refine ⟨-y, neg_lt_neg hy,
        (exists_isForwardSol_neg_iff (W := w)).2 ⟨u, hu⟩, ?_⟩
      rw [fwdMap_neg_real hw hu ⟨ht, le_rfl⟩, Complex.neg_re]
    · rintro ⟨y, hy, ⟨u, hu⟩, hv⟩
      have he := (exists_isForwardSol_neg_iff (W := fun s => -w s)
        (x := y) (T := t)).2 ⟨u, hu⟩
      simp only [neg_neg] at he
      refine ⟨-y, neg_lt.mp hy, he, ?_⟩
      have hm := fwdMap_neg_real hw.neg hu ⟨ht, le_rfl⟩
      simp only [Pi.neg_apply, neg_neg] at hm
      rw [hm, Complex.neg_re]
      change -v = (fwdMap (-w) t (y : ℂ)).re at hv
      exact neg_eq_iff_eq_neg.1 hv
  rw [hset, Real.sSup_neg]
  have hr := right_force_image_eq hw.neg (by simp only [Pi.neg_apply, hw0, neg_zero])
    (neg_nonneg.2 hx) ht
  change -w t + sInf S = rightImg (fun s => -w s) (-x) t at hr
  linarith only [hr]

/-- Specialization to the stochastic right-force coordinates used by the converse theorem. -/
theorem right_force_image_eq_geomRW {Ω : Type*} {nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {xR : Ω → Fin nR → ℝ} {ω : Ω} (hw : Continuous (W · ω)) (hw0 : W 0 ω = 0)
    (j : Fin nR) (hx : 0 ≤ xR ω j) (t : ℝ≥0) :
    W t ω + sInf {v : ℝ | ∃ y : ℝ, xR ω j < y ∧
      (∃ u : ℝ → ℂ, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (y : ℂ) t u) ∧
      v = (fwdMap (fun s : ℝ => W s.toNNReal ω) t (y : ℂ)).re} =
      Sec7.PocketTraversal.geomRW W xR j t ω := by
  unfold Sec7.PocketTraversal.geomRW InteractingSLE.Bessel.realPath
  simpa only [Real.toNNReal_coe] using right_force_image_eq
    (w := fun s : ℝ => W s.toNNReal ω) (hw.comp continuous_real_toNNReal)
      (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) hx t.coe_nonneg

/-- Specialization to the stochastic left-force coordinates used by the converse theorem. -/
theorem left_force_image_eq_geomLW {Ω : Type*} {nL : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {xL : Ω → Fin nL → ℝ} {ω : Ω} (hw : Continuous (W · ω)) (hw0 : W 0 ω = 0)
    (i : Fin nL) (hx : xL ω i ≤ 0) (t : ℝ≥0) :
    W t ω + sSup {v : ℝ | ∃ y : ℝ, y < xL ω i ∧
      (∃ u : ℝ → ℂ, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (y : ℂ) t u) ∧
      v = (fwdMap (fun s : ℝ => W s.toNNReal ω) t (y : ℂ)).re} =
      Sec7.PocketTraversal.geomLW W xL i t ω := by
  unfold Sec7.PocketTraversal.geomLW InteractingSLE.Bessel.realPath
  simpa only [Real.toNNReal_coe] using left_force_image_eq
    (w := fun s : ℝ => W s.toNNReal ω) (hw.comp continuous_real_toNNReal)
      (by simpa only [Function.comp_apply, Real.toNNReal_zero] using hw0) hx t.coe_nonneg

end InteractingSLE.Sec2.T24Bridge
