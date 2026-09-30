import QuantumZipper.Proofs.Thm18.R18G3TRegion
import QuantumZipper.Proofs.Thm18.R18G3TFidB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (R-b): the Palm point of schemes `B` and `C` in region 1

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71. Schemes `B` (profile `g3wCut γ η`) and
`C` (profile `g3wProf γ`) have the same region-1 boundary measure (`g3pν₁_cut_eq`); their gap
measures `ν₀` differ but give no mass to the closed region-1 interval `[A, B]`
(`A = t₁ − r₁`, `B = t₁ + r₁ = −3η/4`). Hence, for `x ≤ 0` inside region 1,
`(ν₁ + ν₀)[x, 0] = ν₁[x, B) + (ν₁ + ν₀)[B, 0]`, and the Palm point read from the length `ℓ`
in scheme `B` equals the Palm point read from `ℓ − c_B + c_C` in scheme `C`, where
`c = (ν₁ + ν₀)[B, 0]` is read from the gap field (outside-measurable):

* `lenLeft_congr`: deterministic transfer of `lenLeft` (own elementary argument);
* `g3pν₀_region_null_of`: `ν₀[A, B] = 0` (`G3Fid.gapCut`);
* `g3pX_cut_prof`: the transfer of the Palm point between the two schemes.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Transfer of `lenLeft`.** If two measures agree to the left of `B < 0` up to their masses
`c, c'` of `[B, 0]`, and the point read from `ℓ` lies in `(A, B)`, then the point read from
`ℓ − c + c'` is the same. -/
theorem lenLeft_congr {m m' : Measure ℝ} {A B ℓ c c' : ℝ} (hB : B < 0) (hc0 : 0 ≤ c)
    (hc0' : 0 ≤ c') (hc : m (Icc B 0) = ENNReal.ofReal c)
    (hc' : m' (Icc B 0) = ENNReal.ofReal c') (F : ℝ → ℝ≥0∞)
    (hF : ∀ y ∈ Ioo (-B) (-A), m (Icc (-y) 0) = F y + ENNReal.ofReal c ∧
      m' (Icc (-y) 0) = F y + ENNReal.ofReal c')
    (hx : lenLeft m ℓ ∈ Ioo A B) : lenLeft m' (ℓ - c + c') = lenLeft m ℓ := by
  set S : Set ℝ := {y | 0 < y ∧ ENNReal.ofReal ℓ ≤ m (Icc (-y) 0)} with hS
  set S' : Set ℝ := {y | 0 < y ∧ ENNReal.ofReal (ℓ - c + c') ≤ m' (Icc (-y) 0)} with hS'
  have hs : sInf S ∈ Ioo (-B) (-A) := by
    have := hx; unfold lenLeft at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hbdd : BddBelow S := ⟨0, fun y hy => hy.1.le⟩
  have hbdd' : BddBelow S' := ⟨0, fun y hy => hy.1.le⟩
  have hne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hs.1
    rw [h, Real.sInf_empty] at this
    linarith
  -- `ℓ > c`
  have hℓc : c < ℓ := by
    by_contra h
    push Not at h
    have hmem : -B ∈ S := ⟨by linarith, by rw [neg_neg, hc]; exact ENNReal.ofReal_le_ofReal h⟩
    have := csInf_le hbdd hmem
    linarith [hs.1]
  have hup : ∀ y z, y ∈ S → y ≤ z → z ∈ S := fun y z hy hyz =>
    ⟨hy.1.trans_le hyz, hy.2.trans (measure_mono (Icc_subset_Icc (by linarith) le_rfl))⟩
  -- membership agrees on the region
  have hiff : ∀ y ∈ Ioo (-B) (-A), y ∈ S ↔ y ∈ S' := fun y hy => by
    obtain ⟨h1, h2⟩ := hF y hy
    have hy0 : 0 < y := by linarith [hy.1]
    have e1 : ENNReal.ofReal ℓ = ENNReal.ofReal (ℓ - c) + ENNReal.ofReal c := by
      rw [← ENNReal.ofReal_add (by linarith) hc0]; ring_nf
    have e2 : ENNReal.ofReal (ℓ - c + c') = ENNReal.ofReal (ℓ - c) + ENNReal.ofReal c' := by
      rw [← ENNReal.ofReal_add (by linarith) hc0']
    simp only [hS, hS', mem_ofPred_eq, h1, h2, e1, e2,
      ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top, hy0, true_and]
  -- no point of `(0, −B]` is in `S'`
  have hno : ∀ y, 0 < y → y ≤ -B → y ∉ S' := fun y _ hyB hy => by
    have h1 : m' (Icc (-y) 0) ≤ ENNReal.ofReal c' := by
      rw [← hc']; exact measure_mono (Icc_subset_Icc (by linarith) le_rfl)
    have h2 : ENNReal.ofReal c' < ENNReal.ofReal (ℓ - c + c') :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    exact absurd (hy.2.trans h1) (not_le.2 h2)
  -- points of `(s, −A)` are in `S'`
  have hin : ∀ z ∈ Ioo (sInf S) (-A), z ∈ S' := fun z hz => by
    obtain ⟨y, hyS, hyz⟩ := exists_lt_of_csInf_lt hne hz.1
    exact (hiff z ⟨hs.1.trans hz.1, hz.2⟩).1 (hup y z hyS hyz.le)
  have hmid : (sInf S + -A) / 2 ∈ Ioo (sInf S) (-A) := ⟨by linarith [hs.2], by linarith [hs.2]⟩
  have heq : sInf S' = sInf S := by
    refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun z hz => ?_
      by_cases hzA : z < -A
      · exact csInf_le hbdd' (hin z ⟨hz, hzA⟩)
      · exact (csInf_le hbdd' (hin _ hmid)).trans (by linarith [hmid.2])
    · refine le_csInf ⟨_, hin _ hmid⟩ fun y hy => ?_
      by_contra hlt
      push Not at hlt
      by_cases hyB : y ≤ -B
      · exact hno y hy.1 hyB hy
      · have hyr : y ∈ Ioo (-B) (-A) := ⟨not_le.1 hyB, hlt.trans hs.2⟩
        have := csInf_le hbdd ((hiff y hyr).2 hy)
        linarith
  unfold lenLeft
  rw [← hS', heq]

/-- The gap mass of `[t₁ + r₁, 0]` (read from the gap field only, hence outside-measurable). -/
def g3pc (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : gffBase.Ω) : ℝ :=
  (g3pν₀ γ g i ω (Icc (i.t₁ + i.r₁) 0)).toReal

/-- The region-1 measure gives no mass to `[t₁ + r₁, 0]`. -/
theorem g3pν₁_null_of {γ : ℝ} (hγ : 0 < γ) (g : ℂ → ℝ) (i : G3Idx) (ω : gffBase.Ω)
    (hv : IsVagueLimitR (bdryApprox γ (g3pField γ g ω)) (qBoundaryMeasure γ (g3pField γ g ω)))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ g ω) k))
    (hat : ∀ s, qBoundaryMeasure γ (g3pField γ g ω) {s} = 0) :
    g3pν₁ γ g i ω (Icc (i.t₁ + i.r₁) 0) = 0 := by
  obtain ⟨hB1, e1⟩ := G3Fid.regionCut hγ hv hfin hat (t := i.t₁) i.r₁_pos
  rw [g3pν₁, bdryM, if_pos hB1, e1, Measure.restrict_apply measurableSet_Icc]
  exact measure_mono_null (fun x hx => absurd hx.2.2 (not_lt.2 hx.1.1)) measure_empty

/-- The gap measure gives no mass to the closed region-1 interval. -/
theorem g3pν₀_region_null_of {γ : ℝ} (hγ : 0 < γ) (g : ℂ → ℝ) (i : G3Idx) (ω : gffBase.Ω)
    (hv : IsVagueLimitR (bdryApprox γ (g3pField γ g ω)) (qBoundaryMeasure γ (g3pField γ g ω)))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ g ω) k))
    (hat : ∀ s, qBoundaryMeasure γ (g3pField γ g ω) {s} = 0) :
    g3pν₀ γ g i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0 := by
  obtain ⟨hB0, e0⟩ := G3Fid.gapCut hγ hv hfin hat (t₁ := i.t₁) (t₂ := i.t₂) i.r₁_pos i.r₂_pos
  rw [g3pν₀, bdryM, if_pos hB0, e0, Measure.restrict_apply measurableSet_Icc]
  exact measure_mono_null (fun x hx => (hx.2 (Or.inl hx.1)).elim) measure_empty

/-- Splitting the Palm measure at `B = t₁ + r₁`. -/
theorem g3pm_split {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : gffBase.Ω}
    (h0 : g3pν₀ γ g i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0) {y : ℝ}
    (hy : y ∈ Ioo (-(i.t₁ + i.r₁)) (-(i.t₁ - i.r₁))) :
    (g3pν₁ γ g i ω + g3pν₀ γ g i ω) (Icc (-y) 0) =
      g3pν₁ γ g i ω (Ico (-y) (i.t₁ + i.r₁)) +
        (g3pν₁ γ g i ω + g3pν₀ γ g i ω) (Icc (i.t₁ + i.r₁) 0) := by
  have hB : i.t₁ + i.r₁ < 0 := by
    have := i.hη; unfold G3Idx.t₁ G3Idx.r₁; linarith
  have hu : Icc (-y) 0 = Ico (-y) (i.t₁ + i.r₁) ∪ Icc (i.t₁ + i.r₁) 0 :=
    (Ico_union_Icc_eq_Icc (by linarith [hy.1]) hB.le).symm
  rw [hu, measure_union (disjoint_left.2 fun x h1 h2 => absurd h2.1 (not_le.2 h1.2))
    measurableSet_Icc, Measure.add_apply _ _ (Ico (-y) (i.t₁ + i.r₁))]
  have hz : g3pν₀ γ g i ω (Ico (-y) (i.t₁ + i.r₁)) = 0 :=
    measure_mono_null (fun x (hx : x ∈ Ico (-y) (i.t₁ + i.r₁)) =>
      (⟨by linarith [hx.1, hy.2], hx.2.le⟩ : x ∈ Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁))) h0
  rw [hz, add_zero]

/-- **The Palm point of `B` in region 1 is that of `C` at the shifted length.** -/
theorem g3pX_transfer {γ : ℝ} {g g' : ℂ → ℝ} {i : G3Idx} {ω : gffBase.Ω} {ℓ : ℝ}
    (h1 : g3pν₁ γ g i ω = g3pν₁ γ g' i ω)
    (h1z : g3pν₁ γ g i ω (Icc (i.t₁ + i.r₁) 0) = 0)
    (h0 : g3pν₀ γ g i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (h0' : g3pν₀ γ g' i ω (Icc (i.t₁ - i.r₁) (i.t₁ + i.r₁)) = 0)
    (hf : g3pν₀ γ g i ω (Icc (i.t₁ + i.r₁) 0) ≠ ⊤)
    (hf' : g3pν₀ γ g' i ω (Icc (i.t₁ + i.r₁) 0) ≠ ⊤)
    (hx : g3pX γ g i (ω, ℓ) ∈ Ioo (i.t₁ - i.r₁) (i.t₁ + i.r₁)) :
    g3pX γ g' i (ω, ℓ - g3pc γ g i ω + g3pc γ g' i ω) = g3pX γ g i (ω, ℓ) := by
  have hB : i.t₁ + i.r₁ < 0 := by
    have := i.hη; unfold G3Idx.t₁ G3Idx.r₁; linarith
  have hm : (g3pν₁ γ g i ω + g3pν₀ γ g i ω) (Icc (i.t₁ + i.r₁) 0) =
      ENNReal.ofReal (g3pc γ g i ω) := by
    rw [Measure.add_apply, h1z, zero_add, g3pc, ENNReal.ofReal_toReal hf]
  have hm' : (g3pν₁ γ g' i ω + g3pν₀ γ g' i ω) (Icc (i.t₁ + i.r₁) 0) =
      ENNReal.ofReal (g3pc γ g' i ω) := by
    rw [Measure.add_apply, ← h1, h1z, zero_add, g3pc, ENNReal.ofReal_toReal hf']
  exact lenLeft_congr hB ENNReal.toReal_nonneg ENNReal.toReal_nonneg hm hm'
    (fun y => g3pν₁ γ g i ω (Ico (-y) (i.t₁ + i.r₁)))
    (fun y hy => ⟨by rw [g3pm_split h0 hy, hm], by rw [g3pm_split h0' hy, hm', h1]⟩) hx

end R18
end QuantumZipper
