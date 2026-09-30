import QuantumZipper.Proofs.Thm18.G3Fid2Region

/-!
# G3 fidelity F2 (part 4): the region and gap cuts, instantiated

For a field sample `y` whose boundary approximations are finite on compacts and converge vaguely
to an atomless `ν` (`γ > 0`):

* `regionCut`: `BCert` for `restrictField (circIn t r) y` (`r > 0`), with boundary measure
  `ν|_(t − r, t + r)`;
* `gapCut`: `BCert` for `restrictField (circOut t₁ r₁ t₂ r₂) y` (`r₁, r₂ > 0`), with boundary
  measure `ν` restricted to the complement of `[t₁ − r₁, t₁ + r₁] ∪ [t₂ − r₂, t₂ + r₂]`.

Own elementary bookkeeping (AGENT_GUIDE cost rule), on top of `G3Fid2Region`.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Fid

theorem volume_abs_sub_eq (t d : ℝ) : volume {s : ℝ | |s - t| = d} = 0 := by
  refine measure_mono_null (fun s hs => ?_)
    ((({t + d, t - d} : Set ℝ).toFinite).measure_zero volume)
  simp only [mem_setOf_eq] at hs
  simp only [mem_insert_iff, mem_singleton_iff]
  rcases abs_cases (s - t) with ⟨e, -⟩ | ⟨e, -⟩
  · left; linarith
  · right; linarith

theorem mem_Icc_iff_abs {s t r : ℝ} : s ∈ Icc (t - r) (t + r) ↔ |s - t| ≤ r := by
  rw [mem_Icc, abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem mem_Ioo_iff_abs {s t r : ℝ} : s ∈ Ioo (t - r) (t + r) ↔ |s - t| < r := by
  rw [mem_Ioo, abs_sub_lt_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Far from `t ± r`, thickening by `ρ < δ` does not change the side. -/
theorem far_iff {s t r δ ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < δ) (h1 : δ < |s - (t - r)|)
    (h2 : δ < |s - (t + r)|) :
    (|s - t| + ρ < r ↔ |s - t| < r) ∧ (r + ρ < |s - t| ↔ r < |s - t|) := by
  rcases abs_cases (s - t) with ⟨e, -⟩ | ⟨e, -⟩ <;>
  rcases abs_cases (s - (t - r)) with ⟨e1, -⟩ | ⟨e1, -⟩ <;>
  rcases abs_cases (s - (t + r)) with ⟨e2, -⟩ | ⟨e2, -⟩ <;>
  rw [e1] at h1 <;> rw [e2] at h2 <;> rw [e] <;>
  exact ⟨⟨fun _ => by linarith, fun _ => by linarith⟩, ⟨fun _ => by linarith, fun _ => by linarith⟩⟩

theorem tendsto_radius_zero : Tendsto radius atTop (𝓝 0) := by
  unfold radius
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem measurableSet_abs_lt {t : ℝ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    MeasurableSet {s : ℝ | f |s - t| < g |s - t|} :=
  measurableSet_lt (hf.comp (continuous_id.sub continuous_const).abs).measurable
    (hg.comp (continuous_id.sub continuous_const).abs).measurable

variable {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}

/-- **The region cut.** -/
theorem regionCut (hγ : 0 < γ) (hν : IsVagueLimitR (bdryApprox γ y) ν)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ y k)) (hat : ∀ s, ν {s} = 0)
    {t r : ℝ} (hr : 0 < r) :
    E1.M4.BCert γ (restrictField (circIn t r) y) ∧
      qBoundaryMeasure γ (restrictField (circIn t r) y) = ν.restrict (Ioo (t - r) (t + r)) := by
  refine bCert_and_eq_of_cut (isVagueLimitR_cut hγ hν hfin
    (A := fun k => {s | |s - t| + radius k < r}) (B := fun k => {s | r < |s - t| + radius k})
    (fun k => measurableSet_abs_lt (continuous_id.add continuous_const) continuous_const)
    (fun k => measurableSet_abs_lt continuous_const (continuous_id.add continuous_const))
    (fun k => bdryApprox_eq_cut γ
      (measurableSet_abs_lt (continuous_id.add continuous_const) continuous_const)
      (measurableSet_abs_lt continuous_const (continuous_id.add continuous_const))
      (disjoint_left.2 fun s (h1 : |s - t| + radius k < r) (h2 : r < |s - t| + radius k) =>
        lt_asymm h1 h2)
      (measure_mono_null (fun s hs => ?_) (volume_abs_sub_eq t (r - radius k)))
      (fun s hs => avgReg_region_in hs) (fun s hs => avgReg_region_out hs))
    (F := {t - r, t + r}) (fun p hp => hat p) measurableSet_Ioo ?_ ?_)
  · simp only [mem_compl_iff, mem_union, mem_setOf_eq, not_or, not_lt] at hs
    show |s - t| = r - radius k
    linarith [hs.1, hs.2]
  · rw [frontier_Ioo (by linarith)]
    simp
  · intro δ hδ
    filter_upwards [tendsto_radius_zero.eventually (gt_mem_nhds hδ)] with k hk s hs
    have h1 := hs (t - r) (by simp)
    have h2 := hs (t + r) (by simp)
    rw [mem_Ioo_iff_abs]
    exact (far_iff (radius_pos k).le hk h1 h2).1

/-- **The gap cut.** -/
theorem gapCut (hγ : 0 < γ) (hν : IsVagueLimitR (bdryApprox γ y) ν)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ y k)) (hat : ∀ s, ν {s} = 0)
    {t₁ r₁ t₂ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    E1.M4.BCert γ (restrictField (circOut t₁ r₁ t₂ r₂) y) ∧
      qBoundaryMeasure γ (restrictField (circOut t₁ r₁ t₂ r₂) y) =
        ν.restrict (Icc (t₁ - r₁) (t₁ + r₁) ∪ Icc (t₂ - r₂) (t₂ + r₂))ᶜ := by
  have hmA : ∀ k, MeasurableSet {s : ℝ | Miss t₁ r₁ (radius k) |s - t₁| ∧
      Miss t₂ r₂ (radius k) |s - t₂|} := fun k =>
    ((measurableSet_abs_lt continuous_const continuous_id).union
      (measurableSet_abs_lt (continuous_id.add continuous_const) continuous_const)).inter
    ((measurableSet_abs_lt continuous_const continuous_id).union
      (measurableSet_abs_lt (continuous_id.add continuous_const) continuous_const))
  have hmB : ∀ k, MeasurableSet {s : ℝ | Hit r₁ (radius k) |s - t₁| ∨
      Hit r₂ (radius k) |s - t₂|} := fun k =>
    ((measurableSet_abs_lt continuous_const continuous_id).inter
      (measurableSet_abs_lt continuous_id continuous_const)).union
    ((measurableSet_abs_lt continuous_const continuous_id).inter
      (measurableSet_abs_lt continuous_id continuous_const))
  refine bCert_and_eq_of_cut (isVagueLimitR_cut hγ hν hfin hmA hmB
    (fun k => bdryApprox_eq_cut γ (hmA k) (hmB k) ?_ ?_ (fun s hs => avgReg_gap_miss hs.1 hs.2)
      (fun s hs => avgReg_gap_hit hs))
    (F := {t₁ - r₁, t₁ + r₁, t₂ - r₂, t₂ + r₂}) (fun p _ => hat p)
    (measurableSet_Icc.union measurableSet_Icc).compl ?_ ?_)
  · refine disjoint_left.2 fun s hA hB => ?_
    obtain ⟨hA1, hA2⟩ := hA
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hA1 with h | h <;> linarith
    · rcases hA2 with h | h <;> linarith
  · refine measure_mono_null (t := ({s | |s - t₁| = r₁ + radius k} ∪
      {s | |s - t₁| = radius k - r₁}) ∪ ({s | |s - t₂| = r₂ + radius k} ∪
      {s | |s - t₂| = radius k - r₂})) (fun s hs => ?_)
      (measure_union_null (measure_union_null (volume_abs_sub_eq _ _) (volume_abs_sub_eq _ _))
        (measure_union_null (volume_abs_sub_eq _ _) (volume_abs_sub_eq _ _)))
    simp only [mem_compl_iff, mem_union, mem_setOf_eq, not_or, not_and_or, Miss, Hit,
      not_lt] at hs ⊢
    obtain ⟨hA, ⟨hB1, hB2⟩⟩ := hs
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rcases hB1 with h | h
      · right; linarith
      · left; linarith
    · right
      rcases hB2 with h | h
      · right; linarith
      · left; linarith
  · rw [frontier_compl]
    refine (frontier_union_subset _ _).trans ?_
    rw [frontier_Icc (by linarith), frontier_Icc (by linarith)]
    intro p hp
    simp only [mem_union, mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hp
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
    rcases hp with ⟨hp | hp, -⟩ | ⟨-, hp | hp⟩ <;> simp [hp]
  · intro δ hδ
    filter_upwards [tendsto_radius_zero.eventually (gt_mem_nhds hδ),
      tendsto_radius_zero.eventually (gt_mem_nhds hr₁),
      tendsto_radius_zero.eventually (gt_mem_nhds hr₂)] with k hk hk₁ hk₂ s hs
    have f1 := far_iff (radius_pos k).le hk (hs (t₁ - r₁) (by simp)) (hs (t₁ + r₁) (by simp))
    have f2 := far_iff (radius_pos k).le hk (hs (t₂ - r₂) (by simp)) (hs (t₂ + r₂) (by simp))
    have hρ := radius_pos k
    simp only [mem_compl_iff, mem_union, not_or, mem_Icc_iff_abs, not_le, Miss]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact ⟨f1.2.1 h1, f2.2.1 h2⟩
      · exact absurd h2 (by linarith [abs_nonneg (s - t₂)])
      · exact absurd h1 (by linarith [abs_nonneg (s - t₁)])
      · exact absurd h1 (by linarith [abs_nonneg (s - t₁)])
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl (f1.2.2 h1), Or.inl (f2.2.2 h2)⟩

end G3Fid
end Thm18Asm
end QuantumZipper
