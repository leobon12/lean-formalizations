/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopPathSample
import InteractingSLE.Spec.Supplement.AStopProcEnds

/-!
# The chart is increasing along untouched real intervals

Packet PROVE-T15-ASTOP-PATH (the terminal case of item 6). `IsAMono ψ K`: along every real interval of chart points
whose images are off `K`, the real part of `ψ` is strictly increasing. Proved from the zone data:

* **`isAMono_of_setting`** (disjoint prefixes): the untouched chart points of one interval lie in one chart zone (the
  zone gaps `[L₂, R₂]`, `[L₁, R₁]` are over `K`, PROVE-T15-ASTOP-PROC's `aStopSet_zoneData`), the zone map `T` is
  strictly increasing on the original zone (`ZW.Good.mono₀/₁/₂`) and `T (Re ψ r) = r`;
* **`isAMono_of_touch`** (touching prefixes, `[L₂, R₁]` over `K`, `GoodT.mono₀/₂`);
* `IsAMono.shift` (charts translated by a real number); `IsOrdSample.isAMono_snd`, `IsOrdSample.isAMono_fst`.

With it, **`IsAChart.limits_of_mono`**: at an untouched real chart point the one-sided limits of an untouched word are
the one-sided limits of the original datum at the image point (including at an original jump).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE.RLC.AStopPath

open Supp7 Restart Sec7.Lemma76G RetTouch PiecewiseConstantBoundaryData OrdModel

/-- **The chart is increasing along untouched real intervals.** -/
def IsAMono (ψ : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ r₁ r₂ : ℝ, r₁ < r₂ → (∀ r ∈ Icc r₁ r₂, ψ r ∉ K) → (ψ r₁).re < (ψ r₂).re

theorem IsAMono.shift {ψ : ℂ → ℂ} {K : Set ℂ} (hM : IsAMono ψ K) (τ : ℝ) :
    IsAMono (fun z => ψ (z + τ)) K := by
  intro r₁ r₂ h12 hoff
  have e : ∀ r : ℝ, (r : ℂ) + (τ : ℂ) = ((r + τ : ℝ) : ℂ) := fun r => (ofReal_add r τ).symm
  simp only [e]
  refine hM _ _ (by linarith) fun r hr => ?_
  have h := hoff (r - τ) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  simp only [e, sub_add_cancel] at h
  exact h

/-! ### Disjoint prefixes -/

section Setting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

theorem mem_K_of_mem_zoneGap (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {r : ℝ}
    (hr : r ∈ Icc (zoneData φ α a β b).L₂ (zoneData φ α a β b).R₂ ∨
      r ∈ Icc (zoneData φ α a β b).L₁ (zoneData φ α a β b).R₁) :
    ψ r ∈ α '' Icc 0 a ∪ β '' Icc 0 b := by
  have hz := hs.zoneData_good
  have h2 : (zoneData φ α a β b).L₂ ≤ (zoneData φ α a β b).R₂ := hz.L₂_le.trans hz.M₂_le
  have h1 : (zoneData φ α a β b).L₁ ≤ (zoneData φ α a β b).R₁ := hz.L₁_le.trans hz.M₁_le
  have hmem : (r : ℂ) ∈ aStopSet ((zoneData φ α a β b).L₂, (zoneData φ α a β b).R₂, (zoneData φ α a β b).L₁,
      (zoneData φ α a β b).R₁) := by
    rcases hr with hr | hr
    · exact Or.inl ((AStopProc.mem_seg_iff h2).2 ⟨ofReal_im r, by simpa using hr.1, by simpa using hr.2⟩)
    · exact Or.inr ((AStopProc.mem_seg_iff h1).2 ⟨ofReal_im r, by simpa using hr.1, by simpa using hr.2⟩)
  rw [AStopProc.aStopSet_zoneData hs] at hmem
  exact hmem.2

/-- **Monotonicity of the chart along untouched intervals, disjoint prefixes.** -/
theorem isAMono_of_setting (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) :
    IsAMono ψ (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  intro r₁ r₂ h12 hoff
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  have hRL := hs.R₂_lt_L₁
  have hu : ∀ r : ℝ, ψ r ∉ α '' Icc 0 a ∪ β '' Icc 0 b →
      IsUntouched α a β b (ψ r).re ∧ z.T (ψ r).re = r := by
    intro r hr
    rcases hs.inv_cases r with h | h | h
    · exact absurd (Or.inl h) hr
    · exact absurd (Or.inr h) hr
    obtain ⟨-, hU, hT⟩ := hs.untouched_cases h
    exact ⟨hU, hT⟩
  obtain ⟨hU₁, hT₁⟩ := hu r₁ (hoff r₁ ⟨le_rfl, h12.le⟩)
  obtain ⟨hU₂, hT₂⟩ := hu r₂ (hoff r₂ ⟨h12.le, le_rfl⟩)
  have hgap : ∀ r, r₁ ≤ r → r ≤ r₂ → r ∉ Icc z.L₂ z.R₂ ∧ r ∉ Icc z.L₁ z.R₁ := fun r h1 h2 =>
    ⟨fun hr => hoff r ⟨h1, h2⟩ (mem_K_of_mem_zoneGap hs (Or.inl hr)),
      fun hr => hoff r ⟨h1, h2⟩ (mem_K_of_mem_zoneGap hs (Or.inr hr))⟩
  have hmono : ∀ {S : Set ℝ}, StrictMonoOn z.T S → (ψ r₁).re ∈ S → (ψ r₂).re ∈ S → (ψ r₁).re < (ψ r₂).re := by
    intro S hS h1 h2
    by_contra hle
    push Not at hle
    have := hS.monotoneOn h2 h1 hle
    rw [hT₁, hT₂] at this
    linarith
  have hL₂R₂ : z.L₂ ≤ z.R₂ := hz.L₂_le.trans hz.M₂_le
  have hL₁R₁ : z.L₁ ≤ z.R₁ := hz.L₁_le.trans hz.M₁_le
  rcases (hs.isUntouched_iff _).1 hU₁ with a₁ | a₁ | a₁ <;> rcases (hs.isUntouched_iff _).1 hU₂ with b₁ | b₁ | b₁
  · exact hmono hz.mono₀ a₁ b₁
  · have h1 := hz.T₀_lt _ a₁
    have h2 := hz.lt_T₁ _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    exact absurd ⟨le_rfl, hL₂R₂⟩ (hgap z.L₂ h1.le (hL₂R₂.trans h2.le)).1
  · have h1 := hz.T₀_lt _ a₁
    have h2 := hz.lt_T₂ _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    exact absurd ⟨le_rfl, hL₂R₂⟩ (hgap z.L₂ h1.le (by linarith)).1
  · have h1 := hz.lt_T₁ _ a₁
    have h2 := hz.T₀_lt _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    linarith
  · exact hmono hz.mono₁ a₁ b₁
  · have h1 := hz.T₁_lt _ a₁
    have h2 := hz.lt_T₂ _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    exact absurd ⟨le_rfl, hL₁R₁⟩ (hgap z.L₁ h1.le (hL₁R₁.trans h2.le)).2
  · have h1 := hz.lt_T₂ _ a₁
    have h2 := hz.T₀_lt _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    linarith
  · have h1 := hz.lt_T₂ _ a₁
    have h2 := hz.T₁_lt _ b₁
    rw [hT₁] at h1
    rw [hT₂] at h2
    linarith
  · exact hmono hz.mono₂ a₁ b₁

end Setting

/-! ### Touching prefixes -/

section Touch

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW}

/-- **Monotonicity of the chart along untouched intervals, touching prefixes.** -/
theorem isAMono_of_touch (ht : IsTouchZones α a β b ψ z) : IsAMono ψ (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  intro r₁ r₂ h12 hoff
  have hz := ht.good
  have hL₂R₁ : z.L₂ ≤ z.R₁ := ht.L₂_lt_R₁.le
  have hzone : ∀ r : ℝ, ψ r ∉ α '' Icc 0 a ∪ β '' Icc 0 b →
      ((ψ r).re < z.a₂ ∧ z.T (ψ r).re = r ∧ r < z.L₂) ∨ (z.b₁ < (ψ r).re ∧ z.T (ψ r).re = r ∧ z.R₁ < r) := by
    intro r hr
    rcases ht.lt_or_gt_of_notMem hr with h | h
    · obtain ⟨-, h1, h2⟩ := ht.zone₀ r h
      exact Or.inl ⟨h1, h2, h⟩
    · obtain ⟨-, h1, h2⟩ := ht.zone₂ r h
      exact Or.inr ⟨h1, h2, h⟩
  have hgap : ψ (z.L₂ : ℂ) ∈ α '' Icc 0 a ∪ β '' Icc 0 b := Or.inr ht.L₂_mem
  have hmono : ∀ {S : Set ℝ}, StrictMonoOn z.T S → (ψ r₁).re ∈ S → (ψ r₂).re ∈ S →
      z.T (ψ r₁).re = r₁ → z.T (ψ r₂).re = r₂ → (ψ r₁).re < (ψ r₂).re := by
    intro S hS h1 h2 hT₁ hT₂
    by_contra hle
    push Not at hle
    have := hS.monotoneOn h2 h1 hle
    rw [hT₁, hT₂] at this
    linarith
  rcases hzone r₁ (hoff r₁ ⟨le_rfl, h12.le⟩) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    rcases hzone r₂ (hoff r₂ ⟨h12.le, le_rfl⟩) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩
  · exact hmono hz.mono₀ a1 b1 a2 b2
  · exact absurd hgap (hoff z.L₂ ⟨a3.le, hL₂R₁.trans b3.le⟩)
  · linarith
  · exact hmono hz.mono₂ a1 b1 a2 b2

end Touch


/-! ### At an ordinary sample -/

namespace IsOrdSample

variable {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω} {ω : Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {x₁ x₂ : ℝ} (hd : d.IsMeasGood) (hS : IsOrdSample d η₁ η₂ ζ₁ ζ₂ x₁ x₂ ω)
include hd hS

theorem isAMono_snd : IsAMono (d.inv ω) (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) := by
  by_cases hdis : Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)
  · have hx : x₂ < x₁ := by
      refine lt_of_le_of_ne hS.x fun he => Set.disjoint_left.1 hdis
        ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₁⟩ ?_
      rw [← he]
      exact ⟨0, ⟨le_rfl, zero_le⟩, Sec7.IsPathGood.zero hS.p₂⟩
    have hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r :=
      ⟨hS.ord.1, hS.ord.2.1, hS.ord.2.2.2.1, hdis, hS.ord.2.2.2.2.2.2.2.1, hS.ord.2.2.2.2.2.2.1⟩
    obtain ⟨-, hs⟩ := RetAux79.isSetting_of_retData hd hS.G hS.p₁ hS.p₂ hx hS.a₁ hS.a₂ hpair
    exact isAMono_of_setting hs
  · exact isAMono_of_touch
      (RLC.Aux85.retTouchZonesStatement _ _ _ _ _ _ _ _ _ _ _ hS.p₁ hS.p₂ hS.x hS.ord hdis (hS.chart hd))

theorem isAMono_fst :
    IsAMono (fun w => d.inv ω (w + tipPos d η₁ ω)) (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) :=
  (hS.isAMono_snd hd).shift _

end IsOrdSample

/-! ### One-sided limits of an untouched word -/

/-- **One-sided limits of an untouched word at an untouched real chart point** are those of the original datum at the
image point (the chart is increasing there). -/
theorem IsAChart.limits_of_mono {ψ : ℂ → ℂ} {K : Set ℂ} {x : ℝ} (hA : IsAChart ψ K x) (hM : IsAMono ψ K)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {c : BoundaryWord}
    (hu : IsUntouchedWord b jumps K ψ c) {w : ℝ} (hw : ψ w ∉ K) :
    leftLim c.fn w = leftLim b (ψ w).re ∧ rightLim c.fn w = rightLim b (ψ w).re := by
  set y := (ψ w).re with hydef
  have hm : Continuous fun r : ℝ => (ψ r).re := Complex.continuous_re.comp hA.continuous_real
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hA.isOpen_off.mem_nhds hw)
  have hoff : ∀ r : ℝ, w - ε < r → r < w + ε → ψ r ∉ K := fun r h1 h2 =>
    hball (by rw [Real.ball_eq_Ioo]; exact ⟨h1, h2⟩)
  constructor
  · obtain ⟨a, -, hay, haJ, hcut⟩ := FlowStopIdentLL.exists_left_cut isOpen_univ (mem_univ y) jumps
    have hJ : ∀ z ∈ Ioo a y, z ∉ jumps := fun z hz hzJ => (not_le_of_gt hz.2) ((hcut z hzJ).1 hz.1)
    have hbz : ∀ z ∈ Ioo a y, b z = b a := fun z hz =>
      Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.1.le fun v hv => by
        rcases eq_or_lt_of_le hv.1 with h | h
        · rw [← h]; exact haJ
        · exact hJ v ⟨h, hv.2.trans_lt hz.2⟩
    rw [Sec4.leftLim_eq_of_forall hay hbz]
    have hev : ∀ᶠ t in 𝓝[<] w, b a = c.fn t := by
      filter_upwards [nhdsWithin_le_nhds ((hm.tendsto w).eventually (lt_mem_nhds hay)),
        Ioo_mem_nhdsLT (show w - ε < w by linarith)] with t ht1 ht2
      have hoff' : ∀ r ∈ Icc t w, ψ r ∉ K := fun r hr => hoff r (by linarith [ht2.1, hr.1]) (by linarith [hr.2])
      have hin : (ψ t).re ∈ Ioo a y := ⟨ht1, hM t w ht2.2 hoff'⟩
      have hU := hu t (hA.real t (hoff' t ⟨le_rfl, ht2.2.le⟩)) (hoff' t ⟨le_rfl, ht2.2.le⟩) (hJ _ hin)
      rw [hU.2, hbz _ hin]
    exact (tendsto_const_nhds.congr' hev).limUnder_eq
  · obtain ⟨a, -, hya, haJ, hcut⟩ := FlowStopIdentLL.exists_right_cut isOpen_univ (mem_univ y) jumps
    have hJ : ∀ z ∈ Ioo y a, z ∉ jumps := fun z hz hzJ => (not_le_of_gt hz.1) ((hcut z hzJ).1 hz.2.le)
    have hbz : ∀ z ∈ Ioo y a, b z = b a := fun z hz =>
      (Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb hz.2.le fun v hv => by
        rcases eq_or_lt_of_le hv.2 with h | h
        · rw [h]; exact haJ
        · exact hJ v ⟨hz.1.trans_le hv.1, h⟩).symm
    rw [Sec4.rightLim_eq_of_forall hya hbz]
    have hev : ∀ᶠ t in 𝓝[>] w, b a = c.fn t := by
      filter_upwards [nhdsWithin_le_nhds ((hm.tendsto w).eventually (gt_mem_nhds hya)),
        Ioo_mem_nhdsGT (show w < w + ε by linarith)] with t ht1 ht2
      have hoff' : ∀ r ∈ Icc w t, ψ r ∉ K := fun r hr => hoff r (by linarith [hr.1]) (by linarith [ht2.2, hr.2])
      have hin : (ψ t).re ∈ Ioo y a := ⟨hM w t ht2.1 hoff', ht1⟩
      have hU := hu t (hA.real t (hoff' t ⟨ht2.1.le, le_rfl⟩)) (hoff' t ⟨ht2.1.le, le_rfl⟩) (hJ _ hin)
      rw [hU.2, hbz _ hin]
    exact (tendsto_const_nhds.congr' hev).limUnder_eq

end InteractingSLE.RLC.AStopPath
