/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrTopo
import InteractingSLE.Spec.Supplement.SB4RArc

/-!
# Sets and charts under the translation by `−v`

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). The set-level facts translating SB2(2)'s hypotheses
and outputs between the plane of the initial-arc leaf and the plane read from `v`:

* `rightSideOf_subset_of_restart`: the right side of the restarted walk `X` is inside the translated right side of
  the walk `W` when `W − v = [−v, 0] ∪ X`;
* `realMax_translate`: `max` of the translated history;
* `isRightEntryValue_of_trChart`: a right entry value in the translated chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lf

open FlowDilate Lx Lu

theorem aff_one (v : ℝ) (z : ℂ) : aff 1 v z = z + v := by simp [aff]

/-- **The right side of the restarted walk is inside the translated right side.** -/
theorem rightSideOf_subset_of_restart {W X : Set ℂ} {v : ℝ} (hv : 0 ≤ v)
    (hWX : (fun z => z - (v : ℂ)) '' W = ((↑) : ℝ → ℂ) '' Icc (-v) 0 ∪ X) :
    rightSideOf X ⊆ (fun z => z - (v : ℂ)) '' rightSideOf W := by
  have hτ : ∀ S : Set ℂ, aff 1 v '' S = (fun z => z + (v : ℂ)) '' S := fun S => by
    congr 1; funext z; exact aff_one v z
  have hWeq : W = (fun z => z + (v : ℂ)) '' (((↑) : ℝ → ℂ) '' Icc (-v) 0 ∪ X) := by
    rw [← hWX, Set.image_image]; simp
  have hHW : H \ W = aff 1 v '' (H \ X) := by
    rw [aff_image_diff_H one_pos, hτ, hWeq, Set.image_union]
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, not_or]
    constructor
    · rintro ⟨hz, -, h2⟩; exact ⟨hz, h2⟩
    · rintro ⟨hz, h2⟩
      refine ⟨hz, ?_, h2⟩
      rintro ⟨_, ⟨x, -, rfl⟩, hzx⟩
      have : z.im = 0 := by rw [← hzx]; simp
      exact absurd hz (by show ¬ 0 < z.im; rw [this]; exact lt_irrefl 0)
  have hreal : ∀ z : ℂ, z ∈ H → z ∉ ((↑) : ℝ → ℂ) '' Icc (-v) 0 := fun z hz ⟨y, _, hy⟩ => by
    have : z.im = 0 := by rw [← hy]; simp
    exact absurd hz (by show ¬ 0 < z.im; rw [this]; exact lt_irrefl 0)
  rintro z ⟨⟨hzH, hzX⟩, x, hx0, hxX, hxc⟩
  have hzv : z + v ∈ H := by
    show 0 < (z + (v : ℂ)).im
    rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hzH
  refine ⟨z + v, ⟨⟨hzv, fun hw => ?_⟩, x + v, by linarith, fun hw => ?_, ?_⟩, by simp⟩
  · have : z ∈ (fun z => z - (v : ℂ)) '' W := ⟨z + v, hw, by simp⟩
    rw [hWX] at this
    rcases this with h1 | h1
    · exact hreal z hzH h1
    · exact hzX h1
  · have : (x : ℂ) ∈ (fun z => z - (v : ℂ)) '' W := ⟨((x + v : ℝ) : ℂ), hw, by push_cast; ring⟩
    rw [hWX] at this
    rcases this with ⟨y, hy, hyx⟩ | h1
    · have : y = x := Complex.ofReal_injective hyx
      linarith [hy.2]
    · exact hxX h1
  · have hc := (FlowDilate.affHomeo (a := 1) (m := v) one_ne_zero).image_closure (connectedComponentIn (H \ X) z)
    change aff 1 v '' closure (connectedComponentIn (H \ X) z) =
      closure (aff 1 v '' connectedComponentIn (H \ X) z) at hc
    rw [hHW, show z + (v : ℂ) = aff 1 v z from (aff_one v z).symm, ← image_connectedComponentIn_aff one_ne_zero, ← hc]
    exact ⟨x, hxc, by rw [aff_one]; push_cast; ring⟩

/-! ### Real extremes and entry values -/

theorem realPts_translate (A : Set ℂ) (v : ℝ) :
    {x : ℝ | (x : ℂ) ∈ (fun z => z - (v : ℂ)) '' A} = (fun x => x - v) '' {x : ℝ | (x : ℂ) ∈ A} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨x + v, ?_, by ring⟩
    have : z = ((x + v : ℝ) : ℂ) := by rw [← sub_add_cancel z (v : ℂ), hzx]; push_cast; ring
    rwa [this] at hz
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by push_cast; ring⟩

/-- **The largest real point of a translated set.** -/
theorem realMax_translate {A : Set ℂ} (v : ℝ) (hne : {x : ℝ | (x : ℂ) ∈ A}.Nonempty)
    (hbdd : BddAbove {x : ℝ | (x : ℂ) ∈ A}) : realMax ((fun z => z - (v : ℂ)) '' A) = realMax A - v := by
  unfold realMax
  rw [realPts_translate]
  have := (OrderIso.addRight (-v)).map_csSup' hne hbdd
  simp only [OrderIso.addRight_apply, ← sub_eq_add_neg] at this
  rw [this]

/-- The real segment `[0, v]` below a real point `v` of a set does not change its largest real point. -/
theorem realMax_union_Icc {A : Set ℂ} {v : ℝ} (hvA : (v : ℂ) ∈ A) (hbdd : BddAbove {x : ℝ | (x : ℂ) ∈ A}) :
    realMax (A ∪ ((↑) : ℝ → ℂ) '' Icc 0 v) = realMax A := by
  unfold realMax
  have hne : {x : ℝ | (x : ℂ) ∈ A}.Nonempty := ⟨v, hvA⟩
  have hsub : {x : ℝ | (x : ℂ) ∈ A} ⊆ {x : ℝ | (x : ℂ) ∈ A ∪ ((↑) : ℝ → ℂ) '' Icc 0 v} := fun x hx => Or.inl hx
  have hle : ∀ x ∈ {x : ℝ | (x : ℂ) ∈ A ∪ ((↑) : ℝ → ℂ) '' Icc 0 v}, x ≤ sSup {x : ℝ | (x : ℂ) ∈ A} := by
    rintro x (hx | ⟨y, hy, hyx⟩)
    · exact le_csSup hbdd hx
    · have : y = x := Complex.ofReal_injective hyx
      exact (this ▸ hy.2).trans (le_csSup hbdd hvA)
  exact le_antisymm (csSup_le (hne.mono hsub) hle) (csSup_le_csSup ⟨_, hle⟩ hne hsub)

/-- **A right entry value read in the translated chart.** -/
theorem isRightEntryValue_of_trChart {c : Chart} {R e v : ℝ} (h : IsRightEntryValue (trChart v c) (R - v) e) :
    IsRightEntryValue c R e := by
  obtain ⟨f, hf, hfe⟩ := h
  refine ⟨fun x => f (x - v), fun x hx => ?_, ?_⟩
  · have h1 := hf (x - v) (by linarith)
    have h2 : Tendsto (fun z : ℂ => z - (v : ℂ)) (𝓝[H] (x : ℂ)) (𝓝[H] (((x - v : ℝ) : ℂ))) := by
      have := tendsto_aff_nhdsWithin_H (a := 1) (m := -v) one_pos (x : ℂ)
      have e1 : aff 1 (-v) = fun z => z - (v : ℂ) := by
        funext z; simp [aff, sub_eq_add_neg]
      have e2 : aff 1 (-v) (x : ℂ) = ((x - v : ℝ) : ℂ) := by simp [aff, sub_eq_add_neg]
      rw [e2, e1] at this
      exact this
    have h3 := h1.comp h2
    have e3 : (trChart v c).1 ∘ (fun z : ℂ => z - (v : ℂ)) = c.1 := by
      funext z; simp [trChart]
    rwa [e3] at h3
  · have h2 : Tendsto (fun x : ℝ => x - v) (𝓝[>] R) (𝓝[>] (R - v)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_sub_right v).tendsto R |>.mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with x (hx : R < x)
      show R - v < x - v
      linarith
    exact hfe.comp h2

end InteractingSLE.Theorem14.SB.Lf
