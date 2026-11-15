/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RLower

/-!
# SB4's sewing geometry for a general retained history; the initial-arc history

Packet PROVE-T14-SB4LEAF. `Lf.ae_relTailGeometry_of_lift` builds SB4's conditional sewing geometry for the
distinct-seed history `upperPrefix` (the bridge `[u, 0]` and the schedule from `u ≤ 0`). Here the same construction is
stated for any retained history given as a path from `0` (`ae_relTailGeometry_of_path`), and the initial-arc history
of SB4's last paragraph (supplement p. 635: "For a connector seed `v`, retain the lower prefix through `v`") is
introduced: the schedule history from a seed `v > 0` on the lower walk's initial forced arc, with the arc `[0, v]`.

* `inter_rightSideOf_union_real`: real points add no point of a right side;
* `subset_closedLeftSide_of_avoid'` (a general retained part on the closed left);
* **`ae_relTailGeometry_of_path`**;
* `arcPrefix`, `exists_path_arcPrefix`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule GW1P

/-- Real points add no point of a right side (`rightSideOf` lies in `ℍ`). -/
theorem inter_rightSideOf_union_real {X B : Set ℂ} {T : Set ℝ} (h : X ∩ rightSideOf B = ∅) :
    (X ∪ ((↑) : ℝ → ℂ) '' T) ∩ rightSideOf B = ∅ := by
  rw [union_inter_distrib_right, h, empty_union]
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨⟨y, -, hy⟩, hz⟩ := hz
  have := hz.1.1
  rw [← hy] at this
  exact absurd (show (0 : ℝ) < ((y : ℂ)).im from this) (by simp)

/-- **A retained history adherent to its interior points and to a part `Y` on the closed left, avoiding the right
side of a proper curve, is on its closed left.** -/
theorem subset_closedLeftSide_of_avoid' {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    {X Y : Set ℂ} (hcl : X ⊆ closure (X ∩ H) ∪ Y) (hY : Y ⊆ closedLeftSide β₀)
    (havoid : X ∩ rightSideOf (range β₀) = ∅) : X ∪ Y ⊆ closedLeftSide β₀ := by
  have hXH : X ∩ H ⊆ closedLeftSide β₀ := fun z hz =>
    mem_closedLeftSide_of_notMem_rightSideOf hβ hβ0 hz.2 fun hR =>
      (Set.eq_empty_iff_forall_notMem.1 havoid) z ⟨hz.1, hR⟩
  have hcl' : closure (X ∩ H) ⊆ closedLeftSide β₀ :=
    closure_minimal hXH (Theorem15D5.isClosed_closedLeftSide (isClosed_seedRayClosure hβ))
  rintro z (hz | hz)
  · rcases hcl hz with h | h
    · exact hcl' h
    · exact hY h
  · exact hY hz

/-- **SB4's S1-free conditional sewing geometry for a retained history given as a path from `0`.** Under a probability
`Q` with the actual flow driver of the new piece: the history `A = p([0, 1])`, its recentred launch chart `c − (−m)`
a right entry chart at `R = max (A ∩ ℝ)`, the launch readout `f` with the readout of the new piece; and, `Q`-almost
surely, a proper parametrization of the lower walk `B` from `0`, the lift of its tail to `Wrel` with a free collar,
`A` on its closed left, and the forbidden side `S` in its right side. -/
theorem ae_relTailGeometry_of_path (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {A : Set ℂ} {pA : ℝ → ℂ}
    (hp : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im)
    (hpA : pA '' Icc 0 1 = A) {c : Chart} (hcc : c.IsConformal) {m : ℝ} (hm : m ≤ 0)
    (hrc : IsRightEntryChart A (realMax A) (c.recenter (-m))) {f : ℂ → ℂ}
    (hf : ∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z))) (hfc : ContinuousOn f Hbar)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {θ : ℝ} {hl : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b' J' θ Q hl W ζ) {Apiece S B Wrel : Ω → Set ℂ} {T : ℝ≥0∞}
    (hread : ∀ᵐ ω ∂Q, Apiece ω ⊆ f '' (GW2aSingle.chosenTrace W ζ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min T (ζ ω)}))
    (hβ : ∀ᵐ ω ∂Q, ∃ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ ∧ β₀ 0 = 0 ∧ range β₀ = B ω)
    (hlift : ∀ᵐ ω ∂Q, (∃ y : ℝ, y < 0 ∧ y < realMin A ∧ (y : ℂ) ∉ B ω) ∧
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = B ω → IsTailLiftOf c (realMax A) m β₀ (Wrel ω))
    (hAL : ∀ᵐ ω ∂Q, ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = B ω → A ⊆ closedLeftSide β₀)
    (hS : ∀ᵐ ω ∂Q, S ω ⊆ rightSideOf (B ω)) :
    ∀ᵐ ω ∂Q, HasRelTailGeometry (Apiece ω) (S ω) (Wrel ω) m
      (fun t => aff 1 m (GW2aSingle.chosenTrace W ζ ω t)) (ζ ω) := by
  have hframe : ∀ᵐ ω ∂Q, Retain.RetainedTailFrame f (S ω) (Wrel ω) m := by
    filter_upwards [hβ, hlift, hAL, hS] with ω hβω hliftω hALω hSω
    obtain ⟨β₀, hβ₀, hβ₀0, hβ₀r⟩ := hβω
    obtain ⟨⟨y, hy0, hyA, hyB⟩, hlt⟩ := hliftω
    obtain ⟨tL, γ, htL, hγ, hγ0, hγW, hγl⟩ := hlt β₀ hβ₀ hβ₀0 hβ₀r
    exact retainedTailFrame_of_lift hp hp0 hpH hpA hcc hrc hf hfc hm hβ₀ hβ₀0 (hALω β₀ hβ₀ hβ₀0 hβ₀r) htL
      ⟨y, hy0, hyA, by rw [hβ₀r]; exact hyB⟩ hγ hγ0 hγW hγl (by rw [hβ₀r]; exact hSω)
  exact Retain.ae_relTailGeometry_of_frame_readout h13 hκ hfl hread hframe

/-! ### The initial-arc history -/

/-- **The retained history of SB4's initial-arc case**: the schedule `l` from the seed `v` through `k` instructions,
with the lower walk's initial arc `[0, v]` ("retain the lower prefix through `v`", p. 635). -/
def arcPrefix {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (v : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω : Ω) : Set ℂ :=
  prefixPhysSet κ b jumps (sspec v l) (fun j => E (sspec v l) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc 0 v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The initial-arc history is a path from `0`**: the arc from `0` to `v`, followed by the schedule path from `v`.
Every point of the schedule history off the arc is a limit of its points in `ℍ`. -/
theorem exists_path_arcPrefix {v : ℝ} (hv : 0 ≤ v) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (sspec v l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (sspec v l) k) (D k).2)) (k : ℕ) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      p '' Icc 0 1 = SB.prefixPhysSet κ b jumps (sspec v l) D k ∪ ((↑) : ℝ → ℂ) '' Icc 0 v ∧
      SB.prefixPhysSet κ b jumps (sspec v l) D k ⊆
        closure (SB.prefixPhysSet κ b jumps (sspec v l) D k ∩ H) ∪ ((↑) : ℝ → ℂ) '' Icc 0 v := by
  obtain ⟨x, Γ, hrange, him, hcl, -⟩ := exists_path_schedule_seed (κ := κ) (b := b) (jumps := jumps) v l D hreg k
  let B : Path (0 : ℂ) (v : ℂ) :=
    { toFun := fun s => (((s : ℝ) * v : ℝ) : ℂ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hBrange : range B = ((↑) : ℝ → ℂ) '' Icc 0 v := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨(s : ℝ) * v, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [s.2.1, s.2.2]
      · nlinarith [s.2.1, s.2.2]
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      rcases hv.lt_or_eq with hv' | rfl
      · refine ⟨⟨y / v, div_nonneg hy1 hv'.le, (div_le_one hv').2 hy2⟩, ?_⟩
        change (((y / v) * v : ℝ) : ℂ) = (y : ℂ)
        rw [div_mul_cancel₀ _ hv'.ne']
      · have : y = 0 := le_antisymm hy2 hy1
        exact ⟨0, by simp [B, this]⟩
  set P : Path (0 : ℂ) x := B.trans Γ with hP
  have himg : P.extend '' Icc 0 1 = range P := P.image_extend_of_subset subset_rfl
  have hPrange : range P = SB.prefixPhysSet κ b jumps (sspec v l) D k ∪ ((↑) : ℝ → ℂ) '' Icc 0 v := by
    rw [hP, Path.trans_range, hBrange, hrange, union_comm]
  have hv0 : (v : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc 0 v := ⟨v, ⟨hv, le_rfl⟩, rfl⟩
  refine ⟨P.extend, P.continuous_extend.continuousOn, P.extend_zero, fun s hs => ?_, by rw [himg, hPrange],
    fun z hz => ?_⟩
  · have hz : P.extend s ∈ range P := himg ▸ mem_image_of_mem _ hs
    rw [hPrange] at hz
    rcases hz with hz | ⟨y, -, hy⟩
    · exact him _ (hrange ▸ hz)
    · rw [← hy]; simp
  · rw [← hrange] at hz
    rcases hcl hz with h | h
    · exact Or.inl (hrange ▸ h)
    · rw [mem_singleton_iff] at h
      exact Or.inr (h ▸ hv0)

end InteractingSLE.Theorem14.SB.Lf
