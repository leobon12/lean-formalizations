/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtTail
import InteractingSLE.Spec.Supplement.SB2JyHull
import InteractingSLE.Spec.Supplement.SB2JyTip

/-!
# Zero lifetime together: a relative piece lifting a positive actual piece has positive lifetime

Packet PROVE-T14-SB2LIFT (round 28; LIFTSET's item 4). The relative fields of the run inputs (`trLift` at a stage
whose actual piece has positive lifetime) and PROVE-SB2-LCMEAN's zero clause need: a relative piece that is the lift
of an actual piece of positive lifetime has positive lifetime.

* **`subsingleton_tipSet_zero`**: a piece of lifetime `0` has at most one point (its tip set is the set of limits of
  one function along `𝓝[>] 0`);
* **`two_tail_points`**: a launched actual piece of positive lifetime with dense good times has two distinct points on
  the tail of `β₀` (two good times, injectivity of the piece's point map `pcPt_injOn_launch`, the tail position of its
  part in the upper domain `tail_of_launch`);
* **`pos_of_liftRel`**: hence the lift image has two points, so the relative piece is not of lifetime `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep

/-- **A piece of lifetime `0` has at most one point.** -/
theorem subsingleton_tipSet_zero (c : Chart) (W : ℝ≥0 → ℝ) : (c.tipSet W 0).Subsingleton := by
  rintro z ⟨t, ht, hz⟩ w ⟨t', ht', hw⟩
  have h0 : t = 0 := by exact_mod_cast le_antisymm ht bot_le
  have h0' : t' = 0 := by exact_mod_cast le_antisymm ht' bot_le
  subst h0 h0'
  exact tendsto_nhds_unique hz hw

/-- The tip set of a recorded piece of relative lifetime `0` is a subsingleton. -/
theorem subsingleton_tipSet_newPc {s : ExplState} {e : Drv} (h0 : e.2 = 0) :
    ((newPc s e).1.tipSet (newPc s e).2.1 (newPc s e).2.2).Subsingleton := by
  have : (newPc s e).2.2 = 0 := by simp [newPc, h0]
  rw [this]
  exact subsingleton_tipSet_zero _ _

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv} {n : ℕ} {c : Chart} {A : Set ℂ}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **Two distinct tail points** of a launched actual piece of positive lifetime with dense good times. -/
theorem two_tail_points (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)))
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A) :
    ∃ s₁ s₂ : ℝ≥0, s₁ ≠ s₂ ∧
      β₀ (tL + s₁) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∧
      β₀ (tL + s₂) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hinj := pcPt_injOn_launch hP hW hl
  have htail := tail_of_launch hl hβr hK hDom
  -- a positive time before the lifetime
  obtain ⟨τ, hτ0, hτL⟩ : ∃ τ : ℝ≥0, 0 < τ ∧ (τ : ℝ≥0∞) < (D n).2 := by
    obtain ⟨q, hq0, hqL⟩ := exists_between (pos_iff_ne_zero.2 hpos)
    have hqt : q ≠ ⊤ := ne_top_of_lt hqL
    refine ⟨q.toNNReal, ?_, by rwa [ENNReal.coe_toNNReal hqt]⟩
    exact ENNReal.toNNReal_pos (ne_of_gt hq0) hqt
  have hopen : ∀ a a' : ℝ≥0, a' ≤ τ → IsOpen (Ioo a a') := fun a a' _ => isOpen_Ioo
  -- a good time in each half of `(0, τ)`
  have hgood : ∀ a a' : ℝ≥0, a < a' → a' ≤ τ → ∃ t ∈ goodT c s (D n), t ∈ Ioo a a' := by
    intro a a' haa' ha'
    have hmid : (a + a') / 2 ∈ Ioo a a' := ⟨by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; rw [mul_two]; exact add_lt_add_of_le_of_lt le_rfl haa', by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; rw [mul_two]; exact add_lt_add_of_lt_of_le haa' le_rfl⟩
    have hmL : (((a + a') / 2 : ℝ≥0) : ℝ≥0∞) < (D n).2 :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hmid.2.le.trans ha')) hτL
    obtain ⟨t, ht, htmem⟩ := mem_closure_iff.1 (hgd hmL) _ (hopen a a' ha') hmid
    exact ⟨t, htmem, ht⟩
  obtain ⟨t₁, hg₁, ht₁⟩ := hgood 0 (τ / 2) (by positivity) (by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; exact le_mul_of_one_le_right (zero_le) (by norm_num))
  obtain ⟨t₂, hg₂, ht₂⟩ := hgood (τ / 2) τ (by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; exact lt_mul_of_one_lt_right hτ0 (by norm_num)) le_rfl
  have hne : t₁ ≠ t₂ := ne_of_lt (ht₁.2.trans ht₂.1)
  have hlt : ∀ t : ℝ≥0, t < τ → (t : ℝ≥0∞) < (D n).2 := fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.le) hτL
  have hp₁ : (t₁ : ℝ≥0∞) < (D n).2 := hlt t₁ (ht₁.2.trans_le (by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; exact le_mul_of_one_le_right zero_le (by norm_num)))
  have hp₂ : (t₂ : ℝ≥0∞) < (D n).2 := hlt t₂ ht₂.2
  have hpne : pcPt s (D n) t₁ ≠ pcPt s (D n) t₂ := fun h => hne (hinj hp₁ hp₂ h)
  have hmemT : ∀ t ∈ goodT c s (D n), pcPt s (D n) t ∈ (newPc s (D n)).1.tipSet (newPc s (D n)).2.1
      (newPc s (D n)).2.2 := fun t ht => by rw [htip]; exact ⟨t, ht.1, rfl⟩
  have hmemD : ∀ t ∈ goodT c s (D n), pcPt s (D n) t ∈ β₀ '' Ici tL := fun t ht =>
    htail ⟨hmemT t ht, ht.2⟩
  obtain ⟨x₁, hx₁, hx₁e⟩ := hmemD t₁ hg₁
  obtain ⟨x₂, hx₂, hx₂e⟩ := hmemD t₂ hg₂
  have e₁ : tL + (x₁ - tL) = x₁ := add_tsub_cancel_of_le (show tL ≤ x₁ from hx₁)
  have e₂ : tL + (x₂ - tL) = x₂ := add_tsub_cancel_of_le (show tL ≤ x₂ from hx₂)
  refine ⟨x₁ - tL, x₂ - tL, fun h => hpne ?_, ?_, ?_⟩
  · rw [← hx₁e, ← hx₂e, ← e₁, ← e₂, h]
  · rw [e₁, hx₁e]; exact hmemT t₁ hg₁
  · rw [e₂, hx₂e]; exact hmemT t₂ hg₂

/-- **Zero lifetime together**: the lift of a launched actual piece of positive lifetime (dense good times) is not a
piece of lifetime `0`. -/
theorem pos_of_liftRel (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)))
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A) (hγ : Function.Injective γ)
    {s₂ : ExplState} {e₂ : Drv}
    (hL : LiftRel β₀ tL γ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (newPc s₂ e₂)) : e₂.2 ≠ 0 := by
  intro h0
  obtain ⟨s₁, s₂', hne, h₁, h₂⟩ := two_tail_points hP hW hl hpos hgd hβr hK hDom
  have hsub := subsingleton_tipSet_newPc (s := s₂) h0
  have hL' : (newPc s₂ e₂).1.tipSet (newPc s₂ e₂).2.1 (newPc s₂ e₂).2.2 = liftImage β₀ tL γ _ := hL
  rw [hL'] at hsub
  exact hne (hγ (hsub ⟨s₁, h₁, rfl⟩ ⟨s₂', h₂, rfl⟩))

end InteractingSLE.Theorem14.SB.Mn
