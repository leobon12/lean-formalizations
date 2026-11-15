/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LpAE
import InteractingSLE.Spec.Supplement.SB2LuRange

/-!
# The connector form of `tail`

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle of handoff §R29.3). `ClauseT`'s field `tail` ("every real
point of the actual tail after its visit to `R` is `≥ R`") is false (handoff §R29.1: the lower walk can touch the real
line left of `0` mid-piece). The lockstep chain reads it only through `liftImage_ofReal`, at points of connectors.
This file states the connector form and the base lemmas taking it:
* **`ArcPt`**: a real point of some connector of the run; **`TailArc`**: the real points of the tail after `t_L` that
  are connector points are `≥ R`; `TailArc.of_mem`: its form at one connector;
* **`liftImage_ofRealW`**, **`liftImage_start_arcW`**: `liftImage_ofReal` and `liftImage_start_arc` with `tail` read
  only on the connector;
* **`CurveInputsW`**: `CurveInputs` with `TailArc` as its tail field;
* **`start_arc_physW`**: `start_arc_phys`, also recording the connector appended at the start.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **A connector point of the right walk run**: a real point of a connector recorded at some stage. -/
def ArcPt (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) : Prop :=
  ∃ n, ∃ a ∈ (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1, x ∈ a

/-- **The connector form of `tail`**: the real points of `β₀` after `t_L` that are connector points are `≥ R`. -/
def TailArc (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (R : ℝ) (β₀ : ℝ≥0 → ℂ)
    (tL : ℝ≥0) : Prop :=
  ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → ArcPt κ θ b J D x → R ≤ x

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- `TailArc` at one connector of the run. -/
theorem TailArc.of_mem {D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (h : TailArc κ θ b₁ J₁ D₁ R β₀ tL) {n : ℕ} {a : Set ℝ}
    (ha : a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n).2.1) :
    ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → x ∈ a → R ≤ x :=
  fun s x hx hxa => h s x hx ⟨n, a, ha, hxa⟩

/-- The full `tail` gives its connector form. -/
theorem tailArc_of_tail {D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (h : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x) :
    TailArc κ θ b₁ J₁ D₁ R β₀ tL :=
  fun s x hx _ => h s x hx

/-- **The lift image of a real connector** (`liftImage_ofReal` with `tail` read only on the connector). -/
theorem liftImage_ofRealW (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0) (hι0 : ι R = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) {a : Set ℝ}
    (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → x ∈ a → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (ha : ∀ x ∈ a, R ≤ x → (x : ℂ) ∈ range β₀) :
    liftImage β₀ tL γ (((↑) : ℝ → ℂ) '' a) = ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) := by
  ext z
  constructor
  · rintro ⟨s, ⟨x, hxa, hx⟩, rfl⟩
    have hRx : R ≤ x := htail s x hx.symm hxa
    rcases eq_or_lt_of_le hRx with hxR | hxR
    · have hs : s = 0 := eq_zero_of_tail_eq hβ (by rw [← hx, hβL, hxR])
      subst hs
      exact ⟨ι x, ⟨x, ⟨hxa, hRx⟩, rfl⟩, by rw [hγ0, ← hxR, hι0, Complex.ofReal_zero]⟩
    · exact ⟨ι x, ⟨x, ⟨hxa, hRx⟩, rfl⟩, (hray s x hxR hx.symm).symm⟩
  · rintro ⟨_, ⟨x, ⟨hxa, hRx⟩, rfl⟩, rfl⟩
    have hRx : R ≤ x := hRx
    obtain ⟨t, ht⟩ := ha x hxa hRx
    have htL : tL ≤ t := by
      by_contra hlt
      push Not at hlt
      have hxR : x ≤ R := hhead t hlt.le x ht
      have hxR' : x = R := le_antisymm hxR hRx
      rw [hxR', ← hβL] at ht
      exact absurd (hβ ht) hlt.ne
    obtain ⟨s, rfl⟩ : ∃ s, t = tL + s := ⟨t - tL, (add_tsub_cancel_of_le htL).symm⟩
    refine ⟨s, ⟨x, hxa, ht.symm⟩, ?_⟩
    rcases eq_or_lt_of_le hRx with hxR | hxR
    · have hs : s = 0 := eq_zero_of_tail_eq hβ (by rw [ht, hβL, hxR])
      subst hs
      rw [hγ0, ← hxR, hι0, Complex.ofReal_zero]
    · exact hray s x hxR ht

/-- **The start part when `R` lies on an actual connector `a`** (`liftImage_start_arc` with `tail` read only on the
connector). -/
theorem liftImage_start_arcW (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0) (hι0 : ι R = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) {a : Set ℝ}
    (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → x ∈ a → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x) {P₀ : Set ℂ} (hP₀ : P₀ ⊆ β₀ '' Iic tL)
    (hRa : R ∈ a) (ha : ∀ x ∈ a, R ≤ x → (x : ℂ) ∈ range β₀) :
    liftImage β₀ tL γ (P₀ ∪ ((↑) : ℝ → ℂ) '' a) = {0} ∪ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) := by
  rw [liftImage_union, liftImage_ofRealW hβ hβL hγ0 hι0 hhead htail hray ha]
  have h0 : (0 : ℂ) ∈ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) :=
    ⟨ι R, ⟨R, ⟨hRa, mem_Ici.2 le_rfl⟩, rfl⟩, by rw [hι0, Complex.ofReal_zero]⟩
  have hP := liftImage_subset_of_head (γ := γ) hβ hP₀
  rw [hγ0] at hP
  refine Subset.antisymm (union_subset (hP.trans subset_union_left) subset_union_right)
    (union_subset ?_ subset_union_right)
  rw [singleton_subset_iff]
  exact Or.inr h0

/-- **The curve inputs with the connector form of `tail`** (`CurveInputs` with `TailArc`). -/
structure CurveInputsW (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop where
  range_eq : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  inj : Function.Injective β₀
  visit : β₀ tL = R
  lift_zero : γ 0 = 0
  head : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R
  tail : TailArc κ θ b₁ J₁ D₁ R β₀ tL
  ray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x

/-- **The starting stage on an actual connector, with the physical parts** (`start_arc_phys`), also recording that
the connector `a` is the one appended at the step. -/
theorem start_arc_physW (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hn : n < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hodd : n % 2 = 1)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) none true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ)
    (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0) :
    ∃ a : Set ℝ, R ∈ a ∧
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) ∧
      statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)) =
        statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ∪ ((↑) : ℝ → ℂ) '' a ∧
      statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) =
        {0} ∪ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) ∧
      a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.1 := by
  obtain ⟨hc, a, ha₁, ha₂⟩ := stCorr_start_arc h hn hodd hmove hθ hpt hrec hgap hlow hreg h0
  obtain ⟨a', hRa', ha'⟩ := exists_arc_mem_of_move hmove hpt hgap
  have hmem : a ∈ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.1 := by
    rw [ha₁]
    exact List.mem_append_right _ (List.mem_singleton_self a)
  have hrun₁ : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) =
      ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) none true :=
    run_succ_walk_cont hn hodd
  have haa : a = a' := by
    rw [hrun₁] at ha₁
    have := ha₁.symm.trans ha'
    simpa using this
  subst haa
  refine ⟨a, hRa', hc, ?_, ?_, hmem⟩
  · rw [statePhysicalSet_append (t := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (Y := [])
      (by rw [hrun₁, contStep_pieces, List.append_nil]) ha₁]
    simp
  · have hp₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2).1 =
        (ExplState.init 0).1 ++ [newPc (ExplState.init 0) (D₂ 0)] := by
      rw [run_succ_walk_cont (by have := one_lt_length_boundaryWalkSpec b₂ J₂ θ true; omega) (by norm_num),
        contStep_pieces, run_one_walk, launch_pieces]
      rfl
    have ha₂' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2).2.1 =
        (ExplState.init 0).2.1 ++ [ι '' (a ∩ Ici R)] := by
      rw [ha₂]
      rfl
    rw [statePhysicalSet_append hp₂ ha₂', statePhysicalSet_init]
    simp only [List.mem_singleton, iUnion_iUnion_eq_left, tipSet_newPc_init_zero hreg h0, union_self]

end InteractingSLE.Theorem14.SB.Lk
