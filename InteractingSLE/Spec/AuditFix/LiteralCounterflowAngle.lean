/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.LiteralCounterflowBridge
import InteractingSLE.Spec.Sec4.Prob41Flow

/-!
# FD11.3: angle labels in the literal and the centred background

Packet PROVE-AF-CFLIT. The specification's translation FD11.3 (p. 12): with the literal background `ĥ = h + πχ` and
the angle labels `θ̂ = θ − π`, "`h + θχ = ĥ + θ̂χ`. Both actual coupling fields are unchanged. Every boundary height of
the flow background is shifted along with `h`." Formally, for one flow line from `0` in `ℍ`:

* `leftLim_add_const`, `rightLim_add_const`, `jumpSet_add_const`: for finite piecewise-constant data `b`, the data
  `b + s` has one-sided limits shifted by `s` and the same genuine jumps;
* `flowLineLeftWord_shift`, `flowLineRightWord_shift`: the induced force word of the angle-`θ′` flow line for the data
  `b + s` is the word of the angle-`θ` flow line for `b` when `θ′χ + s = θχ` (same mark count, positions, weights);
* **`isFlowLineDriver_shift_iff`**: for `ĥ = h + s`, `IsFlowLineDriver κ (b + s) jumps θ′ P ĥ W ζ ↔
  IsFlowLineDriver κ b jumps θ P h W ζ` when `θ′χ + s = θχ`; with `s = πχ`: the angle-`θ` flow line of `h` is the
  angle-`(θ − π)` flow line of `ĥ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)
open InteractingSLE.PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.AuditFix.CFLit

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-! ### One-sided limits and jumps of shifted data -/

/-- The left limit of finite piecewise-constant data moves with a constant shift. -/
theorem leftLim_add_const (hb : IsPiecewiseConstantBoundaryData b J) (s y : ℝ) :
    leftLim (fun x => b x + s) y = leftLim b y + s := by
  set M : Finset ℝ := insert (y - 1) (J.filter (· < y))
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hmy : M.max' hMne < y := by
    rcases Finset.mem_insert.1 (M.max'_mem hMne) with h' | h'
    · rw [h']
      linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Set.Ioo (M.max' hMne) y := fun w hwJ hw =>
    absurd (M.le_max' w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.2⟩))) (not_le.2 hw.1)
  set t := (M.max' hMne + y) / 2 with ht
  have htI : t ∈ Set.Ioo (M.max' hMne) y := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have hconst : ∀ r ∈ Set.Ioo (M.max' hMne) y, b r = b t := fun r hr =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ htI hr
  rw [Sec4.leftLim_eq_of_forall hmy hconst,
    Sec4.leftLim_eq_of_forall (b := fun x => b x + s) (c := b t + s) hmy fun r hr => by
      simp only [hconst r hr]]

/-- The right limit of finite piecewise-constant data moves with a constant shift. -/
theorem rightLim_add_const (hb : IsPiecewiseConstantBoundaryData b J) (s y : ℝ) :
    rightLim (fun x => b x + s) y = rightLim b y + s := by
  set M : Finset ℝ := insert (y + 1) (J.filter (y < ·))
  have hMne : M.Nonempty := Finset.insert_nonempty _ _
  have hym : y < M.min' hMne := by
    rcases Finset.mem_insert.1 (M.min'_mem hMne) with h' | h'
    · rw [h']
      linarith
    · exact (Finset.mem_filter.1 h').2
  have hnoJ : ∀ w ∈ J, w ∉ Set.Ioo y (M.min' hMne) := fun w hwJ hw =>
    absurd (M.min'_le w (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hwJ, hw.1⟩))) (not_le.2 hw.2)
  set t := (y + M.min' hMne) / 2 with ht
  have htI : t ∈ Set.Ioo y (M.min' hMne) := ⟨by rw [ht]; linarith, by rw [ht]; linarith⟩
  have hconst : ∀ r ∈ Set.Ioo y (M.min' hMne), b r = b t := fun r hr =>
    Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant hb hnoJ htI hr
  rw [Sec4.rightLim_eq_of_forall hym hconst,
    Sec4.rightLim_eq_of_forall (b := fun x => b x + s) (c := b t + s) hym fun r hr => by
      simp only [hconst r hr]]

/-- Shifted finite piecewise-constant data has the same genuine jumps. -/
theorem jumpSet_add_const (hb : IsPiecewiseConstantBoundaryData b J) (s : ℝ) :
    jumpSet (fun x => b x + s) J = jumpSet b J := by
  unfold PiecewiseConstantBoundaryData.jumpSet
  refine Finset.filter_congr fun y _ => ?_
  rw [leftLim_add_const hb, rightLim_add_const hb]
  simp only [ne_eq, add_left_inj]

/-! ### The induced force words -/

/-- The left half of a seed-`0` force word from a jump set `S`, a seed weight and a jump-weight function (the shape
of the frozen `flowLineNL`, `flowLineXL`, `flowLineRhoL` at `x = 0`). -/
def leftWordOf (S : Finset ℝ) (seed : ℝ) (D : ℝ → ℝ) : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ) :=
  ⟨(S.filter (· < (0 : ℝ))).card + 1,
    Fin.cons 0 fun i => (S.filter (· < (0 : ℝ))).orderEmbOfFin rfl (Fin.rev i) - 0,
    Fin.cons seed fun i => D ((S.filter (· < (0 : ℝ))).orderEmbOfFin rfl (Fin.rev i))⟩

/-- The right half (the shape of the frozen `flowLineNR`, `flowLineXR`, `flowLineRhoR` at `x = 0`). -/
def rightWordOf (S : Finset ℝ) (seed : ℝ) (D : ℝ → ℝ) : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ) :=
  ⟨(S.filter ((0 : ℝ) < ·)).card + 1,
    Fin.cons 0 fun i => (S.filter ((0 : ℝ) < ·)).orderEmbOfFin rfl i - 0,
    Fin.cons seed fun i => D ((S.filter ((0 : ℝ) < ·)).orderEmbOfFin rfl i)⟩

theorem flowLineLeftWord_eq (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    (⟨flowLineNL b J 0, flowLineXL b J 0, flowLineRhoL κ b J 0 θ⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) =
      leftWordOf (jumpSet b J) (-(leftLim b 0 + θ * chiC κ) / sleLambda κ - 1)
        (fun y => (rightLim b y - leftLim b y) / sleLambda κ) :=
  rfl

theorem flowLineRightWord_eq (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    (⟨flowLineNR b J 0, flowLineXR b J 0, flowLineRhoR κ b J 0 θ⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) =
      rightWordOf (jumpSet b J) ((rightLim b 0 + θ * chiC κ) / sleLambda κ - 1)
        (fun y => (rightLim b y - leftLim b y) / sleLambda κ) :=
  rfl

/-- The left word of the angle-`θ′` flow line for `b + s` is that of the angle-`θ` flow line for `b`
(`θ′χ + s = θχ`). -/
theorem flowLineLeftWord_shift (hb : IsPiecewiseConstantBoundaryData b J) {κ s θ θ' : ℝ}
    (hθ : θ' * chiC κ + s = θ * chiC κ) :
    (⟨flowLineNL (fun x => b x + s) J 0, flowLineXL (fun x => b x + s) J 0,
        flowLineRhoL κ (fun x => b x + s) J 0 θ'⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) =
      ⟨flowLineNL b J 0, flowLineXL b J 0, flowLineRhoL κ b J 0 θ⟩ := by
  rw [flowLineLeftWord_eq, flowLineLeftWord_eq, jumpSet_add_const hb, leftLim_add_const hb,
    show leftLim b 0 + s + θ' * chiC κ = leftLim b 0 + θ * chiC κ by linarith]
  congr 1
  funext y
  simp only [leftLim_add_const hb, rightLim_add_const hb]
  ring

/-- The right word of the angle-`θ′` flow line for `b + s` is that of the angle-`θ` flow line for `b`
(`θ′χ + s = θχ`). -/
theorem flowLineRightWord_shift (hb : IsPiecewiseConstantBoundaryData b J) {κ s θ θ' : ℝ}
    (hθ : θ' * chiC κ + s = θ * chiC κ) :
    (⟨flowLineNR (fun x => b x + s) J 0, flowLineXR (fun x => b x + s) J 0,
        flowLineRhoR κ (fun x => b x + s) J 0 θ'⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) =
      ⟨flowLineNR b J 0, flowLineXR b J 0, flowLineRhoR κ b J 0 θ⟩ := by
  rw [flowLineRightWord_eq, flowLineRightWord_eq, jumpSet_add_const hb, rightLim_add_const hb,
    show rightLim b 0 + s + θ' * chiC κ = rightLim b 0 + θ * chiC κ by linarith]
  congr 1
  funext y
  simp only [leftLim_add_const hb, rightLim_add_const hb]
  ring

/-- Equal force words (as dependent triples) give the same optional hull couplings. -/
theorem exists_isOptionalHullCoupling_congr {κ : ℝ} {nL nR nL' nR' : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {xL' ρL' : Fin nL' → ℝ} {xR' ρR' : Fin nR' → ℝ}
    (hL : (⟨nL, xL, ρL⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) = ⟨nL', xL', ρL'⟩)
    (hR : (⟨nR, xR, ρR⟩ : Σ n : ℕ, (Fin n → ℝ) × (Fin n → ℝ)) = ⟨nR', xR', ρR'⟩)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens) :
    (∃ (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) ↔
      ∃ (VL : Fin nL' → ℝ≥0 → Ω → ℝ) (VR : Fin nR' → ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕 W VL VR B ζ h := by
  cases hL
  cases hR
  exact Iff.rfl

/-- `IsTranslateAddConst 0 c f g` is `g = f + c` in pairing form. -/
theorem isTranslateAddConst_zero_iff {c : ℝ} {f g : DistOn upperHalfPlaneOpens} :
    IsTranslateAddConst 0 c f g ↔ ∀ φ : TestOn upperHalfPlaneOpens, g φ = f φ + c * ∫ z, φ z := by
  refine ⟨fun hg φ => translateAddConst_zero_apply hg φ, fun hg φ φ' hφ => ?_⟩
  have e : φ' = φ := by
    ext z
    rw [hφ z, Complex.ofReal_zero, add_zero]
  subst e
  exact hg φ'

/-! ### FD11.3 for one flow line -/

/-- **FD11.3 for one flow line from `0`**: if `ĥ = h + s` (every `ω`) and `θ′χ + s = θχ`, then `W` (lifetime `ζ`)
drives the angle-`θ′` flow line of `ĥ`, whose data is `b + s`, iff it drives the angle-`θ` flow line of `h`, whose
data is `b`: the coupling field `ĥ + θ′χ = h + θχ` and the induced force word (both sides) are the same. With
`s = πχ`: the angle-`θ` flow line of the flow background `h` is the angle-`(θ − π)` flow line of the literal
background `ĥ = h + πχ`. -/
theorem isFlowLineDriver_shift_iff {κ : ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {s θ θ' : ℝ}
    (hθ : θ' * chiC κ + s = θ * chiC κ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    {h ĥ : Ω → DistOn upperHalfPlaneOpens} (hĥ : ∀ ω, IsTranslateAddConst 0 s (h ω) (ĥ ω))
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    IsFlowLineDriver κ (fun x => b x + s) J θ' P ĥ W ζ ↔ IsFlowLineDriver κ b J θ P h W ζ := by
  have hT : ∀ ω (g : DistOn upperHalfPlaneOpens),
      IsTranslateAddConst 0 (θ' * chiC κ) (ĥ ω) g ↔ IsTranslateAddConst 0 (θ * chiC κ) (h ω) g := by
    intro ω g
    rw [isTranslateAddConst_zero_iff, isTranslateAddConst_zero_iff]
    refine forall_congr' fun φ => ?_
    rw [translateAddConst_zero_apply (hĥ ω), ← hθ]
    constructor
    · intro e
      rw [e]
      ring
    · intro e
      rw [e]
      ring
  have hL := flowLineLeftWord_shift (κ := κ) hb hθ
  have hR := flowLineRightWord_shift (κ := κ) hb hθ
  constructor
  · rintro ⟨g, 𝓕, VL, VR, B, hg, hC⟩
    obtain ⟨VL', VR', hC'⟩ := (exists_isOptionalHullCoupling_congr hL hR P 𝓕 W B ζ g).1 ⟨VL, VR, hC⟩
    exact ⟨g, 𝓕, VL', VR', B, fun ω => (hT ω (g ω)).1 (hg ω), hC'⟩
  · rintro ⟨g, 𝓕, VL, VR, B, hg, hC⟩
    obtain ⟨VL', VR', hC'⟩ := (exists_isOptionalHullCoupling_congr hL hR P 𝓕 W B ζ g).2 ⟨VL, VR, hC⟩
    exact ⟨g, 𝓕, VL', VR', B, fun ω => (hT ω (g ω)).2 (hg ω), hC'⟩

end InteractingSLE.AuditFix.CFLit
