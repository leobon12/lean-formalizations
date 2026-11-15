/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedKCandDisint

/-!
# Prop 5.9's killed law: killed pieces frozen at their kill time

Packet PROVE-STAGEDK-CAND (ruling R78). The concrete candidate pieces are killed (`0` from their lifetime on), while a
stopped representation (`IsStoppedRep`) needs processes continuous through a finite kill time. This file freezes a
killed piece at its left limit:

* `freeze`, `continuousOn_Iic_freeze`: a path continuous before `T > 0` with a left limit `L` at `T`, frozen at `L`
  from `T` on, is continuous on `[0, T]`;
* `IsKilledAtFarLim`: a killed path with a positive kill time, no far contact before it and, at a finite kill time,
  a left limit of the state at which the driver meets a far mark;
* **`IsKilledStageRep`**: the stopped conditional law of a killed piece in Aux. lemma 122's form, stated for the
  piece itself — a filtration `𝓕 ⊇ 𝓠` at time `0`, a Brownian motion `B'` of `𝓕` equal to the piece's noise before the
  kill, the piece adapted before the kill, and almost surely on the stage event the local integrated path of the start's
  word before the kill, killed at its first far contact with left limits there, and traced up to it;
* **`IsKilledStageRep.isStoppedRep`**, **`IsKilledStageRep.isStageLawFarK`**: the frozen piece is a stopped
  representation, hence the killed law `IsStageLawFarK`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedKCand

open Prop59Stage Prop59Nodes StagedKill

/-! ### Freezing at the kill time -/

section Freeze

open scoped Classical in
/-- The path `f` before `τ`, frozen at its left limit at `τ` from `τ` on. -/
def freeze (τ : ℝ≥0∞) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if (t : ℝ≥0∞) < τ then f t else limUnder (𝓝[<] τ.toNNReal) f

theorem freeze_of_lt {τ : ℝ≥0∞} {f : ℝ≥0 → ℝ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : freeze τ f t = f t := by
  simp only [freeze, ht, ↓reduceIte]

/-- At a finite kill time with a left limit, the frozen value is the left limit. -/
theorem freeze_of_le {T : ℝ≥0} (hT : 0 < T) {f : ℝ≥0 → ℝ} {L : ℝ} (hL : Tendsto f (𝓝[<] T) (𝓝 L)) {t : ℝ≥0}
    (ht : T ≤ t) : freeze (T : ℝ≥0∞) f t = L := by
  have hnt : ¬ ((t : ℝ≥0∞) < (T : ℝ≥0∞)) := not_lt.2 (by exact_mod_cast ht)
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  unfold freeze
  split_ifs
  rw [ENNReal.toNNReal_coe]
  exact hL.limUnder_eq

/-- **A frozen path is continuous through the kill time.** -/
theorem continuousOn_Iic_freeze {T : ℝ≥0} (hT : 0 < T) {f : ℝ≥0 → ℝ}
    (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < T}) {L : ℝ} (hL : Tendsto f (𝓝[<] T) (𝓝 L)) :
    ContinuousOn (freeze (T : ℝ≥0∞) f) (Iic T) := by
  intro t ht
  rcases lt_or_eq_of_le (show t ≤ T from ht) with hlt | rfl
  · have hU : {s : ℝ≥0 | (s : ℝ≥0∞) < T} ∈ 𝓝 t :=
      (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (by exact_mod_cast hlt)
    have hfa : ContinuousAt f t := hf.continuousAt hU
    refine (hfa.congr ?_).continuousWithinAt
    filter_upwards [hU] with s hs
    exact (freeze_of_lt hs).symm
  · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, freeze_of_le hT hL le_rfl]
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (freeze_of_lt (by exact_mod_cast hs)).symm

end Freeze

/-! ### Killed pieces with left limits -/

section Lim

variable {nL nR : ℕ}

/-- **A killed path at its first far contact, with left limits**: a positive kill time `τ`, no contact of the driver
with the far marks `iL`, `iR` before `τ`, and at a finite `τ` a left limit of the state at which the driver meets a far
mark. -/
structure IsKilledAtFarLim (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop where
  pos : 0 < τ
  noContact : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t ≠ vL iL t ∧ w t ≠ vR iR t
  lim : ∀ T : ℝ≥0, (T : ℝ≥0∞) = τ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
    Tendsto w (𝓝[<] T) (𝓝 w₀) ∧ (∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (vL₀ i))) ∧
      (∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (vR₀ j))) ∧ (w₀ = vL₀ iL ∨ w₀ = vR₀ iR)

variable {iL : Fin nL} {iR : Fin nR} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **The frozen path is killed at its first far contact continuously.** -/
theorem IsKilledAtFarLim.isKilledAtFar (h : IsKilledAtFarLim iL iR w vL vR τ)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < τ}) (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < τ})
    (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < τ}) :
    IsKilledAtFar iL iR (freeze τ w) (fun i => freeze τ (vL i)) (fun j => freeze τ (vR j)) τ := by
  refine ⟨fun T hT => ?_, fun t ht => ?_, fun T hT => ?_⟩
  · subst hT
    obtain ⟨w₀, vL₀, vR₀, hw₀, hvL₀, hvR₀, -⟩ := h.lim T rfl
    have hT0 : 0 < T := by exact_mod_cast h.pos
    exact (continuousOn_Iic_freeze hT0 hw hw₀).prodMk
      ((continuousOn_pi.2 fun i => continuousOn_Iic_freeze hT0 (hvL i) (hvL₀ i)).prodMk
        (continuousOn_pi.2 fun j => continuousOn_Iic_freeze hT0 (hvR j) (hvR₀ j)))
  · rw [freeze_of_lt ht, freeze_of_lt ht, freeze_of_lt ht]
    exact h.noContact t ht
  · subst hT
    obtain ⟨w₀, vL₀, vR₀, hw₀, hvL₀, hvR₀, hc⟩ := h.lim T rfl
    have hT0 : 0 < T := by exact_mod_cast h.pos
    rw [freeze_of_le hT0 hw₀ le_rfl, freeze_of_le hT0 (hvL₀ iL) le_rfl, freeze_of_le hT0 (hvR₀ iR) le_rfl]
    exact hc

end Lim

/-! ### The killed stage representation -/

section Rep

variable {Ω : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **The stopped conditional law of a killed piece, stated for the piece itself** (Aux. lemma 122's form, p. 391,
stopped at the first far contact): a filtration `𝓕` with `𝓠 ≤ 𝓕 0`, a Brownian motion `B'` of `𝓕`, the piece
`(W, V)` adapted before its lifetime `ζ`, and almost surely on the stage event `R`: an ordered strict start, the local
integrated path of the start's word before `ζ` driven by the piece's noise `B`, which agrees with `B'` before `ζ`, a
kill at the first far contact with left limits there (`IsKilledAtFarLim`), and a generating trace up to `ζ`. -/
structure IsKilledStageRep (κ : ℝ) (P : Measure Ω) (𝓠 : MeasurableSpace Ω) (R : Set Ω) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR) (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (𝓕 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ) : Prop where
  le0 : 𝓠 ≤ 𝓕 0
  brownian : IsFilteredBrownianReal 𝓕 B' P
  adapted_W : AdaptedBefore 𝓕 ζ W
  adapted_VL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)
  adapted_VR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)
  ae_path : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧
    StrictMono (y ω).2.2 ∧
    Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω)
      (ζ ω) ∧
    IsKilledAtFarLim iL iR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) ∧
    (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) (ζ ω) η) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → B t ω = B' t ω

/-- The process frozen at its left limit at `ζ`. -/
def freezeP (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := freeze (ζ ω) (X · ω) t

omit mΩ in
theorem freezeP_of_lt {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < ζ ω) :
    freezeP ζ X t ω = X t ω :=
  freeze_of_lt ht

/-- Freezing after `ζ` keeps adaptedness before `ζ`. -/
theorem adaptedBefore_freezeP {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 ζ X) : AdaptedBefore 𝓕 ζ (freezeP ζ X) := by
  intro t A hA
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ freezeP ζ X t ω ∈ A} = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
    ext ω
    simp only [mem_ofPred_eq, freezeP]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [freeze_of_lt h1] at h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [freeze_of_lt h1]⟩
  rw [e]
  exact hX t A hA

variable {κ : ℝ} {P : Measure Ω} {R : Set Ω} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {B' : ℝ≥0 → Ω → ℝ}

/-- **The frozen piece is a stopped representation.** -/
theorem IsKilledStageRep.isStoppedRep (h : IsKilledStageRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 B') :
    IsStoppedRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 (freezeP ζ W) (fun i => freezeP ζ (VL i))
      (fun j => freezeP ζ (VR j)) B' := by
  refine ⟨h.le0, h.brownian, adaptedBefore_freezeP h.adapted_W, fun i => adaptedBefore_freezeP (h.adapted_VL i),
    fun j => adaptedBefore_freezeP (h.adapted_VR j), ?_⟩
  filter_upwards [h.ae_path] with ω hω hωR
  obtain ⟨hord, hanti, hmono, hp, hK, ⟨η, hη⟩, hB⟩ := hω hωR
  have hpos : (((0 : ℝ≥0)) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact hK.pos
  have hK' := hK.isKilledAtFar hp.continuousOn_w hp.continuousOn_vL hp.continuousOn_vR
  have hag : AgreeBefore (freezeP ζ W · ω) (W · ω) (fun i t => freezeP ζ (VL i) t ω) (fun i t => VL i t ω)
      (fun j t => freezeP ζ (VR j) t ω) (fun j t => VR j t ω) (ζ ω) := fun t ht =>
    ⟨(freezeP_of_lt (X := W) ht).symm, fun i => (freezeP_of_lt (X := VL i) ht).symm,
      fun j => (freezeP_of_lt (X := VR j) ht).symm⟩
  have h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < ζ ω := hpos
  refine ⟨hord, hanti, hmono, ?_, hK', ⟨η, Sec7.IsGeneratingTrace.congr_lt hη fun t ht => freezeP_of_lt ht⟩, hag,
    ⟨(freezeP_of_lt (X := W) h0).symm, fun i => (freezeP_of_lt (X := VL i) h0).symm,
      fun j => (freezeP_of_lt (X := VR j) h0).symm⟩, hB⟩
  exact Sec2.Assembly2.isSLEPathUpTo_congr hp (freezeP_of_lt (X := W) h0) (fun i => freezeP_of_lt (X := VL i) h0)
    (fun j => freezeP_of_lt (X := VR j) h0) (fun t ht => freezeP_of_lt (X := W) ht)
    (fun t ht i => freezeP_of_lt (X := VL i) ht) (fun t ht j => freezeP_of_lt (X := VR j) ht)
    (fun t ht => (hB t ht).symm)

end Rep

end InteractingSLE.Sec5.CrossCond.StagedKCand
