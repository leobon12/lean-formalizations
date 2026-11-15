/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageExp
import InteractingSLE.Spec.Sec2.PatchingNonaccum
import InteractingSLE.Spec.Sec5.Prop59StageLawProofBridge

/-!
# Proposition 5.9's stage law for pieces killed at their first far contact

Packet PROVE-PROP59-NODES. Specification §5.2, proof of Proposition 5.9 (p. 144: the trajectory "is used only before
its first new contact with the conditional domain boundary"); Astra's follow-up 4, §3.4 (ruling R71: the conditional
word holds strictly before the first new contact and the continuation threshold) and follow-up 5, §2.4 (ruling R73:
the first new contact is a.s. on a far counterflow interval, with far totals `κ − 4` and `κ/2 − 2`).

PROVE-PROP59T2's stage law `IsStageLaw` compares the piece with integrated evolutions **run to their continuation
threshold**. PROVE-PROP59-PIECES' concrete pieces are killed at their first contact with the revealed counterflow,
i.e. when the driver meets a far mark. For `κ ∈ (2, 4)` neither far total (`κ − 4`, `κ/2 − 2`) is a threshold, so a
piece killed there is not an integrated path of Definition 2.1 (its lifetime is not maximal) and the piece law in the
form `IsStagePieceLaw` cannot hold for it. This file states the law in the form that holds for every `κ ∈ (0, 4)`:

* `farHit`, `farLife`: the first contact of the driver with the far left or far right mark, and the lifetime killed
  there;
* **`IsStageLawFar`**: almost surely on the stage event, the start is a strict ordered word and the piece is a local
  solution of Definition 2.1's equations before its lifetime (`Sec2.IsSLEPathUpTo`); and the conditional law of the
  piece given the past is the `SLE_κ(ρ)` law **killed at its first far contact**, in comparison form (`CompPremiseFar`:
  premises over every integrated evolution, sampled with the killed lifetime `farLife`);
* **`Prop59StageLawFarStatement`**: every stage of a stage system obeys `IsStageLawFar` with the deterministic stage
  word.

The experiment only looks at the piece before its first far contact, so the comparison premises it uses hold in the
killed form: `compPremiseFar_crossL/R` (the crossing of `∓(2 + 1/8)` happens strictly before the first far contact,
and the opposite far mark is never met, PROVE-PROP59T's `ae_stage_cross_left`) and `exists_compPremiseFar_unit`
(the unit event is monotone in the lifetime).

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop59Stage Supp8.GB8 Prop59Tips

/-! ### The first far contact -/

section Far

variable {nL nR : ℕ}

/-- **The first far contact**: the first time the driver meets the far left mark `iL` or the far right mark `iR`. -/
def farHit (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : w t = vL iL t ∨ w t = vR iR t), (t : ℝ≥0∞)

/-- **The lifetime killed at the first far contact.** -/
def farLife (iL : Fin nL) (iR : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  min ζ (farHit iL iR w vL vR)

variable {iL : Fin nL} {iR : Fin nR} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem farLife_le : farLife iL iR w vL vR ζ ≤ ζ := min_le_left _ _

theorem le_farHit {τ : ℝ≥0∞} (h : ∀ t : ℝ≥0, (w t = vL iL t ∨ w t = vR iR t) → τ ≤ t) :
    τ ≤ farHit iL iR w vL vR :=
  le_iInf₂ fun t ht => h t ht

/-- **Strictly before the first far contact.** If both far gaps are positive on `[0, t]`, `t` is before the lifetime
and the gaps are continuous there, then `t` is strictly before the killed lifetime. -/
theorem lt_farLife_of (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hl : ContinuousOn (vL iL) {s | (s : ℝ≥0∞) < ζ})
    (hr : ContinuousOn (vR iR) {s | (s : ℝ≥0∞) < ζ}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hgap : ∀ u ≤ t, vL iL u < w u ∧ w u < vR iR u) : (t : ℝ≥0∞) < farLife iL iR w vL vR ζ := by
  have hO : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} ∈ 𝓝 t :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht
  have hcl : ContinuousAt (fun s => w s - vL iL s) t := (hw.sub hl).continuousAt hO
  have hcr : ContinuousAt (fun s => vR iR s - w s) t := (hr.sub hw).continuousAt hO
  have h1 := hcl.eventually (lt_mem_nhds (sub_pos.2 (hgap t le_rfl).1))
  have h2 := hcr.eventually (lt_mem_nhds (sub_pos.2 (hgap t le_rfl).2))
  obtain ⟨c, hc, hsub⟩ := exists_Ico_subset_of_mem_nhds (h1.and h2) (show ∃ c, t < c from ⟨t + 1, by simp⟩)
  have hfar : (c : ℝ≥0∞) ≤ farHit iL iR w vL vR := by
    refine le_farHit fun s hs => ?_
    by_contra hlt
    push Not at hlt
    have hsc : s < c := by exact_mod_cast hlt
    rcases le_or_gt s t with hst | hst
    · rcases hs with h | h
      · exact absurd h (ne_of_gt (hgap s hst).1)
      · exact absurd h (ne_of_lt (hgap s hst).2)
    · obtain ⟨g1, g2⟩ := hsub ⟨hst.le, hsc⟩
      simp only [sub_pos] at g1 g2
      rcases hs with h | h
      · exact absurd h (ne_of_gt g1)
      · exact absurd h (ne_of_lt g2)
  exact lt_min ht (lt_of_lt_of_le (by exact_mod_cast hc) hfar)

/-- The rational samples of a state killed at an earlier lifetime agree with the original ones before it. -/
theorem samp_snd_of_lt_farLife {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ≥0∞) < farLife iL iR w vL vR ζ) :
    (samp w vL vR (farLife iL iR w vL vR ζ)).2 q = (samp w vL vR ζ).2 q := by
  rw [samp_snd_of_lt _ _ _ hq, samp_snd_of_lt _ _ _ (lt_of_lt_of_le hq farLife_le)]

end Far

/-! ### The killed stage law -/

section Law

/-- **The premise of the killed comparison form** on a start set `D`: every integrated evolution (with an almost
surely existing generating trace) from a start in `D`, **killed at its first far contact**, gives the section of `S`
probability at least `p`. -/
def CompPremiseFar (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (D : Set (Start nL nR)) (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  ∀ y₀ ∈ D, ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (ζ' ω') η) →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
      (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈ S}

/-- **The law of one stage, killed at the first far contact** (Proposition 5.9, p. 144; R71, R73). `𝓠` is the past,
`R ∈ 𝓠` the event that the stage is reached, `y` the stage start and `(W, V_L, V_R, B, ζ)` the piece relative to its
start, killed at its first contact with the revealed counterflow (the far marks `iL`, `iR`). The two clauses:

1. almost surely on `R`, the start is an ordered force word with distinct positions on each side, and the piece
   solves Definition 2.1's equations before its lifetime (`Sec2.IsSLEPathUpTo`);
2. **the conditional law of the piece given `𝓠` is the `SLE_κ(ρ)` law from the start killed at its first far
   contact**, tested on Borel events of (start, samples): if every integrated evolution from every `y₀`, killed at its
   first far contact, gives the section of `S` probability at least `p`, then every past event `A ⊆ R` satisfies
   `p P(A) ≤ P(A ∩ {(start, samples) ∈ S})`. -/
def IsStageLawFar (κ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓠 : MeasurableSpace Ω)
    (R : Set Ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2 ∧
    Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
      (B · ω) (ζ ω)) ∧
  ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞, CompPremiseFar κ ρL ρR iL iR univ S p →
    ∀ A : Set Ω, MeasurableSet[𝓠] A → A ⊆ R →
      p * P A ≤ P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S})

/-- **Named input of PROVE-PROP59-NODES: the killed stage law of Proposition 5.9's alternating construction.**
Every stage of the stage system obeys `IsStageLawFar` with the deterministic stage word
`(stageρL κ ρL₀ j; stageρR κ ρR₀ j)` and the far marks (the last indices): conditionally on the revealed counterflow
and flow prefix, the next extreme-angle piece in the joint chart is an integrated `SLE_κ(ρ)` evolution of the
Figure 5.8 word from the current configuration, killed at its first contact with the revealed counterflow. -/
def Prop59StageLawFarStatement (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {nL₀ nR₀ : ℕ}
    (hnL : 0 < nL₀) (hnR : 0 < nR₀) (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (sys : StageSys Ω nL₀ nR₀) : Prop :=
  ∀ (r : ℕ → ℕ) (j : ℕ), IsStageLawFar κ P (sys r j).past (sys r j).R (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
    (farL (Nat.lt_of_lt_of_le hnL (Nat.le_add_right nL₀ j)))
    (farR (Nat.lt_of_lt_of_le hnR (Nat.le_add_right nR₀ j)))
    (sys r j).y (sys r j).W (sys r j).VL (sys r j).VR (sys r j).B (sys r j).ζ

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓠 : MeasurableSpace Ω} {R : Set Ω}
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The killed comparison form restricted to a start set `D`** (as PROVE-PROP59T2's `IsStageLaw.le_measure`). -/
theorem IsStageLawFar.le_measure (hL : @IsStageLawFar κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ)
    {D : Set (Start nL nR)} (hD : MeasurableSet D) {S : Set (Start nL nR × Samp nL nR)} (hS : MeasurableSet S)
    {p : ℝ≥0∞} (hp1 : p ≤ 1) (hp : CompPremiseFar κ ρL ρR iL iR D S p) {A : Set Ω} (hA : MeasurableSet[𝓠] A)
    (hAR : A ⊆ R) :
    p * P A ≤ P (A ∩ {ω | y ω ∈ D → (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
  have hS' : MeasurableSet ((Prod.fst ⁻¹' Dᶜ) ∪ S) := (measurable_fst hD.compl).union hS
  have h := hL.2 _ hS' p (fun y₀ _ Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr => by
    by_cases hy : y₀ ∈ D
    · refine (hp y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr).trans (measure_mono fun ω' hω' => ?_)
      exact Or.inr hω'
    · have : {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω')
          (farLife iL iR (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω'))) ∈
          (Prod.fst ⁻¹' Dᶜ) ∪ S} = univ := by
        ext ω'
        simp only [mem_union, mem_preimage, mem_compl_iff, hy, not_false_eq_true, true_or, mem_ofPred_eq,
          mem_univ]
      rw [this, measure_univ]
      exact hp1) A hA hAR
  refine h.trans (measure_mono fun ω hω => ⟨hω.1, fun hyD => ?_⟩)
  rcases hω.2 with h1 | h1
  · exact absurd hyD h1
  · exact h1

/-- **Versions** (as PROVE-PROP59T3's `IsStageLaw.congr`): the killed stage law passes to a family with the same
(start, samples) almost surely on the stage event and the pathwise properties of clause 1. -/
theorem IsStageLawFar.congr {y' : Ω → Start nL nR} {W' : ℝ≥0 → Ω → ℝ} {VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (h : @IsStageLawFar κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ)
    (hobs : ∀ᵐ ω ∂P, ω ∈ R → stageObs y' W' VL' VR' ζ' ω = stageObs y W VL VR ζ ω)
    (h1 : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y' ω).2.1 (y' ω).2.2 ∧ StrictAnti (y' ω).2.1 ∧
      StrictMono (y' ω).2.2 ∧ Sec2.IsSLEPathUpTo κ (y' ω).2.1 (y' ω).2.2 ρL ρR (W' · ω)
        (fun i t => VL' i t ω) (fun k t => VR' k t ω) (B' · ω) (ζ' ω)) :
    @IsStageLawFar κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y' W' VL' VR' B' ζ' := by
  refine ⟨h1, fun S hS p hp A hA hAR => (h.2 S hS p hp A hA hAR).trans (le_of_eq (measure_congr ?_))⟩
  filter_upwards [hobs] with ω hω
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · have e := hω (hAR h1)
    show stageObs y' W' VL' VR' ζ' ω ∈ S
    rw [e]; exact h2
  · have e := hω (hAR h1)
    show stageObs y W VL VR ζ ω ∈ S
    rw [← e]; exact h2

/-- A smaller past (as `IsStageLaw.mono_past`). -/
theorem IsStageLawFar.mono_past {𝓠' : MeasurableSpace Ω}
    (h : @IsStageLawFar κ Ω mΩ P 𝓠 R nL nR ρL ρR iL iR y W VL VR B ζ) (h' : 𝓠' ≤ 𝓠) :
    @IsStageLawFar κ Ω mΩ P 𝓠' R nL nR ρL ρR iL iR y W VL VR B ζ :=
  ⟨h.1, fun S hS p hp A hA hAR => h.2 S hS p hp A (h' _ hA) hAR⟩

end Law

end InteractingSLE.Sec5.Prop59Nodes
