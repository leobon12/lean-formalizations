/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompWord
import InteractingSLE.Spec.Sec5.StagedRepEntr
import InteractingSLE.Spec.Sec7.PhaseSelFullPhase
import InteractingSLE.Spec.Sec7.PhaseSelFullWord

/-!
# The flag candidate's stopped representation and killed comparison clause on the glued space

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S6 §5 item 1 for the flag candidate of arbitrary angle flags `fl`
(PROVE-STAGED-S7 does it for the root flags): the word entrance after the last switch (`exists_isWordEntrance_candF`)
is turned into a stopped representation (`StagedRep.isKilledStageRep_of_entrance`), hence into the killed stage law
and its comparison clause, on the glued space conditioned on the alive event, for the past `candFiltF … 0`.

* `not_threshold_consAlt`: a strictly ordered start of a born-weight word (`ℓ ≥ 1` switches) is below the threshold
  (only the newest mark on each side can sit at the driver; born weights `0`, `±(2 − κ/2)` are `> −2`);
* `FlagGluedRep`, `FlagGluedClause`: the stopped representation (`IsKilledStageRep`, on the glued space times a noise
  factor) and the comparison clause (`CompClauseK`, R78) of the flag candidate's restarted word in tree order, with
  weights `consAlt (bornL κ fl) (nodeρL0 κ c θ₀) ℓ` (`StagedNCompWord`) and far marks the junction marks;
* **`flagGluedRep_of_paths`**: `FlagGluedRep` from three pathwise almost-sure facts on the alive event, kept as
  hypotheses: the strict order of the start (`hstrict`), the killing at the far marks with left limits (`hfar`) and a
  trace up to the restarted lifetime (`htr`) — PROVE-STAGED-S7's items 1 and 3 for the flag word;
* **`flagGluedClause_of_rep`**: `FlagGluedClause` from `FlagGluedRep` (disintegration over the past,
  `IsStoppedRep.isStageLawFarK`, and descent from the noise factor).

Conditional helpers with distinct names; they replace no source theorem. R48: the only named input is
`h44 : Theorem12ParamCond44Statement` (R74); nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater Prop59NodeTree
open Prop59Stage Prop59System StagedKCand StagedKill StagedRep
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open StagedFinal (imgStageRhoL imgStageRhoR)

/-! ### The threshold at time `0` of a born-weight word -/

section Threshold

variable {κ : ℝ}

theorem zero_lt_of_ne_zero {m : ℕ} (hm : 0 < m) (i : Fin m) (hi : i ≠ ⟨0, hm⟩) : (⟨0, hm⟩ : Fin m) < i := by
  rw [Fin.lt_def]
  have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  simp only
  omega

/-- **A strictly ordered start of a born-weight word is below the threshold** (`ℓ ≥ 1` switches, the driver at `0`
and the newest marks at most at the driver). -/
theorem not_threshold_consAlt (hκ : 0 < κ) (hκ4 : κ < 4) (fl : ℕ → Bool) {nL₀ nR₀ ℓ : ℕ} (hℓ : 0 < ℓ)
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) {xL : Fin (nL₀ + ℓ) → ℝ} {xR : Fin (nR₀ + ℓ) → ℝ}
    (hL : StrictAnti xL) (hR : StrictMono xR) (hL0 : xL ⟨0, by omega⟩ ≤ 0) (hR0 : 0 ≤ xR ⟨0, by omega⟩) :
    ¬ ForceWord.ThresholdCondition (consAlt (bornL κ fl) ρL₀ ℓ) (consAlt (bornR κ fl) ρR₀ ℓ) 0 xL xR := by
  refine StagedNode.not_threshold_of_unique ⟨0, by omega⟩
    (fun i hi => (lt_of_lt_of_le (hL (zero_lt_of_ne_zero _ i hi)) hL0).ne) ?_ ⟨0, by omega⟩
    (fun j hj => (lt_of_le_of_lt hR0 (hR (zero_lt_of_ne_zero _ j hj))).ne') ?_
  · rw [StagedNode.consAlt_zero_idx _ _ hℓ]
    exact StagedNode.neg_two_lt_bornL hκ hκ4 fl _
  · rw [StagedNode.consAlt_zero_idx _ _ hℓ]
    exact StagedNode.neg_two_lt_bornR hκ hκ4 fl _

end Threshold

/-! ### The comparison clause of the flag candidate on the glued space -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

/-- **A stopped representation of the flag candidate `(ℓ, t)` on the glued space** (extended by a noise factor):
under the glued law conditioned on the alive event times a noise law, a filtration containing `candFiltF … 0` at
time `0` with a Brownian motion `B` that drives the restarted word (in tree order, born-weight word in front of the
initial root word, far marks the junction marks) as a local integrated path from its start, killed at its far contact
with left limits and traced up to it (`StagedKCand.IsKilledStageRep`). -/
def FlagGluedRep (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) : Prop :=
  ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace ((Ω × HistorySpace 0 0) × (ℕ → ℝ))))
    (B : ℝ≥0 → (Ω × HistorySpace 0 0) × (ℕ → ℝ) → ℝ),
    IsKilledStageRep κ (((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)]).prod P₀)
      ((candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0).comap Prod.fst)
      (Prod.fst ⁻¹' s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ))
      (consAlt (bornL κ fl) (nodeρL0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
      (consAlt (bornR κ fl) (nodeρR0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
      (fun p => ((0 : ℝ),
        fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) i 0 p.1,
        fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) j 0 p.1))
      (fun r p => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) r p.1)
      (fun i r p => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i r p.1)
      (fun j r p => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) j r p.1)
      B (fun p => s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) p.1) 𝓕 B

/-- **The killed comparison clause of the flag candidate `(ℓ, t)` on the glued space** (conditioned on the alive
event, past `candFiltF … 0`, start the restarted word at time `0` in tree order, weights the born-weight word in front
of the initial root word at the first angle, far marks the junction marks). -/
def FlagGluedClause (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) : Prop :=
  CompClauseK κ ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)])
    (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0)
    (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
      (lastO ℓ t : ℝ))
    (consAlt (bornL κ fl) (nodeρL0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
    (consAlt (bornR κ fl) (nodeρR0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
    (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
    (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
    (fun p => ((0 : ℝ),
      fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i 0 p,
      fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) j 0 p))
    (s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))
    (s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
      (lastO ℓ t : ℝ))
    (s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
      (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
      (lastO ℓ t : ℝ))
    (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ))

include hκ4 in
/-- **The stopped representation of the flag candidate's restarted word on the glued space**, from the strict start,
the far kill with left limits and a trace up to the restarted lifetime, almost surely on the alive event (the word
entrance `exists_isWordEntrance_candF`, the threshold `not_threshold_consAlt`, `isKilledStageRep_of_entrance`). -/
theorem flagGluedRep_of_paths (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) (hℓ : 0 < ℓ) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0)
    (hstrict : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) →
      StrictAnti (fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) i 0 p) ∧
      StrictMono (fun j => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
        (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
        (lastO ℓ t : ℝ) j 0 p))
    (hfar : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) →
      IsKilledAtFarLim (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
        (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) r p)
        (fun i r => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) i r p)
        (fun j r => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTsF fl ℓ t) ℓ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) j r p)
        (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) p))
    (htr : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun r => s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
        (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ) r p)
        (s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
          (lastO ℓ t : ℝ) p) η) :
    FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set μA := μ[|A] with hμA
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have h𝓐𝓖 : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  obtain ⟨P₀, hP₀, 𝓦, B, hB, -, hent⟩ :=
    exists_isWordEntrance_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf hus hv hs hA0
  have := hP₀
  set 𝓕 := WholeField.prodFiltration 𝓖 𝓦 with h𝓕
  set VLc := s6VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) with hVLc
  set VRc := s6VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) with hVRc
  set Wr := s3W s Wc Eg (lastO ℓ t : ℝ) with hWr
  set ζr := s3ζ s Wc Eg (lastO ℓ t : ℝ) with hζr
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hK := isKilledWord_s6 (xL := flowLineXL c.fn c.jumps 0) (xR := flowLineXR c.fn c.jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTsF_bounds (fl := fl) hv) (monotone_candTsF (fl := fl) hv)
  -- adaptedness to the product filtration before the restarted lifetime
  have hWa : StronglyAdapted 𝓖 Wr := fun r =>
    (stronglyAdapted_s3W_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r).mono (h𝓐𝓖 r)
  have hVLa : ∀ i, StronglyAdapted 𝓖 (VLc i) := fun i r =>
    (stronglyAdapted_s6VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ i r).mono (h𝓐𝓖 r)
  have hVRa : ∀ j, StronglyAdapted 𝓖 (VRc j) := fun j r =>
    (stronglyAdapted_s6VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ j r).mono (h𝓐𝓖 r)
  have hζ𝓖 : IsStoppingTime 𝓖 fun p => (ζr p : WithTop ℝ≥0) := fun r => by
    have h1 := (measurableSet_lt_s3ζ_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r).compl
    convert h𝓐𝓖 r _ h1 using 1
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    exact Iff.rfl
  have hζ𝓕 := Sec7.PhaseSelFull.isStoppingTime_fst (𝓦 := 𝓦) hζ𝓖
  have hWb : AdaptedBefore 𝓕 (fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => ζr p.1) (fun r p => Wr r p.1) :=
    Sec7.PhaseSelFull.adaptedBefore_of_stronglyAdapted' (Sec7.PhaseSelFull.stronglyAdapted_fst hWa) hζ𝓕
  have hVLb : ∀ i, AdaptedBefore 𝓕 (fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => ζr p.1)
      (fun r p => VLc i r p.1) := fun i =>
    Sec7.PhaseSelFull.adaptedBefore_of_stronglyAdapted' (Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i)) hζ𝓕
  have hVRb : ∀ j, AdaptedBefore 𝓕 (fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => ζr p.1)
      (fun r p => VRc j r p.1) := fun j =>
    Sec7.PhaseSelFull.adaptedBefore_of_stronglyAdapted' (Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa j)) hζ𝓕
  -- the past
  have hle : (𝓐 0).comap (Prod.fst : (Ω × HistorySpace 0 0) × (ℕ → ℝ) → Ω × HistorySpace 0 0) ≤ 𝓕 0 :=
    (MeasurableSpace.comap_mono (h𝓐𝓖 0)).trans (WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 0)
  -- the pathwise facts, lifted to the product
  have hlift : ∀ {Q : Ω × HistorySpace 0 0 → Prop}, (∀ᵐ p ∂μ, p ∈ A → Q p) →
      ∀ᵐ p ∂(μA.prod P₀), p.1 ∈ A → Q p.1 := fun hQ =>
    Measure.quasiMeasurePreserving_fst.ae (cond_absolutelyContinuous.ae_le hQ)
  have hτs := candTsF_bounds (fl := fl) hv
  have hτm := monotone_candTsF (fl := fl) hv
  have hwt : ∀ i, imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0)))
      (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ i) =
      consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ i := fun i => imgStageRhoL_treeIdxF hκ c hv i
  have hwtR : ∀ j, imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0)))
      (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ j) =
      consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ j := fun j => imgStageRhoR_treeIdxF hκ c hv j
  have hrep := isKilledStageRep_of_entrance (κ := κ) (P := μA.prod P₀) (R := Prod.fst ⁻¹' A)
    (ρL := consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ)
    (ρR := consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ)
    (iL := farL (Nat.lt_of_lt_of_le (rootNL_pos c) (Nat.le_add_right _ ℓ)))
    (iR := farR (Nat.lt_of_lt_of_le (rootNR_pos c) (Nat.le_add_right _ ℓ)))
    (y := fun p => ((0 : ℝ), fun i => VLc i 0 p.1, fun j => VRc j 0 p.1)) hle hB hWb hVLb hVRb (by
      filter_upwards [hent, hlift hstrict, hlift hfar, hlift htr] with p hE hst hfr htp hpA
      have hpA' : p.1 ∈ A := hpA
      obtain ⟨hsa, hsm⟩ := hst hpA'
      have h0ζ : ((0 : ℝ≥0) : WithTop ℝ≥0) < ζr p.1 := by
        have := (hfr hpA').pos
        exact_mod_cast this
      have hL0 : VLc ⟨0, by omega⟩ 0 p.1 ≤ 0 := by
        have := hK.ordL p.1 0 ⟨0, by omega⟩ h0ζ
        rwa [hK.w_zero p.1] at this
      have hR0 : 0 ≤ VRc ⟨0, by omega⟩ 0 p.1 := by
        have := hK.ordR p.1 0 ⟨0, by omega⟩ h0ζ
        rwa [hK.w_zero p.1] at this
      refine ⟨isOrderedForceWord_s6Start hEg hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs hτm p.1, hsa, hsm, ?_, ?_,
        fun r hr0 hr i => hK.sepL p.1 r hr0 hr i, fun r hr0 hr j => hK.sepR p.1 r hr0 hr j, hfr hpA', htp hpA'⟩
      · have e1 : (fun i => imgStageRhoL κ (flagAngle (fl 0)) (flowLineRhoL κ c.fn c.jumps 0 (flagAngle (fl 0)))
            (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ i)) =
            consAlt (bornL κ fl) (nodeρL0 κ c (flagAngle (fl 0))) ℓ := funext hwt
        have e2 : (fun j => imgStageRhoR κ (flagAngle (fl 0)) (flowLineRhoR κ c.fn c.jumps 0 (flagAngle (fl 0)))
            (fun j => candAngF fl ℓ t j - candAngF fl ℓ t 0) ℓ (treeIdx ℓ _ j)) =
            consAlt (bornR κ fl) (nodeρR0 κ c (flagAngle (fl 0))) ℓ := funext hwtR
        rw [← e1, ← e2]
        exact hE
      · show ¬ ForceWord.ThresholdCondition _ _ (Wr 0 p.1) (fun i => VLc i 0 p.1) (fun j => VRc j 0 p.1)
        have hw0 : Wr 0 p.1 = 0 := hK.w_zero p.1
        rw [hw0]
        exact not_threshold_consAlt hκ hκ4 fl hℓ _ _ hsa hsm hL0 hR0)
  exact ⟨P₀, hP₀, 𝓕, B, hrep⟩

include hκ4 in
/-- **The comparison clause of the flag candidate on the glued space from its stopped representation**
(`IsStoppedRep.isStageLawFarK`, descended from the noise factor). -/
theorem flagGluedClause_of_rep (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t)
      (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) (lastO ℓ t : ℝ)) ≠ 0)
    (hrep : FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs) :
    FlagGluedClause x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs := by
  obtain ⟨P₀, hP₀, 𝓕, B, hrep⟩ := hrep
  have := hP₀
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set Wc := candWF x₀ h44 hκ hκ4 hb h fl ℓ t with hWc
  set Eg := candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hEgdef
  set A := s3Alive s Wc Eg (lastO ℓ t : ℝ) with hAdef
  set μA := μ[|A] with hμA
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  set VLc := s6VL (flowLineXL c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) with hVLc
  set VRc := s6VR (flowLineXR c.fn c.jumps 0) (candTsF fl ℓ t) ℓ s Wc Eg (lastO ℓ t : ℝ) with hVRc
  have : StandardBorelSpace (Ω × HistorySpace 0 0) := StandardBorelSpace.prod
  have : StandardBorelSpace ((Ω × HistorySpace 0 0) × (ℕ → ℝ)) := StandardBorelSpace.prod
  have hAm : MeasurableSet[𝓐 0] A := measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0
  have hR : MeasurableSet[(𝓐 0).comap Prod.fst] (Prod.fst ⁻¹' A :
      Set ((Ω × HistorySpace 0 0) × (ℕ → ℝ))) := ⟨A, hAm, rfl⟩
  have hy0 : Measurable[𝓐 0] fun p : Ω × HistorySpace 0 0 =>
      (((0 : ℝ), fun i => VLc i 0 p, fun j => VRc j 0 p) : Start (rootNL c + ℓ) (rootNR c + ℓ)) := by
    let _ : MeasurableSpace (Ω × HistorySpace 0 0) := 𝓐 0
    have h1 : ∀ i, Measurable fun p : Ω × HistorySpace 0 0 => VLc i 0 p := fun i =>
      ((stronglyAdapted_s6VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ i) 0).measurable
    have h2 : ∀ j, Measurable fun p : Ω × HistorySpace 0 0 => VRc j 0 p := fun j =>
      ((stronglyAdapted_s6VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs _ j) 0).measurable
    exact measurable_const.prodMk ((measurable_pi_iff.2 h1).prodMk (measurable_pi_iff.2 h2))
  have hy : Measurable[(𝓐 0).comap Prod.fst] fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) =>
      (((0 : ℝ), fun i => VLc i 0 p.1, fun j => VRc j 0 p.1) : Start (rootNL c + ℓ) (rootNR c + ℓ)) :=
    hy0.comp (Measurable.of_comap_le le_rfl)
  have hobs := measurable_samp_of_adaptedBefore hrep.adapted_W hrep.adapted_VL hrep.adapted_VR
  have hL := hrep.isStoppedRep.isStageLawFarK hκ hR hy hobs
  exact CompClauseK.of_prod_fst (P₀ := P₀) (𝓐.le 0) hL.compClauseK

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
