/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsTail
import InteractingSLE.Spec.Zhan.WordsRef
import InteractingSLE.Spec.Zhan.Empty
import InteractingSLE.Spec.Zhan.WW83

/-!
# Transience for every separated word, `κ ≤ 4`: assembly

Packet PROVE-ZHAN-B4. Astra §3, "Chordal transience for an arbitrary finite word" (`source/external/AstraIG1/
ig1_formalization_proofs.txt` L1585–L1615). For `0 < κ ≤ 4`, an ordered admissible word whose marks are all
strictly separated from the seed:

* with no marks, it is ordinary `SLE_κ` (`Empty.lean`);
* otherwise, move every weight of a side onto its outermost mark (`WordsRef.lean`: the reference is a two-group word
  after relabelling, transient by PROVE-ZHAN-B3). The change of weights has finite total energy — the linear escape
  of the inner strip gaps (Astra (3.24)), recorded here as `MergeEnergyStatement κ` — and the whole-tail comparison
  (`WordsTail.lean`) transfers transience.

## Main results

* `MergeEnergyStatement κ`: almost-sure finiteness of the total energy of the merge (the input still named).
* `IsIntegratedSLEEvolution.ae_tendsto_norm_trace_of_mergeEnergy`: transience of one separated word from the
  finiteness of its merge energy.
* `separatedTransienceStatement_of_mergeEnergy`: `SeparatedTransienceStatement κ` for `0 < κ ≤ 4`, given
  `MergeEnergyStatement κ`; hence `aux7Statement_of_mergeEnergy` (Aux. lemma 7) and
  `zhanNonboundaryTransience_of_mergeEnergy` (Wang–Wu's input 8.3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart Coupling

/-- **Finite energy of the merge** (Astra §3, linear escape of lower strip gaps (3.24) and the exponential decay of
the coth errors, L1520–L1563, L1590–L1594). For an ordered admissible word whose marks are all strictly separated
from the seed, every integrated evolution has, almost surely, bounded energy
`κ⁻¹ ∫₀ᵀ (∑ⱼ (ρ'ⱼ − ρⱼ)/(W − Vⱼ))²` (uniformly in `T`) for the change of weights `ρ → ρ'` that moves every weight of a
side onto its outermost mark. -/
def MergeEnergyStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR → (∀ i, xL i < 0) →
      (∀ j, 0 < xR j) → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL (outerW ρL) ρR (outerW ρR) W VL VR T ω ≤ m

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- The good event of a separated admissible word: infinite lifetime, `W₀ = 0`, a continuous state, and all gaps
positive at every time (Aux. lemma 6). -/
theorem IsIntegratedSLEEvolution.ae_good_separated (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (fun s => stateAt W VL VR s ω) ∧
      ∀ s, 0 < minGap (stateAt W VL VR s ω) := by
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.2.2.2.2]
    with ω h6 hp
  obtain ⟨hζ, hsep⟩ := h6
  rw [hζ] at hp
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf => by
    rw [← continuousOn_univ]; exact hf.mono fun t _ => ENNReal.coe_lt_top
  refine ⟨hζ, hp.1, ?_, fun s => ?_⟩
  · exact (hcont hp.2.2.2.1).prodMk ((continuous_pi fun i => hcont (hp.2.2.2.2.1 i)).prodMk
      (continuous_pi fun j => hcont (hp.2.2.2.2.2.1 j)))
  · rw [minGap, Finset.lt_inf'_iff]
    intro k _
    have hgL : ∀ i, VL i s ω < W s ω := fun i => by
      rcases eq_zero_or_pos s with rfl | hs
      · have h1 : VL i 0 ω = xL i := hp.2.1 i
        have h2 : W 0 ω = 0 := hp.1
        rw [h1, h2]; exact hxL i
      · exact (hsep s hs).1 i
    have hgR : ∀ j, W s ω < VR j s ω := fun j => by
      rcases eq_zero_or_pos s with rfl | hs
      · have h1 : VR j 0 ω = xR j := hp.2.2.1 j
        have h2 : W 0 ω = 0 := hp.1
        rw [h1, h2]; exact hxR j
      · exact (hsep s hs).2 j
    rcases k with _ | i | j
    · exact one_pos
    · exact abs_pos.2 (sub_ne_zero.2 (hgL i).ne')
    · exact abs_pos.2 (sub_ne_zero.2 (hgR j).ne)

/-- **Transience of a separated word from the finiteness of its merge energy** (`0 < κ ≤ 4`). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_of_mergeEnergy [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0) (hxR : ∀ j, 0 < xR j)
    (hn : 0 < nL + nR) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (henergy : ∀ᵐ ω ∂P, ∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL (outerW ρL) ρR (outerW ρR) W VL VR T ω ≤ m) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  ae_tendsto_of_changeEnergy hκ (fun i j => (hxL i).trans (hxR j)) hE
    (IsIntegratedSLEEvolution.ae_good_separated hκ hF hadm hxL hxR hE) henergy
    (codeLaw_outerW_lifetime hκ hκ4 hF hadm hxL hxR)
    (codeLaw_outerW_lateSet_tendsto_zero hκ hκ4 hF hadm hxL hxR hn)

/-- **Transience for every separated word** (`0 < κ ≤ 4`), given the finiteness of merge energies. -/
theorem separatedTransienceStatement_of_mergeEnergy (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hM : MergeEnergyStatement.{u} κ) : SeparatedTransienceStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hF hadm hxL hxR hE
  rcases Nat.eq_zero_or_pos (nL + nR) with h0 | hn
  · obtain ⟨rfl, rfl⟩ : nL = 0 ∧ nR = 0 := ⟨by omega, by omega⟩
    exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_empty hκ hE
  · exact IsIntegratedSLEEvolution.ae_tendsto_norm_trace_of_mergeEnergy hκ hκ4 hF hadm hxL hxR hn hE
      (hM xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hxL hxR hE)

/-- **Aux. lemma 7 for `0 < κ ≤ 4`**, given the finiteness of merge energies. -/
theorem aux7Statement_of_mergeEnergy (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hM : MergeEnergyStatement.{u} κ) :
    Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_separatedTransience hκ hκ4 (separatedTransienceStatement_of_mergeEnergy hκ hκ4 hM)
    (Sec7.RandRestart.randomRestartTraceStatement hκ)

/-- **Wang–Wu's input 8.3** (Zhan's nonboundary transience at `κ = 4`), given the finiteness of merge energies. -/
theorem zhanNonboundaryTransience_of_mergeEnergy (hM : MergeEnergyStatement.{u} 4) :
    WangWu.ZhanNonboundaryTransience.{u} :=
  zhanNonboundaryTransience_of_separatedTransience
    (separatedTransienceStatement_of_mergeEnergy (by norm_num) le_rfl hM)

end InteractingSLE.Zhan
