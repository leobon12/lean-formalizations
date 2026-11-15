/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtConc
import InteractingSLE.Spec.Supplement.GW1PieceChart

/-!
# SB2(2): the relative pieces are regular (`StageFactsAll`'s last field)

Packet PROVE-SB2-LIFTSET (round 18). `Mn.StageFacts` ends with `GW1P.PieceRegular e₂.1 e₂.2` for the relative driver
`e₂` of a stage. It follows from the stage's relative facts (`StageRelP`) and the generation of the stage curve below
its capacity lifetime:

* **`pieceRegular_of_stageRelFinP`**: at a finite piece (the endpoint extension `α` generates on the closed interval);
* **`pieceRegular_of_stageRelInfP`**: at an infinite piece, given transience of the capacity trace when the relative
  lifetime is infinite;
* **`pieceRegular_of_stageRelP`**: both cases.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {e₂ : Drv}

/-- An extension of the capacity trace that is continuous through the relative lifetime generates there. -/
theorem isGeneratingTrace_of_ext {ρ : ℝ → ℂ} {α : ℝ≥0 → ℂ} (he₂ : e₂.2 = capLife ρ)
    (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ))
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ) (hα0 : α 0 = 0)
    (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) : IsGeneratingTrace e₂.1 e₂.2 α := by
  refine ⟨hα0, hαc, fun t ht => ?_⟩
  obtain ⟨T'', htT'', hT''⟩ := exists_between ht
  have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
  rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]

/-- **A finite stage's relative driver is regular** (from its relative facts and generation). -/
theorem pieceRegular_of_stageRelFinP (hg : StageRelFinP c m p L s₂ e₂)
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0) : GW1P.PieceRegular e₂.1 e₂.2 := by
  obtain ⟨hfin, hW, ⟨α, f, hαeq, hα0, hαc, -, -⟩, -, -, -⟩ := hg
  exact ⟨hW0, hW, α, isGeneratingTrace_of_ext he₂ hgen hαeq hα0 hαc, fun h => absurd h hfin⟩

/-- **An infinite stage's relative driver is regular**, given transience of the capacity trace when the relative
lifetime is infinite. -/
theorem pieceRegular_of_stageRelInfP (hg : StageRelInfP c m p L s₂ e₂)
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0)
    (htr : e₂.2 = ⊤ → Tendsto (fun τ => ‖capTrace (stCurvep c m p L s₂) τ‖) atTop atTop) :
    GW1P.PieceRegular e₂.1 e₂.2 := by
  obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, -, -, -⟩, -, -, -⟩ := hg
  refine ⟨hW0, hW, α, isGeneratingTrace_of_ext he₂ hgen hαeq hα0 hαc, fun htop => ?_⟩
  refine (htr htop).congr' (Eventually.of_forall fun τ => ?_)
  show _ = ‖α τ‖
  rw [hαeq τ (by rw [htop]; exact ENNReal.coe_lt_top)]

/-- **A stage's relative driver is regular** (both cases). -/
theorem pieceRegular_of_stageRelP (hg : StageRelP c m p L s₂ e₂)
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0)
    (htr : L = ⊤ → e₂.2 = ⊤ → Tendsto (fun τ => ‖capTrace (stCurvep c m p L s₂) τ‖) atTop atTop) :
    GW1P.PieceRegular e₂.1 e₂.2 := by
  by_cases hL : L = ⊤
  · exact pieceRegular_of_stageRelInfP (hg.2 hL) he₂ hgen hW0 (htr hL)
  · exact pieceRegular_of_stageRelFinP (hg.1 hL) he₂ hgen hW0

end InteractingSLE.Theorem14.SB.Lk
