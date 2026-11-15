/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XfChain
import InteractingSLE.Spec.Supplement.SB2JiGeom

/-!
# Sample-level glue for (G3): the relative chain core from LIFTSET's per-stage geometry

Packet PROVE-T14-SB2LIFT (round 26). **`relChain_of_stageGeomFin`**: at a stage of PROVE-SB2-LIFTSET's concrete rule
with a finite positive actual piece — LIFTSET's per-stage geometry `StageGeomFin` (landed, `SB2JiGeom`), the drivenness
of the stage curve and generation below its capacity lifetime — there is a relative chart-coordinate lift `γ` (the
stage lift of `SB2XfChain`, with `StageGeomFin`'s continuous extension `α`) such that:

* for every `S₀` before the actual lifetime, all fields of `FinRel.IsSB2RelChain` except the two hull fields hold for a
  driver and trace agreeing with the relative driver and **its chosen trace `LuM.trOf e₂`** on `[0, capClock γ S₀]`;
* the relative lifetime is the supremum of `γ`'s capacity clock before the actual lifetime.

This is the chain clause of `Mn.StageChainAtR2` without the hull fields (PROVE-GW2-GEOM2's builder).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {m : ℝ} {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ s₂ : ExplState} {e₁ e₂ : Drv}

/-- **(G3) at a stage of the concrete rule with a finite positive actual piece**, from LIFTSET's per-stage geometry. -/
theorem relChain_of_stageGeomFin (hg : StageGeomFin c m β₀ tL s₁ e₁ s₂ e₂)
    (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂)) (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW0 : e₂.1 0 = 0) (he₁ : e₁.2 ≠ ⊤) (hpos : e₁.2 ≠ 0) :
    ∃ γ : ℝ≥0 → ℂ,
      (∀ S₀ : ℝ≥0, (S₀ : ℝ≥0∞) < e₁.2 → ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
          Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
        RelChainCore γ (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : (S₀ : ℝ≥0∞) < e₁.2),
        ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  obtain ⟨-, -, -, -, hfin, hW, ⟨α, f, hαeq, hα0, hαc, -, -⟩, -, -, -, -, -⟩ := hg
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : ℝ≥0, e₁.2 = L₁ := ⟨e₁.2.toNNReal, (ENNReal.coe_toNNReal he₁).symm⟩
  have hL₁pos : 0 < L₁ := by
    rw [hL₁] at hpos
    exact pos_iff_ne_zero.2 (by exact_mod_cast hpos)
  have hlt : ∀ S₀ : ℝ≥0, (S₀ : ℝ≥0∞) < e₁.2 ↔ S₀ < L₁ := fun S₀ => by rw [hL₁]; exact ENNReal.coe_lt_coe
  -- the relative trace is `α`, and `trOf e₂ = α` up to the relative lifetime
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T'', htT'', hT''⟩ := exists_between ht
    have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hpr₂ : GW1P.PieceRegular e₂.1 e₂.2 := ⟨hW0, hW, α, hαg, fun h => absurd h hfin⟩
  have htr : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.trOf e₂ τ = α τ :=
    GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr₂) hWlt hW0
  refine ⟨stageLift c m s₁ e₁ s₂ α, fun S₀ hS₀ => ?_, lifetime_eq_iSup_capClock hρ he₂ hαeq hL₁ hL₁pos⟩
  have hS₀L : (S₀ : ℝ) < L₁ := NNReal.coe_lt_coe.2 ((hlt S₀).1 hS₀)
  obtain ⟨Wr, ηr, hagree, hcore⟩ := relChainCore_concrete hρ he₂ hgen hfin hW hW0 hαeq hα0 hαc hL₁ S₀.2 hS₀L
  refine ⟨Wr, ηr, fun r hr0 hr => ?_, hcore⟩
  obtain ⟨h1, h2⟩ := hagree r hr0 hr
  refine ⟨h1, ?_⟩
  -- `r` is below the relative lifetime
  have hcapS : capClock (fun r : ℝ => stageLift c m s₁ e₁ s₂ α r.toNNReal) (S₀ : ℝ) =
      capClock (stCurve c m s₁ e₁ s₂) ((S₀ : ℝ) / (L₁ - S₀)) :=
    capClock_stageLift hρ he₂ hαeq hL₁ S₀.2 hS₀L
  have hu0 : 0 ≤ (S₀ : ℝ) / (L₁ - S₀) := div_nonneg S₀.2 (sub_nonneg.2 hS₀L.le)
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
    rw [he₂]
    refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt hu0))
    rw [← hcapS]
    exact ENNReal.ofReal_le_ofReal hr
  rw [h2, htr _ hrle]

end InteractingSLE.Theorem14.SB.Mn
