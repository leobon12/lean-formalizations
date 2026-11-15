/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XoGen
import InteractingSLE.Spec.Supplement.SB2JtConc

/-!
# (G3) from PROVE-SB2-LIFTSET's v3 relative facts (D6)

Packet PROVE-T14-SB2LIFT (round 26). LIFTSET's v3 rule reads the actual piece through a general point map `p` (the
shifted start piece at stage `0`, the unshifted pieces elsewhere) with stage curves `stCurvep c m p L s₂`; its
relative facts are `StageRelP` (`StageRelFinP` at a finite piece, `StageRelInfP` at an infinite one). With the
drivenness of the stage curve and generation below its capacity lifetime:

* **`trOf_eq_of_gen`**: the relative driver's chosen trace is `α` up to a finite relative lifetime;
* **`relChain_of_stageRelFinP`**: at a finite positive piece, the chain clause of `StageChainAtR2` without the hull
  fields (agreement with `LuM.trOf e₂`) and the lifetime clause, for the lift `liftCurve (stCurvep …) L α`;
* **`relChain_of_stageRelInfP`**: the same at an infinite piece whose relative lifetime is finite, for
  `liftCurveTop (stCurvep …) α`; **`relChain_of_stageRelInfP'`**: at any relative lifetime, from the regularity of
  the relative launch (`PieceRegular`, given by the bundle's relative `RegLaunches`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk Sec7.PocketTraversal Sec7.Lemma71C

variable {ρ : ℝ → ℂ} {e₂ : Drv} {α : ℝ≥0 → ℂ}

/-- **The chosen trace of the relative driver is `α`** up to a finite relative lifetime. -/
theorem trOf_eq_of_gen (he₂ : e₂.2 = capLife ρ) (hgen : ∀ T < capLife ρ, IsGeneratingTrace e₂.1 T (capTrace ρ))
    (hfin : e₂.2 ≠ ⊤) (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace ρ τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) :
    ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.trOf e₂ τ = α τ := by
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T'', htT'', hT''⟩ := exists_between ht
    have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hpr₂ : GW1P.PieceRegular e₂.1 e₂.2 := ⟨hW0, hW, α, hαg, fun h => absurd h hfin⟩
  exact GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr₂) hWlt hW0

variable {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState}

/-- **(G3) at a finite positive piece of the v3 rule.** -/
theorem relChain_of_stageRelFinP (hg : StageRelFinP c m p L s₂ e₂) (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0) {L₁ : ℝ≥0} (hpos : 0 < L₁) :
    ∃ γ : ℝ≥0 → ℂ,
      (∀ S₀ : ℝ≥0, S₀ < L₁ → ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
          Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
        RelChainCore γ (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0) (_ : S₀ < L₁), ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  obtain ⟨hfin, hW, ⟨α, f, hαeq, hα0, hαc, -, -⟩, -, -, -⟩ := hg
  have htr := trOf_eq_of_gen he₂ hgen hfin hW hW0 hαeq hα0 hαc
  refine ⟨liftCurve (stCurvep c m p L s₂) L₁ α, fun S₀ hS₀ => ?_, lifetime_eq_iSup_gen hρ he₂ hαeq hpos⟩
  have hS₀L : (S₀ : ℝ) < L₁ := NNReal.coe_lt_coe.2 hS₀
  obtain ⟨Wr, ηr, hagree, hcore⟩ := relChainCore_gen hρ he₂ hgen hfin hW hW0 hαeq hα0 hαc (NNReal.coe_nonneg S₀) hS₀L
  refine ⟨Wr, ηr, fun r hr0 hr => ?_, hcore⟩
  obtain ⟨h1, h2⟩ := hagree r hr0 hr
  refine ⟨h1, ?_⟩
  have hu0 : 0 ≤ (S₀ : ℝ) / (L₁ - S₀) := div_nonneg (NNReal.coe_nonneg S₀) (sub_nonneg.2 hS₀L.le)
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
    rw [he₂]
    refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt hu0))
    rw [← capClock_liftCurve hρ he₂ hαeq (NNReal.coe_nonneg S₀) hS₀L]
    exact ENNReal.ofReal_le_ofReal hr
  rw [h2, htr _ hrle]

/-- **(G3) at an infinite piece of the v3 rule with a finite relative lifetime.** -/
theorem relChain_of_stageRelInfP (hg : StageRelInfP c m p L s₂ e₂) (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0) (hfin : e₂.2 ≠ ⊤) :
    ∃ γ : ℝ≥0 → ℂ,
      (∀ S₀ : ℝ≥0, ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
          Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
        RelChainCore γ (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0), ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, -, -, -⟩, -, -, -⟩ := hg
  have htr := trOf_eq_of_gen he₂ hgen hfin hW hW0 hαeq hα0 hαc
  refine ⟨liftCurveTop (stCurvep c m p L s₂) α, fun S₀ => ?_, lifetime_eq_iSup_genTop hρ he₂ hαeq⟩
  obtain ⟨Wr, ηr, hagree, hcore⟩ := relChainCore_genTop hρ he₂ hgen hW hW0 hαeq hα0 hαc S₀.2
  refine ⟨Wr, ηr, fun r hr0 hr => ?_, hcore⟩
  obtain ⟨h1, h2⟩ := hagree r hr0 hr
  refine ⟨h1, ?_⟩
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
    rw [he₂]
    refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt (NNReal.coe_nonneg S₀)))
    rw [← capClock_liftCurveTop hρ he₂ hαeq (NNReal.coe_nonneg S₀)]
    exact ENNReal.ofReal_le_ofReal hr
  rw [h2, htr _ hrle]

/-- **(G3) at an infinite piece of the v3 rule, any relative lifetime**: the regularity of the relative launch
(`RegLaunches` of the relative walk gives `PieceRegular`, with a transient trace at an infinite lifetime) identifies its
chosen trace with `α`. -/
theorem relChain_of_stageRelInfP' (hg : StageRelInfP c m p L s₂ e₂) (hρ : IsDrivenCurve (stCurvep c m p L s₂))
    (he₂ : e₂.2 = capLife (stCurvep c m p L s₂))
    (hgen : ∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂)))
    (hW0 : e₂.1 0 = 0) (hpr : GW1P.PieceRegular e₂.1 e₂.2) :
    ∃ γ : ℝ≥0 → ℂ,
      (∀ S₀ : ℝ≥0, ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
        (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
          Wr r = e₂.1 r.toNNReal ∧ ηr r = LuM.trOf e₂ r.toNNReal) ∧
        RelChainCore γ (S₀ : ℝ) Wr ηr) ∧
      e₂.2 = ⨆ (S₀ : ℝ≥0), ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) := by
  obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, -, -, -⟩, -, -, -⟩ := hg
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T'', htT'', hT''⟩ := exists_between ht
    have h := (hgen T'' (by rw [← he₂]; exact hT'')).2.2 t htT''
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {s | (s : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have htr : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → LuM.trOf e₂ τ = α τ :=
    GW4Leaf.eqOn_of_isGeneratingTrace hαg (LuM.isGeneratingTrace_trOf hpr) hWlt hW0
  refine ⟨liftCurveTop (stCurvep c m p L s₂) α, fun S₀ => ?_, lifetime_eq_iSup_genTop hρ he₂ hαeq⟩
  obtain ⟨Wr, ηr, hagree, hcore⟩ := relChainCore_genTop hρ he₂ hgen hW hW0 hαeq hα0 hαc (NNReal.coe_nonneg S₀)
  refine ⟨Wr, ηr, fun r hr0 hr => ?_, hcore⟩
  obtain ⟨h1, h2⟩ := hagree r hr0 hr
  refine ⟨h1, ?_⟩
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ e₂.2 := by
    rw [he₂]
    refine le_of_lt (lt_of_le_of_lt ?_ (hρ.ofReal_capClock_lt (NNReal.coe_nonneg S₀)))
    rw [← capClock_liftCurveTop hρ he₂ hαeq (NNReal.coe_nonneg S₀)]
    exact ENNReal.ofReal_le_ofReal hr
  rw [h2, htr _ hrle]

end InteractingSLE.Theorem14.SB.Mn
