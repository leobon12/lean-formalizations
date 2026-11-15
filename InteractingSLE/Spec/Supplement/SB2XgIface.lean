/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XcIface
import InteractingSLE.Spec.Supplement.SB2XfChain

/-!
# The per-stage correspondence with the chain's driver agreeing with `EL`'s up to the chain's horizon (D11 addendum)

Packet PROVE-T14-SB2LIFT (round 25). `StageChainAtR` (D11, accepted) keeps `EL`'s driver itself as the chain's
driver and asks the chain's global `IsLoewnerTrace` field for a trace agreeing with `EL`'s below the relative
lifetime. At a finite relative lifetime this needs a Loewner trace of the driver frozen exactly at its lifetime; the
library extends a trace only from a time strictly before its horizon (`IsLoewnerTraceLT.isLoewnerTrace_ext`). The
relative chain at `S₀` is used only up to `capClock γ S₀`, which is strictly below the relative lifetime.

* **`StageChainAtR2`** / **`SB2LowerStageChainStatementR2`**: `StageChainAtR` with the chain's driver and trace any
  pair agreeing with `EL`'s driver and trace on `[0, capClock γ S₀]` (for each `S₀`). This is what
  `relChainCore_concrete` (`SB2XfChain`) proves.
* **`StageChainAtR.toR2`**, **`sb2LowerStageChainStatementR2_of`**: it is a weakening of the R form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Mn

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk
open LuM (trOf)
open FinRel (IsSB2RelChain)

section Corr

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (EL : ℕ → Ω → Drv)

/-- **The per-stage correspondence, R2**: `StageChainAtR` with the chain's driver and trace agreeing with `EL`'s on
`[0, capClock γ S₀]`. -/
def StageChainAtR2 (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ') →
    (EL j ω).2 ≠ 0 →
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 1)).2.2.2.1
      (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ≠ none ∧
    IsDomainChart (H \ stageRetained (walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω)
        (upperPrefix κ b jumps E u l k ω₀ ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
      (stageRelChart (walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m) ∧
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      (∀ s : ℝ≥0, ((tL + s : ℝ≥0) : ℝ≥0∞) <
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2 →
        Tendsto (stageRelChart (walkStageChart κ b jumps E
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m).2.1
        (𝓝[H] (γ s)) (𝓝 (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) (tL + s)))) ∧
      (∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2 →
        ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
          (∀ r : ℝ, 0 ≤ r → r ≤ Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
            Wr r = (EL j ω).1 r.toNNReal ∧ ηr r = trOf (EL j ω) r.toNNReal) ∧
        IsSB2RelChain (stageRetained (walkStageChart κ b jumps E
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω)
            (upperPrefix κ b jumps E u l k ω₀ ∪
              SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
                (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                  (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
          (stageRelChart (walkStageChart κ b jumps E
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m)
          (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω))
          γ tL (S₀ : ℝ) Wr ηr) ∧
      (EL j ω).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2),
        ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ))

/-- **R2 is a weakening of the R form.** -/
theorem StageChainAtR.toR2 {ω : Ω} (h : StageChainAtR κ b jumps E u l k ω₀ c b' J' m EL ω) :
    StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω := by
  intro j c₁ θ' hl hz
  obtain ⟨h1, h2, tL, γ, h3, ⟨ηr, hηr, h4⟩, h5⟩ := h j c₁ θ' hl hz
  refine ⟨h1, h2, tL, γ, h3, fun S₀ hS₀ => ⟨_, ηr, fun r hr0 hr => ⟨rfl, hηr r hr0 ?_⟩, h4 S₀ hS₀⟩, h5⟩
  -- below the relative lifetime: a later `S₀'` before B's lifetime has a strictly larger capacity
  obtain ⟨q, hq1, hq2⟩ := exists_between hS₀
  have hqt : q ≠ ⊤ := ne_top_of_lt hq2
  have hQ : tL + S₀ < q.toNNReal := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hqt]
    exact hq1
  set S₀' : ℝ≥0 := q.toNNReal - tL with hS₀'
  have htS : tL + S₀' = q.toNNReal := add_tsub_cancel_of_le (le_of_lt (lt_of_le_of_lt le_self_add hQ))
  have hS₀'q := lt_of_eq_of_lt
    (show ((tL + S₀' : ℝ≥0) : ℝ≥0∞) = q by rw [htS, ENNReal.coe_toNNReal hqt]) hq2
  have hlt : S₀ < S₀' := by
    have : tL + S₀ < tL + S₀' := by rw [htS]; exact hQ
    exact lt_of_add_lt_add_left this
  have hch := h4 S₀' hS₀'q
  have hmono := hch.2.2.2.2.1
  have hS₀mem : (S₀ : ℝ) ∈ Icc (0 : ℝ) S₀' := ⟨S₀.2, NNReal.coe_le_coe.2 hlt.le⟩
  have hS₀'mem : (S₀' : ℝ) ∈ Icc (0 : ℝ) S₀' := ⟨S₀'.2, le_rfl⟩
  have hc0 : 0 ≤ Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) := ((hch.2.2.2.2.2.2 _ hS₀mem).1)
  have hclt := hmono hS₀mem hS₀'mem (NNReal.coe_lt_coe.2 hlt)
  rw [h5]
  calc ENNReal.ofReal r ≤ ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) :=
        ENNReal.ofReal_le_ofReal hr
    _ < ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀' : ℝ)) :=
        (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hc0 hclt)).2 hclt
    _ ≤ _ := le_iSup₂_of_le (f := fun (S : ℝ≥0) (_ : ((tL + S : ℝ≥0) : ℝ≥0∞) < _) =>
        ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S : ℝ))) S₀' hS₀'q le_rfl

end Corr

/-- **SB2(2)'s per-stage correspondence, R2** (`SB2LowerStageChainStatementR` with `StageChainAtR2`). -/
def SB2LowerStageChainStatementR2 : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω

/-- The R form implies R2. -/
theorem sb2LowerStageChainStatementR2_of (h : SB2LowerStageChainStatementR.{u}) :
    SB2LowerStageChainStatementR2.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hω₀
  intro c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hD
  filter_upwards [hω₀ c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hD] with ω hω
  exact StageChainAtR.toR2 κ b jumps E u l k ω₀ c b' J' m EL hω

end InteractingSLE.Theorem14.SB.Mn
