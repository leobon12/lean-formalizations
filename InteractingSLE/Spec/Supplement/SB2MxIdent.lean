/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxStage
import InteractingSLE.Spec.Supplement.SB2XgIface

/-!
# Identification of `EL`'s stage driver with the canonical driver at one sample

Packet PROVE-SB2-LCMEAN, round 14 (item 4: identification with `EL`). `Mn.StageChainAtR2` says, at a launched relative
stage of positive lifetime, that `EL`'s stage driver is the driver of relative chains of B's matched piece, with its
lifetime the supremum of the chain clocks. **`ChainFor`** is that clause as a predicate of a driver. Two drivers with
`ChainFor` for the same piece, in two domain charts of the same domain that differ by a real translation, are equal
before their common lifetime:

* **`ChainFor`**, **`chainFor_of_stageChainAtR2`** (the projection of R2);
* **`ident_of_chainFor`**: both lifetimes positive ⇒ the translation is `0`, the lifetimes agree and the drivers agree
  before them (`Mx.tL_eq_of_chains`, `Mx.eqOn_of_chains`).

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mx

open Sec7.Lemma71C

/-- **The chain clause of a driver** (the form of `Mn.StageChainAtR2`): for some start `tL` and stage curve `γ`, at
every `S₀` with `tL + S₀` before the piece's lifetime `BL`, the driver is, up to the clock time at `S₀`, the driver of
a relative chain of the piece `β'` over `A` in the chart `c`, and its lifetime is the supremum of these clock times. -/
def ChainFor (A : Set ℂ) (c : Chart) (β' : ℝ≥0 → ℂ) (BL : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
    (∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL → ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ),
      (∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) → Wr r = e.1 r.toNNReal) ∧
      FinRel.IsSB2RelChain A c β' γ tL (S₀ : ℝ) Wr ηr) ∧
    e.2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL),
      ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ))

/-- From a positive lifetime, a positive `S₀` before the piece's lifetime with a positive clock. -/
theorem exists_pos_of_chainFor {BL : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {tL : ℝ≥0} {γ : ℝ≥0 → ℂ}
    (he : e.2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL),
      ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)))
    {t : ℝ≥0∞} (ht : t < e.2) :
    ∃ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL ∧ t < ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) S₀) := by
  rw [he] at ht
  obtain ⟨S₀, hS₀⟩ := lt_iSup_iff.1 ht
  obtain ⟨hlt, h⟩ := lt_iSup_iff.1 hS₀
  exact ⟨S₀, hlt, h⟩

/-- **Two drivers with the chain clause of the same piece, in charts differing by a real translation, agree.** -/
theorem ident_of_chainFor {A : Set ℂ} {cR cC : Chart} {β' : ℝ≥0 → ℂ} {BL : ℝ≥0∞} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {d : ℝ} (hdR : IsDomainChart (H \ A) cR) (hdC : IsDomainChart (H \ A) cC)
    (hfill : ∀ z ∈ H \ A, z ∉ fillH A) (hfwd : ∀ z ∈ H \ A, cC.1 z = cR.1 z + d)
    (hR : ChainFor A cR β' BL e) (hC : ChainFor A cC β' BL e') (he : e.2 ≠ 0) (he' : e'.2 ≠ 0) :
    d = 0 ∧ e.2 = e'.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = e'.1 t := by
  obtain ⟨tL, γ, hRc, hRe⟩ := hR
  obtain ⟨tL', γ', hCc, hCe⟩ := hC
  -- a positive `S₀` on each side
  have hpos : ∀ {tL : ℝ≥0} {γ : ℝ≥0 → ℂ} {e : (ℝ≥0 → ℝ) × ℝ≥0∞},
      e.2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL),
        ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ)) → e.2 ≠ 0 →
      ∃ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL ∧ 0 < capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) := by
    intro tL γ e hE hne
    obtain ⟨S₀, h1, h2⟩ := exists_pos_of_chainFor hE (pos_iff_ne_zero.2 hne)
    exact ⟨S₀, h1, ENNReal.ofReal_pos.1 h2⟩
  -- the clock is `0` at `0`, so a positive clock time needs a positive `S₀`
  have hS₀pos : ∀ {A : Set ℂ} {c : Chart} {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {S₀ : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ},
      FinRel.IsSB2RelChain A c β' γ tL (S₀ : ℝ) W η → 0 < capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) →
      (0 : ℝ) < S₀ := by
    intro _ _ _ _ S₀ _ _ hch hcap
    obtain ⟨-, -, -, h0, -, -, -⟩ := hch
    rcases (NNReal.coe_nonneg S₀).lt_or_eq with h | h
    · exact h
    · rw [← h, h0] at hcap
      exact absurd hcap (lt_irrefl 0)
  obtain ⟨S₁, hS₁, hcap₁⟩ := hpos hRe he
  obtain ⟨S₂, hS₂, hcap₂⟩ := hpos hCe he'
  obtain ⟨W₁, η₁, -, hch₁⟩ := hRc S₁ hS₁
  obtain ⟨W₂, η₂, -, hch₂⟩ := hCc S₂ hS₂
  have htL : tL = tL' :=
    tL_eq_of_chains hdR hdC hfill (hS₀pos hch₁ hcap₁) (hS₀pos hch₂ hcap₂) hch₁ hch₂
  subst htL
  -- at every positive `S₀` before the lifetime, the two chains agree
  have hcmp : ∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL → (0 : ℝ) < S₀ →
      capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) = capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ) ∧ d = 0 ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) → e.1 r.toNNReal = e'.1 r.toNNReal := by
    intro S₀ hS₀ hpos₀
    obtain ⟨WR, ηR, hWR, hchR⟩ := hRc S₀ hS₀
    obtain ⟨WC, ηC, hWC, hchC⟩ := hCc S₀ hS₀
    obtain ⟨hclk, hd, heq⟩ := eqOn_of_chains hdR hdC hfill hfwd hpos₀ hchR hchC
    refine ⟨hclk S₀ ⟨NNReal.coe_nonneg S₀, le_rfl⟩, hd, fun r hr0 hr => ?_⟩
    rw [← hWR r hr0 hr, heq ⟨hr0, hr⟩, hWC r hr0 (by rw [← hclk S₀ ⟨NNReal.coe_nonneg S₀, le_rfl⟩]; exact hr)]
  -- the clocks agree at every `S₀` before the lifetime (`0` at `0`)
  have hclk : ∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) < BL →
      capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) = capClock (fun r : ℝ => γ' r.toNNReal) (S₀ : ℝ) := by
    intro S₀ hS₀
    rcases (NNReal.coe_nonneg S₀).lt_or_eq with h | h
    · exact (hcmp S₀ hS₀ h).1
    · obtain ⟨WR, ηR, -, hchR⟩ := hRc S₀ hS₀
      obtain ⟨WC, ηC, -, hchC⟩ := hCc S₀ hS₀
      obtain ⟨-, -, -, h0R, -, -, -⟩ := hchR
      obtain ⟨-, -, -, h0C, -, -, -⟩ := hchC
      rw [← h, h0R, h0C]
  have hlife : e.2 = e'.2 := by
    rw [hRe, hCe]
    exact iSup_congr fun S₀ => iSup_congr fun hS₀ => by rw [hclk S₀ hS₀]
  refine ⟨(hcmp S₁ hS₁ (hS₀pos hch₁ hcap₁)).2.1, hlife, fun t ht => ?_⟩
  obtain ⟨S₀, hS₀, htS⟩ := exists_pos_of_chainFor hRe ht
  have hcpos : 0 < capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) :=
    ENNReal.ofReal_pos.1 (lt_of_le_of_lt bot_le htS)
  obtain ⟨-, -, hagree⟩ := hcmp S₀ hS₀ (hS₀pos (Classical.choose_spec (Classical.choose_spec (hRc S₀ hS₀))).2
    hcpos)
  have htle : (t : ℝ) ≤ capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ) := by
    have := (ENNReal.ofReal_lt_ofReal_iff hcpos).1 (by rwa [ENNReal.ofReal_coe_nnreal])
    exact this.le
  have := hagree (t : ℝ) (NNReal.coe_nonneg t) htle
  simpa only [Real.toNNReal_coe] using this

section R2

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk LuM

/-- **`EL`'s stage driver has the chain clause** (the projection of `Mn.StageChainAtR2`). -/
theorem chainFor_of_stageChainAtR2 {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω}
    {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}
    (hR2 : Mn.StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω) {j : ℕ} {c₁ : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ'))
    (hz : (EL j ω).2 ≠ 0) :
    ChainFor (Mn.stageRetained (Mn.walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω)
        (upperPrefix κ b jumps E u l k ω₀ ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
      (Mn.stageRelChart (Mn.walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m)
      (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω))
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2
      (EL j ω) := by
  obtain ⟨-, -, tL, γ, -, hch, hlife⟩ := hR2 j c₁ θ' hl hz
  refine ⟨tL, γ, fun S₀ hS₀ => ?_, hlife⟩
  obtain ⟨Wr, ηr, hW, hc⟩ := hch S₀ hS₀
  exact ⟨Wr, ηr, fun r hr0 hr => (hW r hr0 hr).1, hc⟩

end R2

end InteractingSLE.Theorem14.SB.Mx
