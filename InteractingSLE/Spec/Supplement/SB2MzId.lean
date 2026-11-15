/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzTr
import InteractingSLE.Spec.Supplement.SB2MqIface

/-!
# The identification at a relative stage, in the notation of the per-stage correspondence

Packet PROVE-SB2-LCMEAN, round 15 (item 4). `Mz.ident_at_sample` read with the objects of SB2LIFT's
`Mn.StageChainAtR2` and `Mq.StageChainAtP` at a sample `ω` under the upper kernel. The canonical objects of the
matched B-stage come from the `P`-level clause `Mz.CanonIdentOn` and use the upper prefix at `ω`, which is the one at
`ω₀` (the upper run is frozen under the upper kernel):

* **`ident_rel_stage`**: at a launched relative stage `i` of positive lifetime, with normalized upper chart, relative
  run chart and B's stage chart, `EL i` agrees with the canonical driver before their common lifetime, and the
  canonical hull chart agrees with the physical relative chart on the retained complement;
* **`recOf_eq_of_ident`**: the records then agree.

All statements are deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Mz

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mx

/-- **The identification at a relative stage** in the notation of the per-stage correspondence. -/
theorem ident_rel_stage {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ ω : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {EL : ℕ → Ω → Drv} (hR2 : Mn.StageChainAtR2 κ b jumps E u l k ω₀ c b' J' m EL ω)
    (hP : Mq.StageChainAtP κ b jumps E u l k ω₀ c b' J' m EL ω)
    (hup : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀) {i : ℕ} {c₁ : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (i + 1)).2.2.2.1 i = some (c₁, θ')) (hz : (EL i ω).2 ≠ 0)
    (hcN : WalkIntCanon.IsNormalized c) (hc₁N : WalkIntCanon.IsNormalized c₁)
    (hcℓN : WalkIntCanon.IsNormalized (Mn.walkStageChart κ b jumps E
      (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω))
    {K : Set ℂ} (hK : IsHPHull (fillH K)) {x₀ : ℝ} {D : Drv}
    (hfillK : fillH K = fillH (retY (κ := κ) b jumps E u l k
      (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω))
    (hC : ChainFor (Mn.stageRetained (Mn.walkStageChart κ b jumps E
        (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)
        (retY (κ := κ) b jumps E u l k
          (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω))
      (stageChartOf (Mn.walkStageChart κ b jumps E
        (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)) ω)
        (Mo.hullChart (fillH K) x₀))
      (LuM.trOf (lowerD b jumps E ω
        (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω))))
      (lowerD b jumps E ω
        (i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω))).2 D)
    (hD : D.2 ≠ 0) :
    (EL i ω).2 = D.2 ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < (EL i ω).2 → (EL i ω).1 t = D.1 t) ∧
      EqOn (Mo.hullChart (fillH K) x₀).1 (Mo.physRelChart c c₁ m).1 (H \ fillH K) ∧
      EqOn (Mo.hullChart (fillH K) x₀).2.2 (Mo.physRelChart c c₁ m).2.2 (H \ fillH K) := by
  set N := i + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) (lowerD b jumps E ω)
    with hN
  have hY : retY (κ := κ) b jumps E u l k N ω = upperPrefix κ b jumps E u l k ω₀ ∪
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) N := by
    show upperPrefix κ b jumps E u l k ω ∪ _ = _
    rw [hup]
  rw [hY] at hfillK hC
  rw [hfillK] at hK hC ⊢
  obtain ⟨hPd⟩ : Nonempty (IsDomainChart (H \ fillH (upperPrefix κ b jumps E u l k ω₀ ∪
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) N)) (Mo.physRelChart c c₁ m)) :=
    ⟨hP i c₁ θ' hl hz⟩
  obtain ⟨-, hdR, -⟩ := hR2 i c₁ θ' hl hz
  have hfill := notMem_fillH_stageRetained hcℓN hK.2.1 hdR
  obtain ⟨hlife, hagree, hfwd, hlift⟩ :=
    ident_at_sample hK hcN hc₁N hcℓN.conformal hPd hdR hfill (chainFor_of_stageChainAtR2 hR2 hl hz) hC hz hD
  exact ⟨hlife, hagree, hfwd, hlift⟩

/-- **The records of identified drivers agree** (the relative driver continuous up to its lifetime). -/
theorem recOf_eq_of_ident {e D : Drv} (he : IsRegularDriver e) (hD : IsRegularDriver D)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min ⊤ e.2}) (hlife : e.2 = D.2)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = D.1 t) : recOf ⊤ e = recOf ⊤ D := by
  unfold recOf
  rw [StagedDet.retOf_eq_of_agree he hD hc hlife.symm fun s hs => (hagree s hs).symm]

end InteractingSLE.Theorem14.SB.Mz
