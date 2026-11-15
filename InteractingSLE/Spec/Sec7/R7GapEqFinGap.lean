/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinAttach
import InteractingSLE.Spec.Sec7.R7GapEqFinCorner
import InteractingSLE.Spec.Sec7.R7GapEqFinOuter

/-!
# The finite mixed gap equality with attachment and corner inputs expanded

PROVE-R7-GAPEQ continuation. Combine the Jordan collar, full contained-arm extension,
one-barrier rational witnesses, and the landed phase contradiction. The original
`PocketGapEq` conclusion is unchanged. The remaining field and local face geometry are
displayed as named hypotheses rather than concealed in `BarrierAttachConst` or a gap axiom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq R7StopIn PocketJordan Aux37Attach

/-- Reverse visit order passes to an increasing affine subarc. -/
theorem reverseVisitOrder_affine_subarc {η α B : ℝ → ℂ} {a b : ℝ}
    (hα : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a))) :
    R16.IsReverseVisitOrder B fun t => η '' Icc 0 t := by
  have hm : ∀ v ∈ Icc (0 : ℝ) 1, a + v * (b - a) ∈ Icc (0 : ℝ) 1 := by
    intro v hv
    have hnonneg := mul_nonneg hv.1 (sub_nonneg.2 hab.le)
    have hle := mul_le_mul_of_nonneg_right hv.2 (sub_nonneg.2 hab.le)
    constructor <;> linarith
  intro t v hv w hw hvw hvis
  have hmono : a + v * (b - a) ≤ a + w * (b - a) := by
    linarith only [mul_le_mul_of_nonneg_right hvw (sub_nonneg.2 hab.le)]
  rw [hB v hv] at hvis
  rw [hB w hw]
  exact hα t _ (hm v hv) _ (hm w hw) hmono hvis

/-- **Finite mixed gap equality, expanded inputs.** The proof discharges both the one-barrier
attachment constancy and the shared-corner input of `pocketGapEq_of_exterior_incidence`.
The newly isolated mathematics is `hinc`/`hfr` (outer local geometry), the allowed enlargement
`V` (its old boundary uses the full contained arm), and `hcompare` (the field germs at one
rational witness). No theorem taking full determination as an input is used. -/
theorem pocketGapEq_of_extension_and_germs
    {W : ℝ → ℝ} {η B A α : ℝ → ℂ} {C F K V D : Set ℂ} {τ σ a b : ℝ}
    (hC : IsCfPocket C B A) (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (h42 : ∀ r s : ℝ, 0 ≤ r → r < s → ¬ η '' Icc r s ⊆ K) (hfrK : frontier C ⊆ K)
    (hFo : IsOpen F) (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hinc : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 → p ∈ closure (F \ closure C))
    (hfr : ∀ p ∈ A '' Icc 0 1, p ∉ B '' Icc 0 1 →
      ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (hτf : η τ ∉ η '' Ico 0 τ)
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hαrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (ha : 0 ≤ a) (hab : a < b) (hb : b < 1)
    (hB : ∀ v ∈ Icc (0 : ℝ) 1, B v = α (a + v * (b - a)))
    (hVo : IsOpen V) (hCV : C ⊆ V) (hV : V ⊆ C ∪ F ∪ K)
    (hVK : frontier V ⊆ K) (hD : IsClosed D)
    (hfrV : frontier V ⊆ α '' Icc 0 1 ∪ D) (hpD : α b ∉ D)
    (marks : Finset ℝ) {χ lam lam' ε θ : ℝ}
    (hχ : 0 < χ) (hlam : lam - lam' = Real.pi * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) ∨
      (ε = -1 ∧ θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)))
    (hcompare : ∀ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ →
      (∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂) →
      ∃ (G : Filter ℂ) (M Lf Lc : ℂ → ℝ) (k : ℤ), G.NeBot ∧
        Tendsto (fun z => M z + χ * Lf z) G (𝓝 (ε * lam - θ * χ)) ∧
        Tendsto (fun z => M z + χ * Lc z) G (𝓝 (ε * lam' - Real.pi * χ)) ∧
        Tendsto (fun z => Lf z - Lc z) G (𝓝 (2 * Real.pi * k))) :
    PocketGapEq η C τ σ := by
  have hrev := reverseVisitOrder_affine_subarc hαrev ha hab hb.le hB
  have hAC := barrierAttachConst_of_germs hη.2.1 hC.cont₁ hC.inj₁ hrev hτ0 hτ marks
    hχ hlam hside hcompare
  have hcorner := cornerCover_of_contained_extension (σ := σ) hη.2.1 hC.cont₁ hαc hαi hαrev
    ha hab hb hB hτ0 hτ hVo hCV hV hVK hD hfrV hpD
  have hfrC : frontier C ⊆ B '' Icc 0 1 ∪ A '' Icc 0 1 := hC.frontier_eq.le
  have hA : IsClosed (A '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hC.cont₂).isClosed
  have hdisj : ∀ v ∈ Ioo (0 : ℝ) 1, B v ∉ A '' Icc 0 1 := by
    rintro v hv ⟨w, hw, hwv⟩
    have hw0 : w ≠ 0 := fun hw0 => hv.1.ne' (hC.inj₁ ⟨hv.1.le, hv.2.le⟩
      ⟨le_rfl, zero_le_one⟩ (hwv.symm.trans (by rw [hw0, hC.junction])))
    have hw1 : w ≠ 1 := fun hw1 => hv.2.ne (hC.inj₁ ⟨hv.1.le, hv.2.le⟩
      ⟨zero_le_one, le_rfl⟩ (hwv.symm.trans (by rw [hw1, hC.seed])))
    exact hC.sides v hv w ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0), lt_of_le_of_ne hw.2 hw1⟩ hwv.symm
  apply pocketGapEq_of_cornerCover hη hW hW0 hC.isOpen h42 hfrK havoid hA hfrC hdisj
    (fun p hp hpB => ?_) hC.cont₁ hC.inj₁ hrev hτ0 hτ hτf hAC hcorner
  exact hasExteriorCollar_of_exterior_incidence hC.isOpen hC.isConnected hC.isBounded
    (isJordanCurve_frontier_of_isCfPocket hC) (hC.frontier_eq.symm ▸ Or.inr hp)
    hFo hfrK (hinc p hp hpB) (hfr p hp hpB)

end InteractingSLE.Sec7.R7GapEqFin
