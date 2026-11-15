/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T15AsmLeaves

/-!
# Theorem 1.5 assembled: the tops

Packet PROVE-T15-ASSEMBLE. `Wire.theorem15Statement_lateD_expanded` (PROVE-T15-FCKER4) with every leaf discharged
except the roots, (G5) and (E1):

* **`theorem15Statement_of_g5_tgt`**: Theorem 1.5 from Theorems 1.2–1.3 (universes `u` and `0`), (G5) at `16/κ` and
  (E1) below the critical gap (universes `u` and `0`). Lemma 7.5 at `u` and `0` comes from Part A and Prop. 5.1
  (`lemma75Statement_current`); Lemma 7.6's determination from PROVE-T15-MATCH; the retained conditional determination
  from Aux. 85, Aux. 82 and leaf 3 (`T15Asm.retainedCanonCondDetHistStatement_of_lemma75`); the through kernel from
  PROVE-T15-WFS (`WFS.throughKernelStatement`); the corrected first-contact kernels inside
  `theorem15Statement_nowD` (PROVE-T15-FCKER4).
* **`theorem15Statement_of_dirsC_dyCover`** (the main top): the roots, A.1's three open directional C laws at the
  parameters (G5) uses, and the dyadic fibre cover of Prop. 5.1's (E1) at `u` and `0`.
* `theorem15Statement_of_core_dyCover` (A.1's two cores instead of the directions) and
  `theorem15Statement_of_dirsC_localCover` (the fibre-local cover `GluedLocalCoverOn` instead of the dyadic cover).

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.5 tops only.
-/

set_option autoImplicit false

noncomputable section

namespace InteractingSLE.Wire.T15Asm

universe u

/-- **Theorem 1.5 from Theorems 1.2–1.3, (G5) at `16/κ` and (E1) below the critical gap** (every other leaf of
`theorem15Statement_lateD_expanded` discharged). -/
theorem theorem15Statement_of_g5_tgt
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ))
    (htgt : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
    (htgt₀ : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{0}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) :
    Theorem15Statement.{u} := by
  have hA := Sec5.partAInputsSixteenDivOfClearance_of_inverseBoundary hG5
  have h411 : Sec5.Cond44Ref.Prop411QStatement.{u} := prop411QStatement_of_partA_clearance_now hA
  have h411₀ : Sec5.Cond44Ref.Prop411QStatement.{0} := prop411QStatement_of_partA_clearance_now hA
  have h75 := lemma75Statement_current h411 (prop51QStatement_of_partA_clearance_of_target_now hA htgt)
  have h75₀ := lemma75Statement_current h411₀ (prop51QStatement_of_partA_clearance_of_target_now hA htgt₀)
  exact theorem15Statement_nowD h12 h13 h12₀ h13₀ hA htgt htgt₀
    (lemma76DetRStatement_of_lemma75 h75 h13₀) (lemma76DetRStatement_of_lemma75 h75₀ h13₀)
    (retainedCanonCondDetHistStatement_of_lemma75 h75 h13₀)
    (retainedCanonCondDetHistStatement_of_lemma75 h75₀ h13₀)
    (fun _ hκ _ => WFS.throughKernelStatement h12₀ h13₀ hκ)

/-- **Theorem 1.5 (main top): Theorems 1.2–1.3 at `u` and `0`, A.1's three open directional C laws at the parameters
(G5) uses, and the dyadic fibre cover of Prop. 5.1's (E1) at `u` and `0`.** -/
theorem theorem15Statement_of_dirsC_dyCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hG3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ)
    (hES : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Theorem15Statement.{u} :=
  theorem15Statement_of_g5_tgt h12 h13 h12₀ h13₀ (stoppingInverseBoundary_sixteen_div_of_dirsC hG3S hG3F hES)
    (fwdNoEastSmallGap_of_thm13_dyCover h13 hDy) (fwdNoEastSmallGap_of_thm13_dyCover h13₀ hDy₀)

/-- **Theorem 1.5 from the roots, A.1's two cores and the dyadic fibre cover.** -/
theorem theorem15Statement_of_core_dyCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG3 : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hE : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂)
      Sec5.Aux61Cov.RefWin) :
    Theorem15Statement.{u} :=
  theorem15Statement_of_g5_tgt h12 h13 h12₀ h13₀
    (ZhanGT4.StopInvB.stoppingInverseBoundaryStatement_sixteen_div_of_core hG3 hE)
    (fwdNoEastSmallGap_of_thm13_dyCover h13 hDy) (fwdNoEastSmallGap_of_thm13_dyCover h13₀ hDy₀)

/-- **Theorem 1.5 from the roots, A.1's three open directional C laws and the fibre-local cover** (PROVE-T15-FWDNOEAST's
form of Prop. 5.1's (E1) input). -/
theorem theorem15Statement_of_dirsC_localCover
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hG3S : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hG3F : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ)
    (hES : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ)
    (hcov : Sec5.Aux61UnionK.GluedLocalCoverOn.{u}) (hcov₀ : Sec5.Aux61UnionK.GluedLocalCoverOn.{0}) :
    Theorem15Statement.{u} :=
  theorem15Statement_of_g5_tgt h12 h13 h12₀ h13₀ (stoppingInverseBoundary_sixteen_div_of_dirsC hG3S hG3F hES)
    (fwdNoEastSmallGap_of_thm13_localCover h13 hcov) (fwdNoEastSmallGap_of_thm13_localCover h13₀ hcov₀)

end InteractingSLE.Wire.T15Asm
