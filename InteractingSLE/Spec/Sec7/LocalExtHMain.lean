/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHKer

/-!
# Aux. lemma 54 for stopped seed couplings, from its four remaining inputs

Packet PROVE-LOCEXT-H. **`stoppedSeedExtensionStatement_of_inputs`**: LOCEXT-F's named input
`StoppedSeedExtensionStatement κ` (Aux. lemma 54 for a stopped seed coupling, the one step shared by Theorem 1.2's
time-`0` extension and its restarts) holds for every `κ > 0`, given the four named inputs of `LocalExtHStmt`:

* `StdTwoSeedReferenceStatement κ` — a standard reference (Theorem 1.1's construction on a standard Borel space);
* `StoppedTwoSeedLawStatement κ` — **(U)**, uniqueness in law of the merged two-seed history through the local stop;
* `ExtPreStopStatement κ` — **(K-pre)**, the protected kernel before the local stop on the extension;
* `ExtLocalityStatement κ` — **(Loc)**, locality of the hulls on the extension.

Proved here (with `LocalExtHExt`, `LocalExtHLaw`, `LocalExtHKer`): the record law **(M)** — the record (stopped history,
field off its hull) has the same law in the stopped coupling and in the reference (`map_recOf_eq_of_hasHistKernel`, with
the kernels `IsStoppedSeedCoupling.exists_hasHistKernel` and `exists_hasHistKernel_ref`); the extension by one
disintegration of the reference, its evolution **(V)**, its time-`0` field law, the protected kernel after the local stop
**(K-post)**, the good event and the recovery of the stopped history (`hasReferenceExtension_of_recordLaw`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 LQGMetric

/-- The left seed sum of a side without seed is `0`. -/
theorem seedSumL_eq_zero {nL : ℕ} {xL ρL : Fin nL → ℝ} (h : ¬ ∃ i, xL i = 0) : seedSumL xL ρL = 0 := by
  rw [seedSumL_eq]
  exact Finset.sum_eq_zero fun i hi => absurd ⟨i, (Finset.mem_filter.1 hi).2⟩ h

/-- The right seed sum of a side without seed is `0`. -/
theorem seedSumR_eq_zero {nR : ℕ} {xR ρR : Fin nR → ℝ} (h : ¬ ∃ j, xR j = 0) : seedSumR xR ρR = 0 := by
  rw [seedSumR_eq]
  exact Finset.sum_eq_zero fun i hi => absurd ⟨i, (Finset.mem_filter.1 hi).2⟩ h

/-- **Aux. lemma 54 for stopped seed couplings** (LOCEXT-F's `StoppedSeedExtensionStatement κ`), from a standard
reference (`StdTwoSeedReferenceStatement`), uniqueness in law through the local stop (U), the protected kernel before the
local stop on the extension (K-pre) and locality on the extension (Loc). -/
theorem stoppedSeedExtensionStatement_of_inputs {κ : ℝ} (hκ : 0 < κ) (hRef : StdTwoSeedReferenceStatement.{u} κ)
    (hU : StoppedTwoSeedLawStatement.{u} κ) (hPre : ExtPreStopStatement.{u} κ) (hLoc : ExtLocalityStatement.{u} κ) :
    StoppedSeedExtensionStatement.{u} κ := by
  intro nL nR xL xR ρL ρR r hF hr hL hR Ω mΩ Q hQ W VL VR S h hc
  obtain ⟨Ωr, mΩr, Pr, 𝓕r, Wr, VLr, VRr, Br, ζr, hr', href⟩ := hRef _ _ hL hR
  obtain ⟨-, hPr, hC, -, -⟩ := id href
  have : IsProbabilityMeasure Pr := hPr
  obtain ⟨Gr, hGm, hG0, hG⟩ := exists_goodEvent hC.1 hκ
  have hlawU := hU xL xR ρL ρR r hF hr hL hR Q W VL VR S h hc Pr 𝓕r Wr VLr VRr Br ζr hC.1 Gr hGm hG0 hG
  have hver := ae_refVer_eq xL xR hL hR hr hG0 hG
  obtain ⟨-, -, -, -, -, -, -, hhm, -⟩ := id hc
  have hlaw : Q.map (stRecHist xL xR W VL VR S) = Pr.map (refVer xL xR r Gr Wr VLr VRr ζr) := by
    rw [Measure.map_congr (hc.ae_stRecHist_eq hr), hlawU, (Measure.map_congr hver).symm]
  have hY₂m : Measurable (refVer xL xR r Gr Wr VLr VRr ζr) := by
    obtain ⟨m₂, hm₂, hY₂, -⟩ := exists_hasHistKernel_ref (hr' := hr') xL xR hL hR hr hC hGm hG0 hG
      seedSumL_eq_zero seedSumR_eq_zero
    exact hY₂.mono hm₂ le_rfl
  have hrec : Q.map (fun ω => recOf (h ω) (stRecHist xL xR W VL VR S ω)) =
      Pr.map (fun ω => recOf (hr' ω) (refVer xL xR r Gr Wr VLr VRr ζr ω)) := by
    obtain ⟨m₁, hm₁, hY₁, hk₁⟩ := hc.exists_hasHistKernel hr
    obtain ⟨m₂, hm₂, hY₂, hk₂⟩ := exists_hasHistKernel_ref xL xR hL hR hr hC hGm hG0 hG seedSumL_eq_zero
      seedSumR_eq_zero
    exact map_recOf_eq_of_hasHistKernel (mΩ₁ := mΩ) (mΩ₂ := mΩr) hm₁ hm₂ hY₁ hY₂ hhm hC.2.1
      (measurable_kerFun κ _ _) hk₁ hk₂ hlaw
  exact hasReferenceExtension_of_recordLaw hκ hF hr hL hR hc href hGm hG0 hG
    (Rr := fun ω => recOf (hr' ω) (refVer xL xR r Gr Wr VLr VRr ζr ω))
    (measurable_recOf.comp (hC.2.1.prodMk hY₂m))
    (by filter_upwards [hver] with ω hω; rw [hω]) hrec hPre hLoc

end LocalExt

end InteractingSLE
