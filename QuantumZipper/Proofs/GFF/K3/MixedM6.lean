import QuantumZipper.Proofs.GFF.K3.MixedM6Kernel
import QuantumZipper.Proofs.GFF.K3.MixedM6Cont

/-!
# GFF-K3 node M6: the mixed covariance is `neumannH + k` near the free arc

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M6). Statement fixed in `MixedM5Stmt.lean`
(`MixedLocalKernelStmt`). Proof: route (ii) of `handoff/K3-MIXED.md` (`D`-only):
`MixedM6Sing` (singular part), `MixedM6Kernel` (assembly, kernel `mixedK`),
`MixedM6Cont` (norm continuity of `z ↦ v_{fold_{z,s}}` on `K`). The radius is `s = R / 2`.
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper.K3

/-- **M6.** Near the free arc, the mixed covariance is `neumannH` plus a kernel continuous on
`K × K`. -/
theorem mixedLocalKernel {D K : Set ℂ} {c d R : ℝ} : MixedLocalKernelStmt D c d K R := by
  intro hG h
  have hpos := exists_pos_energy_mixedSpace (S := realSet (Icc c d)) hG.1 hG.2.1.nonempty
  have hR := h.pos
  have hs : 0 < R / 2 := by positivity
  have hsR : R / 2 < R := by linarith
  have hcont := continuousOn_rieszVec_foldedCircle h hs hsR
  exact ⟨mixedK D (realSet (Icc c d)) (R / 2),
    continuousOn_mixedK (fun z hz => (h.local_ z hz).1) hs hcont,
    fun μ ν hμ hμK hν hνK => dualCov_mixed_eq_kernelCov_mixedK h hpos hs hsR hcont hμ hμK hν hνK⟩

end QuantumZipper.K3
