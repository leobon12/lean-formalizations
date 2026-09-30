import QuantumZipper.Proofs.Thm18.G1PkgPsi

/-!
# G1 package: right-normalized uniformizers from left-normalized ones

`G1Chord.SideUnifExistStmt` (G1PkgChordFin.lean) asks for left- and right-normalized
uniformizers of every simple chord. By the reflection `refl z = −z̄` (which swaps the two
components, `CA.Uniformizer.bijOn_refl_right`), a left-normalized uniformizer `φ` of `refl ∘ η`
gives the right-normalized uniformizer `refl ∘ φ ∘ refl` of `η`
(`isRightUniformizer_of_refl`, the converse direction of `CA.Kernel.isLeftUniformizer_refl`).
So only the left existence `LeftUnifExistStmt` remains:
`g1PsiSelStmt_of_leftUnifExist : LeftUnifExistStmt → G1PsiSelStmt`.

Own elementary argument (mirror of `CA.Kernel.isLeftUniformizer_refl`).
-/

noncomputable section

open Filter Set Function Topology Bornology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

open CA.Kernel CA.Uniformizer

/-- Every simple chord has a left-normalized uniformizer (`φ(−1) = −1`). -/
def LeftUnifExistStmt : Prop := ∀ η : ℝ → ℂ, IsSimpleChord η → ∃ φ, IsLeftUniformizer η φ

theorem isRightUniformizer_of_refl {η : ℝ → ℂ} (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsLeftUniformizer (refl ∘ η) φ) :
    IsRightUniformizer η (fun z => refl (φ (refl z))) := by
  obtain ⟨⟨hφb, hφd, hφ0, hφinf⟩, hφ1⟩ := hφ
  have hLo := isOpen_leftComponent (isSimpleChord_refl_comp hη)
  have hT : ∀ a : ℂ, Tendsto refl (𝓝[rightComponent η] a)
      (𝓝[leftComponent (refl ∘ η)] (refl a)) := fun a =>
    tendsto_nhdsWithin_iff.2 ⟨(continuous_refl.tendsto a).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono fun _ hz => refl_mem_left_of_mem_right hz⟩
  refine ⟨⟨bijOn_refl_H.comp (hφb.comp (bijOn_refl_right η)), fun z hz => ?_, ?_, ?_⟩, ?_⟩
  · have hz' := refl_mem_left_of_mem_right hz
    exact (differentiableAt_refl_comp_refl
      (hφd.differentiableAt (hLo.mem_nhds hz'))).differentiableWithinAt
  · have h0' : Tendsto refl (𝓝[rightComponent η] 0) (𝓝[leftComponent (refl ∘ η)] 0) := by
      simpa [CA.Uniformizer.refl] using hT 0
    have h := (continuous_refl.tendsto 0).comp (hφ0.comp h0')
    simpa [CA.Uniformizer.refl, Function.comp_def] using h
  · have h1 : Tendsto refl (cobounded ℂ ⊓ 𝓟 (rightComponent η))
        (cobounded ℂ ⊓ 𝓟 (leftComponent (refl ∘ η))) := by
      refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (eventually_inf_principal.2
        (Eventually.of_forall fun z hz => refl_mem_left_of_mem_right hz))⟩
      rw [← tendsto_norm_atTop_iff_cobounded]
      simpa using tendsto_norm_cobounded_atTop.mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 (rightComponent η) ≤ cobounded ℂ)
    simpa [Function.comp_def] using hφinf.comp h1
  · have h1' : Tendsto refl (𝓝[rightComponent η] 1) (𝓝[leftComponent (refl ∘ η)] (-1)) := by
      simpa [CA.Uniformizer.refl] using hT 1
    have h := (continuous_refl.tendsto (-1)).comp (hφ1.comp h1')
    simpa [CA.Uniformizer.refl, Function.comp_def] using h

theorem sideUnifExistStmt_of_left (h : LeftUnifExistStmt) : SideUnifExistStmt := by
  intro η hη
  refine ⟨h η hη, ?_⟩
  obtain ⟨φ, hφ⟩ := h (refl ∘ η) (isSimpleChord_refl_comp hη)
  exact ⟨_, isRightUniformizer_of_refl hη hφ⟩

end G1Chord

/-- **`G1PsiSelStmt` from the existence of left-normalized uniformizers.** -/
theorem g1PsiSelStmt_of_leftUnifExist (h : G1Chord.LeftUnifExistStmt) : G1PsiSelStmt :=
  g1PsiSelStmt_of_sideUnifExist (G1Chord.sideUnifExistStmt_of_left h)

end Thm18Asm
end QuantumZipper
