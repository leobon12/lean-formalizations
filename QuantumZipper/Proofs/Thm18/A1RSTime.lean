import QuantumZipper.Proofs.Thm18.A1RMass
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Loewner.ForwardFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (2): time displacement of the pushing map `f_t ∘ ψ`

Toward the time modulus of the smeared-loop family `a1rfNu` (A1RFSmear.lean), whose loops are
centred at `Φ_t(w) = f_t(ψ(w))`, `ψ` the side map. For a point `z ∈ ℍ` not swallowed before
`t + h`,

`‖f_{t+h}(z) − f_t(z)‖ ≤ 24 M + 8 √h`, `M = sup_{r ∈ [0,h]} |W(t + r) − W(t)|`

(`norm_fwdMap_add_sub_le`): by the flow property `f_{t+h} = f̃_h ∘ f_t` (`fwdMap_add`, `f̃`
driven by `W(t + ·) − W(t)`) and the uniform displacement bound for a hull of half-plane
capacity `2h` (`CoreArc.norm_fwdMap_sub_le_uniform`; Lawler, *Conformally Invariant Processes in
the Plane*, Lemma 4.13 and Prop. 3.46). The bound is uniform in `z`: no Hölder regularity of the
curve is needed. The side map sends `ℍ` into the complement of every hull
(`sideMap_mem_compl_fwdHull`), so the pushing maps satisfy the same bound at every point of `ℍ`
(`norm_sidePush_add_sub_le`).

Own elementary bookkeeping on the cited Loewner estimates.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **Time displacement of the forward map, uniform in the point.** -/
theorem norm_fwdMap_add_sub_le {W : ℝ → ℝ} (hW : Continuous W) {t h M : ℝ} (ht : 0 ≤ t)
    (hh : 0 < h) (hM : ∀ r ∈ Icc (0 : ℝ) h, |W (t + r) - W t| ≤ M) {z : ℂ}
    (hz : z ∈ H \ fwdHull W (t + h)) :
    ‖fwdMap W (t + h) z - fwdMap W t z‖ ≤ 24 * M + 8 * Real.sqrt h := by
  obtain ⟨hz0, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff (by linarith)).1 hz
  rw [fwdMap_add hW hz0 ht hh.le ⟨u, isForwardSol_restrict hu (by linarith) hT'.le⟩]
  set A : ℝ → ℝ := fun r => W (t + r) - W t with hAdef
  have hA : Continuous A := by rw [hAdef]; fun_prop
  have hA0 : A 0 = 0 := by simp [hAdef]
  have hu' : IsForwardSol W z (t + (T' - t)) u := by
    rw [show t + (T' - t) = T' by ring]; exact hu
  have hsh := isForwardSol_shift hu' ht (by linarith)
  have hft : fwdMap W t z = u t := fwdMap_eq hW hz0 hu ⟨ht, by linarith⟩
  have him : 0 < (u t).im := (im_isForwardSol_le hW hz0 hu).2 t ⟨ht, by linarith⟩
  have hmem : fwdMap W t z ∈ H \ fwdHull A h := by
    rw [hft]
    exact (FwdHolo.mem_compl_fwdHull_iff hh.le).2 ⟨him, T' - t, by linarith, _, hsh⟩
  exact CoreArc.norm_fwdMap_sub_le_uniform hA hA0 hh hM hmem

/-- The side map sends `ℍ` into the complement of every hull. -/
theorem sideMap_mem_compl_fwdHull {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 ≤ t)
    (left : Bool) {w : ℂ} (hw : w ∈ H) : g1zSideMap left W w ∈ H \ fwdHull W t := by
  obtain ⟨-, -, -, hη, hK⟩ := hG
  have hU := G1ZA1a.isNormalizedUniformizer_sideDom hη left
  obtain ⟨-, -, -, hmaps⟩ := G1.invFunOn_props (G1ZA1a.isOpen_sideDom hη left) hU
  have hzD : g1zSideMap left W w ∈ sideDom (trace W) left := hmaps hw
  refine ⟨G1ZA1a.sideDom_subset_H _ left hzD, ?_⟩
  rw [hK t ht]
  rintro ⟨u, hu, hzu⟩
  have hnot : g1zSideMap left W w ∉ trace W '' Ici (0 : ℝ) := by
    cases left
    · exact hzD.1.2
    · exact hzD.1.2
  exact hnot ⟨u, le_of_lt hu.1, hzu⟩

/-- **Time displacement of the pushing maps `f_t ∘ ψ`, uniform on `ℍ`.** -/
theorem norm_sidePush_add_sub_le {W : ℝ → ℝ} (hG : G1zDrvGood W) {t h M : ℝ} (ht : 0 ≤ t)
    (hh : 0 < h) (hM : ∀ r ∈ Icc (0 : ℝ) h, |W (t + r) - W t| ≤ M) (left : Bool) {w : ℂ}
    (hw : w ∈ H) :
    ‖fwdMap W (t + h) (g1zSideMap left W w) - fwdMap W t (g1zSideMap left W w)‖ ≤
      24 * M + 8 * Real.sqrt h :=
  norm_fwdMap_add_sub_le hG.1 ht hh hM (sideMap_mem_compl_fwdHull hG (by linarith) left hw)

end A1RS
end R18
end QuantumZipper
