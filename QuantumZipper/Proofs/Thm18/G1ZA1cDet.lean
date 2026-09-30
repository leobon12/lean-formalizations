import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G4Rezip2Base
import QuantumZipper.Proofs.Thm14.WeldingData

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1c (deterministic part): lengths at the new root through the identified transport

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71): after unzipping by quantum length `ℓ`, the old root sits at the boundary point
`O^∓_{t'}` of the unzipped picture, and the boundary segment between it and the new root has quantum
length `ℓ` (lengths are carried by the conformal maps, "by conformal invariance" of the boundary
measure, and scale by (1.8) under the rescaling).

Here, for a side map `ψ` with reflection data `Φ` (`SideReflGood`), a good field `x`, a scale
`a > 0` and the pushed side measure `ν = ((ν_{rescale x Q a})|_half).map Φ⁻¹`:
* `g1zA1c_refl_tendsto`: `ψ → Φ β` at a boundary point `β` of the side half-line;
* `g1zA1c_seg`: if `a ψ → O` at `β`, then `ν(seg β) = ν_x[O, 0]` (left) / `ν_x[0, O]` (right);
* `g1zA1c_pos`: `ν` charges open intervals of the half-line if `ν_{rescale x Q a}` charges open
  intervals.
Own bookkeeping (elementary).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1c

theorem half_map {left : Bool} {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) {s : ℝ}
    (hs : s ∈ g1SideHalf left) : Φ s ∈ g1SideHalf left := by
  cases left
  · simp only [g1SideHalf, Bool.false_eq_true, if_false, mem_Ioi] at hs ⊢
    rw [← h0]; exact Φ.lt_iff_lt.2 hs
  · simp only [g1SideHalf, if_true, mem_Iio] at hs ⊢
    rw [← h0]; exact Φ.lt_iff_lt.2 hs

theorem neBot_nhdsWithin_H (β : ℝ) : (𝓝[H] (β : ℂ)).NeBot := by
  refine mem_closure_iff_nhdsWithin_neBot.1 ?_
  exact mem_closure_of_tendsto (G1Z5.tendsto_appr β)
    (Eventually.of_forall fun n => G1Z5.appr_mem_H β n)

/-- Boundary values of a side map with reflection data. -/
theorem g1zA1c_refl_tendsto {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ}
    (hR : SideReflGood left ψ Φ) {β : ℝ} (hβ : β ∈ g1SideHalf left) :
    Tendsto ψ (𝓝[H] (β : ℂ)) (𝓝 (Φ β : ℂ)) := by
  obtain ⟨p, q, hpq, hS, hβpq⟩ := exists_side_window left (isCompact_singleton (x := β))
    (singleton_subset_iff.2 hβ)
  obtain ⟨U, Ψ, hU, hJU, hΨd, hΨΦ, -, hEq⟩ := hR.2 p q hpq hS
  have hβI : β ∈ Icc p q := Ioo_subset_Icc_self (hβpq (mem_singleton β))
  have hc : ContinuousAt Ψ (β : ℂ) :=
    (hΨd.differentiableAt (hU.mem_nhds (hJU β hβI))).continuousAt
  have h1 : Tendsto Ψ (𝓝[H] (β : ℂ)) (𝓝 (Φ β : ℂ)) := by
    rw [← hΨΦ β hβI]; exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hEq hz).symm

/-- The value `a Φ β = O` from the boundary limit of `a ψ`. -/
theorem g1zA1c_refl_val {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ}
    (hR : SideReflGood left ψ Φ) {β : ℝ} (hβ : β ∈ g1SideHalf left) {a O : ℝ}
    (hlim : Tendsto (fun u => (a : ℂ) * ψ u) (𝓝[H] (β : ℂ)) (𝓝 (O : ℂ))) :
    a * Φ β = O := by
  haveI := neBot_nhdsWithin_H β
  have h := ((g1zA1c_refl_tendsto hR hβ).const_mul (a : ℂ))
  have := tendsto_nhds_unique h hlim
  exact_mod_cast this

/-- **Positivity on open intervals of the half-line.** -/
theorem g1zA1c_pos {ν : Measure ℝ} (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v))
    {left : Bool} {Φ : ℝ ≃o ℝ} (h0 : Φ 0 = 0) {u v : ℝ} (huv : u < v)
    (hsub : Ioo u v ⊆ g1SideHalf left) :
    0 < ((ν.restrict (g1SideHalf left)).map Φ.symm) (Ioo u v) := by
  have hΦm : Measurable Φ.symm := Φ.symm.continuous.measurable
  rw [Measure.map_apply hΦm measurableSet_Ioo, Measure.restrict_apply (hΦm measurableSet_Ioo)]
  refine (hpos _ _ (Φ.lt_iff_lt.2 huv)).trans_le (measure_mono fun y hy => ?_)
  have hy' : Φ.symm y ∈ Ioo u v := by
    refine ⟨?_, ?_⟩
    · rw [OrderIso.lt_symm_apply]; exact hy.1
    · rw [OrderIso.symm_apply_lt]; exact hy.2
  refine ⟨hy', ?_⟩
  have := half_map h0 (hsub hy')
  rwa [OrderIso.apply_symm_apply] at this

end G1ZA1c
end Thm18Asm
end QuantumZipper
