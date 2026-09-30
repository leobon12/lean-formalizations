import QuantumZipper.Proofs.Zipper.ESMLRCV

/-!
# LR-ID core: the collided-point integral as a length integral (deterministic part)

Node **LR-ID** (E-SM-inst (a)) of `handoff/E-PLAN-2.md`, blueprint
`blueprint/E_BRANCH_BLUEPRINT.md` node E-SM: in the proof of Sheffield, arXiv:1012.4797,
Lemma 5.6, a boundary point `x ∈ (0₋, 0]` of the zipped-up field `h⁰` is parametrized by its
quantum length `ℓ = ν[0₋, x]` from the left end `0₋ = zeroMinus V T` of the zipped segment; the
point collides with `0` at reverse time `τ_x`, i.e. after unzipping by capacity time `T − τ_x`
from the `Γ⁰` configuration, and `T − τ_x` is exactly the capacity time at which the unzipped
left length `L⁻` reaches `ℓ` (identity B5-V).

This file proves the deterministic core (one sample `ω`), with the objects abstracted:
`ν` (atomless, positive on intervals, finite on `[a, b]`), `z r` (= `zeroMinus V r`, strictly
decreasing on `[0, T]` with `z T = a`), `τ x` (the hit time, with `τ x ∈ [0, T]` and
`z (τ x) = x` for `x ∈ (a, b]`), and `A s` (= `L⁻_s`) with **B5-V** in the form
`A s = ν[a, z (T − s)]` for `s ∈ [0, T]`. Then (`lintegral_Ioc_eq_lintegral_lenTime`), for every
`Φ ≥ 0` (no measurability needed),
`∫⁻_{(a,b]} Φ(x, T − τ x) dν = ∫⁻_{[0, ν[a,b])} Φ(z (T − tᴸ ℓ), tᴸ ℓ) dℓ`,
`tᴸ ℓ = inf {s ≥ 0 | ℓ ≤ A s}` (`lenTime`, the `tLen` of E-PLAN-2 with `A = L⁻`).

Own elementary argument (LR-CV change of variables `ESM.lintegral_Icc_eq_lintegral_xOf'` plus
`tᴸ (ν[a,x]) = T − τ x`), following the blueprint sketch of E-SM-inst (a).
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace ESM

/-- `tᴸ ℓ = inf {s ≥ 0 | ℓ ≤ A s}`. -/
noncomputable def lenTime (A : ℝ → ℝ≥0∞) (ℓ : ℝ) : ℝ :=
  sInf {s | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ A s}

variable {ν : Measure ℝ} {a b T : ℝ} {z τ : ℝ → ℝ} {A : ℝ → ℝ≥0∞}

/-- `tᴸ (ν[a, x]) = T − τ x` for `x ∈ (a, b]`. -/
lemma lenTime_lenFn (hpos : ∀ u v, u < v → 0 < ν (Ioo u v)) (hfin : ν (Icc a b) < ⊤)
    (hT : 0 ≤ T) (hA : ∀ s ∈ Icc 0 T, A s = ν (Icc a (z (T - s))))
    (hz : StrictAntiOn z (Icc 0 T)) (hzT : z T = a)
    {x : ℝ} (hx : x ∈ Ioc a b) (hτ : τ x ∈ Icc 0 T) (hzτ : z (τ x) = x) :
    lenTime A (lenFn ν a b x) = T - τ x := by
  have hxf : ν (Icc a x) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Icc_subset_Icc_right hx.2)) hfin).ne
  unfold lenTime
  rw [lenFn_of_le hx.2, ENNReal.ofReal_toReal hxf]
  refine IsLeast.csInf_eq ⟨⟨by linarith [hτ.2], ?_⟩, fun s hs => ?_⟩
  · rw [hA _ ⟨by linarith [hτ.2], by linarith [hτ.1]⟩, sub_sub_cancel, hzτ]
  · by_contra hlt
    push Not at hlt
    have hsT : s ∈ Icc 0 T := ⟨hs.1, by linarith [hτ.1]⟩
    have hmem : T - s ∈ Icc 0 T := ⟨by linarith [hsT.2], by linarith [hs.1]⟩
    have h1 : z (T - s) < x := hzτ ▸ hz hτ hmem (by linarith)
    have h2 : a ≤ z (T - s) := by
      rcases eq_or_lt_of_le hmem.2 with h | h
      · rw [h, hzT]
      · exact hzT ▸ (hz hmem ⟨hT, le_rfl⟩ h).le
    have hlt' := lrcv_measure_lt hpos h2 h1
      (ne_top_of_le_ne_top hxf (measure_mono (Icc_subset_Icc_right h1.le)))
    have hs2 : ν (Icc a x) ≤ A s := hs.2
    rw [hA s hsT] at hs2
    exact absurd hs2 (not_le.2 hlt')

/-- **LR-ID core.** Under B5-V (`hA`) and the collision structure (`hz`, `hzT`, `hτ`):
`∫⁻_{(a,b]} Φ(x, T − τ x) dν = ∫⁻_{[0, ν[a,b])} Φ(z (T − tᴸ ℓ), tᴸ ℓ) dℓ` for every `Φ ≥ 0`. -/
theorem lintegral_Ioc_eq_lintegral_lenTime (hatom : ∀ x, ν {x} = 0)
    (hpos : ∀ u v, u < v → 0 < ν (Ioo u v)) (hab : a ≤ b) (hfin : ν (Icc a b) < ⊤)
    (hT : 0 ≤ T) (hA : ∀ s ∈ Icc 0 T, A s = ν (Icc a (z (T - s))))
    (hz : StrictAntiOn z (Icc 0 T)) (hzT : z T = a)
    (hτ : ∀ x ∈ Ioc a b, τ x ∈ Icc 0 T ∧ z (τ x) = x) (Φ : ℝ → ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioc a b, Φ x (T - τ x) ∂ν =
      ∫⁻ ℓ in Ico 0 (ν (Icc a b)).toReal, Φ (z (T - lenTime A ℓ)) (lenTime A ℓ) := by
  have key : EqOn (fun x => Φ x (T - τ x))
      (fun x => Φ (z (T - lenTime A (lenFn ν a b x))) (lenTime A (lenFn ν a b x))) (Ioc a b) := by
    intro x hx
    simp only
    rw [lenTime_lenFn hpos hfin hT hA hz hzT hx (hτ x hx).1 (hτ x hx).2, sub_sub_cancel,
      (hτ x hx).2]
  rw [setLIntegral_congr_fun measurableSet_Ioc key,
    Measure.restrict_congr_set (Ioc_ae_eq_Icc' (hatom a)),
    lintegral_Icc_eq_lintegral_xOf' ν a b hab hatom hpos hfin]
  exact setLIntegral_congr_fun measurableSet_Ico fun ℓ hℓ => by
    simp only [lenFn_xOf hab hatom hpos hfin hℓ]

end ESM
end QuantumZipper
