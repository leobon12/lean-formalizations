import QuantumZipper.Proofs.Zipper.B3dDet

/-!
# B3(d): both unzipped lengths are rescaling-equivariant (deterministic)

For F2 step (2a) (`F2.F2UnscaledStmt`: F1 for the canonical wedge plus random rescaling B3(d)
gives `L⁻ = L⁺` for the unscaled wedge field): with `a = scaleParam γ y`, the pair of lengths
unzipped from `canonConfig γ (y, W)` in capacity time `s` equals the pair unzipped from `(y, W)`
in time `a² s` (`unzipLengths_canon`), given the field identity (B3(d) at the field level),
goodness of the unzipped field and existence of both side images. Hence the agreement
`L⁻ = L⁺` transfers between a configuration and its canonicalization (`lenAgree_canon_iff`).
Own elementary argument (Sheffield, arXiv:1012.4797, §5.1 states the scaling without proof).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B3d

theorem tendsto_mul_nhdsGT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => a * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_nhdsWithin_of_forall fun r (hr : 0 < r) => mul_pos ha hr⟩
  have := ((continuous_const_mul a).tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-- **Right side image of the rescaled driver.** -/
theorem sideImages_snd_scale (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {s l : ℝ} (hs : 0 ≤ s)
    (hL : Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * s) r).re) (𝓝[>] (0 : ℝ)) (𝓝 l)) :
    (sideImages (fun r => W (a ^ 2 * r) / a) s).2 = l / a := by
  unfold sideImages
  refine Tendsto.limUnder_eq ?_
  refine ((hL.comp (tendsto_mul_nhdsGT ha)).div_const a).congr fun r => ?_
  simp only [Function.comp_apply]
  rw [fwdMap_scale_of W ha hs, Complex.div_ofReal_re]
  push_cast
  rfl

variable {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ}

end B3d
end QuantumZipper
