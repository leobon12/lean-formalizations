import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.TraceHull
import QuantumZipper.Proofs.RS.HullBasics
import QuantumZipper.Proofs.RS.RealAlive

/-!
# EXT-RS node NR: the SLE trace hits the real line only at 0 (κ ≤ 4)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **NR** (task RS-TR6-NR).

## Main result (namespace `QuantumZipper.RS`)

* `ae_sleTrace_real_eq_zero` (**NR**): for `0 < κ ≤ 4`, almost surely, for every `t > 0`, if
  `(η t).im = 0` then `η t = 0`, where `η = sleTrace κ B ω`.

## Proof (Rohde–Schramm, Lemma 6.2, last paragraph of the proof, p. 24)

Almost surely the trace exists as the radial limit `f̂_t(iy) → η t` (TR4, `ae_sleTrace_good`)
and every real `x ≠ 0` is alive at every time (RL, `ae_real_alive`). If `η t = x` were real and
nonzero, let `v` be the forward flow from `x` on `[0,t]`. Since `f̂_t(iy) ∈ ℍ` and
`f̂_t(iy) → x`, D5 (`fwdFlow_near_alive_real`: `f_t w → v t` as `w → x` in `ℍ`) gives
`iy = f_t(f̂_t(iy)) → v t`; but `iy → 0`, so `v t = 0`, contradicting `v t ≠ 0`.
This is RS's "a.s. for every `x > 0` and every `s > 0` there is some neighborhood `N` of `x` in
`ℂ` such that (2.1) has a solution in `z ∈ N`, `t ∈ [0,s]`" (p. 24).

Sources: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Lemma 6.2 and
its proof (pp. 23–24); A. Kemppainen, *Schramm–Loewner Evolution*, Prop. 5.1–5.2 (pp. 78–80).
The parameter range is `0 < κ ≤ 4` (RS: `κ ∈ [0,4]`; `κ = 0` is excluded as in RL).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **NR (EXT-RS): no real hits except `0`.** For `0 < κ ≤ 4`, almost surely every real value of
the SLE trace at a positive time is `0`. Rohde–Schramm, Lemma 6.2 (pp. 23–24). -/
theorem ae_sleTrace_real_eq_zero [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), (sleTrace κ B ω t).im = 0 → sleTrace κ B ω t = 0 := by
  obtain ⟨δ, hδ, h⟩ := ae_sleTrace_good hB hκ (by linarith)
  filter_upwards [h, ae_real_alive hB hκ hκ4, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hω hRL hc h0 t ht him
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  by_contra hne
  set p := sleTrace κ B ω t with hp_def
  have hx : ((p.re : ℝ) : ℂ) = p := Complex.ext (by simp) (by simp [him])
  have hx0 : p.re ≠ 0 := fun h => hne (by rw [← hx, h]; simp)
  obtain ⟨v, hv⟩ := hRL p.re hx0 t ht.le
  obtain ⟨-, htend, hv0⟩ := fwdFlow_near_alive_real hW ht.le hv
  obtain ⟨C, hC⟩ := hω.2.2 ⌈t⌉₊
  have hlim : Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * Complex.I)) (𝓝[>] 0)
      (𝓝 p) := tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht.le, Nat.le_ceil t⟩)
  have hlimH : Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) t (y * Complex.I)) (𝓝[>] 0)
      (𝓝[H] ((p.re : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hx.symm ▸ hlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fwdMapInv_mem_H hW hW0 ht.le (mul_I_mem_H hy)
  have h1 := htend.comp hlimH
  have hev : (fwdMap (drive κ B ω) t ∘ fun y : ℝ => fwdMapInv (drive κ B ω) t (y * Complex.I))
      =ᶠ[𝓝[>] (0 : ℝ)] fun y : ℝ => y * Complex.I := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fwdMap_fwdMapInv hW hW0 ht.le (mul_I_mem_H hy)
  have hvt : v t = 0 := tendsto_nhds_unique (h1.congr' hev) tendsto_ofReal_mul_I_nhdsGT_zero
  exact hv0 hvt

end RS
end QuantumZipper
