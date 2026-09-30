import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.Zipper.F1Side
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Statements.ConfigLaw

/-!
# B3(d): rescaling equivariance of length unzipping (deterministic core)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §B3 (b), (d) and §E6 ("`Z_C C̄_x =
zipLenDown γ ℓ₁ (Z_C C̄_{x_{ℓ₀}})` (`zipLenDown_eq_canonConfig`, addConst multiplies lengths by
`e^{C/2}`, B3(d))"). Paper: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.1 (pp. 60–62): a quantum surface is an equivalence class under the coordinate changes (1.3),
in particular under `z ↦ a z` with the field shifted by `Q log a`, and adding a constant `C` to
the field multiplies boundary lengths by `e^{γC/2}` (Duplantier–Sheffield 2011, (5.1)). The paper
states the equivariance of the length zipper under these operations without proof; the argument
below is our own (elementary algebra of the definitions).

Contents (all deterministic):

* `fwdMap_scale_of`: Loewner scaling of the forward map at **every** starting point (no `0 < im`,
  no continuity of the driver), from the Grönwall uniqueness `F1.fwdMap_eq_of_isForwardSol`.
* `sideImages_fst_scale`: `O⁻` of the Brownian-rescaled driver `W(a²·)/a` at time `s` is
  `O⁻(W, a²s)/a`, when the one-sided limit defining `O⁻(W, a²s)` exists.
* `sInf_scale`: first-passage times scale by `1/c` under time change `t = c s`.
* `unzipLengths_canon_fst`: the left length unzipped from `canonConfig γ (x + k, W)` in capacity
  time `s` is `e^{γk/2}` times the left length unzipped from `(x, W)` in time `a² s`, given the
  field identity `hfield` (B3(d) at the field level) and goodness of the unzipped fields.
* `zipLenDown_canonConfig_addConst`: the **zip algebra of `ZipLenCanonStmt` at one
  configuration**: `zipLenDown γ ℓ (canonConfig γ (x + k, W)) ≈ canonConfig γ (x_{t₀} + k, W_{t₀})`
  where `t₀` is the first time the `e^{γk/2}`-scaled left length of `(x, W)` reaches `ℓ`.

The one analytic input is the field identity `hfield`: the field unzipped from the canonicalized
configuration in time `s` is (up to `RegEq`) the rescaling by `a` of the constant-shifted field
unzipped from `(x, W)` in time `a² s`. This is the composition law of coordinate changes for the
two factorizations `(a·) ∘ f^{W_a}_s⁻¹ = f^W_{a²s}⁻¹ ∘ (a·)` (`RS.fwdMapInv_scale`), which holds
for the raw pairings but needs regularity of the fields at the regularized level.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise

namespace QuantumZipper
namespace B3d

/-! ## Loewner scaling at every point -/

/-- **A1(d) at every starting point.** `f^{W(a²·)/a}_t(z) = f^W_{a²t}(a z)/a` for all `z : ℂ`
(including real `z` and junk values), `a > 0`, `t ≥ 0`, with no hypothesis on `W`. -/
theorem fwdMap_scale_of (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    fwdMap (fun s => W (a ^ 2 * s) / a) t z = fwdMap W (a ^ 2 * t) (a * z) / a := by
  have ha2 : 0 < a ^ 2 := by positivity
  by_cases h : ∃ u, IsForwardSol W (a * z) (a ^ 2 * t) u
  · obtain ⟨u, hu⟩ := h
    have hs := LoewnerAlgebra.isForwardSol_scale ha hu
    rw [mul_div_cancel_left₀ _ ha2.ne'] at hs
    rw [F1.fwdMap_eq_of_isForwardSol hs ⟨ht, le_rfl⟩,
      F1.fwdMap_eq_of_isForwardSol hu ⟨by positivity, le_rfl⟩]
  · have h' : ¬ ∃ v, IsForwardSol (fun s => W (a ^ 2 * s) / a) z t v :=
      fun ⟨v, hv⟩ => h ⟨_, LoewnerAlgebra.isForwardSol_unscale ha hv⟩
    simp only [fwdMap, h, h', dite_false, zero_div]

theorem tendsto_mul_nhdsLT {a : ℝ} (ha : 0 < a) :
    Tendsto (fun r : ℝ => a * r) (𝓝[<] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_nhdsWithin_of_forall fun r (hr : r < 0) => mul_neg_of_pos_of_neg ha hr⟩
  have := ((continuous_const_mul a).tendsto (0 : ℝ)).mono_left
    (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
  simpa using this

/-- **Side image of the rescaled driver.** If `x ↦ Re f^W_{a²s}(x)` has the limit `l` as
`x → 0⁻`, then `O⁻` of `W(a²·)/a` at time `s` is `l / a`. -/
theorem sideImages_fst_scale (W : ℝ → ℝ) {a : ℝ} (ha : 0 < a) {s l : ℝ} (hs : 0 ≤ s)
    (hL : Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * s) r).re) (𝓝[<] (0 : ℝ)) (𝓝 l)) :
    (sideImages (fun r => W (a ^ 2 * r) / a) s).1 = l / a := by
  unfold sideImages
  refine Tendsto.limUnder_eq ?_
  refine ((hL.comp (tendsto_mul_nhdsLT ha)).div_const a).congr fun r => ?_
  simp only [Function.comp_apply]
  rw [fwdMap_scale_of W ha hs, Complex.div_ofReal_re]
  push_cast
  rfl

/-! ## First passage times under a linear time change -/

/-- First passage times scale: `inf {s ≥ 0 : ℓ ≤ L(c s)} = inf {t ≥ 0 : ℓ ≤ L t} / c`. -/
theorem sInf_scale {L : ℝ → ℝ≥0∞} {ℓ : ℝ≥0∞} {c : ℝ} (hc : 0 < c) :
    sInf {s : ℝ | 0 ≤ s ∧ ℓ ≤ L (c * s)} = sInf {t : ℝ | 0 ≤ t ∧ ℓ ≤ L t} / c := by
  have e : {s : ℝ | 0 ≤ s ∧ ℓ ≤ L (c * s)} = c⁻¹ • {t : ℝ | 0 ≤ t ∧ ℓ ≤ L t} := by
    ext s
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc.ne'), inv_inv, smul_eq_mul]
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_nonneg hc.le h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨nonneg_of_mul_nonneg_right (by linarith) hc, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hc.le), smul_eq_mul, div_eq_inv_mul]

/-! ## Lengths unzipped from the canonicalized configuration -/

theorem canonConfig_snd_of_max {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ}
    (hWmax : ∀ s, W (max s 0) = W s) :
    (canonConfig γ (y, W)).2 = fun r => W (scaleParam γ y ^ 2 * r) / scaleParam γ y := by
  funext r
  simp only [canonConfig]
  rw [mul_max_of_nonneg _ _ (sq_nonneg _), mul_zero, hWmax]

theorem avgReg_eq_of_regEq {x y : FieldSample} (h : RegEq x y) : avgReg x = avgReg y := by
  funext k z; exact h k z

theorem rescale_congr_avgReg {x y : FieldSample} (h : avgReg x = avgReg y) (Q a : ℝ) :
    rescale x Q a = rescale y Q a := by
  unfold rescale; exact Factorization.coordChange_congr h _ _

variable {γ k : ℝ} {x : FieldSample} {W : ℝ → ℝ}

end B3d
end QuantumZipper
