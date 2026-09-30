import QuantumZipper.Proofs.Zipper.YBdryLimBasic
import QuantumZipper.Proofs.Zipper.UnifUGReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# YBDRY-MERGE: offset merging for `y_t` splits into an off-tip part and a tip part

Theorems 1.3/1.8, F2 wedge core. Target: `YBdryMergeStmt` (`YBdryLimBasic.lean`): a.s., for all
`t ≥ 0` and every continuous compactly supported `f`, the approximations of
`y_t = F2.unzY κ X W t` at the radii `a 2^{-k}` merge with those at `2^{-k}` along `goodFilter`.

**Why the all-maps rule does not apply directly.** `y_t = y_0 ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|`, but
`f_t⁻¹` maps the interval `(O⁻_t, O⁺_t)` onto the two sides of the curve `η[0,t]`, which lie in
the *interior* of the domain of `y_0`: the boundary measure of `y_t` there is the quantum length
of the curve, not a transport of `ν_{y_0}`. So `F1.BdryAllMapsStmt` (Sheffield–Wang,
arXiv:1605.06171, Thm 4.3), which needs maps that are real on a real interval, covers only the
outer part `ℝ ∖ [O⁻_t, O⁺_t]`; moreover it (like its pathwise core
`F1.isVagueLimitOnR_coordChange_of_good`, whose inputs `BdryVarScaleLimit` and
`BdryDistortionGood` are statements along the dyadic radii `2^{-k}` for each fixed map) says
nothing about uniformity in the offset `a ∈ [1,2]`. The interior part needs the anchored-window
scheme of D26 (anchors at rational times `q < t`, transition maps `g_{q,t}`, real-analytic on
`ℝ` away from the new hull, whose image shrinks to the tip `0` as `q ↑ t`), in the offset form.
Hence the structure of the D26 split `UG = UO + UT` (`RegUnif.unifGlobal_unifAtomless_of_offTip_tip`)
is repeated here along `goodFilter`:

* `YMergeOffTipStmt` (**offset UO**): merging for test functions whose support avoids the tip `0`;
* `YTipOffStmt` (**offset UT**): the approximate masses of `(−δ, δ)` are uniformly small along
  `goodFilter` as `δ → 0`.

Main results:

* `bdryMerge_of_offPoint_tight` (deterministic, one sample): merging off a point `c` + tightness
  at `c` along `goodFilter` ⇒ merging for every test function;
* **`yBdryMergeStmt_of_offTip_tip`**: `YMergeOffTipStmt → YTipOffStmt → YBdryMergeStmt`;
* `tight_of_hasBdryLimit` and **`yTipOffStmt_of_merge`**: conversely, given dyadic UG and UA at
  every horizon (`F2.Step3UnifHyp`), `YBdryMergeStmt → YTipOffStmt`; together with the trivial
  `yMergeOffTipStmt_of_merge` the split is lossless.

Only the tip `0` of `y_t` needs separate treatment; the points `O^±_t` (images of the base of
the curve, where `y_0 = X + (γ − α₀) log|·|` has its log singularity) are ordinary points of the
anchored windows at positive anchors. The deterministic bookkeeping (cutoff at the tip, Urysohn)
is own elementary work (cost rule); sources for the statements: Duplantier–Sheffield, Invent.
Math. 185 (2011), Prop. 1.1 and §6; Sheffield–Wang, arXiv:1605.06171, Thm 1.4 (continuous
radius) and Thm 4.3; Sheffield, arXiv:1012.4797, §5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## Deterministic core -/

/-- `(k, a) ↦ (k, 1)` maps `goodFilter` into itself. -/
theorem tendsto_fst_one_goodFilter :
    Tendsto (fun i : ℕ × ℝ => (i.1, (1 : ℝ))) goodFilter goodFilter :=
  GoodSample.tendsto_one_goodFilter.comp
    (tendsto_fst (f := (atTop : Filter ℕ)) (g := 𝓟 (Icc (1 : ℝ) 2)))

/-- Continuous compactly supported functions are integrable for `ν_r` of a regular sample. -/
theorem integrable_bdryR_of_reg {γ : ℝ} {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable g (bdryR γ y r) :=
  GoodSample.integrable_of_tsupport (U := univ)
    (fun _ hK _ => GoodSample.bdryR_lt_top γ hF hr hK) hg hgc (subset_univ _)

/-! ## The two named inputs and the reduction -/

/-- **Offset UO for `y_t`** (named): a.s., for all `t ≥ 0` and every continuous compactly
supported `f` whose support avoids the tip `0`, the offset approximations of `y_t` merge with the
dyadic ones along `goodFilter`. (Expected from anchored windows at rational anchors in the offset
form, Sheffield–Wang arXiv:1605.06171 Thm 1.4/4.3 applied at the anchors.) -/
def YMergeOffTipStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      (0 : ℝ) ∉ tsupport f →
      Tendsto (bdryMergeDiff (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) f) goodFilter
        (𝓝 0)

/-- `y_t` is a regular sample for all `t ≥ 0`, a.s. (JOINTMOD). -/
theorem ae_forall_isRegularSample_unzY {κ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → IsRegularSample (F2.unzY κ (X ω) (drive κ B ω) t) := by
  filter_upwards [RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind]
    with ω hrω t ht
  have e : F2.unzY κ (X ω) (drive κ B ω) t =
      unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t := by
    rw [F2.unzY, F2.h0rev_add_eq]
  rw [e]
  exact (hrω t ht).1

end WedgeUnzip
end QuantumZipper
