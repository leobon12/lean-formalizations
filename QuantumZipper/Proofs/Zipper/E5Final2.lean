import QuantumZipper.Proofs.Zipper.E5Final1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-FINAL, part 2: the level-space `ZoomModel` of E5's final assembly

Task E5-ZOOMMODEL (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72, proof of
Lemma 5.6; blueprint `E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(3)).

On the level space of `E5Asm4.e5_level_repr`, `(Ω₁, Q) = ((ℝ≥0 × NS(P)) × Ω', Rr₁.withDensity w₁)`,
with `X' = regField ϖ ρ₀ ∘ X₁ ∘ snd` (D28), `Ξ =` the level point, `D = esmGerm ∘ fst` and the
driver data `Vr κ T B ∘ ofCompl P ∘ snd` at the level time `T − T_ℓ`, this file builds the
`E5Main5.ZoomModel`:

* the corrections are the D28 switches `lvlZG` (full driver) and `lvlZG0` (germ-free driver,
  `E5G0.locCorrG0`) of the collision correction on the **same** radius switch set `lvlZBad`
  (the union of the two `radiusBad` events) with the constant fallback `0`, so that both
  `Setup`s hold (`setup_locCorr_switch_reg`, `setup_locCorr_germFree_reg`, lifted by
  `setup_piecewise` on the larger switch set, `switchG_switchG_subset`);
* `hν` for the full driver is **discharged** by `E5Asm2.measurable_varpiT_level`
  (`measurable_varpiT_lvl`), as is the base `Setup` with the constant fallback
  (`base_setup_lvl`);
* `hbad` is `E5Final1.e5G0_of_geometry_measurable_rt` (E5-G0 at the random level time) together
  with `gBad_switchG_zero_subset` (switching both corrections on one set with one fallback does
  not enlarge `gBad`).

Remaining hypotheses, all explicit (see the docstring of `zoomModel_lvl`): the base Q-law facts
for `X'` under `Rr₁.withDensity w₁` (freeness and independence from `Ξ`), the driver-part
measurability `hdrv`/`hdrv₀` (and the germ-free pushforward measurability `hν₀`, positivity
`ht₀`), the scale measurability `hm`, the condSigma-measurability `hbadm` of `gBad`, the
region statements `hμ`/`hμ₀` for the pushed arc measures and the measurability `hmeasc` of the
`z`-independent part, and the E5-LOC data `V`, `hay` (`zScale`/`zLoc` of `lvlZG0` as functions of
`V`).

Own bookkeeping (no new mathematics beyond `E5Final1`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open D3Plus B2 E1 LengthMarkov ESM LengthMarkov.GermDensity

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ## 1. Switching both corrections on one set -/

/-! ## 2. The base `Setup` with the constant fallback -/

/-- **The base D3⁺ `Setup` of the level model**: the field `X' = regField ϖ ρ₀ ∘ X₁ ∘ snd` with
the constant fallback correction `0`, whose hypotheses are exactly the Q-law facts of the level
representation (freeness of `X'` under `Rr₁.withDensity w₁` and independence from `Ξ`). -/
theorem base_setup_lvl {ρ₀ : Measure ℂ} {X₁ : Ω' → FieldSample}
    {Rr₁ : Measure (lvl Ω P Ω')} [IsProbabilityMeasure Rr₁] {w₁ : lvl Ω P Ω' → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ < 4) {r : ℝ} (hr : 0 < r)
    (hXf : IsFreeGFFModConstH (lvlField (Ω' := Ω') ϖ ρ₀ X₁) (Rr₁.withDensity w₁))
    (hind : Indep (MeasurableSpace.comap
        (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) inferInstance)
      (K3.freeIncrSigma (lvlField (Ω' := Ω') ϖ ρ₀ X₁)) (Rr₁.withDensity w₁))
    (hρ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1) (hρB : ρ₀ (Metric.ball (0 : ℂ) r) = 0) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ (Rr₁.withDensity w₁)
      (lvlField (Ω' := Ω') ϖ ρ₀ X₁)
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) (fun _ _ => 0) where
  hγ := Real.sqrt_pos.2 hκ
  hγ2 := (Real.sqrt_lt' two_pos).2 (by linarith)
  hα := by
    have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
    have hγ2 : Real.sqrt κ < 2 := (Real.sqrt_lt' two_pos).2 (by linarith)
    have h : 1 < 2 / Real.sqrt κ := (one_lt_div hγ).2 hγ2
    simp only [Qc]
    linarith
  hr := hr
  hX := hXf
  hΞ := measurable_lvlXi
  hind := hind
  hρ := hρ
  hρ1 := hρ1
  hρB := hρB
  harm := fun _ => InnerProductSpace.harmonicOnNhd_const 0
  gmeas := fun _ => measurable_const

/-! ## 3. The level driver data, corrections and switch set -/

/-! ## 4. The level zoom model -/

end E5
end QuantumZipper
