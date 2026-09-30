import QuantumZipper.Proofs.Thm18.ExactClG1
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.Thm18.G1RegCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# EXACT-CLUSTER (3): `G1ZA1bSideExactStmt` from the raw circle identity

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71. Decision: `handoff/G4-CORE.md` §8.

The conclusion of `G1ZA1bSideExactStmt` at a sample is
`evalReg X' (fc(e, r)) = coordChange Y Φ Q (fc(e, r))` for all `e ∈ ℍ̄`, `r > 0`, where
`X'` is the new side field and `Φ = f_{t'}⁻¹ ∘ (a ·) ∘ ψ'`. This file proves (per sample,
deterministically) that it follows from

* the **raw** identity `X' (fc(d, s)) = coordChange Y Φ Q (fc(d, s))` at every folded circle
  (the pushed-circle exactness of the two intermediate fields at `ψ'`-pushed circles, i.e. the
  `DriverPushExactI`-shaped conjuncts for the side-map family), and
* regularity and exactness of the OLD side field `X = coordChange Y ψ Q` (the first two clauses of
  `G1.ChoiceRegularCore`, available a.s. from the proved `G1RegExStmt`),

through the A1a affine identity (`ExactClG1.coordChange_comp_affine`): `X'` is then, at every
circle, the affine pullback of `X`, which is regular by the closure of regular samples under real
translations and dilations (`IsRegularWith.translate'`, `IsRegularWith.rescale'`).

* `isRegularWith_of_raw_affine`, `evalReg_fc_of_raw_affine`: generic affine-pullback regularity;
* **`g1za1b_exact_of_raw`**: the per-sample reduction.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ExactCl

/-- **Affine pullback of a regular exact sample is regular.** If `X` is regular with witness `F`
and exact at every folded circle, and `X'` takes at every folded circle `fc(d, s)` (`d ∈ ℍ̄`) the
value `X (fc(b d + t, b s)) + Q log b` (`b > 0`, `t` real), then `X'` is regular with witness
`(d, s) ↦ F (b d + t, b s) + Q log b`. -/
theorem isRegularWith_of_raw_affine {X X' : FieldSample} {F : ℂ × ℝ → ℝ}
    (hX : IsRegularWith X F)
    (hex : ∀ d ∈ Hbar, ∀ s > 0, evalReg X (foldedCircle d s) = X (foldedCircle d s))
    {Q b t : ℝ} (hb : 0 < b)
    (hraw : ∀ d ∈ Hbar, ∀ s > 0, X' (foldedCircle d s) =
      X (foldedCircle ((b : ℂ) * d + t) (b * s)) + Q * Real.log b) :
    IsRegularWith X' (fun q => F ((b : ℂ) * q.1 + t, b * q.2) + Q * Real.log b) := by
  have h2 := (hX.translate' t).rescale' Q hb
  refine ⟨h2.1, fun k z hz => RegClosure.tendsto_of_eval_eq h2.1 ?_ k hz, h2.2.2⟩
  intro d hd s hs
  have hmem : (b : ℂ) * d + t ∈ Hbar :=
    RegClosure.mapsTo_add_real t (RegClosure.mapsTo_mul_pos hb hd)
  rw [hraw d hd s hs, ← hex _ hmem _ (mul_pos hb hs), hX.evalReg_fc_of_mem hmem (mul_pos hb hs)]

theorem evalReg_fc_of_raw_affine {X X' : FieldSample} {F : ℂ × ℝ → ℝ}
    (hX : IsRegularWith X F)
    (hex : ∀ d ∈ Hbar, ∀ s > 0, evalReg X (foldedCircle d s) = X (foldedCircle d s))
    {Q b t : ℝ} (hb : 0 < b)
    (hraw : ∀ d ∈ Hbar, ∀ s > 0, X' (foldedCircle d s) =
      X (foldedCircle ((b : ℂ) * d + t) (b * s)) + Q * Real.log b)
    {e : ℂ} (he : e ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    evalReg X' (foldedCircle e r) =
      X (foldedCircle ((b : ℂ) * e + t) (b * r)) + Q * Real.log b := by
  have hmem : (b : ℂ) * e + t ∈ Hbar :=
    RegClosure.mapsTo_add_real t (RegClosure.mapsTo_mul_pos hb he)
  rw [(isRegularWith_of_raw_affine hX hex hb hraw).evalReg_fc_of_mem he hr,
    ← hX.evalReg_fc_of_mem hmem (mul_pos hb hr), hex _ hmem _ (mul_pos hb hr)]

/-- **`G1ZA1bSideExactStmt` at one sample, from the raw circle identity.** Let `X = coordChange Y
ψ Q` be regular and exact at every folded circle (the old side field), let the A1a identity
`F (a ψ'(u + β)) = ψ(u/λ)` hold on `ℍ`, let `ψ` be measurable, holomorphic with nonvanishing
derivative on `ℍ` and `log ‖ψ'‖` integrable on every folded circle. If the new side field `X'`
satisfies the raw identity `X'(fc) = coordChange Y Φ Q (fc)` (`Φ = F ∘ (a ψ')`) at every folded
circle, then it satisfies the regularized one. -/
theorem g1za1b_exact_of_raw {Y X' : FieldSample} {Q : ℝ} {F ψ ψ' : ℂ → ℂ} {a β lam : ℝ}
    (hreg : IsRegularSample (coordChange Y ψ Q))
    (hex : ∀ d ∈ Hbar, ∀ s > 0, evalReg (coordChange Y ψ Q) (foldedCircle d s) =
      coordChange Y ψ Q (foldedCircle d s))
    (hlam : 0 < lam) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hne : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hint : ∀ (d : ℂ) (s : ℝ), 0 < s →
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d s))
    (hEq : EqOn (fun u => F ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    (hraw : ∀ d ∈ Hbar, ∀ s > 0, X' (foldedCircle d s) =
      coordChange Y (fun u => F ((a : ℂ) * ψ' u)) Q (foldedCircle d s)) :
    ∀ e ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg X' (foldedCircle e r) =
        coordChange Y (fun u => F ((a : ℂ) * ψ' u)) Q (foldedCircle e r) := by
  obtain ⟨G, hG⟩ := hreg
  have hb : 0 < lam⁻¹ := inv_pos.2 hlam
  have hcirc : ∀ (d : ℂ), ((lam⁻¹ : ℝ) : ℂ) * (d + ((-β : ℝ) : ℂ)) =
      ((lam⁻¹ : ℝ) : ℂ) * d + ((-(lam⁻¹ * β) : ℝ) : ℂ) := fun d => by push_cast; ring
  have hlog : -(Q * Real.log lam) = Q * Real.log lam⁻¹ := by rw [Real.log_inv]; ring
  have hraw' : ∀ d ∈ Hbar, ∀ s > 0, X' (foldedCircle d s) =
      coordChange Y ψ Q (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * d + ((-(lam⁻¹ * β) : ℝ) : ℂ))
        (lam⁻¹ * s)) + Q * Real.log lam⁻¹ := by
    intro d hd s hs
    rw [hraw d hd s hs, coordChange_comp_affine Y Q hlam hψm hψd hne hEq d hs
      (hint _ _ (mul_pos hb hs)), hcirc, ← hlog]
    ring
  intro e he r hr
  rw [evalReg_fc_of_raw_affine hG hex hb hraw' he hr,
    coordChange_comp_affine Y Q hlam hψm hψd hne hEq e hr (hint _ _ (mul_pos hb hr)), hcirc,
    ← hlog]
  ring

/-- **The raw identity from the two pushed-circle exactness facts.** For `Z = rescale U Q a`,
`U = coordChange Y f Q`, `a > 0` and a probability measure `μ`: if `Z` is exact at `μ.map ψ'`
(E1), `U` is exact at `μ.map (a ψ')` (E2), the two log-derivative terms are `μ`-integrable and the
chain rule holds `μ`-a.e., then `coordChange Z ψ' Q μ = coordChange Y (f ∘ (a ψ')) Q μ`. These
are exactly the `DriverPushExactI`-shaped data (conjuncts 1–4) for the map `ψ'`. -/
theorem coordChange_rescale_coordChange_raw {Y : FieldSample} {Q a : ℝ} (ha : 0 < a)
    {f ψ' : ℂ → ℂ} (hψ'm : Measurable ψ') {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hfm : AEMeasurable f (μ.map fun u => (a : ℂ) * ψ' u))
    (hE1 : evalReg (rescale (coordChange Y f Q) Q a) (μ.map ψ') =
      rescale (coordChange Y f Q) Q a (μ.map ψ'))
    (hE2 : evalReg (coordChange Y f Q) (μ.map fun u => (a : ℂ) * ψ' u) =
      coordChange Y f Q (μ.map fun u => (a : ℂ) * ψ' u))
    (hI1 : Integrable (fun u => Real.log ‖deriv f ((a : ℂ) * ψ' u)‖) μ)
    (hI2 : Integrable (fun u => Real.log ‖deriv ψ' u‖) μ)
    (hchain : ∀ᵐ u ∂μ, Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ =
      Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a + Real.log ‖deriv ψ' u‖) :
    coordChange (rescale (coordChange Y f Q) Q a) ψ' Q μ =
      coordChange Y (fun u => f ((a : ℂ) * ψ' u)) Q μ := by
  have hm : Measurable fun u => (a : ℂ) * ψ' u := measurable_const_mul _ |>.comp hψ'm
  have hmap1 : (μ.map ψ').map (fun w : ℂ => (a : ℂ) * w) = μ.map fun u => (a : ℂ) * ψ' u :=
    Measure.map_map (measurable_const_mul _) hψ'm
  have hmap2 : (μ.map fun u => (a : ℂ) * ψ' u).map f = μ.map fun u => f ((a : ℂ) * ψ' u) :=
    AEMeasurable.map_map_of_aemeasurable hfm hm.aemeasurable
  have hL : Measurable fun z => Real.log ‖deriv f z‖ :=
    Real.measurable_log.comp (measurable_deriv f).norm
  have hint2 : ∫ z, Real.log ‖deriv f z‖ ∂(μ.map fun u => (a : ℂ) * ψ' u) =
      ∫ u, Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ ∂μ :=
    integral_map hm.aemeasurable hL.aestronglyMeasurable
  have hchainI : ∫ u, Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ ∂μ =
      ∫ u, Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ ∂μ + Real.log a +
        ∫ u, Real.log ‖deriv ψ' u‖ ∂μ := by
    have e1 : ∫ u, (Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a + Real.log ‖deriv ψ' u‖) ∂μ
        = ∫ u, (Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a) ∂μ +
          ∫ u, Real.log ‖deriv ψ' u‖ ∂μ := integral_add (hI1.add (integrable_const _)) hI2
    have e2 : ∫ u, (Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a) ∂μ
        = ∫ u, Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ ∂μ + ∫ _u, Real.log a ∂μ :=
      integral_add hI1 (integrable_const _)
    have e3 : ∫ _u : ℂ, Real.log a ∂μ = Real.log a := by
      rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [integral_congr_ae hchain, e1, e2, e3]
  show evalReg (rescale (coordChange Y f Q) Q a) (μ.map ψ') + Q * ∫ z, Real.log ‖deriv ψ' z‖ ∂μ =
    evalReg Y (μ.map fun u => f ((a : ℂ) * ψ' u)) +
      Q * ∫ z, Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) z‖ ∂μ
  rw [hE1]
  show evalReg (coordChange Y f Q) ((μ.map ψ').map fun w : ℂ => (a : ℂ) * w) +
      Q * (∫ z, Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖ ∂(μ.map ψ')) +
      Q * ∫ z, Real.log ‖deriv ψ' z‖ ∂μ = _
  rw [RegClosure.integral_log_deriv_mul ha, hmap1, hE2]
  show evalReg Y ((μ.map fun u => (a : ℂ) * ψ' u).map f) +
      Q * ∫ z, Real.log ‖deriv f z‖ ∂(μ.map fun u => (a : ℂ) * ψ' u) +
      Q * Real.log a + Q * ∫ z, Real.log ‖deriv ψ' z‖ ∂μ = _
  rw [hmap2, hint2, hchainI]
  ring

/-- **Per-sample reduction of `G1ZA1bSideExactStmt` to pushed-circle exactness.** With the old
side field `coordChange Y ψ Q` regular and exact, the A1a identity for `f = f_{t'}⁻¹`, and, at
every folded circle `σ = fc(d, s)`, the `DriverPushExactI`-shaped data for the new side map `ψ'`
(E1: `rescale U Q a` exact at `σ.map ψ'`; E2: `U = coordChange Y f Q` exact at `σ.map (a ψ')`;
integrability of `log ‖f'(a ψ')‖`, `log ‖ψ''‖`; the chain rule a.e.), the new side field
`coordChange (rescale U Q a) ψ' Q` satisfies the conclusion of `G1ZA1bSideExactStmt`. -/
theorem g1za1b_exact_of_push {Y : FieldSample} {Q a β lam : ℝ} (ha : 0 < a)
    {f ψ ψ' : ℂ → ℂ}
    (hreg : IsRegularSample (coordChange Y ψ Q))
    (hex : ∀ d ∈ Hbar, ∀ s > 0, evalReg (coordChange Y ψ Q) (foldedCircle d s) =
      coordChange Y ψ Q (foldedCircle d s))
    (hlam : 0 < lam) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hne : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hint : ∀ (d : ℂ) (s : ℝ), 0 < s →
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d s))
    (hEq : EqOn (fun u => f ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    (hψ'm : Measurable ψ')
    (hfm : ∀ (d : ℂ) (s : ℝ), AEMeasurable f ((foldedCircle d s).map fun u => (a : ℂ) * ψ' u))
    (hpush : ∀ d ∈ Hbar, ∀ s > 0,
      evalReg (rescale (coordChange Y f Q) Q a) ((foldedCircle d s).map ψ') =
        rescale (coordChange Y f Q) Q a ((foldedCircle d s).map ψ') ∧
      evalReg (coordChange Y f Q) ((foldedCircle d s).map fun u => (a : ℂ) * ψ' u) =
        coordChange Y f Q ((foldedCircle d s).map fun u => (a : ℂ) * ψ' u) ∧
      Integrable (fun u => Real.log ‖deriv f ((a : ℂ) * ψ' u)‖) (foldedCircle d s) ∧
      Integrable (fun u => Real.log ‖deriv ψ' u‖) (foldedCircle d s) ∧
      ∀ᵐ u ∂(foldedCircle d s), Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ =
        Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a + Real.log ‖deriv ψ' u‖) :
    ∀ e ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (coordChange Y f Q) Q a) ψ' Q) (foldedCircle e r) =
        coordChange Y (fun u => f ((a : ℂ) * ψ' u)) Q (foldedCircle e r) :=
  g1za1b_exact_of_raw hreg hex hlam hψm hψd hne hint hEq fun d hd s hs =>
    let ⟨h1, h2, h3, h4, h5⟩ := hpush d hd s hs
    coordChange_rescale_coordChange_raw ha hψ'm (hfm d s) h1 h2 h3 h4 h5

end ExactCl
end Thm18Asm
end QuantumZipper
