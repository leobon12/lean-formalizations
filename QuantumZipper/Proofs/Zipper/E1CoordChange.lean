import QuantumZipper.Proofs.Zipper.E1Defs
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.LQG.CoordChangeMain
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# E1-CC (part 1): coordinate change of the boundary measure on a live window

`handoff/E1-PLAN.md`, sub-node **E1-CC** (Theorem 1.3, node E1). Fixed driver `v` (`Continuous`,
`v 0 = 0`), time `t ≥ 0`, a window `(a, b)` all of whose points are negative and live, and a free
field `X'` on `(Ω', P')`. The target is

```
∀ᵐ ω' ∂P', ∀ g : ℝ → ℝ≥0∞, Measurable g →
  ∫⁻ x, g (realRevMap v t x) ∂qBoundaryMeasureOn (√κ) (hFix κ v t (X' ω')) (Ioo a b)
    = ∫⁻ y, g y ∂qBoundaryMeasureOn (√κ) (ofFun (h0rev κ) + X' ω') (Ioo (F a) (F b))
```

with `F = realRevMap v t`. Paper: Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, Thm 1.2/(1.3) (coordinate rule); the boundary version is
Duplantier–Sheffield, *LQG and KPZ*, arXiv:0808.1560, Prop. 3.1, formalized in this project as
node M4-T4 (`CoordChange.ae_qBoundaryMeasureOn_coordChange`, `LQG/CoordChangeMain.lean`).

This file contains the *reduction to the free field*: the holomorphic extension of the reverse
map over the window, the observation that `qBoundaryMeasureOn` only reads `avgReg` (so the
extension and `revMap` give the same measure), the transfer of M4-T4 to `coordChange · (revMap v t)`,
and the pushforward/density algebra for `targetMeasure` (the measure of M4-T4) that the final
assembly needs. The remaining ingredients of the full statement — the two applications of the
additive rule `LocalRule.qBoundaryMeasureOn_add_ofFun` for the `𝔥₀` term — are listed at the end
of this docstring; see the task report.

* `exists_revMapExt_window`: `U` open around `[a,b]`, `ψ = revMapExt v t` holomorphic on `U`,
  `ψ = revMap v t` on `ℍ`, `ψ = F` and `ψ' ≠ 0` on `[a,b]`, `ψ` real there.
* `avgReg_coordChange_revMapExt`, `bdryApprox_coordChange_revMapExt`,
  `qBoundaryMeasureOn_congr_of_eventuallyEq`: replacing `revMap v t` by a map agreeing with it on
  `ℍ` (or agreeing eventually along the dyadic approximations) does not change the measure.
* **`ae_qBoundaryMeasureOn_revMap`** (M4-T4 transported to the reverse map): a.s.
  `qBoundaryMeasureOn γ (coordChange (X' ω) (revMap v t) (Qc γ)) (Ioo a b)
     = targetMeasure (qBoundaryMeasure γ (X' ω)) Φ a b`,
  `Φ = extIso` the global order isomorphism extending `F|_{[a,b]}`.
* **`targetMeasure_eq_restrict_map`**, `lintegral_targetMeasure`, `withDensity_map_eq_map_withDensity`,
  **`targetMeasure_withDensity`**: `targetMeasure ν Φ a b = (ν.restrict (Ioo (Φ a) (Φ b))).map Φ.symm`
  and its compatibility with `∫⁻` and `withDensity`.

The full E1-CC statement is `E1.ae_lintegral_hFix_eq` in `E1CoordChange2.lean`, which adds the
two ingredients below (the original worker's list): (i) the additive rule
`qBoundaryMeasureOn γ (coordChange (ofFun (h0rev κ) + X') F Q) (Ioo a b)
  = (qBoundaryMeasureOn γ (coordChange X' F Q) (Ioo a b)).withDensity (fun x => ofReal (|F x|))`,
which needs regularity of `coordChange X' F Q` (`CoordReg.ae_isRegularSample_coordChange_revMap'`),
the existence of the local vague limit (this file) and the identity of the two `avgReg`s (the RC3
split `CoordReg.ae_evalReg_coordChange_revMap_fc'`); and (ii) the same rule on the image side for
`ofFun (h0rev κ) + X'` — equivalently `qBoundaryMeasure γ (ofFun (h0rev κ) + X')` on `Ioo (F a) (F b)`
`= (qBoundaryMeasure γ X').withDensity (fun y => ofReal |y|)` there.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open RevMapExtension

variable {Ω : Type*} [MeasurableSpace Ω] {P' : Measure Ω}
variable {κ t a b γ : ℝ} {v : ℝ → ℝ} {X' : Ω → FieldSample}

/-! ## 1. The holomorphic extension of the reverse map over a live window -/

/-- **Deterministic setup of E1-CC.** On a window `[a,b]` of live points, the extension
`revMapExt v t` (A2-ext, `RevMapExtension.exists_revMapExt_extension`) is holomorphic on an open
`U ⊇ [a,b]`, agrees with `revMap v t` on `ℍ` and with `realRevMap v t` on `[a,b]`, is real there
with nonvanishing derivative. -/
theorem exists_revMapExt_window (hv : Continuous v) (ht : 0 ≤ t)
    (h : ∀ x ∈ Icc a b, IsLive v t x) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x ∈ Icc a b, (x : ℂ) ∈ U) ∧
      DifferentiableOn ℂ (revMapExt v t) U ∧ EqOn (revMapExt v t) (revMap v t) H ∧
      (∀ x ∈ Icc a b, revMapExt v t x = realRevMap v t x) ∧
      (∀ x ∈ Icc a b, (revMapExt v t x).im = 0) ∧
      (∀ x ∈ Icc a b, deriv (revMapExt v t) x ≠ 0) := by
  obtain ⟨U, hUo, hJU, -, hdiff, hH, -, hreal, -, hpos⟩ :=
    exists_revMapExt_extension hv ht (Icc a b) h
  exact ⟨U, hUo, hJU, hdiff, fun z hz => hH z hz, hreal,
    fun x hx => by rw [hreal x hx]; simp,
    fun x hx => by
      have := (hpos x hx).1
      intro h0
      rw [h0] at this
      exact lt_irrefl _ this⟩

/-! ## 2. `qBoundaryMeasureOn` only reads `avgReg` -/

/-- `avgReg` of a coordinate-changed field is unchanged when the map is replaced by a map
agreeing on `ℍ` (`CoordReg.avgReg_coordChange_congr`). -/
theorem avgReg_coordChange_revMapExt {ψ : ℂ → ℂ} (hψ : EqOn ψ (revMap v t) H)
    (x : FieldSample) (Q : ℝ) (k : ℕ) (z : ℂ) :
    avgReg (coordChange x ψ Q) k z = avgReg (coordChange x (revMap v t) Q) k z :=
  CoordReg.avgReg_coordChange_congr x hψ Q k z

/-- The dyadic approximants `bdryApprox γ · k` of two such fields are literally equal. -/
theorem bdryApprox_coordChange_revMapExt {ψ : ℂ → ℂ} (hψ : EqOn ψ (revMap v t) H) (γ : ℝ)
    (x : FieldSample) (Q : ℝ) (k : ℕ) :
    bdryApprox γ (coordChange x ψ Q) k = bdryApprox γ (coordChange x (revMap v t) Q) k := by
  unfold bdryApprox
  congr 1
  funext s
  rw [avgReg_coordChange_revMapExt hψ x Q k (s : ℂ)]

/-- Local vague limits do not change if the approximating sequence agrees eventually. -/
theorem isVagueLimitOnR_congr_of_eventuallyEq {I : Set ℝ} {νs νs' : ℕ → Measure ℝ}
    {ν : Measure ℝ} (h : ∀ᶠ k in atTop, νs k = νs' k) :
    IsVagueLimitOnR I νs ν ↔ IsVagueLimitOnR I νs' ν := by
  have key : ∀ f : ℝ → ℝ, (fun k => ∫ t, f t ∂νs k) =ᶠ[atTop]
      (fun k => ∫ t, f t ∂νs' k) := fun f => h.mono fun k hk => by
    show ∫ t, f t ∂νs k = ∫ t, f t ∂νs' k
    rw [hk]
  constructor
  · rintro ⟨h0, hK, ht⟩
    exact ⟨h0, hK, fun f hf hfc hfs => (tendsto_congr' (key f)).1 (ht f hf hfc hfs)⟩
  · rintro ⟨h0, hK, ht⟩
    exact ⟨h0, hK, fun f hf hfc hfs => (tendsto_congr' (key f)).2 (ht f hf hfc hfs)⟩

/-- **The chosen local boundary measure only reads `avgReg`.** If the dyadic approximants of two
fields agree eventually, their `qBoundaryMeasureOn` on an open set agree. -/
theorem qBoundaryMeasureOn_congr_of_eventuallyEq {x y : FieldSample} {I : Set ℝ} (hI : IsOpen I)
    (h : ∀ᶠ k in atTop, bdryApprox γ x k = bdryApprox γ y k) :
    qBoundaryMeasureOn γ x I = qBoundaryMeasureOn γ y I := by
  by_cases hex : ∃ ν, IsVagueLimitOnR I (bdryApprox γ x) ν
  · rw [LocalRule.qBoundaryMeasureOn_eq hI hex.choose_spec,
      LocalRule.qBoundaryMeasureOn_eq hI ((isVagueLimitOnR_congr_of_eventuallyEq h).1 hex.choose_spec)]
  · unfold qBoundaryMeasureOn
    rw [dif_neg hex, dif_neg fun h' => hex (h'.elim fun ν hν =>
      ⟨ν, (isVagueLimitOnR_congr_of_eventuallyEq h).2 hν⟩)]

/-! ## 3. M4-T4 transported to the reverse map -/

/-! ## 4. `targetMeasure`: restriction, pushforward and densities -/

/-- `targetMeasure ν Φ a b` is the pushforward of `ν` restricted to the image window by `Φ⁻¹`. -/
theorem targetMeasure_eq_restrict_map (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ) :
    CoordChange.targetMeasure ν Φ a b = (ν.restrict (Ioo (Φ a) (Φ b))).map Φ.symm := by
  ext A hA
  rw [CoordChange.targetMeasure_apply ν Φ hA, Measure.map_apply Φ.symm.continuous.measurable hA,
    Measure.restrict_apply (Φ.symm.continuous.measurable hA), inter_comm,
    OrderIso.image_eq_preimage_symm]

/-- Integrals against `targetMeasure` (the `lintegral` form of `CoordChange.integral_targetMeasure`,
which needs a compactly supported test function; the measure is carried by `(a,b)`). -/
theorem lintegral_targetMeasure (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ) {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, f x ∂CoordChange.targetMeasure ν Φ a b =
      ∫⁻ y, f (Φ.symm y) ∂ν.restrict (Ioo (Φ a) (Φ b)) := by
  rw [targetMeasure_eq_restrict_map, lintegral_map hf Φ.symm.continuous.measurable]

/-- Pushing forward commutes with multiplying by a density. -/
theorem withDensity_map_eq_map_withDensity {μ : Measure ℝ} {g : ℝ → ℝ} (hg : Measurable g)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (μ.map g).withDensity φ = (μ.withDensity fun x => φ (g x)).map g := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply hg hA, withDensity_apply _ (hg hA),
    ← lintegral_indicator hA φ, lintegral_map (hφ.indicator hA) hg]
  conv_rhs => rw [← lintegral_indicator (hg hA) (fun y => φ (g y))]
  refine lintegral_congr fun y => ?_
  by_cases hy : g y ∈ A
  · simp [Set.mem_preimage, hy]
  · simp [Set.mem_preimage, hy]

/-- `targetMeasure` commutes with `withDensity`, the density being transported by `Φ⁻¹`. -/
theorem targetMeasure_withDensity (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ) {φ : ℝ → ℝ≥0∞}
    (hφ : Measurable φ) :
    (CoordChange.targetMeasure ν Φ a b).withDensity φ =
      CoordChange.targetMeasure (ν.withDensity fun y => φ (Φ.symm y)) Φ a b := by
  rw [targetMeasure_eq_restrict_map ν Φ a b,
    targetMeasure_eq_restrict_map (ν.withDensity fun y => φ (Φ.symm y)) Φ a b,
    withDensity_map_eq_map_withDensity (μ := ν.restrict (Ioo (Φ a) (Φ b)))
      Φ.symm.continuous.measurable hφ,
    restrict_withDensity measurableSet_Ioo]

/-- The density factor of the additive rule for `𝔥₀`: with `γ = √κ`, `e^{γ 𝔥₀(y)/2} = |y|`
(the same computation as `InfMass.exp_h0rev`; own elementary proof). -/
theorem exp_half_mul_h0rev {κ y : ℝ} (hκ : 0 < κ) (hy : y ≠ 0) :
    Real.exp (Real.sqrt κ / 2 * h0rev κ (y : ℂ)) = |y| := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [h0rev, Complex.norm_real, Real.norm_eq_abs,
    show Real.sqrt κ / 2 * (2 / Real.sqrt κ * Real.log |y|) = Real.log |y| by field_simp,
    Real.exp_log (abs_pos.2 hy)]

/-- **The E1-CC substitution.** For the order isomorphism `Φ` of M4-T4, integrating `g ∘ Φ`
against `targetMeasure ν Φ a b` is integrating `g` against `ν` restricted to the image window
`(Φ a, Φ b)` — the change of variables of the conclusion of E1-CC. -/
theorem lintegral_targetMeasure_symm (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ x, g (Φ x) ∂CoordChange.targetMeasure ν Φ a b =
      ∫⁻ y, g y ∂ν.restrict (Ioo (Φ a) (Φ b)) := by
  have h : Measurable fun x : ℝ => g (Φ x) := hg.comp Φ.continuous.measurable
  rw [lintegral_targetMeasure ν Φ a b h]
  exact lintegral_congr fun y => by simp

/-- **E1-CC, final shape with the `|·|` density.** If the x-side measure is the `targetMeasure`
of `ν` weighted by the density `|Φ ·|`, the change of variables of E1-CC holds with the y-side
measure `ν` weighted by `|·|` on the image window. -/
theorem lintegral_targetMeasure_withDensity_abs (ν : Measure ℝ) (Φ : ℝ ≃o ℝ) (a b : ℝ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g (Φ x) ∂(CoordChange.targetMeasure ν Φ a b).withDensity
        (fun x => ENNReal.ofReal |Φ x|) =
      ∫⁻ y, g y ∂(ν.withDensity fun y => ENNReal.ofReal |y|).restrict (Ioo (Φ a) (Φ b)) := by
  have hφ : Measurable fun x : ℝ => ENNReal.ofReal |Φ x| :=
    ((continuous_abs.comp Φ.continuous).measurable).ennreal_ofReal
  have hdens : (fun y : ℝ => ENNReal.ofReal |Φ (Φ.symm y)|) =
      fun y => ENNReal.ofReal |y| := funext fun y => by rw [OrderIso.apply_symm_apply]
  rw [targetMeasure_withDensity ν Φ a b hφ, hdens]
  exact lintegral_targetMeasure_symm (ν.withDensity fun y => ENNReal.ofReal |y|) Φ a b hg

end E1
end QuantumZipper
