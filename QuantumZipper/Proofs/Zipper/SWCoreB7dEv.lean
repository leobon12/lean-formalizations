import QuantumZipper.Proofs.Zipper.SWCoreB7dPath
import QuantumZipper.Proofs.Zipper.UnifUCTr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (4): the countable transfer event of AC-fam on `C([0,T']) × FieldSample`

For the shifted path `e ∈ C([0,T'])` (horizon `T' = T − q`, local time `σ = s − q`) and a free
field sample `y`:

* `densQ`: the boundary density `2^{-kγ²/4} e^{(γ/2) h_k}` of the unzipped field
  `unzippedField γ (𝔥₀ + y, Wof κ T' e) σ`, read through the jointly measurable proxy
  `RegUnif.AvgQ` (`AvgQ_eq_avgReg`);
* `IQ`: the transported test integral `∫ awProxy(F_σ) u v f · densQ dx`, with the window flow
  `F_σ = realRevMap V_e (T' − σ)` read through `FmR`;
* `EvQ`: uniform Cauchy property in `k` over the rational local times `σ ∈ [0, T']`;
* `measurable_IQ`, `measurableSet_EvQ`.

Same scheme as `SWCore.a8Ev` (SWCoreA8Meas.lean) and `F1.UCsetF` (XFlowUCTr.lean).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

variable (κ : ℝ) {T' : ℝ} (hT' : 0 ≤ T')

/-- The boundary density read through `AvgQ`. -/
def densQ (σ : ℝ) (k : ℕ) (p : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℝ) : ℝ :=
  radius k ^ (Real.sqrt κ ^ 2 / 4) *
    Real.exp (Real.sqrt κ / 2 * RegUnif.AvgQ hT' κ (Real.sqrt κ) σ k (p.1, (p.2 : ℂ)))

/-- The transported test integral, read through the proxies. -/
def IQ (u v : ℝ) (f : ℝ → ℝ) (σ : ℝ) (k : ℕ) (p : C(Icc (0 : ℝ) T', ℝ) × FieldSample) : ℝ :=
  ∫ x, awProxy (fun y => FmR hT' κ (T' - σ) y p.1) u v f x * densQ κ hT' σ k (p, x)

theorem measurable_densQ (σ : ℝ) (k : ℕ) : Measurable (densQ κ hT' σ k) := by
  unfold densQ
  refine measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ?_))
  exact (RegUnif.measurable_AvgQ hT' κ (Real.sqrt κ) σ k).comp
    (measurable_fst.prodMk (Complex.measurable_ofReal.comp measurable_snd))

theorem measurable_IQ (u v : ℝ) {f : ℝ → ℝ} (hf : Measurable f) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) T') (k : ℕ) : Measurable (IQ κ hT' u v f σ k) := by
  have hσ' : T' - σ ∈ Icc (0 : ℝ) T' := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have hA : Measurable fun p : (C(Icc (0 : ℝ) T', ℝ) × FieldSample) × ℝ =>
      awProxy (fun y => FmR hT' κ (T' - σ) y p.1.1) u v f p.2 := by
    have := measurable_awProxy (E := C(Icc (0 : ℝ) T', ℝ) × FieldSample)
      (Fe := fun p y => FmR hT' κ (T' - σ) y p.1)
      (fun y => (measurable_FmR hT' κ hσ' y).comp measurable_fst) u v hf
    exact this
  have hG := (hA.mul (measurable_densQ κ hT' σ k)).stronglyMeasurable
  exact (hG.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

/-- **The countable event**: uniform Cauchy property over the rational local times. -/
def EvQ (u v : ℝ) (f : ℝ → ℝ) (p : C(Icc (0 : ℝ) T', ℝ) × FieldSample) : Prop :=
  ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' → ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) T' →
    |IQ κ hT' u v f σ j p - IQ κ hT' u v f σ j' p| ≤ 1 / ((n : ℝ) + 1)

theorem measurableSet_EvQ (u v : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet {p | EvQ κ hT' u v f p} := by
  refine measurableSet_setOfPred.2 ?_
  unfold EvQ
  refine Measurable.forall fun n => Measurable.exists fun N => Measurable.forall fun j =>
    Measurable.forall fun _ => Measurable.forall fun j' => Measurable.forall fun _ =>
    Measurable.forall fun σ => ?_
  by_cases hσ : (σ : ℝ) ∈ Icc (0 : ℝ) T'
  · simp only [hσ, true_implies]
    exact measurableSet_setOfPred.1 (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_IQ κ hT' u v hf hσ j).sub (measurable_IQ κ hT' u v hf hσ j')))
      measurable_const)
  · simp only [hσ, false_implies]
    exact measurable_const

end SWCore
end QuantumZipper
