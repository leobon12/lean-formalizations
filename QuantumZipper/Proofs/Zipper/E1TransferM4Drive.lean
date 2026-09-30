import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# E1-TR, sub-step M4a: a measurable continuous version on `[0,t]`

We build a measurable map `extC t` from raw paths `ℝ≥0 → ℝ` (product σ-algebra) to
`C(Icc 0 t, ℝ)` (Borel σ-algebra) which returns the restriction of `f` to `[0,t]` whenever
`f` is continuous.

Construction (own elementary construction): `bern t n f` is the Bernstein polynomial of degree
`n` built from the grid values `f (t k / n)`, read on `[0,t]` through `s ↦ s/t`; `extC t f` is
`limUnder atTop (bern t · f)`. Each `bern t n` is measurable (finitely many coordinates), so
`extC t` is measurable (`StronglyMeasurable.limUnder`). For continuous `f` the limit is
identified by the Bernstein approximation theorem (mathlib `bernsteinApproximation_uniform`;
see Beals, *Advanced Mathematical Analysis*, §7D).
-/

open Set Filter Topology MeasureTheory
open scoped NNReal unitInterval

noncomputable section

namespace QuantumZipper
namespace E1
namespace M4

/-- the rescaling `[0,t] → [0,1]`, `s ↦ s/t` (clamped; exact on `[0,t]`). -/
def rescale (t : ℝ) : C(Icc (0 : ℝ) t, I) :=
  ⟨fun s => Set.projIcc 0 1 zero_le_one (s.1 / t),
    continuous_projIcc.comp (continuous_subtype_val.div_const t)⟩

lemma mul_rescale {t : ℝ} (s : Icc (0 : ℝ) t) : t * (rescale t s : ℝ) = s.1 := by
  have h0 : 0 ≤ s.1 := s.2.1
  have hst : s.1 ≤ t := s.2.2
  have hmem : s.1 / t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg h0 (h0.trans hst), div_le_one_of_le₀ hst (h0.trans hst)⟩
  show t * ((Set.projIcc 0 1 zero_le_one (s.1 / t) : Icc (0:ℝ) 1) : ℝ) = s.1
  rw [Set.projIcc_of_mem _ hmem]
  rcases eq_or_lt_of_le (h0.trans hst) with ht | ht
  · subst ht; simp; linarith
  · field_simp

/-- continuous approximants read at the grid points t*k/n -/
def bern (t : ℝ) (n : ℕ) (f : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) t, ℝ) :=
  ∑ k : Fin (n + 1), (bernstein n k).comp (rescale t) *
    ContinuousMap.const _ (f (t * (bernstein.z k : ℝ)).toNNReal)

lemma bern_apply (t : ℝ) (n : ℕ) (f : ℝ≥0 → ℝ) (s : Icc (0 : ℝ) t) :
    bern t n f s = ∑ k : Fin (n + 1),
      bernstein n k (rescale t s) * f (t * (bernstein.z k : ℝ)).toNNReal := by
  simp [bern, ContinuousMap.sum_apply]

/-- continuous version on `[0,t]`: limit of the Bernstein approximants (junk if none). -/
def extC (t : ℝ) (f : ℝ≥0 → ℝ) : C(Icc (0 : ℝ) t, ℝ) := limUnder atTop fun n => bern t n f

lemma measurable_bern (t : ℝ) (n : ℕ) : Measurable (bern t n) := by
  refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
  simp_rw [bern_apply]
  exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply _).const_mul _

theorem measurable_extC (t : ℝ) : Measurable (extC t) := by
  have : Nonempty C(Icc (0 : ℝ) t, ℝ) := ⟨0⟩
  exact (StronglyMeasurable.limUnder
    (f := fun n => bern t n) (l := atTop)
    fun n => (measurable_bern t n).stronglyMeasurable).measurable

theorem extC_apply_of_continuous {t : ℝ} {f : ℝ≥0 → ℝ} (hf : Continuous f)
    (s : Icc (0 : ℝ) t) : extC t f s = f s.1.toNNReal := by
  let fI : C(I, ℝ) := ⟨fun y => f (t * (y : ℝ)).toNNReal,
    hf.comp (continuous_real_toNNReal.comp (continuous_const.mul continuous_subtype_val))⟩
  have hb : ∀ n, bern t n f = (bernsteinApproximation n fI).comp (rescale t) := by
    intro n; ext s
    simp [bern_apply, bernsteinApproximation.apply, fI]
  have hT : Tendsto (fun n => bern t n f) atTop (𝓝 (fI.comp (rescale t))) := by
    simp_rw [hb]
    exact ((ContinuousMap.continuous_precomp (rescale t)).tendsto _).comp
      (bernsteinApproximation_uniform fI)
  rw [extC, hT.limUnder_eq]
  simp [fI, mul_rescale]

end M4
end E1
end QuantumZipper

end
