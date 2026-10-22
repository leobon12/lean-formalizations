import HigherDimLQGMetric.ShellDec.Hilbert
import HigherDimLQGMetric.ShellDec.Prefix

/-!
# Orthonormal bases of finite Gaussian coordinate spans
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

def shellFiniteSpan {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Lp ℝ 2 P) (m : ℕ) : Submodule ℝ (Lp ℝ 2 P) :=
  Submodule.span ℝ (Set.range fun k : Fin m => X k)

private instance shellFiniteSpan_finiteDimensional {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (X : ℕ → Lp ℝ 2 P) (m : ℕ) :
    FiniteDimensional ℝ (shellFiniteSpan X m) := by
  unfold shellFiniteSpan
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

def shellFiniteBasis {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Lp ℝ 2 P) (m : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (shellFiniteSpan X m))) ℝ
      (shellFiniteSpan X m) :=
  stdOrthonormalBasis ℝ (shellFiniteSpan X m)

def shellBasisVec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Lp ℝ 2 P) (m : ℕ)
    (k : Fin (Module.finrank ℝ (shellFiniteSpan X m))) : Lp ℝ 2 P :=
  (shellFiniteBasis X m k : shellFiniteSpan X m)

theorem shellBasisVec_orthonormal {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Lp ℝ 2 P) (m : ℕ) :
    Orthonormal ℝ (shellBasisVec X m) := by
  have hb := (shellFiniteBasis X m).orthonormal
  exact hb

theorem shellBasisVec_mem_annularBlock {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) {a b r : ℝ}
    (X : ℕ → Lp ℝ 2 P) (m : ℕ)
    (hX : ∀ k : Fin m, X k ∈ annularBlock hh a b r)
    (j : Fin (Module.finrank ℝ (shellFiniteSpan X m))) :
    shellBasisVec X m j ∈ annularBlock hh a b r := by
  rw [annularBlock_eq_span_closure]
  have hle : shellFiniteSpan X m ≤ annularBlockSubmodule hh a b r := by
    apply Submodule.span_le.mpr
    rintro Y ⟨k, rfl⟩
    change X k ∈ (annularBlockSubmodule hh a b r : Set (Lp ℝ 2 P))
    rw [← annularBlock_eq_span_closure]
    exact hX k
  exact hle (shellFiniteBasis X m j).property

theorem shellFiniteSpan_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Lp ℝ 2 P) {m : ℕ} (k : Fin m) :
    X k ∈ shellFiniteSpan X m :=
  Submodule.subset_span ⟨k, rfl⟩

def shellBasisCoeff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : ℕ → Lp ℝ 2 P) (m : ℕ) (k : Fin m)
    (j : Fin (Module.finrank ℝ (shellFiniteSpan X m))) : ℝ :=
  (shellFiniteBasis X m).repr ⟨X k, shellFiniteSpan_mem X k⟩ j

theorem shellFiniteBasis_expand {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Lp ℝ 2 P) (m : ℕ) (k : Fin m) :
    X k = ∑ j : Fin (Module.finrank ℝ (shellFiniteSpan X m)),
      shellBasisCoeff X m k j • shellBasisVec X m j := by
  have hb := (shellFiniteBasis X m).sum_repr
    (⟨X k, shellFiniteSpan_mem X k⟩ : shellFiniteSpan X m)
  have hc := congrArg (fun v : shellFiniteSpan X m => (v : Lp ℝ 2 P)) hb
  simpa [shellBasisCoeff, shellBasisVec, Submodule.coe_sum, Submodule.coe_smul]
    using hc.symm

theorem shellFiniteBasis_expand_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : ℕ → Lp ℝ 2 P) (m : ℕ) (k : Fin m) :
    (X k : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ j : Fin (Module.finrank ℝ (shellFiniteSpan X m)),
        shellBasisCoeff X m k j * (shellBasisVec X m j : Ω → ℝ) ω := by
  rw [shellFiniteBasis_expand X m k]
  have ha := (Lp.coeFn_finsetSum
    (Finset.univ : Finset (Fin (Module.finrank ℝ (shellFiniteSpan X m))))
    (fun j => shellBasisCoeff X m k j • shellBasisVec X m j)).trans <|
      eventuallyEq_sum fun j _ =>
        Lp.coeFn_smul (shellBasisCoeff X m k j) (shellBasisVec X m j)
  filter_upwards [ha] with ω hω
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hω

end HigherDimLQGMetric
