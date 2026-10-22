import HigherDimLQGMetric.Gauss.BlockClosure
import HigherDimLQGMetric.LGF.Exists
import HigherDimLQGMetric.LogEnergy.CM
import HigherDimLQGMetric.Core.Defs

/-!
# Mean-zero LGF pairings in the Hilbert space `L²(P)`

The inner product of two paired random variables is their logarithmic
covariance. This identifies the analytic norm with the Hilbert norm used
for the closed annular blocks.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω}
  {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)

def lgfPairLp (φ : TestRd0 d) : Lp ℝ 2 P :=
  MemLp.toLp (fun ω => h ω φ.1)
    ((hh.gaussian.hasGaussianLaw_eval φ).memLp_two)

theorem lgfPairLp_inner_eq (φ ψ : TestRd0 d) :
    inner ℝ (lgfPairLp hh φ) (lgfPairLp hh ψ) =
      logCovRd φ.1 ψ.1 := by
  rw [MeasureTheory.L2.inner_def]
  have hφ := ((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).coeFn_toLp
  have hψ := ((hh.gaussian.hasGaussianLaw_eval ψ).memLp_two).coeFn_toLp
  rw [← hh.covariance_eq φ ψ]
  unfold covariance
  rw [hh.centered φ, hh.centered ψ]
  simp only [sub_zero]
  apply integral_congr_ae
  filter_upwards [hφ, hψ] with ω hφω hψω
  dsimp only [lgfPairLp]
  rw [hφω, hψω]
  simp
  ring

def testRd0Add (φ ψ : TestRd0 d) : TestRd0 d :=
  ⟨φ.1 + ψ.1, by
    have hiφ : Integrable (φ.1 : Rd d → ℝ) := integrable_testOn φ.1
    have hiψ : Integrable (ψ.1 : Rd d → ℝ) := integrable_testOn ψ.1
    change ∫ x : Rd d, ((φ.1 + ψ.1 : TestRd d) x) = 0
    simp [integral_add hiφ hiψ, φ.2, ψ.2]⟩

theorem testRd0Add_val (φ ψ : TestRd0 d) :
    (testRd0Add φ ψ).1 = φ.1 + ψ.1 := rfl

theorem lgfPairLp_add (φ ψ : TestRd0 d) :
    lgfPairLp hh (testRd0Add φ ψ) = lgfPairLp hh φ + lgfPairLp hh ψ := by
  apply Lp.ext
  filter_upwards [(((hh.gaussian.hasGaussianLaw_eval (testRd0Add φ ψ)).memLp_two).coeFn_toLp),
    (((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).coeFn_toLp),
    (((hh.gaussian.hasGaussianLaw_eval ψ).memLp_two).coeFn_toLp),
    Lp.coeFn_add (lgfPairLp hh φ) (lgfPairLp hh ψ)] with ω hχ hφ hψ hadd
  dsimp only [lgfPairLp] at *
  rw [hχ, hadd, Pi.add_apply, hφ, hψ]
  change h ω (φ.1 + ψ.1) = h ω φ.1 + h ω ψ.1
  exact map_add (h ω) φ.1 ψ.1

def testRd0Smul (c : ℝ) (φ : TestRd0 d) : TestRd0 d :=
  ⟨c • φ.1, by
    have hiφ : Integrable (φ.1 : Rd d → ℝ) := integrable_testOn φ.1
    change ∫ x : Rd d, ((c • φ.1 : TestRd d) x) = 0
    simp [integral_const_mul, φ.2]⟩

theorem lgfPairLp_smul (c : ℝ) (φ : TestRd0 d) :
    lgfPairLp hh (testRd0Smul c φ) = c • lgfPairLp hh φ := by
  apply Lp.ext
  filter_upwards [(((hh.gaussian.hasGaussianLaw_eval (testRd0Smul c φ)).memLp_two).coeFn_toLp),
    (((hh.gaussian.hasGaussianLaw_eval φ).memLp_two).coeFn_toLp),
    Lp.coeFn_smul c (lgfPairLp hh φ)] with ω hχ hφ hsmul
  dsimp only [lgfPairLp] at *
  rw [hχ, hsmul, Pi.smul_apply, hφ]
  change h ω (c • φ.1) = c • h ω φ.1
  exact map_smul (h ω) c φ.1

def testRd0Zero : TestRd0 d :=
  ⟨0, by simp⟩

theorem lgfPairLp_zero : lgfPairLp hh (testRd0Zero : TestRd0 d) = 0 := by
  apply Lp.ext
  filter_upwards [(((hh.gaussian.hasGaussianLaw_eval (testRd0Zero : TestRd0 d)).memLp_two).coeFn_toLp),
    (Lp.coeFn_zero ℝ 2 P)] with ω hχ hz
  dsimp only [lgfPairLp] at *
  rw [hχ, hz]
  exact map_zero (h ω)

theorem lgfPairLp_norm_eq (φ : TestRd0 d) :
    ‖lgfPairLp hh φ‖ = logNorm φ.1 := by
  rw [logNorm, ← lgfPairLp_inner_eq hh φ φ, real_inner_self_eq_norm_sq,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The mean-zero field pairings supported in one annulus. -/
def annularPairings (a b r : ℝ) : Set (Lp ℝ 2 P) :=
  {X | ∃ φ : TestRd0 d,
    tsupport (φ.1 : Rd d → ℝ) ⊆ ann 0 (a * r) (b * r) ∧
      lgfPairLp hh φ = X}

/-- The `L²` closure of the annular pairings. -/
def annularBlock (a b r : ℝ) : Set (Lp ℝ 2 P) :=
  closure (annularPairings hh a b r)

/-- The closed linear span of the annular pairings. -/
def annularBlockSubmodule (a b r : ℝ) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (annularPairings hh a b r)).topologicalClosure

theorem lgfPairLp_mem_annularBlock {a b r : ℝ} (φ : TestRd0 d)
    (hs : tsupport (φ.1 : Rd d → ℝ) ⊆ ann 0 (a * r) (b * r)) :
    lgfPairLp hh φ ∈ annularBlock hh a b r := by
  apply subset_closure
  exact ⟨φ, hs, rfl⟩

theorem lgfPairLp_mem_annularBlockSubmodule {a b r : ℝ} (φ : TestRd0 d)
    (hs : tsupport (φ.1 : Rd d → ℝ) ⊆ ann 0 (a * r) (b * r)) :
    lgfPairLp hh φ ∈ annularBlockSubmodule hh a b r := by
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨φ, hs, rfl⟩

def annularPairingsSubmodule (a b r : ℝ) : Submodule ℝ (Lp ℝ 2 P) where
  carrier := annularPairings hh a b r
  zero_mem' := by
    rw [← lgfPairLp_zero hh]
    exact ⟨testRd0Zero, by simp [testRd0Zero], rfl⟩
  add_mem' := by
    rintro X Y ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    refine ⟨testRd0Add φ ψ, ?_, lgfPairLp_add hh φ ψ⟩
    change tsupport (fun x : Rd d => φ.1 x + ψ.1 x) ⊆ ann 0 (a * r) (b * r)
    exact (tsupport_add _ _).trans (Set.union_subset hφ hψ)
  smul_mem' := by
    rintro c X ⟨φ, hφ, rfl⟩
    refine ⟨testRd0Smul c φ, ?_, lgfPairLp_smul hh c φ⟩
    change tsupport (fun x : Rd d => c • φ.1 x) ⊆ ann 0 (a * r) (b * r)
    exact (tsupport_smul_subset_right (fun _ : Rd d => c) (φ.1 : Rd d → ℝ)).trans hφ

theorem annularBlock_eq_span_closure (a b r : ℝ) :
    annularBlock hh a b r = ↑(annularBlockSubmodule hh a b r) := by
  rw [annularBlock, annularBlockSubmodule, Submodule.topologicalClosure_coe]
  have heq : Submodule.span ℝ (annularPairings hh a b r) =
      annularPairingsSubmodule hh a b r :=
    (annularPairingsSubmodule hh a b r).span_eq
  rw [heq]
  rfl

end HigherDimLQGMetric
