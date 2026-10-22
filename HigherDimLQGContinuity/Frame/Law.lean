import HigherDimLQGContinuity.Frame.Form
import LQGDimension.Existence.AssemblyAux1
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import HigherDimLQGMetric.Frozen.NormLGFLawSpec

/-!
# Pairing frame III: the law of the coordinates

Packet N3 (NA4 Details (a) A2, step 6; blueprint Part C `c:prop-frame`, step 4).

The coordinate map `Φ(g) = (g(ψ_j))_j` (`frameCoord`) and the projection `π(ω) = (c_j ω_j)_j` (`frameProj`, which
kills the coordinates outside `J = {c_j = 1}`). Under every whole-space LGF the pairings `h(ψ_j)` are independent
(jointly Gaussian and uncorrelated, Mathlib's `IsGaussianProcess.iIndepFun_of_covariance_eq_zero`) with laws
`N(0, c_j)`, so the law of `Φ ∘ h` is `⊗_j N(0, c_j)` (`map_frameCoord_of_isWholeSpaceLGF`), which is also the law of `π`
under `stdP = ⊗_j N(0, 1)` (`map_frameProj`, Mathlib's `Measure.infinitePi_map_pi`). Hence
`(normLGFLaw d).map Φ = stdP.map π` (`map_frameCoord_normLGFLaw`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The coordinate map `Φ(g) = (g(ψ_j))_j`. -/
def frameCoord (d : ℕ) (g : DistRd d) : ℕ → ℝ := fun j => g (frameGS d j)

/-- The projection `π(ω) = (c_j ω_j)_j`. -/
def frameProj (d : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ := fun j => frameC d j * ω j

/-- `ψ_j` as a mean-zero test function. -/
def frameGS0 (d : ℕ) (j : ℕ) : TestRd0 d := ⟨frameGS d j, integral_frameGS j⟩

theorem measurable_frameCoord : Measurable (frameCoord d) :=
  measurable_pi_iff.2 fun _ => measurable_distOn_apply _

theorem measurable_frameProj : Measurable (frameProj d) :=
  measurable_pi_iff.2 fun j => (measurable_pi_apply j).const_mul _

theorem frameProj_add (ω ω' : ℕ → ℝ) : frameProj d (ω + ω') = frameProj d ω + frameProj d ω' := by
  funext j
  simp only [frameProj, Pi.add_apply, mul_add]

section Law

variable [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

theorem cov_frameGS_of_isWholeSpaceLGF (hh : IsWholeSpaceLGF h P) (i j : ℕ) :
    cov[fun ω => h ω (frameGS d i), fun ω => h ω (frameGS d j); P] =
      if i = j then frameC d i else 0 := by
  have e : cov[fun ω => h ω (frameGS d i), fun ω => h ω (frameGS d j); P] =
      logCovRd ⇑(frameGS d i) ⇑(frameGS d j) := hh.covariance_eq (frameGS0 d i) (frameGS0 d j)
  obtain ⟨M, D, hM⟩ := exists_isBddSupp_testOn (frameGS d i)
  obtain ⟨M', D', hM'⟩ := exists_isBddSupp_testOn (frameGS d j)
  rw [logCovRd_eq_logCovF hM hM'] at e
  exact e.trans (frameGS_orthonormal i j)

theorem iIndepFun_frameGS_of_isWholeSpaceLGF (hh : IsWholeSpaceLGF h P) :
    iIndepFun (fun j ω => h ω (frameGS d j)) P := by
  have hGP : IsGaussianProcess (fun (p : (_ : ℕ) × Unit) ω => h ω (frameGS d p.1)) P :=
    hh.gaussian.comp_right (fun (p : (_ : ℕ) × Unit) => frameGS0 d p.1)
  have hind := hGP.iIndepFun_of_covariance_eq_zero (X := fun t (_ : Unit) ω => h ω (frameGS d t))
    (fun t _ => ((measurable_distOn_apply _).comp hh.measurable).aemeasurable)
    (fun t₁ t₂ hne _ _ => by rw [cov_frameGS_of_isWholeSpaceLGF hh, ite_eq_right hne])
  exact hind.comp (fun _ (f : Unit → ℝ) => f ()) (fun _ => measurable_pi_apply ())

theorem map_frameGS_of_isWholeSpaceLGF (hh : IsWholeSpaceLGF h P) (j : ℕ) :
    P.map (fun ω => h ω (frameGS d j)) = gaussianReal 0 (frameC d j).toNNReal := by
  have hG : HasGaussianLaw (fun ω => h ω (frameGS d j)) P :=
    hh.gaussian.hasGaussianLaw_eval (frameGS0 d j)
  have hm : ∫ ω, h ω (frameGS d j) ∂P = 0 := hh.centered (frameGS0 d j)
  have hv : Var[fun ω => h ω (frameGS d j); P] = frameC d j := by
    rw [← covariance_self hG.aemeasurable, cov_frameGS_of_isWholeSpaceLGF hh, ite_eq_left rfl]
  rw [hG.map_eq_gaussianReal, hm, hv]

/-- **The law of the coordinates under an LGF**: `⊗_j N(0, c_j)`. -/
theorem map_frameCoord_of_isWholeSpaceLGF (hh : IsWholeSpaceLGF h P) :
    P.map (fun ω => frameCoord d (h ω)) =
      Measure.infinitePi fun j => gaussianReal 0 (frameC d j).toNNReal := by
  have := hh.gaussian.isProbabilityMeasure
  have hm : ∀ j, Measurable fun ω => h ω (frameGS d j) := fun j =>
    (measurable_distOn_apply _).comp hh.measurable
  have e := (iIndepFun_iff_map_fun_eq_infinitePi_map hm).1 (iIndepFun_frameGS_of_isWholeSpaceLGF hh)
  have e' : (fun ω => frameCoord d (h ω)) = fun ω j => h ω (frameGS d j) := rfl
  rw [e', e]
  congr 1
  funext j
  exact map_frameGS_of_isWholeSpaceLGF hh j

end Law

/-- The law of `π` under `stdP`: `⊗_j N(0, c_j)`. -/
theorem map_frameProj :
    GaussianLQG.stdP.map (frameProj d) =
      Measure.infinitePi fun j => gaussianReal 0 (frameC d j).toNNReal := by
  have e : frameProj d = fun (ω : ℕ → ℝ) j => (fun x => frameC d j * x) (ω j) := rfl
  rw [e]
  show (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map _ = _
  rw [Measure.infinitePi_map_pi _ fun j => measurable_const_mul _]
  congr 1
  funext j
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk, Real.coe_toNNReal']
  rcases frameC_mem (d := d) j with hc | hc <;> rw [hc] <;> norm_num

/-- **`Φ_* μ = π_* stdP`** (NA4 A2 step 6). -/
theorem map_frameCoord_normLGFLaw [NeZero d] (hd : 2 ≤ d) :
    (normLGFLaw d).map (frameCoord d) = GaussianLQG.stdP.map (frameProj d) := by
  have hh := (normLGFLaw_spec d hd).2.1
  have e := map_frameCoord_of_isWholeSpaceLGF hh.1
  rw [map_frameProj, ← e]
  rfl

end HigherDimLQGContinuity
