import QuantumZipper.Proofs.Thm18.G3CvAdm
import QuantumZipper.Proofs.GFF.K3.MixedM7Local

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1d: the local isometry for the pulled-back free field

Hilbert form of the half-disc Markov covariance of `X ∘ Φ` (G3CvCov/G3CvAdm). In the Hilbert
space `HkE` of the free field (`GFFExist.freeVec`), the pulled-back local generators
`pullLocVec μ = v̂_{Φ_*μ} − v̂_{Φ_*bal μ}` have the Gram matrix `kernelCov (halfDiscGreen b ρ)`
of the free local generators `freeLocVec μ = v̂_μ − v̂_{bal μ}` (`inner_pullLocVec`), hence
(`exists_pullIsometry`) a linear isometry `J` from the closed span of the free local generators
into `HkE` with `J (freeLocVec μ) = pullLocVec μ`. This is the analogue, for the pulled-back
free field, of the M7-c step `exists_localIsometry` (MixedM7Local.lean), whose Hilbert
construction (Sheffield (2007) Thm. 2.17) then produces the coupling of `X ∘ Φ` with a free field
near `b`. Own adaptation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist

open Classical in
/-- The free Hilbert vector of a measure (junk `0` if not admissible). -/
def fvM (ρ : Measure ℂ) : HkE := if h : IsAdmissibleH ρ then freeVec ⟨ρ, h⟩ else 0

theorem fvM_eq {ρ : Measure ℂ} (h : IsAdmissibleH ρ) : fvM ρ = freeVec ⟨ρ, h⟩ := by
  simp [fvM, h]

/-- The data of the pull-back: a local conformal map at `b`, bi-Lipschitz on `closedBall b ρ`
and preserving `Hbar` there, and the radius `r₁ < ρ` of the local measures. -/
structure PullData (Φ : ℂ → ℂ) (b r₀ ρ r₁ m M : ℝ) : Prop where
  conf : LocConf Φ b r₀
  hρ : 0 < ρ
  hρr : ρ < r₀
  bl : BiLip Φ b ρ m M
  hr₁ : r₁ < ρ
  up : ∀ z ∈ closedBall (b : ℂ) ρ ∩ Hbar, Φ z ∈ Hbar

/-- The pulled-back local generator `v̂_{Φ_*μ} − v̂_{Φ_*bal μ}`. -/
def pullLocVec (Φ : ℂ → ℂ) (b ρ : ℝ) (μ : Measure ℂ) : HkE :=
  fvM (μ.map Φ) - fvM ((bal b ρ μ).map Φ)

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

theorem PullData.adm_map (hD : PullData Φ b r₀ ρ r₁ m M) {α : Measure ℂ} (hα : IsAdmissibleH α)
    (hαc : α (closedBall (b : ℂ) ρ)ᶜ = 0) : IsAdmissibleH (α.map Φ) :=
  isAdmissibleH_map_g3cv hD.conf hD.hρr hD.bl hD.up hα hαc

theorem PullData.local_adm (hD : PullData Φ b r₀ ρ r₁ m M) (μ : LocIdx b r₁) :
    IsAdmissibleH (μ.1.map Φ) ∧ IsAdmissibleH ((bal b ρ μ.1).map Φ) ∧
      (μ.1.map Φ) Set.univ = ((bal b ρ μ.1).map Φ) Set.univ := by
  have := μ.2.1.1
  have hsub : (closedBall (b : ℂ) ρ)ᶜ ⊆ (closedBall (b : ℂ) r₁)ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall hD.hr₁.le)
  refine ⟨hD.adm_map μ.2.1 (measure_mono_null hsub μ.2.2),
    hD.adm_map (isAdmissibleH_bal hD.hρ hD.hr₁ μ.2.2) (bal_closedBall_compl_g3cv hD.hρ μ.1), ?_⟩
  rw [Measure.map_apply hD.conf.meas MeasurableSet.univ,
    Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ,
    bal_univ hD.hρ hD.hr₁ μ.2.2]

/-- **Pulled-back local Gram matrix** = `kernelCov (halfDiscGreen b ρ)`. -/
theorem inner_pullLocVec (hD : PullData Φ b r₀ ρ r₁ m M) (μ ν : LocIdx b r₁) :
    ⟪pullLocVec Φ b ρ μ.1, pullLocVec Φ b ρ ν.1⟫ = kernelCov (halfDiscGreen b ρ) μ.1 ν.1 := by
  obtain ⟨a1, a2, e1⟩ := hD.local_adm μ
  obtain ⟨b1, b2, f1⟩ := hD.local_adm ν
  simp only [pullLocVec, fvM_eq a1, fvM_eq a2, fvM_eq b1, fvM_eq b2]
  rw [freeVec_inner ⟨_, a1⟩ ⟨_, a2⟩ ⟨_, b1⟩ ⟨_, b2⟩ e1 f1]
  rw [← inner_freeLocVec hD.hρ hD.hr₁ μ ν]
  have hμl : IsLocalH b ρ μ.1 := ⟨μ.2.1, r₁, hD.hr₁, μ.2.2⟩
  have hνl : IsLocalH b ρ ν.1 := ⟨ν.2.1, r₁, hD.hr₁, ν.2.2⟩
  simp only [freeLocVec]
  rw [freeVec_inner _ _ _ _ (hμl.bal_spec hD.hρ).2 (hνl.bal_spec hD.hρ).2]
  exact kernelCov2_pull_eq hD.conf hD.hρ hD.hρr hD.bl hD.hr₁ μ.2.1 ν.2.1 μ.2.2 ν.2.2

/-- **The local isometry of the pull-back.** -/
theorem exists_pullIsometry (hD : PullData Φ b r₀ ρ r₁ m M) :
    ∃ J : (Submodule.span ℝ (Set.range (freeLocVec hD.hρ hD.hr₁ :
        LocIdx b r₁ → HkE))).topologicalClosure →ₗᵢ[ℝ] HkE,
      (∀ μ : LocIdx b r₁, J ⟨freeLocVec hD.hρ hD.hr₁ μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          pullLocVec Φ b ρ μ.1) ∧
      ∀ x, J x ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx b r₁ =>
        pullLocVec Φ b ρ μ.1)).topologicalClosure :=
  exists_linearIsometry_closure_of_gram _ _ fun μ ν => by
    rw [inner_freeLocVec, inner_pullLocVec hD]

end G3Cv
end QuantumZipper
