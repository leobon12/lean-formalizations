import QuantumZipper.Proofs.Thm18.G3CvAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (b), layer 1: far reference measures in the local conformal coupling

The Palm field is normalized at the unit circle `S = fc(0, 1)` (`normAt g3zS`), which lies far
from the zoom point, while the D3⁺ model is normalized at a reference circle `ρ₀` near it. The
gauge constant is `W(Φ_* ρ₀) − W(S)`. In the coupling of `G3Cv.exists_pullCouplingHarm`
(Gaussian process `Z` over `PIdx`), this constant splits as

  `W(Φ_*μ) − W(S) = X'(μ) − X'(bal μ) + Ξ(u)`      (a.s., `ae_realWP_far`)

for local `μ` and `S` carried away from `Φ(closedBall b ρ)` and its reflection: the first part is
the local part (`realP_local`), and `v̂_{Φ_* bal μ} − v̂_S` is orthogonal to the pulled-back local
generators (`inner_fvM_semi_sub_far_pullLocVec_eq_zero`: semicircle measures reproduce the Neumann
kernel under balayage, `kernelCov_neumannH_bal_right`, the correction `kPull` too; far measures
by `integral_neumannH_comp_bal`), so it is a coordinate of `Ξ`. Hence the gauge constant is
measurable for `σ(Ξ) ⊔ outsideSigma X'` whenever `μ` and `bal μ` avoid the conditioning disc.
Own adaptation of G3CvOut.lean / G3CvAsm.lean (Sheffield, *Gaussian free fields for
mathematicians* (2007), §2.2 and Thm. 2.17: orthogonal decomposition of the Dirichlet space).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Za

open G3Cv K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- **A semicircle measure minus a far measure is orthogonal to the pulled-back local part.** -/
theorem inner_fvM_semi_sub_far_pullLocVec_eq_zero (hD : PullData Φ b r₀ ρ r₁ m M)
    {γ S : Measure ℂ} (hγ : IsAdmissibleH γ) (hS : IsAdmissibleH S)
    (hγc : γ (closedBall (b : ℂ) ρ)ᶜ = 0) (hγB : γ (ball (b : ℂ) ρ) = 0)
    (hm : (γ.map Φ) Set.univ = S Set.univ)
    (hSy : ∀ᵐ y ∂S, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) (ν : LocIdx b r₁) :
    ⟪fvM (γ.map Φ) - fvM S, pullLocVec Φ b ρ ν.1⟫ = 0 := by
  obtain ⟨a1, a2, e1⟩ := hD.local_adm ν
  have := ν.2.1.1
  have := isFiniteMeasure_bal hD.hρ hD.hr₁ ν.2.2
  have := hγ.1
  have g1 := hD.adm_map hγ hγc
  have hνρ : ν.1 (closedBall (b : ℂ) ρ)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall hD.hr₁.le)) ν.2.2
  have hbA := isAdmissibleH_bal hD.hρ hD.hr₁ ν.2.2
  have hbc := bal_closedBall_compl_g3cv (b := b) hD.hρ ν.1
  simp only [pullLocVec, fvM_eq g1, fvM_eq hS, fvM_eq a1, fvM_eq a2]
  rw [freeVec_inner ⟨_, g1⟩ ⟨S, hS⟩ ⟨_, a1⟩ ⟨_, a2⟩ hm e1]
  simp only [kernelCov2]
  have hmap : ∀ (β : Measure ℂ) (y : ℂ),
      ∫ v, neumannH y v ∂(β.map Φ) = ∫ w, neumannH y (Φ w) ∂β := fun β y =>
    integral_map hD.conf.meas.aemeasurable
      ((measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  have hfar : kernelCov neumannH S (ν.1.map Φ) =
      kernelCov neumannH S ((bal b ρ ν.1).map Φ) := by
    unfold kernelCov
    refine integral_congr_ae ?_
    filter_upwards [hSy] with y hy
    rw [hmap, hmap, integral_neumannH_comp_bal hD hy ν]
  have hk : kernelCov (kPull Φ) γ (bal b ρ ν.1) = kernelCov (kPull Φ) γ ν.1 :=
    integral_congr_ae ((ae_mem_of_compl_null_g3cv hγc).mono fun x hx =>
      integral_kPull_bal hD.conf hD.hρ hD.hρr hD.bl hD.hr₁ ν.2.2
        (measure_singleton_of_admissible ν.2.1) hx)
  rw [kernelCov_map_g3cv hD.conf, kernelCov_map_g3cv hD.conf,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ ν.2.1 hγc hνρ,
    kernelCov_pull_split hD.conf hD.hρr hD.bl hγ hbA hγc hbc,
    kernelCov_neumannH_bal_right hD.hρ hD.hr₁ ν hγ hγB, hfar, hk]
  ring

/-- **The gauge constant in the realized coupling.** -/
theorem ae_realWP_far (hD : PullData Φ b r₀ ρ r₁ m M)
    {J : (Submodule.span ℝ (Set.range (freeLocVec hD.hρ hD.hr₁ :
        LocIdx b r₁ → HkE))).topologicalClosure →ₗᵢ[ℝ] HkE}
    (hJ : ∀ μ : LocIdx b r₁, J ⟨freeLocVec hD.hρ hD.hr₁ μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          pullLocVec Φ b ρ μ.1)
    {Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ}
    (hZ : ∀ {ι : Type} [Fintype ι] (τ : ι → PIdx Φ b ρ r₁) (c : ι → ℝ),
      HasLaw (fun ω => ∑ i, c i * Z (τ i) ω)
        (gaussianReal 0 (‖∑ i, c i • pVec J (τ i)‖ ^ 2).toNNReal) stdP)
    (μ : LocIdx b r₁) {S : Measure ℂ} (hS : IsAdmissibleH S)
    (hm : μ.1 Set.univ = S Set.univ)
    (hSy : ∀ᵐ y ∂S, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) :
    ∃ u : PXiIdx Φ b ρ r₁, ∀ᵐ ω ∂stdP, realWP Z ω (μ.1.map Φ) - realWP Z ω S =
      realXP Z ω μ.1 - realXP Z ω (bal b ρ μ.1) + Z (Sum.inr (Sum.inr u)) ω := by
  have := μ.2.1.1
  have := isFiniteMeasure_bal hD.hρ hD.hr₁ μ.2.2
  have hbA := isAdmissibleH_bal hD.hρ hD.hr₁ μ.2.2
  have hbc := bal_closedBall_compl_g3cv (b := b) hD.hρ μ.1
  have a1 := hD.adm_map hbA hbc
  have hm1 : ((bal b ρ μ.1).map Φ) Set.univ = S Set.univ := by
    rw [Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ,
      bal_univ hD.hρ hD.hr₁ μ.2.2, hm]
  have horth : ∀ ν : LocIdx b r₁,
      ⟪freeVec ⟨_, a1⟩ - freeVec ⟨S, hS⟩, pullLocVec Φ b ρ ν.1⟫ = 0 := by
    intro ν
    have h := inner_fvM_semi_sub_far_pullLocVec_eq_zero hD hbA hS hbc (bal_ball hD.hρ) hm1 hSy ν
    rwa [fvM_eq a1, fvM_eq hS] at h
  set u : PXiIdx Φ b ρ r₁ := ⟨freeVec ⟨_, a1⟩ - freeVec ⟨S, hS⟩, horth⟩ with hu
  refine ⟨u, ?_⟩
  have hlaw := gs_comb4 hZ ![Sum.inr (Sum.inr u), Sum.inl ⟨_, a1⟩, Sum.inl ⟨S, hS⟩,
    Sum.inl ⟨_, a1⟩] ![1, -1, 1, 0]
    (fun ω => Z (Sum.inr (Sum.inr u)) ω - (Z (Sum.inl ⟨_, a1⟩) ω - Z (Sum.inl ⟨S, hS⟩) ω))
    (fun ω => by simp [Fin.sum_univ_four]; ring) (0 : WithLp 2 (HkE × HkE))
    (by
      simp [Fin.sum_univ_four, pVec, jointW, hu]
      rw [← WithLp.toLp_neg, ← WithLp.toLp_add, ← WithLp.toLp_add]
      have e : freeVec ⟨Measure.map Φ (bal b ρ μ.1), a1⟩ - freeVec ⟨S, hS⟩ +
            -freeVec ⟨Measure.map Φ (bal b ρ μ.1), a1⟩ + freeVec ⟨S, hS⟩ = 0 := by abel
      simp only [Prod.mk_add_mk, Prod.neg_mk, add_zero, neg_zero, e]
      rfl)
  have h0 : (‖(0 : WithLp 2 (HkE × HkE))‖ ^ 2).toNNReal = 0 := by simp
  have hae : ∀ᵐ ω ∂stdP, Z (Sum.inr (Sum.inr u)) ω -
      (Z (Sum.inl ⟨_, a1⟩) ω - Z (Sum.inl ⟨S, hS⟩) ω) = 0 := by
    refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
    rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [hae, realP_local hZ hD hJ μ] with ω hω hloc
  rw [realWP_apply (Z := Z) _ a1 ω, realWP_apply (Z := Z) _ hS ω] at *
  linarith

end G3Za
end QuantumZipper
