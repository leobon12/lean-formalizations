import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondIndepMoment
import LQGMetric.Field.WhiteNoisePsiBlock

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

private theorem supportedIn_psiKernelL2_Ico (Q : PsiParams) {a : ℝ} (ha : 0 < a)
    (b : ℝ) (x : ℂ) :
    SupportedIn (Ico (a ^ 2) (b ^ 2) ×ˢ univ) (Q.psiKernelL2 a b x) := by
  have h : ∀ᵐ p : ℝ × ℂ ∂volume,
      p ∈ (Ico (a ^ 2) (b ^ 2) ×ˢ univ)ᶜ →
      (Q.psiKernelL2 a b x : ℝ × ℂ → ℝ) p = 0 := by
    filter_upwards [Q.coeFn_psiKernelL2 a b ha x, PsiParams.ae_ne_sq b] with p h1 h2 hp
    rw [h1]
    have hq : p ∉ Icc (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ) := by
      intro hq
      apply hp
      exact ⟨⟨(mem_prod.mp hq).1.1,
        lt_of_le_of_ne (mem_prod.mp hq).1.2 h2⟩, trivial⟩
    simp [PsiParams.psiKernel, phiKernel, indicator_of_notMem hq]
  exact (ae_restrict_iff' ((measurableSet_Ico.prod MeasurableSet.univ).compl)).mpr h

private theorem indepFun_psi_phi (hW : IsWhiteNoise P W) (Q : PsiParams)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    IndepFun (fun ω x => psi Q W a b x ω) (fun ω x => phi W b c x ω) P := by
  have hb : 0 < b := ha.trans_le hab
  have hdisj : Disjoint (Ico (a ^ 2) (b ^ 2) ×ˢ (univ : Set ℂ))
      (Icc (b ^ 2) (c ^ 2) ×ˢ univ) := by
    rw [Set.disjoint_prod]
    left
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.1 (not_le.mpr h1.2)
  have hI := hW.indepFun_of_disjoint hdisj
  let Ψ : ({f // SupportedIn (Ico (a ^ 2) (b ^ 2) ×ˢ univ) f} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨Q.psiKernelL2 a b x,
      supportedIn_psiKernelL2_Ico Q ha b x⟩
  let Φ : ({f // SupportedIn (Icc (b ^ 2) (c ^ 2) ×ˢ univ) f} → ℝ) → ℂ → ℝ :=
    fun F x => Real.sqrt Real.pi * F ⟨phiKernelL2 b c x,
      supportedIn_phiKernelL2' hb x⟩
  have hΨ : Measurable Ψ :=
    measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  have hΦ : Measurable Φ :=
    measurable_pi_iff.mpr fun x => (measurable_pi_apply _).const_mul _
  exact hI.comp hΨ hΦ

 
theorem laneC_indepFun_coarse_phi_fine_psi
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) :
    IndepFun (fun ω x => phiMN W P 0 K x ω)
      (fun ω x => psiMN Q W P K n x ω) P := by
  have := hW.isProbabilityMeasure
  let a : ℝ := (2 : ℝ)⁻¹ ^ n
  let b : ℝ := (2 : ℝ)⁻¹ ^ K
  have ha : 0 < a := by positivity
  have hab : a ≤ b := pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn
  have hraw := (indepFun_psi_phi hW Q ha hab ((2 : ℝ)⁻¹ ^ 0)).symm
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hψ := isPsiVersion_psiMN (Q := Q) hW hKn
  exact IndepFun.of_modification hraw
    (fun x => measurable_phi hW b ((2 : ℝ)⁻¹ ^ 0) x)
    (fun x => measurable_psi hW Q a b x)
    hφ.meas hψ.meas hφ.ae_eq hψ.ae_eq

 
theorem laneC_indep_coarse_point_fine_field
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) (b : ℤ × ℤ) :
    Indep (MeasurableSpace.comap
        (phiMN W P 0 K (T20.dyCenter K b)) (inferInstance : MeasurableSpace ℝ))
      (MeasurableSpace.comap
        (fun ω x => psiMN Q W P K n x ω)
        (inferInstance : MeasurableSpace (ℂ → ℝ))) P := by
  have hI := laneC_indepFun_coarse_phi_fine_psi P W hW Q hKn
  have hpoint : IndepFun (fun ω => phiMN W P 0 K (T20.dyCenter K b) ω)
      (fun ω x => psiMN Q W P K n x ω) P :=
    hI.comp (measurable_pi_apply _) measurable_id
  exact (IndepFun_iff_Indep _ _ P).1 hpoint

 

theorem laneC_conditional_coarse_phi_exp_moment
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) (b : ℤ × ℤ) (a : ℝ) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, ENNReal.ofReal
        (Real.exp (a * phiMN W P 0 K (T20.dyCenter K b) x))
        ∂(condExpKernel P (MeasurableSpace.comap
          (fun ω x => psiMN Q W P K n x ω)
          (inferInstance : MeasurableSpace (ℂ → ℝ))) ω)) ≤
      ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) * a ^ 2 / 2)) := by
  have hψ : Measurable (fun ω x => psiMN Q W P K n x ω) :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW hKn).meas
  exact laneC_conditional_coarse_phi_exp_moment_of_indep P hW hψ.comap_le K b a
    (laneC_indep_coarse_point_fine_field P W hW Q hKn b)

end SupercriticalLQGUniqueness.B2.DG20Conc
