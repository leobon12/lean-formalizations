import QuantumZipper.Proofs.Thm18.G1SideCong
import QuantumZipper.Proofs.Thm18.G1Z3Wedge
import QuantumZipper.Proofs.Zipper.SWCoreB5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (2): the transported wedge boundary measure in terms of the free field

For a map `ψ` of the boundary class `BdryClass a b ρ M m` whose values on the `ρ`-thickening of
`[a,b]` stay at distance `≥ c₀ > 0` from `0`, the transported test integral of the wedge boundary
measure over `ψ([a,b])` equals the transported integral of the free-field boundary measure with the
weight `e^{γ/2 · profile}`, the profile cut off inside the disc of radius `c₀/2`
(`integral_target_wedge`). This is rule (5.1) of Duplantier–Sheffield (*LQG and KPZ*, Invent.
Math. 185 (2011)) through the proved `Thm18Asm.G1Z3.qBoundaryMeasure_wedgeField_restrict`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

variable {a b ρ M m c₀ : ℝ} {ψ : ℂ → ℂ}

/-- The boundary values of a class map on `[a,b]` fill `[ψ(a), ψ(b)]`, and stay `c₀` away
from `0`. -/
theorem exists_preimage_class (hab : a < b) (hρ : 0 < ρ) (hψ : ψ ∈ BdryClass a b ρ M m)
    {u : ℝ} (hu : u ∈ Icc (ψ a).re (ψ b).re) : ∃ t ∈ Icc a b, ψ t = (u : ℂ) := by
  have hthk : ∀ t ∈ Icc a b, ((t : ℝ) : ℂ) ∈ thickening ρ (segC a b) :=
    fun t ht => self_subset_thickening hρ _ (ofReal_mem_segC ht)
  have hc : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn
      (hψ.1.continuousOn.comp Complex.continuous_ofReal.continuousOn fun t ht => hthk t ht)
  obtain ⟨t, ht, htu⟩ := intermediate_value_Icc hab.le hc hu
  refine ⟨t, ht, Complex.ext ?_ ?_⟩
  · simpa using htu
  · simpa using hψ.2.2.1 t ht

theorem norm_ge_of_mem_Icc_class (hab : a < b) (hρ : 0 < ρ) (hψ : ψ ∈ BdryClass a b ρ M m)
    (hsep : ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖ψ z‖) {u : ℝ}
    (hu : u ∈ Icc (ψ a).re (ψ b).re) : c₀ ≤ ‖(u : ℂ)‖ := by
  obtain ⟨t, ht, htu⟩ := exists_preimage_class hab hρ hψ hu
  rw [← htu]
  exact hsep _ (self_subset_thickening hρ _ (ofReal_mem_segC ht))

/-- The transported test function vanishes at the endpoints `ψ(a)`, `ψ(b)`. -/
theorem invFun_endpoint_zero (hab : a < b) (hψ : ψ ∈ BdryClass a b ρ M m) {f : ℝ → ℝ}
    (hfs : tsupport f ⊆ Ioo a b) {t : ℝ} (ht : t = a ∨ t = b) :
    f (Function.invFunOn (fun s : ℝ => (ψ s).re) (Icc a b) (ψ t).re) = 0 := by
  have htI : t ∈ Icc a b := by rcases ht with rfl | rfl <;> simp [hab.le]
  have hmem : (ψ t).re ∈ (fun s : ℝ => (ψ s).re) '' Icc a b := ⟨t, htI, rfl⟩
  have h1 := Function.invFunOn_mem hmem
  have h2 : (ψ ((Function.invFunOn (fun s : ℝ => (ψ s).re) (Icc a b) (ψ t).re : ℝ) : ℂ)).re =
      (ψ t).re :=
    Function.invFunOn_eq hmem
  have e : Function.invFunOn (fun s : ℝ => (ψ s).re) (Icc a b) (ψ t).re = t :=
    hψ.2.2.2.1.injOn h1 htI h2
  rw [e]
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hfs h
  rcases ht with rfl | rfl
  · exact lt_irrefl _ this.1
  · exact lt_irrefl _ this.2

/-- **Transported wedge integral = weighted transported free-field integral.** -/
theorem integral_target_wedge {γ Q₀ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A)
    (hx : IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x))
    (hW : IsVagueLimitR (bdryApprox γ (wedgeField (lateralPart x) A Q₀))
      (qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀)))
    (hab : a < b) (hρ : 0 < ρ) (hψ : ψ ∈ BdryClass a b ρ M m) (hc₀ : 0 < c₀)
    (hsep : ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖ψ z‖) {f : ℝ → ℝ}
    (hfs : tsupport f ⊆ Ioo a b) :
    ∫ u in Icc (ψ a).re (ψ b).re, f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) *
        Real.exp (γ / 2 * profCut x A Q₀ (c₀ / 2) (u : ℂ)) ∂qBoundaryMeasure γ x =
      ∫ u in Icc (ψ a).re (ψ b).re, f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u)
        ∂qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀) := by
  set lo := (ψ a).re
  set hi := (ψ b).re
  set g : ℝ → ℝ := fun u => f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc a b) u) with hg
  have hsd : ∀ u ∈ Icc lo hi \ Ioo lo hi, g u = 0 := by
    intro u hu
    have hlh : u = lo ∨ u = hi := by
      rcases hu with ⟨⟨h1, h2⟩, h3⟩
      by_contra hne
      push_neg at hne
      exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hne.1), lt_of_le_of_ne h2 hne.2⟩
    rcases hlh with rfl | rfl
    · exact invFun_endpoint_zero hab hψ hfs (Or.inl rfl)
    · exact invFun_endpoint_zero hab hψ hfs (Or.inr rfl)
  have hJ0 : (0 : ℝ) ∉ Ioo lo hi := fun h => by
    have := norm_ge_of_mem_Icc_class hab hρ hψ hsep (Ioo_subset_Icc_self h)
    simp at this
    linarith
  have hres := Thm18Asm.G1Z3.qBoundaryMeasure_wedgeField_restrict hG hraw hA hx hW
    isOpen_Ioo hJ0
  have e1 : ∫ u in Icc lo hi, g u * Real.exp (γ / 2 * profCut x A Q₀ (c₀ / 2) (u : ℂ))
        ∂qBoundaryMeasure γ x =
      ∫ u in Ioo lo hi, g u * Real.exp (γ / 2 * profCut x A Q₀ (c₀ / 2) (u : ℂ))
        ∂qBoundaryMeasure γ x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc Ioo_subset_Icc_self
      fun u hu => by rw [hsd u hu, zero_mul]
  have e2 : ∫ u in Icc lo hi, g u ∂qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀) =
      ∫ u in Ioo lo hi, g u ∂qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc Ioo_subset_Icc_self hsd
  show ∫ u in Icc lo hi, g u * Real.exp (γ / 2 * profCut x A Q₀ (c₀ / 2) (u : ℂ))
        ∂qBoundaryMeasure γ x =
      ∫ u in Icc lo hi, g u ∂qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀)
  rw [e1, e2]
  rw [hres, restrict_withDensity measurableSet_Ioo]
  have hEq : EqOn (fun u : ℝ => WedgeCan.wedgeProfile x A Q₀ (u : ℂ))
      (fun u : ℝ => profCut x A Q₀ (c₀ / 2) (u : ℂ)) (Ioo lo hi) := fun u hu =>
    (profCut_eq (le_trans (by linarith)
      (norm_ge_of_mem_Icc_class hab hρ hψ hsep (Ioo_subset_Icc_self hu)))).symm
  have hcont : Continuous fun u : ℝ => profCut x A Q₀ (c₀ / 2) (u : ℂ) :=
    (continuous_profCut hG hA Q₀ (by positivity)).comp Complex.continuous_ofReal
  have hdm : AEMeasurable (fun u : ℝ => ENNReal.ofReal (Real.exp
      (γ / 2 * WedgeCan.wedgeProfile x A Q₀ (u : ℂ)))) ((qBoundaryMeasure γ x).restrict (Ioo lo hi)) := by
    have hm : Measurable fun u : ℝ =>
        ENNReal.ofReal (Real.exp (γ / 2 * profCut x A Q₀ (c₀ / 2) (u : ℂ))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hcont.measurable.const_mul _))
    refine hm.aemeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    simp only [comp_apply, hEq hu]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hdm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, hEq hu]
  ring

end G1Side
end QuantumZipper
