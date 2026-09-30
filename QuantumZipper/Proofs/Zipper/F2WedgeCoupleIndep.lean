import QuantumZipper.Proofs.Zipper.F2WedgeCoupleFree

/-!
# WEDGE-COUPLE (3): independence bookkeeping

* `indepFun_latF_radialProc`: the (sanitized) lateral part `latF X` of a free field is
  independent of its radial process (Sheffield, arXiv:1012.4797, §1.6; Duplantier–Miller–
  Sheffield, arXiv:1409.7055, §4.1: `h†` and `h_{|·|}(0)` are independent). The proof is that of
  `WedgeTK.indepFun_radialProc_lateralPart` (jointly Gaussian families with vanishing
  cross-covariances), for the lateral coordinates `X(μ) − ∫ h_{|z|}(0) dμ` at all admissible `μ`.
* `indepFun_prod_pair`: on a product space, `(f₁ ∘ fst, f₂ ∘ snd) ⊥ (g₁ ∘ fst, g₂ ∘ snd)` when
  `f₁ ⊥ g₁` and `f₂ ⊥ g₂` (generating π-systems of rectangles; own elementary proof).
* `coupleField_eq_add`: `coupleField X₁ X₂ ω = latF X₁ ω.1 + radF (X₂ ω.2)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace F2

open WedgeTK

/-! ## 1. Lateral and radial pieces -/

/-- The sanitized lateral part `μ ↦ X(μ) − ∫ h_{|z|}(0) dμ` (admissible `μ`, else `0`). -/
def latF {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  {μ : Measure ℂ | IsAdmissibleH μ}.indicator (fun μ => X ω μ - radInt (X ω) μ)

/-- The sanitized radial part `μ ↦ ∫ h_{|z|}(0) dμ`. -/
def radF (x : FieldSample) : FieldSample :=
  {μ : Measure ℂ | IsAdmissibleH μ}.indicator (fun μ => radInt x μ)

theorem coupleField_eq_add {Ω Ω' : Type*} (X₁ : Ω → FieldSample) (X₂ : Ω' → FieldSample)
    (ω : Ω × Ω') : coupleField X₁ X₂ ω = latF X₁ ω.1 + radF (X₂ ω.2) := by
  funext μ
  by_cases h : IsAdmissibleH μ
  · simp only [coupleField, latF, radF, Pi.add_apply,
      Set.indicator_of_mem (show μ ∈ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
  · simp only [coupleField, latF, radF, Pi.add_apply,
      Set.indicator_of_notMem (show μ ∉ {μ : Measure ℂ | IsAdmissibleH μ} from h), add_zero]

theorem measurable_radF : Measurable radF := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsAdmissibleH μ
  · have := h.1
    simp only [radF, Set.indicator_of_mem (show μ ∈ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
    exact measurable_radInt μ
  · simp only [radF, Set.indicator_of_notMem (show μ ∉ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
    exact measurable_const

/-- Admissible measures. -/
abbrev AdmIdx : Type := {μ : Measure ℂ // IsAdmissibleH μ}

/-- Extension by `0` from admissible measures to all measures. -/
def extAdm (v : AdmIdx → ℝ) : FieldSample := by
  classical
  exact fun μ => if h : IsAdmissibleH μ then v ⟨μ, h⟩ else 0

theorem measurable_extAdm : Measurable extAdm := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsAdmissibleH μ
  · simp only [extAdm, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extAdm, dif_neg h]
    exact measurable_const

/-- The lateral pair `(μ, radSmear μ)`. -/
def latP (μ : AdmIdx) : BPair :=
  ⟨(μ.1, radSmear μ.1), μ.2, isAdmissibleH_radSmear μ.2, (radSmear_univ _).symm⟩

theorem kernelCov2_latP_radPair (μ : AdmIdx) (t : ℝ) :
    kernelCov2 neumannH (latP μ).1 (radPair t).1 = 0 := by
  simp only [kernelCov2, radPair, latP]
  rw [kernelCov_fc0_right _ (Real.exp_pos _), kernelCov_fc0_right _ one_pos,
    kernelCov_fc0_right _ (Real.exp_pos _), kernelCov_fc0_right _ one_pos,
    integral_phi_radSmear μ.2 (Real.exp_pos _), integral_phi_radSmear μ.2 one_pos]
  ring

section Lat

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

theorem latF_eq_extAdm (ω : Ω) :
    latF X ω = extAdm (fun μ : AdmIdx => X ω μ.1 - radInt (X ω) μ.1) := by
  classical
  funext μ
  by_cases h : IsAdmissibleH μ
  · simp only [latF, extAdm, dif_pos h,
      Set.indicator_of_mem (show μ ∈ {μ : Measure ℂ | IsAdmissibleH μ} from h)]
  · simp only [latF, extAdm, dif_neg h,
      Set.indicator_of_notMem (show μ ∉ {μ : Measure ℂ | IsAdmissibleH μ} from h)]

theorem measurable_latA (hX : IsFreeGFFModConstH X P) :
    Measurable fun ω (μ : AdmIdx) => X ω μ.1 - radInt (X ω) μ.1 :=
  measurable_pi_iff.2 fun μ => by
    have := μ.2.1
    exact (hX.measurable_coord μ.1).sub ((measurable_radInt μ.1).comp (measurable_X_pi hX))

theorem measurable_latF (hX : IsFreeGFFModConstH X P) : Measurable (latF X) := by
  have e : latF X = extAdm ∘ fun ω (μ : AdmIdx) => X ω μ.1 - radInt (X ω) μ.1 :=
    funext fun ω => latF_eq_extAdm ω
  rw [e]
  exact measurable_extAdm.comp (measurable_latA hX)

/-- **Independence of the lateral and radial parts.** -/
theorem indepFun_latF_radialProc (hX : IsFreeGFFModConstH X P) :
    IndepFun (latF X) (fun ω (t : ℝ) => radialProc X t ω) P := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  set latA : Ω → AdmIdx → ℝ := fun ω μ => X ω μ.1 - radInt (X ω) μ.1 with hlatA
  have hmh : Measurable latA := measurable_latA hX
  have hmf : Measurable (fun ω t => radialProc X t ω) :=
    measurable_pi_iff.2 fun t => measurable_radialProc hX t
  suffices h : IndepFun latA (fun ω t => radialProc X t ω) P by
    have e : latF X = extAdm ∘ latA := funext fun ω => latF_eq_extAdm ω
    rw [e]
    exact h.comp measurable_extAdm measurable_id
  have hGs : IsGaussianProcess (Sum.elim (gaussFam X latP) (gaussFam X radPair)) P := by
    refine (hX.gaussian.comp_right (Sum.elim latP radPair)).congr fun i => ?_
    cases i <;> exact ae_of_all _ fun ω => rfl
  have hind' : IndepFun (fun ω μ => gaussFam X latP μ ω) (fun ω t => gaussFam X radPair t ω) P :=
    hGs.indepFun_of_covariance_eq_zero (fun μ => (measurable_gaussFam hX _ μ).aemeasurable)
      (fun t => (measurable_gaussFam hX _ t).aemeasurable) fun μ t =>
        (hX.covariance_eq _ _ (latP μ).2.1 (latP μ).2.2.1 (latP μ).2.2.2
          (radPair t).2.1 (radPair t).2.2.1 (radPair t).2.2.2).trans
          (kernelCov2_latP_radPair μ t)
  have hrad : ∀ t, radialProc X t =ᵐ[P] gaussFam X radPair t := fun t => radialProc_ae_eq hG t
  have hlat : ∀ μ : AdmIdx, (fun ω => latA ω μ) =ᵐ[P] gaussFam X latP μ := fun μ =>
    (ae_radInt_eq hX μ.2).mono fun ω h => by
      simp only [hlatA, gaussFam, latP, h.2]
  rw [indepFun_iff_map_prod_eq_prod_map_map hmh.aemeasurable hmf.aemeasurable]
  have hh_eq : P.map latA = P.map (fun ω μ => gaussFam X latP μ ω) :=
    map_eq_of_forall_ae_eq hmh.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable hlat
  have hf_eq : P.map (fun ω t => radialProc X t ω) = P.map (fun ω t => gaussFam X radPair t ω) :=
    map_eq_of_forall_ae_eq hmf.aemeasurable (measurable_gaussFam_pi hX _).aemeasurable hrad
  set E := MeasurableEquiv.sumPiEquivProdPi fun _ : AdmIdx ⊕ ℝ => ℝ with hE
  have m1 : Measurable fun ω (j : AdmIdx ⊕ ℝ) =>
      Sum.elim (latA ω) (fun t => radialProc X t ω) j := by
    refine measurable_pi_iff.2 fun j => ?_
    rcases j with μ | t
    · exact measurable_pi_iff.1 hmh μ
    · exact measurable_radialProc hX t
  have m2 : Measurable fun ω (j : AdmIdx ⊕ ℝ) =>
      Sum.elim (fun μ => gaussFam X latP μ ω) (fun t => gaussFam X radPair t ω) j := by
    refine measurable_pi_iff.2 fun j => ?_
    rcases j with μ | t
    · exact measurable_gaussFam hX _ μ
    · exact measurable_gaussFam hX _ t
  have hfh_eq : P.map (fun ω => (latA ω, fun t => radialProc X t ω)) =
      P.map (fun ω => ((fun μ => gaussFam X latP μ ω), fun t => gaussFam X radPair t ω)) := by
    have k1 : (fun ω => (latA ω, fun t => radialProc X t ω)) =
        E ∘ fun ω (j : AdmIdx ⊕ ℝ) => Sum.elim (latA ω) (fun t => radialProc X t ω) j := rfl
    have k2 : (fun ω => ((fun μ => gaussFam X latP μ ω), fun t => gaussFam X radPair t ω)) =
        E ∘ fun ω (j : AdmIdx ⊕ ℝ) =>
          Sum.elim (fun μ => gaussFam X latP μ ω) (fun t => gaussFam X radPair t ω) j := rfl
    rw [k1, k2, ← Measure.map_map E.measurable m1, ← Measure.map_map E.measurable m2]
    congr 1
    refine map_eq_of_forall_ae_eq m1.aemeasurable m2.aemeasurable fun j => ?_
    rcases j with μ | t
    · exact hlat μ
    · exact hrad t
  rw [hfh_eq, hh_eq, hf_eq]
  exact (indepFun_iff_map_prod_eq_prod_map_map (measurable_gaussFam_pi hX _).aemeasurable
    (measurable_gaussFam_pi hX _).aemeasurable).1 hind'

end Lat

/-! ## 2. Independence on a product space -/

theorem comap_pair_eq_generateFrom {Ω Ω' E₁ E₂ : Type*} [MeasurableSpace E₁]
    [MeasurableSpace E₂] (u : Ω → E₁) (v : Ω' → E₂) :
    MeasurableSpace.comap (fun ω : Ω × Ω' => (u ω.1, v ω.2)) inferInstance =
      MeasurableSpace.generateFrom
        {s | ∃ t ∈ image2 (· ×ˢ ·) {a : Set E₁ | MeasurableSet a} {b : Set E₂ | MeasurableSet b},
          (fun ω : Ω × Ω' => (u ω.1, v ω.2)) ⁻¹' t = s} := by
  rw [← generateFrom_prod, MeasurableSpace.comap_generateFrom]
  rfl

theorem indepFun_prod_pair {Ω Ω' E₁ E₂ F₁ F₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [MeasurableSpace E₁] [MeasurableSpace E₂] [MeasurableSpace F₁] [MeasurableSpace F₂]
    {f₁ : Ω → E₁} {g₁ : Ω → F₁} {f₂ : Ω' → E₂} {g₂ : Ω' → F₂} (hf₁ : Measurable f₁)
    (hg₁ : Measurable g₁) (hf₂ : Measurable f₂) (hg₂ : Measurable g₂)
    (h₁ : IndepFun f₁ g₁ P) (h₂ : IndepFun f₂ g₂ P') :
    IndepFun (fun ω : Ω × Ω' => (f₁ ω.1, f₂ ω.2)) (fun ω => (g₁ ω.1, g₂ ω.2)) (P.prod P') := by
  rw [IndepFun_iff_Indep]
  have hF : Measurable (fun ω : Ω × Ω' => (f₁ ω.1, f₂ ω.2)) :=
    (hf₁.comp measurable_fst).prodMk (hf₂.comp measurable_snd)
  have hG : Measurable (fun ω : Ω × Ω' => (g₁ ω.1, g₂ ω.2)) :=
    (hg₁.comp measurable_fst).prodMk (hg₂.comp measurable_snd)
  refine IndepSets.indep hF.comap_le hG.comap_le (isPiSystem_prod.comap _)
    (isPiSystem_prod.comap _) (comap_pair_eq_generateFrom f₁ f₂)
    (comap_pair_eq_generateFrom g₁ g₂) ?_
  rw [IndepSets_iff]
  rintro _ _ ⟨_, ⟨A, hA, B, hB, rfl⟩, rfl⟩ ⟨_, ⟨C, hC, D, hD, rfl⟩, rfl⟩
  have e1 : (fun ω : Ω × Ω' => (f₁ ω.1, f₂ ω.2)) ⁻¹' (A ×ˢ B) = (f₁ ⁻¹' A) ×ˢ (f₂ ⁻¹' B) := by
    ext; simp
  have e2 : (fun ω : Ω × Ω' => (g₁ ω.1, g₂ ω.2)) ⁻¹' (C ×ˢ D) = (g₁ ⁻¹' C) ×ˢ (g₂ ⁻¹' D) := by
    ext; simp
  rw [e1, e2, Set.prod_inter_prod, Measure.prod_prod, Measure.prod_prod, Measure.prod_prod,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 h₁) A C hA hC,
    (indepFun_iff_measure_inter_preimage_eq_mul.1 h₂) B D hB hD]
  ring

end F2
end QuantumZipper
