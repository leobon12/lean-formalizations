import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.LQG.CoordChangeKernel
import QuantumZipper.Proofs.NonVacuity

/-!
# WEDGE-COUPLE (1): a free field from a lateral part and an independent radial part

Theorem 1.3, node F2, step (2b), input `WedgeLogCouplingStmt` (`F2Step2b.lean`). The key missing
lemma is the converse of the radial/lateral decomposition of the free field (Sheffield,
arXiv:1012.4797, §1.6 and §5.4 pp. 70–72; Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1:
`h = h_{|·|}(0) + h†` with independent summands): the lateral part of a free field plus an
independent copy of the radial part of a free field is again a free field.

For two free fields `X₁` on `(Ω, P)` and `X₂` on `(Ω', P')` we set on `(Ω × Ω', P ⊗ P')`, for
admissible `μ` (and `0` otherwise — junk coordinates are sanitized, so that the new field is a
function of the lateral part of `X₁` and the radial part of `X₂` only):

  `coupleField X₁ X₂ ω μ = X₁ ω.1 μ − ∫ h¹_{|z|}(0) dμ + ∫ h²_{|z|}(0) dμ`

(`h_r(0) = radAvgReg`). Theorem `isFreeGFFModConstH_coupleField`: this is a free field.

Route (own argument; the sources state the decomposition, not this converse in our
formalism): by radial stochastic Fubini (`WedgeTK.ae_integral_radial`) a.s.
`∫ h_{|z|}(0) dμ = X (radSmear μ)`, so the pair differences of `coupleField` are a.s.
`(D¹_p − D¹_{p̄}) ∘ fst + D²_{p̄} ∘ snd` (`p̄` the radially smeared pair), a linear image of two
independent Gaussian processes (hence Gaussian); the covariance identity reduces to the kernel
identity `kernelCov μ (radSmear ν) = kernelCov (radSmear μ) (radSmear ν)` (the Neumann potential
of a radial measure is radial, `WedgeTK.integral_phi_radSmear`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace F2

open WedgeTK

/-! ## 1. The kernel identity -/

theorem adm_support_ballH {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∃ R₀ : ℝ, ∀ R, R₀ ≤ R → μ (CircleFubini.ballH R)ᶜ = 0 := by
  obtain ⟨-, ⟨K, hK, hKH, hμK⟩, -⟩ := hμ
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  exact ⟨R₀, fun R hR => measure_mono_null (compl_subset_compl.2 fun z hz =>
    ⟨Metric.closedBall_subset_closedBall hR (hR₀ hz), hKH hz⟩) hμK⟩

/-- `kernelCov (radSmear ν) m = ∫ kernelCov (fc(0,|w|)) m dν(w)`. -/
theorem kernelCov_radSmear_eq_integral {ν m : Measure ℂ} (hν : IsAdmissibleH ν)
    (hm : IsAdmissibleH m) :
    kernelCov neumannH (radSmear ν) m = ∫ w, kernelCov neumannH (foldedCircle 0 ‖w‖) m ∂ν := by
  have := hν.1; have := hm.1
  obtain ⟨R₁, hR₁⟩ := adm_support_ballH hν
  obtain ⟨R₂, hR₂⟩ := adm_support_ballH hm
  obtain ⟨-, -, C, hC, hbd⟩ := hm
  exact (kernelCov_radSmear ν (radSmear_support (hR₁ _ (le_max_left R₁ R₂)))
    (hR₂ _ (le_max_right R₁ R₂)) hC.ne hbd).2.symm

/-- **Kernel identity**: pairing with a radially smeared measure only sees the radial smear. -/
theorem kernelCov_radSmear_right {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) :
    kernelCov neumannH μ (radSmear ν) = kernelCov neumannH (radSmear μ) (radSmear ν) := by
  have hrμ := isAdmissibleH_radSmear hμ
  have hrν := isAdmissibleH_radSmear hν
  have hrad : ∀ {a : ℝ}, 0 < a → kernelCov neumannH (foldedCircle 0 a) μ =
      kernelCov neumannH (foldedCircle 0 a) (radSmear μ) := fun {a} ha => by
    have hfa := isAdmissibleH_foldedCircle GaussTK.zero_mem_Hbar ha
    rw [CoordChange.kernelCov_comm_of_admissible hfa hμ,
      CoordChange.kernelCov_comm_of_admissible hfa hrμ, kernelCov_fc0_right _ ha,
      kernelCov_fc0_right _ ha, integral_phi_radSmear hμ ha]
  rw [CoordChange.kernelCov_comm_of_admissible hμ hrν, kernelCov_radSmear_eq_integral hν hμ,
    CoordChange.kernelCov_comm_of_admissible hrμ hrν, kernelCov_radSmear_eq_integral hν hrμ]
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hν 0)] with w hw
  exact hrad (norm_pos_iff.2 hw)

theorem kernelCov_radSmear_left {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) :
    kernelCov neumannH (radSmear μ) ν = kernelCov neumannH (radSmear μ) (radSmear ν) := by
  have hrμ := isAdmissibleH_radSmear hμ
  have hrν := isAdmissibleH_radSmear hν
  rw [CoordChange.kernelCov_comm_of_admissible hrμ hν, kernelCov_radSmear_right hν hμ,
    CoordChange.kernelCov_comm_of_admissible hrν hrμ]

/-- The radially smeared balanced pair. -/
def rsP (p : BPair) : BPair :=
  ⟨(radSmear p.1.1, radSmear p.1.2), isAdmissibleH_radSmear p.2.1,
    isAdmissibleH_radSmear p.2.2.1, by rw [radSmear_univ, radSmear_univ]; exact p.2.2.2⟩

theorem kernelCov2_rsP_right (p q : BPair) :
    kernelCov2 neumannH p.1 (rsP q).1 = kernelCov2 neumannH (rsP p).1 (rsP q).1 := by
  simp only [kernelCov2, rsP]
  rw [kernelCov_radSmear_right p.2.1 q.2.1, kernelCov_radSmear_right p.2.1 q.2.2.1,
    kernelCov_radSmear_right p.2.2.1 q.2.1, kernelCov_radSmear_right p.2.2.1 q.2.2.1]

theorem kernelCov2_rsP_left (p q : BPair) :
    kernelCov2 neumannH (rsP p).1 q.1 = kernelCov2 neumannH (rsP p).1 (rsP q).1 := by
  simp only [kernelCov2, rsP]
  rw [kernelCov_radSmear_left p.2.1 q.2.1, kernelCov_radSmear_left p.2.1 q.2.2.1,
    kernelCov_radSmear_left p.2.2.1 q.2.1, kernelCov_radSmear_left p.2.2.1 q.2.2.1]

/-! ## 2. Independent Gaussian processes on a product space -/

section ProdGauss

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Two Gaussian processes living on the two factors of a product probability space form a
jointly Gaussian process. -/
theorem isGaussianProcess_sumElim_prod {S T : Type*} {Z₁ : S → Ω → ℝ} {Z₂ : T → Ω' → ℝ}
    (h₁ : IsGaussianProcess Z₁ P) (h₂ : IsGaussianProcess Z₂ P') :
    IsGaussianProcess (fun (i : S ⊕ T) (ω : Ω × Ω') =>
      Sum.elim (fun s => Z₁ s ω.1) (fun t => Z₂ t ω.2) i) (P.prod P') := by
  classical
  constructor
  intro I
  have g₁ := NonVacuity.nv_hasGaussianLaw (measurePreserving_fst (μ := P) (ν := P'))
    (h₁.hasGaussianLaw I.toLeft)
  have g₂ := NonVacuity.nv_hasGaussianLaw (measurePreserving_snd (μ := P) (ν := P'))
    (h₂.hasGaussianLaw I.toRight)
  have hind := NonVacuity.nv_indepFun_prod (μ := P) (ν := P')
    (fun ω => I.toLeft.restrict (Z₁ · ω)) (fun ω => I.toRight.restrict (Z₂ · ω))
  have hG := IndepFun.hasGaussianLaw g₁ g₂ hind
  let L : ((I.toLeft → ℝ) × (I.toRight → ℝ)) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi fun i => match i with
      | ⟨Sum.inl s, h⟩ => (ContinuousLinearMap.proj
          (⟨s, Finset.mem_toLeft.2 h⟩ : I.toLeft)).comp (ContinuousLinearMap.fst ℝ _ _)
      | ⟨Sum.inr t, h⟩ => (ContinuousLinearMap.proj
          (⟨t, Finset.mem_toRight.2 h⟩ : I.toRight)).comp (ContinuousLinearMap.snd ℝ _ _)
  have e : (fun ω : Ω × Ω' => I.restrict (fun i =>
      Sum.elim (fun s => Z₁ s ω.1) (fun t => Z₂ t ω.2) i)) =
      fun ω => L (I.toLeft.restrict (Z₁ · ω.1), I.toRight.restrict (Z₂ · ω.2)) := by
    funext ω; funext i
    rcases i with ⟨i | i, h⟩ <;> rfl
  rw [e]
  exact hG.map_fun L

theorem ae_fst {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂(P.prod P'), p ω.1 :=
  (measurePreserving_fst (μ := P) (ν := P')).quasiMeasurePreserving.ae h

theorem ae_snd {p : Ω' → Prop} (h : ∀ᵐ ω ∂P', p ω) : ∀ᵐ ω ∂(P.prod P'), p ω.2 :=
  (measurePreserving_snd (μ := P) (ν := P')).quasiMeasurePreserving.ae h

theorem cov_comp_fst {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    cov[fun ω : Ω × Ω' => f ω.1, fun ω => g ω.1; P.prod P'] = cov[f, g; P] := by
  have hmp := measurePreserving_fst (μ := P) (ν := P')
  rw [← hmp.map_eq] at hf hg
  conv_rhs => rw [← hmp.map_eq]
  rw [covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
    hmp.measurable.aemeasurable]
  rfl

theorem cov_comp_snd {f g : Ω' → ℝ} (hf : MemLp f 2 P') (hg : MemLp g 2 P') :
    cov[fun ω : Ω × Ω' => f ω.2, fun ω => g ω.2; P.prod P'] = cov[f, g; P'] := by
  have hmp := measurePreserving_snd (μ := P) (ν := P')
  rw [← hmp.map_eq] at hf hg
  conv_rhs => rw [← hmp.map_eq]
  rw [covariance_map hf.aestronglyMeasurable hg.aestronglyMeasurable
    hmp.measurable.aemeasurable]
  rfl

/-- Covariance of `f ∘ fst + g ∘ snd` on a product space. -/
theorem cov_fst_add_snd {f f' : Ω → ℝ} {g g' : Ω' → ℝ} (hf : MemLp f 2 P) (hf' : MemLp f' 2 P)
    (hg : MemLp g 2 P') (hg' : MemLp g' 2 P') :
    cov[fun ω : Ω × Ω' => f ω.1 + g ω.2, fun ω => f' ω.1 + g' ω.2; P.prod P'] =
      cov[f, f'; P] + cov[g, g'; P'] := by
  have a1 : MemLp (fun ω : Ω × Ω' => f ω.1) 2 (P.prod P') := hf.comp_fst P'
  have a2 : MemLp (fun ω : Ω × Ω' => g ω.2) 2 (P.prod P') := hg.comp_snd P
  have a3 : MemLp (fun ω : Ω × Ω' => f' ω.1) 2 (P.prod P') := hf'.comp_fst P'
  have a4 : MemLp (fun ω : Ω × Ω' => g' ω.2) 2 (P.prod P') := hg'.comp_snd P
  change cov[(fun ω : Ω × Ω' => f ω.1) + (fun ω => g ω.2),
    (fun ω : Ω × Ω' => f' ω.1) + (fun ω => g' ω.2); P.prod P'] = _
  have hc : cov[fun ω : Ω × Ω' => g ω.2, fun ω => f' ω.1; P.prod P'] = 0 := by
    rw [covariance_comm]; exact covariance_fst_snd_prod hf' hg
  rw [covariance_add_left a1 a2 (a3.add a4), covariance_add_right a1 a3 a4,
    covariance_add_right a2 a3 a4, covariance_fst_snd_prod hf hg', hc,
    cov_comp_fst hf hf', cov_comp_snd hg hg']
  ring

end ProdGauss

/-! ## 3. The coupled field and its freeness -/

/-- `∫ h_{|z|}(0) dμ(z)`, with `h_r(0) = radAvgReg`. -/
def radInt (x : FieldSample) (μ : Measure ℂ) : ℝ := ∫ z, radAvgReg x ‖z‖ ∂μ

theorem measurable_radInt (μ : Measure ℂ) [SFinite μ] : Measurable fun x => radInt x μ :=
  (StronglyMeasurable.integral_prod_right' (ν := μ)
    (measurable_radAvgReg₂.comp (measurable_fst.prodMk
      (measurable_norm.comp measurable_snd))).stronglyMeasurable).measurable

/-- **Lateral part of `X₁` plus the radial part of `X₂`** (sanitized off admissible measures). -/
def coupleField {Ω Ω' : Type*} (X₁ : Ω → FieldSample) (X₂ : Ω' → FieldSample) (ω : Ω × Ω') :
    FieldSample :=
  {μ : Measure ℂ | IsAdmissibleH μ}.indicator
    (fun μ => X₁ ω.1 μ - radInt (X₁ ω.1) μ + radInt (X₂ ω.2) μ)

theorem coupleField_apply {Ω Ω' : Type*} {X₁ : Ω → FieldSample} {X₂ : Ω' → FieldSample}
    (ω : Ω × Ω') {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    coupleField X₁ X₂ ω μ = X₁ ω.1 μ - radInt (X₁ ω.1) μ + radInt (X₂ ω.2) μ :=
  Set.indicator_of_mem (s := {μ : Measure ℂ | IsAdmissibleH μ}) hμ _

/-- Radial stochastic Fubini for `radInt`. -/
theorem ae_radInt_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∀ᵐ ω ∂P, Integrable (fun z => radAvgReg (X ω) ‖z‖) μ ∧ radInt (X ω) μ = X ω (radSmear μ) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  filter_upwards [hG.ae_good, ae_integral_radial hX hG hμ] with ω hg h
  have e : (fun z => radAvgReg (X ω) ‖z‖) =ᵐ[μ] fun z => G ω (0, ‖z‖) :=
    (measure_eq_zero_iff_ae_notMem.1 (noAtoms_of_isAdmissibleH hμ 0)).mono fun z hz =>
      hg.radAvgReg_eq (norm_pos_iff.2 hz)
  exact ⟨h.1.congr e.symm, (integral_congr_ae e).trans h.2⟩

section Couple

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X₁ : Ω → FieldSample} {X₂ : Ω' → FieldSample}

theorem ae_coupleField_eq (hX₁ : IsFreeGFFModConstH X₁ P) (hX₂ : IsFreeGFFModConstH X₂ P')
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) :
    ∀ᵐ ω ∂(P.prod P'), coupleField X₁ X₂ ω μ =
      X₁ ω.1 μ - X₁ ω.1 (radSmear μ) + X₂ ω.2 (radSmear μ) := by
  filter_upwards [ae_fst (P' := P') (ae_radInt_eq hX₁ hμ),
    ae_snd (P := P) (ae_radInt_eq hX₂ hμ)] with ω h1 h2
  rw [coupleField_apply ω hμ, h1.2, h2.2]

/-- The Gaussian model of the pair differences of `coupleField`. -/
def cfModel (X₁ : Ω → FieldSample) (X₂ : Ω' → FieldSample) (p : BPair) (ω : Ω × Ω') : ℝ :=
  (gaussFam X₁ id p ω.1 - gaussFam X₁ id (rsP p) ω.1) + gaussFam X₂ id (rsP p) ω.2

theorem ae_coupleField_pair (hX₁ : IsFreeGFFModConstH X₁ P) (hX₂ : IsFreeGFFModConstH X₂ P')
    (p : BPair) :
    (fun ω => coupleField X₁ X₂ ω p.1.1 - coupleField X₁ X₂ ω p.1.2) =ᵐ[P.prod P']
      cfModel X₁ X₂ p := by
  filter_upwards [ae_coupleField_eq hX₁ hX₂ p.2.1, ae_coupleField_eq hX₁ hX₂ p.2.2.1]
    with ω h1 h2
  rw [h1, h2]
  simp only [cfModel, gaussFam, rsP, id]
  ring

theorem cov_gaussFam_id {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (p q : BPair) :
    cov[gaussFam X id p, gaussFam X id q; P] = kernelCov2 neumannH p.1 q.1 :=
  hX.covariance_eq p.1 q.1 p.2.1 p.2.2.1 p.2.2.2 q.2.1 q.2.2.1 q.2.2.2

/-- **The lateral part of a free field plus the radial part of an independent free field is a
free field.** -/
theorem isFreeGFFModConstH_coupleField (hX₁ : IsFreeGFFModConstH X₁ P)
    (hX₂ : IsFreeGFFModConstH X₂ P') : IsFreeGFFModConstH (coupleField X₁ X₂) (P.prod P') where
  measurable_coord μ := by
    by_cases hμ : IsAdmissibleH μ
    · have := hμ.1
      have e : (fun ω => coupleField X₁ X₂ ω μ) =
          fun ω => X₁ ω.1 μ - radInt (X₁ ω.1) μ + radInt (X₂ ω.2) μ :=
        funext fun ω => coupleField_apply ω hμ
      rw [e]
      exact (((hX₁.measurable_coord μ).comp measurable_fst).sub
        ((measurable_radInt μ).comp ((measurable_X_pi hX₁).comp measurable_fst))).add
        ((measurable_radInt μ).comp ((measurable_X_pi hX₂).comp measurable_snd))
    · have e : (fun ω => coupleField X₁ X₂ ω μ) = fun _ => 0 :=
        funext fun ω => Set.indicator_of_notMem (s := {μ : Measure ℂ | IsAdmissibleH μ}) hμ _
      rw [e]; exact measurable_const
  gaussian := by
    classical
    have hZ := isGaussianProcess_sumElim_prod hX₁.gaussian hX₂.gaussian
    have hY : IsGaussianProcess (cfModel X₁ X₂) (P.prod P') := by
      refine hZ.of_isGaussianProcess fun p => ?_
      let I : Finset (BPair ⊕ BPair) := {Sum.inl p, Sum.inl (rsP p), Sum.inr (rsP p)}
      let a : I := ⟨Sum.inl p, by simp [I]⟩
      let b : I := ⟨Sum.inl (rsP p), by simp [I]⟩
      let c : I := ⟨Sum.inr (rsP p), by simp [I]⟩
      exact ⟨I, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) a -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) b +
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) c, fun ω => rfl⟩
    exact hY.congr fun p => (ae_coupleField_pair hX₁ hX₂ p).symm
  centered μ ν hμ hν hm := by
    set p : BPair := ⟨(μ, ν), hμ, hν, hm⟩
    have i1 := ((memLp_gaussFam hX₁ id p).comp_fst P').integrable one_le_two
    have i2 := ((memLp_gaussFam hX₁ id (rsP p)).comp_fst P').integrable one_le_two
    have i3 := ((memLp_gaussFam hX₂ id (rsP p)).comp_snd P).integrable one_le_two
    rw [integral_congr_ae (ae_coupleField_pair hX₁ hX₂ p)]
    unfold cfModel
    have i12 : Integrable (fun ω : Ω × Ω' =>
        gaussFam X₁ id p ω.1 - gaussFam X₁ id (rsP p) ω.1) (P.prod P') := i1.sub i2
    rw [integral_add i12 i3, integral_sub i1 i2,
      NonVacuity.nv_integral measurePreserving_fst (measurable_gaussFam hX₁ id p),
      NonVacuity.nv_integral measurePreserving_fst (measurable_gaussFam hX₁ id (rsP p)),
      NonVacuity.nv_integral measurePreserving_snd (measurable_gaussFam hX₂ id (rsP p)),
      integral_gaussFam hX₁, integral_gaussFam hX₁, integral_gaussFam hX₂]
    simp
  covariance_eq p q h1 h2 h3 h4 h5 h6 := by
    set p' : BPair := ⟨p, h1, h2, h3⟩
    set q' : BPair := ⟨q, h4, h5, h6⟩
    show _ = kernelCov2 neumannH p'.1 q'.1
    rw [covariance_congr_ae (ae_coupleField_pair hX₁ hX₂ p') (ae_coupleField_pair hX₁ hX₂ q')]
    have m1 := memLp_gaussFam hX₁ id p'
    have m2 := memLp_gaussFam hX₁ id (rsP p')
    have m3 := memLp_gaussFam hX₁ id q'
    have m4 := memLp_gaussFam hX₁ id (rsP q')
    refine (cov_fst_add_snd (m1.sub m2) (m3.sub m4) (memLp_gaussFam hX₂ id (rsP p'))
      (memLp_gaussFam hX₂ id (rsP q'))).trans ?_
    rw [covariance_sub_sub m1 m2 m3 m4, cov_gaussFam_id hX₁, cov_gaussFam_id hX₁,
      cov_gaussFam_id hX₁, cov_gaussFam_id hX₁, cov_gaussFam_id hX₂,
      kernelCov2_rsP_right p' q', kernelCov2_rsP_left p' q']
    ring
  linear μ ν hμ hν a b := by
    have hc := GFFExist.gffEx_admissible_comb hμ hν a b
    have lin : ∀ x : FieldSample, Integrable (fun z => radAvgReg x ‖z‖) μ →
        Integrable (fun z => radAvgReg x ‖z‖) ν →
        radInt x (a • μ + b • ν) = (a : ℝ) * radInt x μ + (b : ℝ) * radInt x ν := by
      intro x hi hj
      unfold radInt
      rw [integral_add_measure hi.smul_measure_nnreal hj.smul_measure_nnreal,
        integral_smul_nnreal_measure, integral_smul_nnreal_measure]
      simp [NNReal.smul_def]
    filter_upwards [ae_fst (P' := P') (hX₁.linear μ ν hμ hν a b),
      ae_fst (P' := P') (ae_radInt_eq hX₁ hμ), ae_fst (P' := P') (ae_radInt_eq hX₁ hν),
      ae_snd (P := P) (ae_radInt_eq hX₂ hμ), ae_snd (P := P) (ae_radInt_eq hX₂ hν)]
      with ω hl e1 e2 e3 e4
    rw [coupleField_apply ω hc, coupleField_apply ω hμ, coupleField_apply ω hν, hl,
      lin _ e1.1 e2.1, lin _ e3.1 e4.1]
    ring

end Couple

end F2
end QuantumZipper
