/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanReal
import InteractingSLE.Spec.Sec6.Aux27Germ
import InteractingSLE.Spec.Coupling.ProtectedKernel
import InteractingSLE.WangWu.ReverseContactLocal

/-!
# Aux. 61's old boundary, I: trivial σ-algebras, the germ of `∅`, trace σ-algebras

Packet PROVE-AUX61-OLDB. Measure-theoretic tools for applying the marked nested Proposition 3.8
(`Aux61MeanId.ae_tendsto_sub_of_condLaw`) in the restart chart with the empty reference set:

* **`exists_ae_eq_of_sup_trivial`**, **`condExp_sup_ae_eq_of_trivial`**: joining a `μ`-trivial σ-algebra (every set
  null or conull) does not change conditional expectations; **`isCondZeroBoundaryGFF_sup_of_trivial`**: nor a
  conditional zero-boundary GFF law;
* **`germSigma_empty_le_comap`**, **`measure_eq_zero_or_compl_of_germSigma_empty`**: the germ σ-algebra of `∅` (the
  field near `ℝ` and near `∞`) of a zero-boundary GFF is trivial (its local-set mean is `0`, so the field is independent
  of its own boundary germ);
* **`measurableSet_inter_of_sup_comap`**: if a generator `G` is constant on `S ∈ 𝒢`, the σ-algebras `𝒢` and
  `𝒢 ∨ σ(G)` have the same trace on `S`;
* **`zeroGFFTestCov_empty`**: the zero-boundary covariance of the empty domain vanishes;
* **`isZeroBoundaryGFF_of_isCondZeroBoundaryGFF_H`**: a conditional zero-boundary GFF on the fixed half-plane is a
  zero-boundary GFF (the tower step of `Sec7.PocketStopSide.isZeroBoundaryGFF_of_conditional_halfPlane`, an in-flight
  file of another worker, restated here with the same proof);
* **`ae_eq_condExp_of_isCondZeroBoundaryGFF`**: a conditional decomposition gives the conditional mean (the proof of
  `Sec6.IsLocalSetMean.ae_eq_condExp` for an arbitrary σ-algebra).

Conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped ENNReal
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec5.Aux61OldB

/-! ### Trivial σ-algebras -/

section Trivial

variable {Ω : Type*} {m 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- The σ-algebra of the sets that are `μ`-a.e. equal to a set of `m`. -/
@[instance_reducible]
def aeSigma (m : MeasurableSpace Ω) (μ : @Measure Ω mΩ) : MeasurableSpace Ω where
  MeasurableSet' s := ∃ J, MeasurableSet[m] J ∧ s =ᵐ[μ] J
  measurableSet_empty := ⟨∅, @MeasurableSet.empty Ω m, EventuallyEq.rfl⟩
  measurableSet_compl := fun _ ⟨J, hJ, hsJ⟩ => ⟨Jᶜ, hJ.compl, hsJ.compl⟩
  measurableSet_iUnion := fun _ hf => by
    choose J hJ hfJ using hf
    exact ⟨⋃ i, J i, MeasurableSet.iUnion hJ, EventuallyEqSet.countable_iUnion hfJ⟩

/-- Every set of `m ⊔ 𝒦` is `μ`-a.e. equal to a set of `m` when every set of `𝒦` is null or conull. -/
theorem exists_ae_eq_of_sup_trivial (htriv : ∀ K, MeasurableSet[𝒦] K → μ K = 0 ∨ μ Kᶜ = 0) {s : Set Ω}
    (hs : MeasurableSet[m ⊔ 𝒦] s) : ∃ J, MeasurableSet[m] J ∧ s =ᵐ[μ] J := by
  have hmC : m ≤ aeSigma m μ := fun J hJ => ⟨J, hJ, EventuallyEq.rfl⟩
  have h𝒦C : 𝒦 ≤ aeSigma m μ := by
    intro K hK
    rcases htriv K hK with h0 | h1
    · exact ⟨∅, @MeasurableSet.empty Ω m, ae_eq_empty.2 h0⟩
    · exact ⟨univ, @MeasurableSet.univ Ω m, ae_eq_univ.2 h1⟩
  exact sup_le hmC h𝒦C s hs

/-- **Joining a trivial σ-algebra does not change a conditional expectation.** -/
theorem condExp_sup_ae_eq_of_trivial [IsFiniteMeasure μ] (hm : m ≤ mΩ) (h𝒦 : 𝒦 ≤ mΩ)
    (htriv : ∀ K, MeasurableSet[𝒦] K → μ K = 0 ∨ μ Kᶜ = 0) {f : Ω → ℂ} (hf : Integrable f μ) :
    μ[f | m ⊔ 𝒦] =ᵐ[μ] μ[f | m] := by
  have hsm : StronglyMeasurable[m ⊔ 𝒦] (μ[f | m]) :=
    (stronglyMeasurable_condExp (m := m) (μ := μ) (f := f)).mono (le_sup_left : m ≤ m ⊔ 𝒦)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (sup_le hm h𝒦) hf
    (fun s _ _ => integrable_condExp.integrableOn) (fun s hs _ => ?_) hsm.aestronglyMeasurable).symm
  obtain ⟨J, hJ, hsJ⟩ := exists_ae_eq_of_sup_trivial htriv hs
  rw [setIntegral_congr_set hsJ, setIntegral_congr_set hsJ, setIntegral_condExp hm hf hJ]

/-- **A conditional zero-boundary GFF law survives joining a trivial σ-algebra.** -/
theorem isCondZeroBoundaryGFF_sup_of_trivial [IsFiniteMeasure μ] (hm : m ≤ mΩ) (h𝒦 : 𝒦 ≤ mΩ)
    (htriv : ∀ K, MeasurableSet[𝒦] K → μ K = 0 ∨ μ Kᶜ = 0) {U : Ω → Set ℂ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X) (hc : IsCondZeroBoundaryGFF μ m U X) :
    IsCondZeroBoundaryGFF μ (m ⊔ 𝒦) U X := by
  intro φ
  have hint : Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) μ := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)
    · exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((LQGMetric.measurable_distOn_apply φ).comp hX)))).aestronglyMeasurable
    · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  exact (condExp_sup_ae_eq_of_trivial hm h𝒦 htriv hint).trans (hc φ)

end Trivial

/-! ### Trace σ-algebras -/

section Trace

variable {X : Type*} {γ : Type*} [MeasurableSpace γ]

/-- The σ-algebra of the sets whose intersection with `S` is `𝒢`-measurable (for `S ∈ 𝒢`). -/
@[instance_reducible]
def traceSigma (𝒢 : MeasurableSpace X) (S : Set X) (hS : MeasurableSet[𝒢] S) : MeasurableSpace X where
  MeasurableSet' u := MeasurableSet[𝒢] (S ∩ u)
  measurableSet_empty := by simp only [inter_empty]; exact @MeasurableSet.empty X 𝒢
  measurableSet_compl := fun u hu => by
    have e : S ∩ uᶜ = S \ (S ∩ u) := by
      ext x; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]; exact hS.diff hu
  measurableSet_iUnion := fun f hf => by
    rw [inter_iUnion]; exact MeasurableSet.iUnion hf

/-- **The trace of `𝒢 ∨ σ(G)` on `S` is that of `𝒢`** when `S ∈ 𝒢` and the generator `G` is constant on `S`. -/
theorem measurableSet_inter_of_sup_comap {𝒢 : MeasurableSpace X} {S : Set X} (hS : MeasurableSet[𝒢] S)
    {G : X → γ} {c : γ} (hG : ∀ x ∈ S, G x = c) {u : Set X}
    (hu : MeasurableSet[𝒢 ⊔ MeasurableSpace.comap G inferInstance] u) : MeasurableSet[𝒢] (S ∩ u) := by
  have h1 : 𝒢 ≤ traceSigma 𝒢 S hS := fun u hu => hS.inter hu
  have h2 : MeasurableSpace.comap G inferInstance ≤ traceSigma 𝒢 S hS := by
    rintro _ ⟨E, -, rfl⟩
    by_cases hc : c ∈ E
    · have e : S ∩ G ⁻¹' E = S := inter_eq_left.2 fun x hx => by
        simp only [mem_preimage, hG x hx]; exact hc
      change MeasurableSet[𝒢] (S ∩ G ⁻¹' E)
      rw [e]; exact hS
    · have e : S ∩ G ⁻¹' E = ∅ := eq_empty_iff_forall_notMem.2 fun x hx => hc (by
        have := hx.2; simp only [mem_preimage, hG x hx.1] at this; exact this)
      change MeasurableSet[𝒢] (S ∩ G ⁻¹' E)
      rw [e]; exact @MeasurableSet.empty X 𝒢
  exact sup_le h1 h2 u hu

end Trace

/-! ### The covariance of the empty domain -/

theorem dualNormSq_empty (V : Set (ℂ → ℝ)) (ν : Measure ℂ) : QuantumZipper.dualNormSq ∅ V ν = 0 := by
  refine le_antisymm (iSup₂_le fun f hf => ?_) bot_le
  have h := hf.2
  simp only [QuantumZipper.dirichletEnergyOn, Measure.restrict_empty, integral_zero_measure, mul_zero,
    lt_self_iff_false] at h

/-- **The zero-boundary covariance of the empty domain vanishes.** -/
theorem zeroGFFTestCov_empty (φ ψ : ℂ → ℝ) : zeroGFFTestCov ∅ φ ψ = 0 := by
  simp only [QuantumZipper.zeroGFFTestCov, QuantumZipper.dualCov, dualNormSq_empty, ENNReal.toReal_zero,
    sub_zero, zero_div, add_zero]

/-! ### The germ of the empty set is trivial -/

section Germ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [IsProbabilityMeasure P] in
/-- The germ σ-algebra of `∅` is generated by pairings of the field. -/
theorem germSigma_empty_le_comap (h : Ω → DistOn upperHalfPlaneOpens) :
    LocalSets.germSigma (fun _ : Ω => (∅ : Set ℂ)) h ≤ MeasurableSpace.comap h inferInstance := by
  refine (iInf_le _ 0).trans ?_
  unfold LocalSets.germSigmaAt
  refine sup_le ?_ (MeasurableSpace.generateFrom_le ?_)
  · rw [MeasurableSpace.comap_const]; exact bot_le
  · rintro _ ⟨φ, B, hB, rfl⟩
    by_cases hP : tsupport φ ⊆ LocalSets.germNbhd (1 / (((0 : ℕ) : ℝ) + 1)) (∅ : Set ℂ)
    · have e : {ω : Ω | tsupport φ ⊆ LocalSets.germNbhd (1 / (((0 : ℕ) : ℝ) + 1)) ((fun _ : Ω => (∅ : Set ℂ)) ω)} ∩
          (fun ω => h ω φ) ⁻¹' B = h ⁻¹' {T : DistOn upperHalfPlaneOpens | T φ ∈ B} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hP, true_and]
      rw [e]; exact ⟨_, LQGMetric.measurable_distOn_apply φ hB, rfl⟩
    · have e : {ω : Ω | tsupport φ ⊆ LocalSets.germNbhd (1 / (((0 : ℕ) : ℝ) + 1)) ((fun _ : Ω => (∅ : Set ℂ)) ω)} ∩
          (fun ω => h ω φ) ⁻¹' B = ∅ := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, hP, false_and, mem_empty_iff_false]
      rw [e]; exact @MeasurableSet.empty Ω (MeasurableSpace.comap h inferInstance)

/-- **The germ σ-algebra of `∅` of a zero-boundary GFF is trivial.** Its local-set mean vanishes
(`Sec7.IsLocalSetMean.ae_apply_eq_zero_of_empty`), so given the germ the field has its unconditional law; for a germ
event `K = h⁻¹(E)` the restricted law `P(K ∩ h⁻¹ ·)` is `P(K) P(h⁻¹ ·)` (characteristic functionals), so
`P(K) = P(K)²`. -/
theorem measure_eq_zero_or_compl_of_germSigma_empty (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {K : Set Ω}
    (hK : MeasurableSet[LocalSets.germSigma (fun _ : Ω => (∅ : Set ℂ)) h] K) : P K = 0 ∨ P Kᶜ = 0 := by
  have hhm := hh.measurable
  have h𝒦 : LocalSets.germSigma (fun _ : Ω => (∅ : Set ℂ)) h ≤ mΩ :=
    LocalSets.germSigma_le measurable_const hhm
  have hKm : MeasurableSet K := h𝒦 K hK
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh measurable_const (WangWu.isLocalSet_empty hh)
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => cexp (I * (h ω φ : ℂ))) P := fun φ =>
    Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply φ).comp hhm)))).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by rw [mul_comm, Complex.norm_exp_ofReal_mul_I])
  have hc : ∀ φ : TestOn upperHalfPlaneOpens,
      P[fun ω => cexp (I * (h ω φ : ℂ)) | LocalSets.germSigma (fun _ : Ω => (∅ : Set ℂ)) h] =ᵐ[P]
        fun _ => ((Real.exp (-(1 / 2) * zeroGFFTestCov H φ φ) : ℝ) : ℂ) := by
    intro φ
    have h0 := Sec7.IsLocalSetMean.ae_apply_eq_zero_of_empty hh hg φ
    have hcong : (fun ω => cexp (I * ((h ω - g ω) φ : ℂ))) =ᵐ[P] fun ω => cexp (I * (h ω φ : ℂ)) := by
      filter_upwards [h0] with ω hω
      simp only [sub_apply, hω, sub_zero]
    refine (condExp_congr_ae hcong.symm).trans ((hg.2.2 φ).trans (Eventually.of_forall fun ω => ?_))
    simp only [sdiff_empty]
  -- the restricted law of the field on `K`
  have hfin : IsFiniteMeasure (P K • P.map h) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top (measure_lt_top P K) (measure_lt_top _ _)⟩
  have hlaw : (P.restrict K).map h = P K • P.map h := by
    refine Coupling.ext_of_integral_cexp fun ψ => ?_
    rw [integral_map hhm.aemeasurable
        (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable,
      integral_smul_measure, integral_map hhm.aemeasurable
        (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).aestronglyMeasurable,
      ← setIntegral_condExp h𝒦 (hint ψ) hK, setIntegral_congr_ae hKm ((hc ψ).mono fun ω hω _ => hω),
      setIntegral_const, ← integral_condExp h𝒦, integral_congr_ae (hc ψ), integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  obtain ⟨E, hE, rfl⟩ := germSigma_empty_le_comap h K hK
  have hval := congrArg (fun ν : Measure (DistOn upperHalfPlaneOpens) => ν E) hlaw
  simp only [Measure.map_apply hhm hE, Measure.restrict_apply (hhm hE), inter_self, Measure.smul_apply,
    smul_eq_mul] at hval
  by_cases h0 : P (h ⁻¹' E) = 0
  · exact Or.inl h0
  · right
    have h1 : P (h ⁻¹' E) = 1 := by
      have := (ENNReal.mul_right_inj h0 (measure_ne_top P _)).1 (hval.symm.trans (mul_one _).symm)
      exact this
    rw [prob_compl_eq_one_sub (hhm hE), h1, tsub_self]

end Germ

/-! ### The tower step and the conditional mean -/

section Tower

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A conditional zero-boundary GFF on the fixed half-plane is a zero-boundary GFF** (the proof of
`Sec7.PocketStopSide.isZeroBoundaryGFF_of_conditional_halfPlane`). -/
theorem isZeroBoundaryGFF_of_isCondZeroBoundaryGFF_H (hℋ : ℋ ≤ mΩ) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hLaw : IsCondZeroBoundaryGFF P ℋ (fun _ => H) X) :
    IsZeroBoundaryGFF upperHalfPlaneOpens X P := by
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  have hMap : P.map X = Coupling.zbLaw upperHalfPlaneOpens := by
    refine Coupling.ext_of_integral_cexp fun φ => ?_
    rw [integral_map hX.aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable]
    calc
      (∫ ω, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂P) =
          ∫ ω, P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | ℋ] ω ∂P :=
        (integral_condExp hℋ).symm
      _ = ((Real.exp (-(1 / 2) * zeroGFFTestCov H φ φ) : ℝ) : ℂ) := by
        rw [integral_congr_ae (hLaw φ), integral_const, probReal_univ, one_smul]
      _ = ∫ g, Complex.exp (Complex.I * (g φ : ℂ)) ∂Coupling.zbLaw upperHalfPlaneOpens :=
        (LocalSets.integral_exp_field hZ φ).symm
  exact WangWu.isZeroBoundaryGFF_comp_of_map_eq (g := id) (f := X) hX hMap hZ

/-- **A conditional decomposition gives the conditional mean** (the proof of `Sec6.IsLocalSetMean.ae_eq_condExp`
for an arbitrary σ-algebra and random domain): if `h − g` is a conditional zero-boundary GFF on `U` given `𝒢` with
`g` `𝒢`-measurable and `U ⊆ ℍ` open, then `g(φ) = E[h(φ) | 𝒢]` for every integrable pairing `h(φ)`. -/
theorem ae_eq_condExp_of_isCondZeroBoundaryGFF (hℋ : ℋ ≤ mΩ) {U : Ω → Set ℂ}
    (hU : ∀ᵐ ω ∂P, IsOpen (U ω) ∧ U ω ⊆ H) {h g : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (hgm : Measurable[ℋ] g) (hc : IsCondZeroBoundaryGFF P ℋ U fun ω => h ω - g ω)
    (φ : TestOn upperHalfPlaneOpens) (hφi : Integrable (fun ω => h ω φ) P) :
    (fun ω => g ω φ) =ᵐ[P] P[fun ω => h ω φ | ℋ] := by
  have hgφ : Measurable[ℋ] fun ω => g ω φ := (LQGMetric.measurable_distOn_apply φ).comp hgm
  set Y : Ω → ℝ := fun ω => h ω φ - g ω φ with hYdef
  have hYm : Measurable Y := ((LQGMetric.measurable_distOn_apply φ).comp hhm).sub (hgφ.mono hℋ le_rfl)
  have hct : ∀ t : ℝ, P[fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) | ℋ] =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * (t ^ 2 * zeroGFFTestCov (U ω) φ φ)) : ℝ) : ℂ) := by
    intro t
    have hc' := hc (t • φ)
    have e1 : (fun ω => cexp (I * (((h ω - g ω) (t • φ) : ℝ) : ℂ))) =
        fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) := by
      funext ω
      congr 3
      simp only [hYdef, sub_apply, map_smul, smul_eq_mul, mul_sub]
    rw [e1] at hc'
    filter_upwards [hc', hU] with ω hω hUo
    rw [hω, LocalSets.zeroGFFTestCov_smul_self hUo.1 hUo.2 t φ]
  have hV : ∀ᵐ ω ∂P, 0 ≤ zeroGFFTestCov (U ω) φ φ ∧ zeroGFFTestCov (U ω) φ φ ≤ zeroGFFTestCov H φ φ := by
    filter_upwards [hU] with ω hUo
    exact ⟨LocalSets.zeroGFFTestCov_self_nonneg hUo.1 hUo.2 φ,
      LocalSets.zeroGFFTestCov_mono hUo.1 QuantumZipper.isOpen_H hUo.2 subset_rfl φ⟩
  obtain ⟨hYi, hY0⟩ := Sec6.condExp_eq_zero_of_condCharFun hℋ hYm hV hct
  have hgi : Integrable (fun ω => g ω φ) P :=
    (hφi.sub hYi).congr (Eventually.of_forall fun ω => by simp [hYdef])
  have hsplit : (fun ω => h ω φ) = fun ω => g ω φ + Y ω := by
    funext ω; simp [hYdef]
  rw [hsplit]
  have hadd := condExp_add (m := ℋ) hgi hYi
  filter_upwards [hadd, hY0] with ω h1 h2
  change g ω φ = (P[(fun ω => g ω φ) + Y | ℋ]) ω
  rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable hℋ hgφ.stronglyMeasurable hgi]
  simp

end Tower

end InteractingSLE.Sec5.Aux61OldB
