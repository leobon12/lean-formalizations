import QuantumZipper.Proofs.GFF.K3.MixedM7AsmXi
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmFree
import QuantumZipper.Proofs.Section5.Prop16DomCoupleFubini

/-!
# K3-mixed M7 (proved): the half-disc coupling `MixedFreeCouplingHalfDiscStmt`

`mixedFreeCouplingHalfDisc_holds D c d t r r' ρ₀ : MixedFreeCouplingHalfDiscStmt D c d t r r' ρ₀`.

Construction (the realization of `exists_mixedFree_markovCoupling`, `MixedM7Couple.lean`, with
M7-a `mixedHalfDiscMarkovCov_holds`): one Gaussian process `Z` realizes the mixed field `Y`, the
free field `X` and the family `Ξ` indexed by the vectors orthogonal to the mixed local part, with
`Ξ ⊥ X` and, for local `μ`, `Y μ = X μ − X(bal μ) + Ξ(v_{bal μ})` a.s. (`real_local` with
`ρ = bal μ`). The correction is

  `g ω = G_Ξ ω − h ω − (X ω (P_t) − X ω ρ₀)`,

where `G_Ξ` is the harmonic version (M7-b, `poissonHarmonicVersion_holds`) of
`z ↦ Ξ(v_{P_z})` (weakly harmonic curve, `harmonicOnNhd_inner_mixCurve`), measurable for
`σ(Ξ)`, and `h` is the free harmonic part (`exists_freeHarmonicPart`), measurable for the outside
σ-algebra, with `X μ − X(bal μ) = X μ − ∫ h dμ − μ(ℂ) X(P_t)` a.s. Stochastic Fubini for the
isonormal family `Ξ` on `xiSub` (`Prop16Asm.gaussFubini_core`) and the weak Bochner identity
`v_{bal μ} = ∫ v_{P_z} dμ(z)` give `Ξ(v_{bal μ}) = ∫ G_Ξ dμ` a.s.

Sources: Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm 2.17 (domain
Markov property); Werner–Powell, arXiv:2004.04720, Prop. 4.3 (harmonic version). The half-disc
mixed form and the product realization are own arguments (see `MixedM7Nodes.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory Function
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

open GFFExist LQGDimension.ExistAsm

theorem continuousOn_of_harmonic_foldH {f : ℂ → ℝ} {t r : ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd (fun z => f (foldH z)) (closedBall (t : ℂ) r)) :
    ContinuousOn f (closedBall (t : ℂ) r ∩ Hbar) := by
  have h := hf.continuousOn.mono (inter_subset_left (t := Hbar))
  refine h.congr fun x hx => ?_
  simp only [CircleFubini.foldH_of_mem' hx.2]

theorem integrable_of_continuousOn_closedBall_Hbar {μ : Measure ℂ} [IsFiniteMeasure μ]
    {f : ℂ → ℝ} {t r : ℝ} (hf : ContinuousOn f (closedBall (t : ℂ) r ∩ Hbar))
    (hμ : μ (closedBall (t : ℂ) r ∩ Hbar)ᶜ = 0) : Integrable f μ := by
  have hKc : IsCompact (closedBall (t : ℂ) r ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hIK : IntegrableOn f (closedBall (t : ℂ) r ∩ Hbar) μ := hf.integrableOn_compact hKc
  have hres : μ.restrict (closedBall (t : ℂ) r ∩ Hbar) = μ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hμ)
  rwa [IntegrableOn, hres] at hIK

/-- **M7 holds** (half-disc form, decision D22). -/
theorem mixedFreeCouplingHalfDisc_holds (D : Set ℂ) (c d t r r' : ℝ) (ρ₀ : Measure ℂ) :
    MixedFreeCouplingHalfDiscStmt D c d t r r' ρ₀ := by
  intro hgeom ht hr' hr'r hsub hρ₀ hρ₀1 hρ₀B
  have hr : 0 < r := hr'.trans hr'r
  set ρ : ℝ := (r' + r) / 2 with hρdef
  have hr'ρ : r' < ρ := by linarith
  have hρr : ρ < r := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hA := mixedHalfDiscMarkovCov_holds D c d t r r'
  have hAρ := (mixedHalfDiscMarkovCov_holds D c d t r ρ hgeom ht hρ0 hρr hsub).1
  obtain ⟨J, hJ1, hJ2⟩ := exists_localIsometry hA hgeom ht hr' hr'r hsub
  obtain ⟨Z, hZm, hZ⟩ := gs_process_hilbert (CIdx D c d t r r') (cVec hr hr'r J)
  set Ξ : (ℕ → ℝ) → (XiIdx D c d t r r' → ℝ) := fun ω u => Z (Sum.inr (Sum.inr u)) ω with hΞ
  have hΞm : Measurable Ξ := Measurable.of_eval fun u => hZm _
  have hY := realY_isMixedGFF hZm hZ
  have hX := realX_isFree hZm hZ
  have hind := real_indep hZm hZ hJ2
  -- the isonormal family on `xiSub`
  set W : xiSub D c d t r r' → (ℕ → ℝ) → ℝ := fun k =>
    Z (Sum.inr (Sum.inr ⟨k.1, mem_xiSub_iff.1 k.2⟩)) with hWdef
  have hWm : ∀ k, Measurable (W k) := fun k => hZm _
  have hW : ∀ {ι : Type} [Fintype ι] (τ : ι → xiSub D c d t r r') (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * W (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP := by
    intro ι _ τ a
    have h := hZ (fun i => Sum.inr (Sum.inr ⟨(τ i).1, mem_xiSub_iff.1 (τ i).2⟩)) a
    have hn : ‖∑ i, a i • cVec hr hr'r J (Sum.inr (Sum.inr ⟨(τ i).1, mem_xiSub_iff.1 (τ i).2⟩))‖
        = ‖∑ i, a i • τ i‖ := by
      have e : ∀ i, cVec hr hr'r J (Sum.inr (Sum.inr ⟨(τ i).1, mem_xiSub_iff.1 (τ i).2⟩)) =
          xiEmb D (τ i).1 := fun i => rfl
      simp only [e, ← map_smul, ← map_sum, LinearIsometry.norm_map]
      have e2 : ((∑ i, a i • τ i : xiSub D c d t r r') : GradSpace D) =
          ∑ i, a i • ((τ i : xiSub D c d t r r') : GradSpace D) := by
        rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      rw [← e2]; rfl
    rw [hn] at h
    exact h
  -- the mixed curve lies in `xiSub`
  have hretrK : ∀ z, retr t ρ z ∈ closedBall (t : ℂ) ρ ∩ Hbar := fun z =>
    ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ0 z), retr_mem_Hbar hρ0 z⟩
  have horth : ∀ z, mixCurve D c d t r ρ z ∈ xiSub D c d t r r' := fun z =>
    mem_xiSub_iff.2 fun ν => inner_rieszVec_mixedLocVec_eq_zero hA hgeom ht hr' hr'r hsub
      (hAρ _ (hretrK z)) (halfDiscPoisson_ball hr _) ν
  set F : ℂ → (ℕ → ℝ) → ℝ := fun z => W ⟨mixCurve D c d t r ρ z, horth z⟩ with hFdef
  have hFlaw : ∀ {ι : Type} [Fintype ι] (τ : ι → ℂ) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * F (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • mixCurve D c d t r ρ (τ i)‖ ^ 2).toNNReal) stdP := by
    intro ι _ τ a
    have h := hW (fun i => ⟨mixCurve D c d t r ρ (τ i), horth (τ i)⟩) a
    have hn : ‖∑ i, a i • (⟨mixCurve D c d t r ρ (τ i), horth (τ i)⟩ : xiSub D c d t r r')‖ =
        ‖∑ i, a i • mixCurve D c d t r ρ (τ i)‖ := by
      have e2 : ((∑ i, a i • (⟨mixCurve D c d t r ρ (τ i), horth (τ i)⟩ :
          xiSub D c d t r r') : xiSub D c d t r r') : GradSpace D) =
          ∑ i, a i • mixCurve D c d t r ρ (τ i) := by
        rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      rw [← e2]; rfl
    rw [hn] at h
    exact h
  obtain ⟨Gx, hGxh, hGxae, hGxm⟩ := poissonHarmonicVersion_holds t ρ r' hr' hr'ρ stdP
    (mixCurve D c d t r ρ) F (harmonicOnNhd_inner_mixCurve hgeom ht hρ0 hρr hsub)
    (fun z => hZm _) hFlaw
  -- the free harmonic part
  obtain ⟨hf, hfh, hfm, hfid⟩ := exists_freeHarmonicPart hX (t := t) hr' hr'r
  have htb : (t : ℂ) ∈ ball (t : ℂ) r := mem_ball_self hr
  have hPt : IsAdmissibleH (halfDiscPoisson t r (t : ℂ)) :=
    isAdmissibleH_halfDiscPoisson hr hr'r (by simp; exact hr'.le)
  have := isProbabilityMeasure_halfDiscPoisson hr htb
  set X := realX Z with hXdef
  set g : (ℕ → ℝ) → ℂ → ℝ := fun ω z =>
    Gx ω z - hf ω z - (X ω (halfDiscPoisson t r (t : ℂ)) - X ω ρ₀) with hgdef
  refine ⟨ℕ → ℝ, inferInstance, stdP, realY Z, X, g, XiIdx D c d t r r' → ℝ, inferInstance, Ξ,
    inferInstance, hY, hX, hΞm, hind, fun ω => ?_, fun z => ?_, fun μ hμ hμr => ?_⟩
  · exact ((hGxh ω).sub (hfh ω)).sub (InnerProductSpace.harmonicOnNhd_const _)
  · have h1 : Measurable[MeasurableSpace.comap Ξ inferInstance] fun ω => Gx ω z := by
      refine hGxm _ (fun w _ => ?_) z
      exact (measurable_pi_apply _).comp (comap_measurable Ξ)
    have h3 : Measurable[outsideSigma X t r] fun ω =>
        X ω (halfDiscPoisson t r (t : ℂ)) - X ω ρ₀ :=
      measurable_outsideSigma hPt hρ₀ (by rw [measure_univ, hρ₀1]) (halfDiscPoisson_ball hr _)
        hρ₀B
    exact ((h1.mono le_sup_left le_rfl).sub ((hfm z).mono le_sup_right le_rfl)).sub
      (h3.mono le_sup_right le_rfl)
  · -- the identity
    have hfin : IsFiniteMeasure μ := hμ.1
    have hμK : μ (closedBall (t : ℂ) r' ∩ Hbar)ᶜ = 0 := by
      rw [compl_inter]
      exact measure_union_null hμr (mem_ae_iff.1 (ae_mem_Hbar_of_admissible hμ))
    obtain ⟨hμA, hbA, -, -⟩ := (hA hgeom ht hr' hr'r hsub).2 μ hμ hμr
    set u : XiIdx D c d t r r' := ⟨_, fun ν => inner_rieszVec_mixedLocVec_eq_zero hA hgeom ht hr'
      hr'r hsub hbA (bal_ball hr) ν⟩ with hu
    have hloc := real_local hZ hJ1 ⟨μ, hμ, hμr⟩ hμA (isAdmissibleH_bal hr hr'r hμr) (bal_ball hr)
      (bal_univ hr hr'r hμr).symm u rfl
    have hfree := hfid μ hμ hμr
    -- stochastic Fubini for `Ξ`
    obtain ⟨L, B, -, hB0, -, hB⟩ := exists_lip_mixCurve hgeom ht hρ0 hρr hsub
    have hcont := continuous_mixCurve hgeom ht hρ0 hρr hsub
    have hr'0 : 0 < r' := hr'
    have hretr' : ∀ i, retr t r' i ∈ closedBall (t : ℂ) r' ∩ Hbar := fun i =>
      ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hr'0 i), retr_mem_Hbar hr'0 i⟩
    set hv : ℂ → xiSub D c d t r r' := fun i =>
      ⟨mixCurve D c d t r ρ (retr t r' i), horth _⟩ with hhv
    have hvc : Continuous fun i => mixCurve D c d t r ρ (retr t r' i) :=
      hcont.comp (continuous_retr_m7b t hr'0)
    set G' : (ℕ → ℝ) → ℂ → ℝ := fun ω i => Gx ω (retr t r' i) with hG'
    have hG'c : ∀ ω, Continuous (G' ω) := fun ω =>
      (continuousOn_of_harmonic_foldH (hGxh ω)).comp_continuous (continuous_retr_m7b t hr'0)
        hretr'
    have hG'm : Measurable (uncurry G') := by
      have hm : Measurable (uncurry fun (i : ℂ) (ω : ℕ → ℝ) => G' ω i) :=
        measurable_uncurry_of_continuous_of_measurable (fun ω => hG'c ω)
          fun i => hGxm _ (fun w _ => hZm _) _
      exact hm.comp measurable_swap
    have hG'v : ∀ i, (fun ω => G' ω i) =ᵐ[stdP] W (hv i) := fun i =>
      hGxae _ (hretr' i)
    set k : xiSub D c d t r r' := ⟨u.1, mem_xiSub_iff.2 u.2⟩ with hk
    have hkid : ∀ x : xiSub D c d t r r', ⟪k, x⟫ = ∫ i, ⟪hv i, x⟫ ∂μ := by
      intro x
      have hμKρ : μ (closedBall (t : ℂ) ρ ∩ Hbar)ᶜ = 0 :=
        measure_mono_null (compl_subset_compl.2 (inter_subset_inter_left _
          (closedBall_subset_closedBall hr'ρ.le))) hμK
      have h1 := inner_rieszVec_bind_eq_integral_mixCurve hgeom ht hρ0 hρr hsub hμKρ hbA x.1
      rw [Submodule.coe_inner, hk]
      simp only [hu]
      rw [show bal t r μ = μ.bind (halfDiscPoisson t r) from rfl, h1]
      refine integral_congr_ae ?_
      filter_upwards [mem_ae_iff.2 hμK] with i hi
      rw [Submodule.coe_inner, hhv]
      simp only [retr_eq_self hi.2 (mem_closedBall_iff_norm.1 hi.1)]
    have hFub := Prop16Asm.gaussFubini_core hW μ hv (M := B) (fun i => hB _)
      (by
        simp only [Submodule.coe_inner, hhv]
        exact ((hvc.comp continuous_fst).inner (hvc.comp continuous_snd)).measurable)
      (fun x => by
        simp only [Submodule.coe_inner, hhv]
        exact (hvc.inner continuous_const).measurable)
      G' hG'm hG'v hWm k hkid
    filter_upwards [hloc, hfree, hFub] with ω h1 h2 h3
    have hint1 : Integrable (Gx ω) μ :=
      integrable_of_continuousOn_closedBall_Hbar (continuousOn_of_harmonic_foldH (hGxh ω)) hμK
    have hint2 : Integrable (hf ω) μ :=
      integrable_of_continuousOn_closedBall_Hbar (continuousOn_of_harmonic_foldH (hfh ω)) hμK
    have hGG : ∫ i, G' ω i ∂μ = ∫ i, Gx ω i ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [mem_ae_iff.2 hμK] with i hi
      simp only [hG', retr_eq_self hi.2 (mem_closedBall_iff_norm.1 hi.1)]
    have hWk : W k ω = Z (Sum.inr (Sum.inr u)) ω := rfl
    rw [hGG, hWk] at h3
    have hgint : ∫ z, g ω z ∂μ = ∫ z, Gx ω z ∂μ - ∫ z, hf ω z ∂μ -
        (μ Set.univ).toReal * (X ω (halfDiscPoisson t r (t : ℂ)) - X ω ρ₀) := by
      have e1 := integral_sub (hint1.sub hint2)
        (integrable_const (X ω (halfDiscPoisson t r (t : ℂ)) - X ω ρ₀) (μ := μ))
      have e2 := integral_sub hint1 hint2
      simp only [Pi.sub_apply] at e1 e2
      simp only [hgdef]
      rw [e1, e2, integral_const, smul_eq_mul, measureReal_def]
    rw [hgint]
    simp only [markovZ] at h2
    simp only [hXdef] at h2 ⊢
    linarith

end QuantumZipper.K3
