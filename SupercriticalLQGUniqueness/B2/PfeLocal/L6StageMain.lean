import SupercriticalLQGUniqueness.B2.PfeLocal.L6Stage

 











set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric LQGMetric.DFGPS LQGMetric.DFGPS.L217 LQGMetric.GM.Bilip PfeWeyl

instance l6BU_scT (R : ℝ) : SecondCountableTopology (L6T2 × C(L6K R, ℝ)) := inferInstance
instance l6BU_borel (R : ℝ) : BorelSpace (L6T2 × C(L6K R, ℝ)) := Prod.borelSpace

section SigmaAlgebras

set_option warn.classDefReducibility false

variable (S : L6Geo)

 
def l6σG : MeasurableSpace (L6Lam S.R × L6Y) :=
  MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.1) (l6G S)
 
def l6σA : MeasurableSpace (L6Lam S.R × L6Y) :=
  MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.2.1) (inferInstance : MeasurableSpace L6T1)
 
def l6σH (g₀ : L6S → DistC) : MeasurableSpace (L6Lam S.R × L6Y) :=
  MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.1) (l6H S g₀) ⊔
    MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.2.2) (inferInstance : MeasurableSpace L6T2)
 
def l6ΛG : MeasurableSpace (L6Lam S.R) :=
  MeasurableSpace.comap (fun l : L6Lam S.R => l.1) (l6G S)
 
def l6ΛA : MeasurableSpace (L6Lam S.R) :=
  ⨆ (d : L5Code) (_ : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)),
    MeasurableSpace.comap (fun l : L6Lam S.R => l.2.2.1 d) (inferInstance : MeasurableSpace ℝ≥0∞)
 
def l6ΛB : MeasurableSpace (L6Lam S.R) :=
  MeasurableSpace.comap (fun l : L6Lam S.R => l.1) (MeasurableSpace.pi : MeasurableSpace L6S) ⊔
    ⨆ (d : L5Code) (_ : l5Rect d.1 ⊆ (S.U₁ : Set ℂ)),
      MeasurableSpace.comap (fun l : L6Lam S.R => l.2.1 d) (inferInstance : MeasurableSpace ℝ≥0∞)

end SigmaAlgebras

 
theorem l6_stage {ξ : ℝ} (hξ : 0 ≤ ξ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)} (hVm : ∀ δ, Measurable (V δ))
    {μ : Measure DistC} [IsProbabilityMeasure μ] (hμ : IsNormalizedWPGFF id μ)
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂μ, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {h' : Ω' → DistC} (hh'm : Measurable h') (hh'law : P'.map h' = μ)
    {hN : ℕ → Ω' → DistC} (hNm : ∀ n, Measurable (hN n)) (hNlaw : ∀ n, P'.map (hN n) = μ)
    (hpair : ∀ φ : TestC, ∀ᵐ ω ∂P', Tendsto (fun n => hN n ω φ) atTop (𝓝 (h' ω φ)))
    {L : Ω' → LSCMetric} (hL : Measurable L)
    (hconv : ∀ᵐ ω ∂P', Tendsto (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω)))
      atTop (𝓝 (L ω)))
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P', SmallAnnulusCosts
      (fun n => normalizedLFPPMetric ξ (m (e n)) (V (e n) (hN n ω))) (L ω) (closedBall 0 k)
      (ball 0 ((k : ℝ) + 1)))
    (S : L6Geo) :
    CondIndepEv (MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) (l6G S))
      (⨆ (d : L5Code) (_ : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)), MeasurableSpace.comap
        (fun ω => ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) * l5Obs (L ω) d) inferInstance)
      (MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) MeasurableSpace.pi ⊔
        l5ObsSigma L (S.U₁ : Set ℂ)) P' := by
  obtain ⟨g₀, hg₀, hind, -, hNdec⟩ := l6_canonical hμ ξ m e S
  obtain ⟨ψ, -, μs, ρ, hμs, hlim, hmarg, hindρ, hgoodρ⟩ := l6_stage_rel hξ m e he hVm hμ hV hh'm
    hh'law hNm hNlaw hpair hL hconv hsmall S hg₀ hind
  have hΛ := measurable_l6Λ S ξ hg₀ hh'm hL
  set ρm : Measure (L6Lam S.R × L6Y) := (ρ : Measure (L6Lam S.R × L6Y)) with hρm
  
  have mx : Measurable fun p : L6Lam S.R × L6Y => p.2.1 := measurable_fst.comp measurable_snd
  have ma : Measurable fun p : L6Lam S.R × L6Y => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have mb : Measurable fun p : L6Lam S.R × L6Y => p.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have my : Measurable fun p : L6Lam S.R × L6Y => p.1.1 := measurable_fst.comp measurable_fst
  have mo : ∀ d : L5Code, Measurable fun p : L6Lam S.R × L6Y => p.1.2.1 d := fun d =>
    (measurable_pi_apply d).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have mor : ∀ d : L5Code, Measurable fun p : L6Lam S.R × L6Y => p.1.2.2.1 d := fun d =>
    (measurable_pi_apply d).comp (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_fst)))
  have mu : Measurable fun p : L6Lam S.R × L6Y => p.1.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  
  have hGLU : ∀ᵐ l ∂(P'.map (l6Λ S ξ g₀ h' L)), l6GoodL l ∧ l.2.2.2 = S.u g₀ (pairJInv ⊤ l.1) := by
    refine (ae_map_iff hΛ.aemeasurable ((measurableSet_l6GoodL S.R).inter
      (measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp measurable_snd))
        ((S.measurable_u hg₀).comp ((measurable_pairJInv ⊤).comp measurable_fst))))).2
      (Eventually.of_forall fun ω => ⟨l6GoodL_Λ S ξ g₀ h' L ω,
        (congrArg (S.u g₀) (pairJInv_pairJ ⊤ (h' ω))).symm⟩)
  have hρL : ∀ᵐ p ∂ρm, l6GoodL p.1 ∧ p.1.2.2.2 = S.u g₀ (pairJInv ⊤ p.1.1) := by
    rw [← hmarg] at hGLU; exact ae_of_ae_map measurable_fst.aemeasurable hGLU
  have hall := hgoodρ.and hρL
  obtain ⟨M, hMsup, hMm, hM0⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  have hLg : MeasurableSet Mᶜ := hMm.compl
  have hLg0 : ρm (Mᶜ)ᶜ = 0 := by rw [compl_compl]; exact hM0
  have hgood : ∀ p ∈ Mᶜ, (l6GoodA S p ∧ l6GoodB S ξ p ∧ p.2.1 = p.1.1) ∧
      (l6GoodL p.1 ∧ p.1.2.2.2 = S.u g₀ (pairJInv ⊤ p.1.1)) := fun p hp => by
    by_contra hn; exact hp (hMsup hn)
  
  have hFA : ∀ d : L5Code, l5Rect d.1 ⊆ (S.V₁ : Set ℂ) →
      MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.1.2.2.1 d) inferInstance ≤
        aeClosure ρm (MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.2.1) inferInstance) :=
    fun d hd => comap_le_aeClosure_of_fiber (mor d) ma hLg hLg0 fun p hp p' hp' he =>
      le_antisymm (l6_fibA S (hgood p hp).1.1 (hgood p hp).2.1 (hgood p' hp').1.1
        (hgood p' hp').2.1 he hd)
        (l6_fibA S (hgood p' hp').1.1 (hgood p' hp').2.1 (hgood p hp).1.1 (hgood p hp).2.1
          he.symm hd)
  have hFB : ∀ d : L5Code, l5Rect d.1 ⊆ (S.U₁ : Set ℂ) →
      MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.1.2.1 d) inferInstance ≤
        aeClosure ρm (MeasurableSpace.comap
          (fun p : L6Lam S.R × L6Y => (p.2.2.2, p.1.2.2.2)) inferInstance) :=
    fun d hd => comap_le_aeClosure_of_fiber (mo d) (mb.prodMk mu) hLg hLg0 fun p hp p' hp' he => by
      have hb : p.2.2.2 = p'.2.2.2 := (Prod.ext_iff.1 he).1
      have hu : p.1.2.2.2 = p'.1.2.2.2 := (Prod.ext_iff.1 he).2
      exact le_antisymm (l6_fibB S (hgood p hp).1.2.1 (hgood p hp).2.1 (hgood p' hp').1.2.1
        (hgood p' hp').2.1 hb hu hd)
        (l6_fibB S (hgood p' hp').1.2.1 (hgood p' hp').2.1 (hgood p hp).1.2.1 (hgood p hp).2.1
          hb.symm hu.symm hd)
  
  have hxy : (fun p : L6Lam S.R × L6Y => p.2.1) =ᵐ[ρm] fun p => p.1.1 :=
    hgoodρ.mono fun p hp => hp.2.2
  have hlawx : ρm.map (fun p : L6Lam S.R × L6Y => p.2.1) = μ.map (pairJ ⊤) := by
    rw [Measure.map_congr hxy]
    have e1 : (fun p : L6Lam S.R × L6Y => p.1.1) = (fun l : L6Lam S.R => l.1) ∘ Prod.fst := rfl
    rw [e1, ← Measure.map_map measurable_fst measurable_fst, hmarg,
      Measure.map_map measurable_fst hΛ, ← hh'law, Measure.map_map (measurable_pairJ ⊤) hh'm]
    rfl
  have hNm : Measurable (normField (pairJInv ⊤) S.z S.r) :=
    isGFFPlusBddCont_normField_pairJInv_measurable S
  have hraw := l6_raw_recovery hμ S
  rw [← hlawx] at hraw
  have hxσ := l6_comap_le_aeClosure_comap mx
    ⟨MeasurableSpace.comap (normField (pairJInv ⊤) S.z S.r) inferInstance, hNm.comap_le⟩ hraw
  
  have hGm : l6σG S ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) :=
    (MeasurableSpace.comap_mono (l6G_le S)).trans mx.comap_le
  have hAm : l6σA S ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) := ma.comap_le
  have hHm : l6σH S g₀ ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) :=
    sup_le ((MeasurableSpace.comap_mono (l6H_le S hg₀)).trans mx.comap_le) mb.comap_le
  have hindρ' : Indep (l6σA S ⊔ l6σG S) (l6σH S g₀) ρm := by
    rw [sup_comm]; exact hindρ
  have hσx : MeasurableSpace.comap (fun p : L6Lam S.R × L6Y => p.2.1)
      (MeasurableSpace.pi : MeasurableSpace L6S) ≤ aeClosure ρm (l6σH S g₀ ⊔ l6σG S) := by
    refine hxσ.trans (aeClosure_mono ?_)
    refine (MeasurableSpace.comap_mono hNdec).trans ?_
    rw [MeasurableSpace.comap_sup]
    exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
  have hA' : (l6ΛA S).comap Prod.fst ≤ aeClosure ρm (l6σA S ⊔ l6σG S) := by
    simp only [l6ΛA, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup₂_le fun d hd => (hFA d hd).trans (aeClosure_mono le_sup_left)
  have hB' : (l6ΛB S).comap Prod.fst ≤ aeClosure ρm (l6σH S g₀ ⊔ l6σG S) := by
    simp only [l6ΛB, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    refine sup_le ?_ (iSup₂_le fun d hd => ?_)
    · exact (l6_comap_le_aeClosure_of_ae_eq _ hxy.symm).trans
        ((aeClosure_mono hσx).trans (aeClosure_aeClosure_le _))
    · refine (hFB d hd).trans ((aeClosure_mono ?_).trans (aeClosure_aeClosure_le _))
      refine (le_of_eq (MeasurableSpace.comap_prodMk _ _)).trans ?_
      refine sup_le ((le_sup_right.trans le_sup_left).trans (le_aeClosure _)) ?_
      have hue : (fun p : L6Lam S.R × L6Y => p.1.2.2.2) =ᵐ[ρm]
          fun p => S.u g₀ (pairJInv ⊤ p.2.1) := by
        filter_upwards [hρL, hxy] with p hp hp'
        rw [hp.2, hp']
      refine (l6_comap_le_aeClosure_of_ae_eq _ hue).trans (aeClosure_mono ?_) |>.trans
        ((aeClosure_mono hσx).trans (aeClosure_aeClosure_le _))
      rw [show (fun p : L6Lam S.R × L6Y => S.u g₀ (pairJInv ⊤ p.2.1)) =
        (fun x => S.u g₀ (pairJInv ⊤ x)) ∘ (fun p : L6Lam S.R × L6Y => p.2.1) from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono ((S.measurable_u hg₀).comp (measurable_pairJInv ⊤)).comap_le
  have H4 := condIndepEv_of_indep_of_le hGm hAm hHm hindρ' hA' hB'
  
  have hΛGm : l6ΛG S ≤ (inferInstance : MeasurableSpace (L6Lam S.R)) :=
    (MeasurableSpace.comap_mono (l6G_le S)).trans measurable_fst.comap_le
  have hΛAm : l6ΛA S ≤ (inferInstance : MeasurableSpace (L6Lam S.R)) :=
    iSup₂_le fun d _ => ((measurable_pi_apply d).comp (measurable_fst.comp
      (measurable_snd.comp measurable_snd))).comap_le
  have hΛBm : l6ΛB S ≤ (inferInstance : MeasurableSpace (L6Lam S.R)) :=
    sup_le measurable_fst.comap_le (iSup₂_le fun d _ =>
      ((measurable_pi_apply d).comp (measurable_fst.comp measurable_snd)).comap_le)
  have hG'm : (l6ΛG S).comap Prod.fst ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) :=
    (MeasurableSpace.comap_mono hΛGm).trans measurable_fst.comap_le
  have hA'm : (l6ΛA S).comap Prod.fst ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) :=
    (MeasurableSpace.comap_mono hΛAm).trans measurable_fst.comap_le
  have hB'm : (l6ΛB S).comap Prod.fst ≤ (inferInstance : MeasurableSpace (L6Lam S.R × L6Y)) :=
    (MeasurableSpace.comap_mono hΛBm).trans measurable_fst.comap_le
  have hGG' : l6σG S ≤ aeClosure ρm ((l6ΛG S).comap Prod.fst) := by
    rw [l6ΛG, MeasurableSpace.comap_comp]
    exact l6_comap_le_aeClosure_of_ae_eq _ hxy
  have hG'G : (l6ΛG S).comap Prod.fst ≤ aeClosure ρm (l6σG S) := by
    rw [l6ΛG, MeasurableSpace.comap_comp]
    exact l6_comap_le_aeClosure_of_ae_eq _ hxy.symm
  have H5 := condIndepEv_congr_cond hGm hG'm hGG' hG'G (hA'm.trans (le_aeClosure _))
    (hB'm.trans (le_aeClosure _)) H4
  
  have H6 := condIndepEv_map measurable_fst hΛGm hΛAm hΛBm H5
  rw [hmarg] at H6
  have H7 := condIndepEv_comap_of_map hΛ hΛGm hΛAm hΛBm H6
  have f1 : (l6ΛG S).comap (l6Λ S ξ g₀ h' L) =
      MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) (l6G S) := by
    rw [l6ΛG, MeasurableSpace.comap_comp]; rfl
  have f2 : (l6ΛA S).comap (l6Λ S ξ g₀ h' L) = ⨆ (d : L5Code) (_ : l5Rect d.1 ⊆ (S.V₁ : Set ℂ)),
      MeasurableSpace.comap (fun ω => ENNReal.ofReal (Real.exp (-(ξ * S.cA (h' ω)))) *
        l5Obs (L ω) d) inferInstance := by
    simp only [l6ΛA, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]; rfl
  have f3 : (l6ΛB S).comap (l6Λ S ξ g₀ h' L) =
      MeasurableSpace.comap (fun ω => pairJ ⊤ (h' ω)) MeasurableSpace.pi ⊔
        l5ObsSigma L (S.U₁ : Set ℂ) := by
    simp only [l6ΛB, MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, l5ObsSigma]; rfl
  rw [f1, f2, f3] at H7
  exact H7

end SupercriticalLQGUniqueness.B2.PfeLocal
