import SupercriticalConformalCovariance.Reversal.Field
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalConformalCovariance.Frozen.IsGreenian
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.GPull.Pairing
import SupercriticalConformalCovariance.ZBConformal.GFFLaw

set_option autoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set Function
open LQGMetric (DistC DistOn IsZeroBoundaryGFF restrictTo IsGFFPlusCont TestOn)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

/-- GM's zero-boundary GFF plus a random continuous function has a whole-plane
realization after a measure-preserving extension. -/
theorem exists_realization_of_zeroBoundary
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Opens ℂ) (hU : IsGreenian U)
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
        (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
      MeasurePreserving π P' P ∧ IsDomainRealization U P' (h ∘ π) g₀ k := by
  obtain ⟨P', F, H, hP', hfst, hg, hFm, hHm, hHc, hzeq, hpair⟩ :=
    SupercriticalConformalCovariance.GPull.exists_reference_coupling P hz hU
  let T : (Ω × DistC) → U → ℝ := fun p x => f p.1 x - H p.2 x
  have hTm : Measurable (fun q : (Ω × DistC) × U => T q.1 q.2) := by
    have hf' : Measurable (fun q : (Ω × DistC) × U => f q.1.1 q.2) :=
      continuous_eval.measurable.comp
        (Measurable.prodMk
          (hf.comp (measurable_fst.comp measurable_fst)) measurable_snd)
    have hH' : Measurable (fun q : (Ω × DistC) × U => H q.1.2 q.2) :=
      hHm.comp (Measurable.prodMk
        (measurable_snd.comp measurable_fst)
        (measurable_subtype_coe.comp measurable_snd))
    exact hf'.sub hH'
  have hTc : ∀ᵐ p ∂P', Continuous (T p) := by
    filter_upwards [hHc] with p hp
    exact (f p.1).continuous.sub hp
  obtain ⟨k, hkm, hk⟩ :=
    SupercriticalConformalCovariance.GPull.exists_measurable_continuous_version hTm hTc
  let g₀ : (Ω × DistC) → DistC := Prod.snd
  have hgp : IsGFFPlusCont g₀ P' :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  have heq' : ∀ᵐ p ∂P', h p.1 = z p.1 +
      Distribution.ofFun U (Function.extend Subtype.val (f p.1) 0) volume ⊤ := by
    have he : ∀ᵐ ω ∂P'.map (Prod.fst : Ω × DistC → Ω),
        h ω = z ω +
          Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤ := by
      simpa only [hfst.map_eq] using heq
    exact ae_of_ae_map measurable_fst.aemeasurable he
  have hreal : ∀ᵐ p ∂P', h p.1 = restrictTo U (g₀ p) +
      Distribution.ofFun U (Function.extend Subtype.val (k p) 0) volume ⊤ := by
    filter_upwards [heq', hzeq, hpair, hk, hHc] with p hp hzpair hpairp hkp hcont
    ext ψ
    have hfcont : ContinuousOn (Function.extend Subtype.val (f p.1) 0)
        (U : Set ℂ) := SupercriticalConformalCovariance.GPull.continuousOn_extZ (f p.1)
    have hHcont : ContinuousOn (H p.2) (U : Set ℂ) :=
      continuousOn_iff_continuous_domRestrict.mpr hcont
    have hKcont : ContinuousOn (fun x : ℂ =>
        Function.extend Subtype.val (k p) 0 x) (U : Set ℂ) :=
      SupercriticalConformalCovariance.GPull.continuousOn_extZ (k p)
    have hKeq : ∀ x (hx : x ∈ (U : Set ℂ)),
        k p ⟨x, hx⟩ =
          Function.extend Subtype.val (f p.1) 0 x - H p.2 x := by
      intro x hx
      calc
        k p ⟨x, hx⟩ = f p.1 ⟨x, hx⟩ - H p.2 x := hkp ⟨x, hx⟩
        _ = Function.extend Subtype.val (f p.1) 0 x - H p.2 x := by
          have hfpoint : Function.extend Subtype.val (f p.1) 0 x = f p.1 ⟨x, hx⟩ := by
            conv_lhs => rw [show x = ((⟨x, hx⟩ : U) : ℂ) from rfl]
            exact Subtype.val_injective.extend_apply _ _ _
          rw [hfpoint]
    have hKi := SupercriticalConformalCovariance.GPull.ofFun_extZ_apply_eq (k p)
      (hfcont.sub hHcont) hKeq ψ
    simp only [Pi.sub_apply] at hKi
    have hFi := SupercriticalConformalCovariance.GPull.ofFun_extZ_pair (f p.1) ψ
    have hsub := SupercriticalConformalCovariance.GPull.integral_test_sub hfcont hHcont ψ
    have hrsub : (restrictTo U (p.2 - F p.2)) ψ =
        (restrictTo U p.2) ψ - (restrictTo U (F p.2)) ψ := rfl
    have hzp : z p.1 ψ = (restrictTo U (F p.2)) ψ := by rw [hzpair]
    have hdiff := hpairp ψ
    rw [hrsub] at hdiff
    rw [hp, add_apply, add_apply, hzp, hFi, hKi, hsub]
    dsimp only [g₀]
    linarith
  exact ⟨Ω × DistC, inferInstance, P', Prod.fst, g₀, k, hfst,
    ⟨hh.comp measurable_fst, hgp, hkm, hreal⟩⟩

end SupercriticalConformalCovariance.GMForm
