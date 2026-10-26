import SupercriticalConformalCovariance.Transport.ConfinedData

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn addFun)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCFun)
open SupercriticalConformalCovariance (IsDomainRealization)
namespace SupercriticalConformalCovariance.Transport

/-- The closed-disk confined domain metric is a measurable function of the domain field itself,
simultaneously at all endpoint pairs. -/
theorem exists_measurable_confined_field_version {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D)
    (V : Opens ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → DistOn V}
    {h₀ : Ω → DistC} {f : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f)
    (c : ℂ) (R : ℝ) (hKV : Metric.closedBall c R ⊆ V)
    [MeasurableSpace LSCFun] [BorelSpace LSCFun] :
    ∃ G : DistOn V → LSCFun, Measurable G ∧
      ∀ᵐ ω ∂P, ∀ q : ℂ × ℂ,
        (G (h ω)).1 q =
          ((SupercriticalConformalCovariance.Domain.confined (ξ : ℝ) (D (h₀ ω)) hKV (f ω) q : ℝ≥0∞) : EReal) := by
  obtain ⟨n, hn⟩ := SupercriticalConformalCovariance.Domain.exists_subset_exW V.isOpen (isCompact_closedBall c R) hKV
  obtain ⟨g, hg, hw⟩ := hR.2.1.2
  let β := DistC × (C(V, ℝ) × C(ℂ, ℝ))
  let Y : Ω → β := fun ω => (h₀ ω, (f ω, g ω))
  have hY : Measurable Y := hR.2.1.1.prodMk (hR.2.2.1.prodMk hg)
  let J : Ω → RealizationData V := fun ω => (h ω, Y ω)
  have hJ : Measurable J := hR.1.prodMk hY
  let ν : Measure (Ω × β) := LQGMetric.condCopyMeasure Y h P hR.1
  haveI : IsProbabilityMeasure ν := inferInstance
  let J₁ : Ω × β → RealizationData V := fun p => J p.1
  let J₂ : Ω × β → RealizationData V := fun p => (h p.1, p.2)
  have hJ₁ : Measurable J₁ := hJ.comp measurable_fst
  have hJ₂ : Measurable J₂ := (hR.1.comp measurable_fst).prodMk measurable_snd
  have hLaw₁ : ν.map J₁ = P.map J := by
    change ν.map (J ∘ Prod.fst) = P.map J
    rw [← Measure.map_map hJ measurable_fst, LQGMetric.condCopyMeasure_fst hR.1]
  have hLaw₂ : ν.map J₂ = P.map J := by
    exact LQGMetric.condCopyMeasure_map_snd hR.1 hY
  have hR₁ : IsDomainRealization V ν (fun p => (J₁ p).1)
      (fun p => (J₁ p).2.1) (fun p => (J₁ p).2.2.1) :=
    realization_of_joint_law_eq V P ν J J₁ hJ hJ₁ hR hw hLaw₁
  have hR₂ : IsDomainRealization V ν (fun p => (J₂ p).1)
      (fun p => (J₂ p).2.1) (fun p => (J₂ p).2.2.1) :=
    realization_of_joint_law_eq V P ν J J₂ hJ hJ₂ hR hw hLaw₂
  let Z : β → LSCFun := fun y =>
    closedDiskFun c R (D (addFun y.1 (SupercriticalConformalCovariance.Domain.cutF V n y.2.1)))
  have hfcut : Measurable (fun y : β => SupercriticalConformalCovariance.Domain.cutF V n y.2.1) := by
    change Measurable (fun y : β => SupercriticalConformalCovariance.Domain.cutExt V.isOpen
      (SupercriticalConformalCovariance.Domain.tsupport_cutoff_subset (V : Set ℂ) n) y.2.1)
    exact SupercriticalConformalCovariance.Domain.measurable_cutExt V.isOpen _ (measurable_fst.comp measurable_snd)
  have hZ : Measurable Z := (measurable_closedDiskFun c R).comp
    (hD.1.comp (LQGMetric.measurable_addFun.comp (measurable_fst.prodMk hfcut)))
  have h₁ := ae_closedDiskFun_eq_confined hD V ν hR₁ c R hKV n hn
  have h₂ := ae_closedDiskFun_eq_confined hD V ν hR₂ c R hKV n hn
  have hEq := ae_confined_eq_of_realisations hD V ν hR₁ hR₂ c R hKV
  have hCopyEq : (fun p : Ω × β => Z (Y p.1)) =ᵐ[ν] (fun p => Z p.2) := by
    filter_upwards [h₁, h₂, hEq] with p e₁ e₂ e₃
    apply Subtype.ext
    funext q
    calc
      (Z (Y p.1)).1 q = ((SupercriticalConformalCovariance.Domain.confined (ξ : ℝ)
          (D (h₀ p.1)) hKV (f p.1) q : ℝ≥0∞) : EReal) := e₁ q
      _ = ((SupercriticalConformalCovariance.Domain.confined (ξ : ℝ)
          (D p.2.1) hKV p.2.2.1 q : ℝ≥0∞) : EReal) :=
          congrArg (fun a : ℂ × ℂ → ℝ≥0∞ => (a q : EReal)) e₃
      _ = (Z p.2).1 q := (e₂ q).symm
  obtain ⟨G, hG, hGae⟩ :=
    ae_determined_of_data_copy_eq P h Y Z hR.1 hY hZ hCopyEq
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGae, ae_closedDiskFun_eq_confined hD V P hR c R hKV n hn]
    with ω e₁ e₂ q
  exact congrArg (fun a : LSCFun => a.1 q) e₁.symm |>.trans (e₂ q)

end SupercriticalConformalCovariance.Transport
