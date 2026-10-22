import HigherDimLQGMetric.Config.Continuous
import HigherDimLQGMetric.Select.InternalBorel
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric

/-! Borel measurability of the continuous configuration encoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open MeasureTheory Set

variable {d : ℕ}

theorem measurable_internalC_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] (F : Ω → ContMetric d) (hF : Measurable F)
    (hLen : ∀ ω, (F ω).IsLength) {U : Set (Rd d)}
    [LocallyCompactSpace U]
    (hU : IsOpen U) (hUc : IsPreconnected U) :
    Measurable (fun ω => internalC (F ω) (hLen ω) hU hUc) := by
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  obtain ⟨G, hG, hGeq⟩ := measurable_internal_ambient hU
  have hpair : Measurable (fun ω => ((F ω).1, p.1.1, p.2.1)) := by
    exact (measurable_subtype_coe.comp hF).prodMk
      (measurable_const.prodMk measurable_const)
  have hval : Measurable (fun ω => (G ((F ω).1, p.1.1, p.2.1)).toReal) :=
    ENNReal.measurable_toReal.comp (hG.comp hpair)
  convert hval using 1
  funext ω
  change ((F ω).internal U p.1.1 p.2.1).toReal = _
  rw [hGeq (F ω) (hLen ω)]

theorem measurable_configScaledMetric
    {Ω : Type*} [MeasurableSpace Ω] (F : Ω → ContMetric d) (hF : Measurable F)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => configScaledMetric (F ω) hs hr z) := by
  have hcont : Continuous (fun D : ContMetric d => configScaledMetric D hs hr z) := by
    apply Continuous.subtype_mk
    change Continuous (fun D : ContMetric d =>
      (s⁻¹ : ℝ) • (D.1.comp
        ⟨fun p : Rd d × Rd d => (r • p.1 + z, r • p.2 + z), by fun_prop⟩))
    exact (continuous_const : Continuous (fun _ : ContMetric d => (s⁻¹ : ℝ))).smul
      ((ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
  exact hcont.measurable.comp hF

theorem measurable_configScaledMetric_var
    {Ω : Type*} [MeasurableSpace Ω] (F : Ω → ContMetric d) (hF : Measurable F)
    (s : Ω → ℝ) (hsm : Measurable s) (hs : ∀ ω, 0 < s ω)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => configScaledMetric (F ω) (hs ω) hr z) := by
  let a : C(Rd d × Rd d, Rd d × Rd d) :=
    ⟨fun p => (r • p.1 + z, r • p.2 + z), by fun_prop⟩
  have hpre : Measurable (fun ω => (F ω).1.comp a) :=
    (ContinuousMap.continuous_precomp a).measurable.comp
      (measurable_subtype_coe.comp hF)
  have hamb : Measurable (fun ω => (s ω)⁻¹ • (F ω).1.comp a) :=
    hsm.inv.smul hpre
  have hEmb : MeasurableEmbedding ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  apply (hEmb.measurable_comp_iff).mp
  convert hamb using 1
  funext ω
  rfl

theorem measurable_configC_var
    {Ω : Type*} [MeasurableSpace Ω] (hd : 2 ≤ d)
    (F Ft : Ω → ContMetric d) (hF : Measurable F) (hFt : Measurable Ft)
    (hLen : ∀ ω, (F ω).IsLength) (hLent : ∀ ω, (Ft ω).IsLength)
    (s : Ω → ℝ) (hsm : Measurable s) (hs : ∀ ω, 0 < s ω)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => configC hd (F ω) (Ft ω) (hLen ω) (hLent ω)
      (hs ω) hr z) := by
  have hFs := measurable_configScaledMetric_var F hF s hsm hs hr z
  have hFts := measurable_configScaledMetric_var Ft hFt s hsm hs hr z
  have ho := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (F ω) (hs ω) hr z) hFs
    (fun ω => configScaledMetric_isLength (F ω) (hLen ω) (hs ω) hr z)
    configOuter_isOpen (configOuter_isPreconnected hd)
  have hot := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (Ft ω) (hs ω) hr z) hFts
    (fun ω => configScaledMetric_isLength (Ft ω) (hLent ω) (hs ω) hr z)
    configOuter_isOpen (configOuter_isPreconnected hd)
  have hi := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (F ω) (hs ω) hr z) hFs
    (fun ω => configScaledMetric_isLength (F ω) (hLen ω) (hs ω) hr z)
    configInner_isOpen (configInner_isPreconnected hd)
  have hit := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (Ft ω) (hs ω) hr z) hFts
    (fun ω => configScaledMetric_isLength (Ft ω) (hLent ω) (hs ω) hr z)
    configInner_isOpen (configInner_isPreconnected hd)
  exact ho.prodMk (hot.prodMk (hi.prodMk hit))

/-- Measurability of the normalized configuration map on a sample space on
which both metric assignments are length metrics pointwise. -/
theorem measurable_configC_sharp
    {Ω : Type*} [MeasurableSpace Ω] (hd : 2 ≤ d)
    (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (hD : Measurable D) (hDt : Measurable Dt)
    (h : Ω → DistRd d) (hh : Measurable h)
    (hLen : ∀ ω, (D (h ω)).IsLength)
    (hLent : ∀ ω, (Dt (h ω)).IsLength)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => configC hd (D (h ω)) (Dt (h ω))
      (hLen ω) (hLent ω) (sNorm_pos ξ Q (h ω) hr z) hr z) := by
  have hsm : Measurable (fun ω => sNorm ξ Q (h ω) r z) := by
    unfold sNorm
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_sphereAvg_left r z).comp hh)))
  exact measurable_configC_var hd (fun ω => D (h ω)) (fun ω => Dt (h ω))
    (hD.comp hh) (hDt.comp hh) hLen hLent
    (fun ω => sNorm ξ Q (h ω) r z) hsm
    (fun ω => sNorm_pos ξ Q (h ω) hr z) hr z

theorem measurable_configC
    {Ω : Type*} [MeasurableSpace Ω] (hd : 2 ≤ d)
    (F Ft : Ω → ContMetric d) (hF : Measurable F) (hFt : Measurable Ft)
    (hLen : ∀ ω, (F ω).IsLength) (hLent : ∀ ω, (Ft ω).IsLength)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => configC hd (F ω) (Ft ω) (hLen ω) (hLent ω) hs hr z) := by
  have hFs := measurable_configScaledMetric F hF hs hr z
  have hFts := measurable_configScaledMetric Ft hFt hs hr z
  have ho := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (F ω) hs hr z) hFs
    (fun ω => configScaledMetric_isLength (F ω) (hLen ω) hs hr z)
    configOuter_isOpen (configOuter_isPreconnected hd)
  have hot := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (Ft ω) hs hr z) hFts
    (fun ω => configScaledMetric_isLength (Ft ω) (hLent ω) hs hr z)
    configOuter_isOpen (configOuter_isPreconnected hd)
  have hi := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (F ω) hs hr z) hFs
    (fun ω => configScaledMetric_isLength (F ω) (hLen ω) hs hr z)
    configInner_isOpen (configInner_isPreconnected hd)
  have hit := measurable_internalC_of_measurable
    (fun ω => configScaledMetric (Ft ω) hs hr z) hFts
    (fun ω => configScaledMetric_isLength (Ft ω) (hLent ω) hs hr z)
    configInner_isOpen (configInner_isPreconnected hd)
  exact ho.prodMk (hot.prodMk (hi.prodMk hit))

/-- A measurable version of the sharp configuration under the actual
almost-sure length hypotheses.  On a measurable full-measure subset, it is
the four continuous internal metrics of the sampled assignments. -/
theorem exists_measurable_configC_sharp_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hd : 2 ≤ d)
    (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∃ Ξ : Ω → ConfigC d, Measurable Ξ ∧
      ∀ᵐ ω ∂P, ∃ (hl : (D (h ω)).IsLength)
        (hlt : (Dt (h ω)).IsLength),
        Ξ ω = configC hd (D (h ω)) (Dt (h ω)) hl hlt
          (sNorm_pos ξ Q (h ω) hr z) hr z := by
  classical
  have hgoodD : ∀ᵐ ω ∂P, (D (h ω)).IsLength :=
    (show IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q)) from hD).length
      P h hh.isLGFPlusCont
  have hgoodDt : ∀ᵐ ω ∂P, (Dt (h ω)).IsLength :=
    (show IsWeakExpMetric d ξ Dt (fun r => r ^ (ξ * Q)) from hDt).length
      P h hh.isLGFPlusCont
  have hgood : ∀ᵐ ω ∂P,
      (D (h ω)).IsLength ∧ (Dt (h ω)).IsLength := hgoodD.and hgoodDt
  obtain ⟨S, hSae, hSm, hSsub⟩ := hgood.exists_measurable_mem
  have hSev : ∀ᵐ ω ∂P, ω ∈ S := hSae
  obtain ⟨ω₀, hω₀⟩ := hSev.exists
  have hω₀' : (D (h ω₀)).IsLength ∧ (Dt (h ω₀)).IsLength := hSsub ω₀ hω₀
  let F : Ω → ContMetric d := fun ω => if ω ∈ S then D (h ω) else D (h ω₀)
  let Ft : Ω → ContMetric d := fun ω => if ω ∈ S then Dt (h ω) else Dt (h ω₀)
  have hFm : Measurable F :=
    (hD.measurable.comp hh.measurable).piecewise hSm measurable_const
  have hFtm : Measurable Ft :=
    (hDt.measurable.comp hh.measurable).piecewise hSm measurable_const
  have hFl (ω : Ω) : (F ω).IsLength := by
    by_cases hω : ω ∈ S
    · simpa [F, hω] using (hSsub ω hω).1
    · simpa [F, hω] using hω₀'.1
  have hFtl (ω : Ω) : (Ft ω).IsLength := by
    by_cases hω : ω ∈ S
    · simpa [Ft, hω] using (hSsub ω hω).2
    · simpa [Ft, hω] using hω₀'.2
  let Ξ : Ω → ConfigC d := fun ω => configC hd (F ω) (Ft ω)
    (hFl ω) (hFtl ω) (sNorm_pos ξ Q (h ω) hr z) hr z
  refine ⟨Ξ, ?_, ?_⟩
  · have hsm : Measurable (fun ω => sNorm ξ Q (h ω) r z) := by
      unfold sNorm
      exact measurable_const.mul (Real.measurable_exp.comp
        (measurable_const.mul ((measurable_sphereAvg_left r z).comp hh.measurable)))
    exact measurable_configC_var hd F Ft hFm hFtm hFl hFtl
      (fun ω => sNorm ξ Q (h ω) r z) hsm
      (fun ω => sNorm_pos ξ Q (h ω) hr z) hr z
  · filter_upwards [hSae] with ω hω
    refine ⟨(hSsub ω hω).1, (hSsub ω hω).2, ?_⟩
    dsimp [Ξ]
    simp [F, Ft, hω]

end HigherDimLQGMetric
