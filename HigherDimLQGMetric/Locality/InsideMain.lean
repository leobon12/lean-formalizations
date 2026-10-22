import HigherDimLQGMetric.Locality.FiniteCore
import HigherDimLQGMetric.Locality.ObservationCI
import HigherDimLQGMetric.Locality.Exhaust
import HigherDimLQGMetric.Select.MetricBorel

/-! The finite result extends to each nice open set through the countable
connected compact exhaustion, on the standard Borel law of `(h,D)`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_inside_locality
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ) (hL2c : L2c_trunc)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ q : ℝ, DGZ.DGZHyp d κ ξ q ∧
      DGZ.RealEpsAdapterShape d κ ξ q)
    (hDM : DMarkovRd)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    (V : TopologicalSpace.Opens (Rd d)) (hV : IsNiceOpen V)
    (z₀ : Rd d) (ρ : ℝ) (hρ : 0 < ρ)
    (hsph : Metric.sphere z₀ ρ ⊆ V) :
    LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) V)
      (famSigmaRd (rescFam ξ h Dh z₀ ρ) V)
      (fullSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) ⊔
        famSigmaRd (rescFam ξ h Dh z₀ ρ) (extOpen V)) P := by
  let ι := l7a_CompIndex V
  let κ' := l7a_CompIndex (extOpen V)
  let W : ι → TopologicalSpace.Opens (Rd d) := l7a_compDomain V
  let W' : κ' → TopologicalSpace.Opens (Rd d) :=
    l7a_compDomain (extOpen V)
  let Base := DistRd d × ContMetric d
  let mBase : MeasurableSpace Base := inferInstance
  let X : Ω → Base := fun ω => (h ω, Dh ω)
  have hX : Measurable X := hh.1.measurable.prodMk hDh
  let g₀ : Base → DistRd d := fun q => l7b_recenter q.1 ρ z₀
  let G : MeasurableSpace Base := fieldSigmaRd g₀ V
  let H : MeasurableSpace Base := fullSigmaRd g₀
  let A : ι → MeasurableSpace Base := fun i =>
    famSigmaRd (l7b_chainFam ξ (fun q => q.1) (fun q => q.2) ρ z₀) (W i)
  let B : κ' → MeasurableSpace Base := fun j =>
    famSigmaRd (l7b_chainFam ξ (fun q => q.1) (fun q => q.2) ρ z₀) (W' j)
  letI : MeasurableSpace Base := mBase
  have hg₀ : Measurable g₀ :=
    (l7b_measurable_recenter ρ z₀).comp measurable_fst
  have hG : G ≤ (inferInstance : MeasurableSpace Base) :=
    ((measurable_restrictTo V).comp hg₀).comap_le
  have hH : H ≤ (inferInstance : MeasurableSpace Base) := hg₀.comap_le
  have hA (i : ι) : A i ≤ (inferInstance : MeasurableSpace Base) :=
    (l7b_measurable_chainFam ξ measurable_fst measurable_snd ρ z₀ (W i)).comap_le
  have hB (j : κ') : B j ≤ (inferInstance : MeasurableSpace Base) :=
    (l7b_measurable_chainFam ξ measurable_fst measurable_snd ρ z₀ (W' j)).comap_le
  have hchainFun (U : Set (Rd d)) :
      (fun ω => l7b_chainFam ξ (fun q : Base => q.1) (fun q => q.2)
        ρ z₀ (h ω, Dh ω) U) =
      (fun ω => l7b_chainFam ξ h Dh ρ z₀ ω U) := by
    funext ω u v
    rfl
  have hfinite (S : Finset ι) (T : Finset κ') :
      LQGMetric.CondIndepEv (G.comap X)
        ((⨆ i ∈ S, A i).comap X)
        ((H ⊔ ⨆ j ∈ T, B j).comap X) P := by
    have hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)) :=
      fun i _ => (l7a_compDomain_connected V i).isPreconnected
    have hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)) :=
      fun j _ => (l7a_compDomain_connected (extOpen V) j).isPreconnected
    have hWcomp : ∀ i ∈ S, IsCompact (closure (W i : Set (Rd d))) :=
      fun i _ => l7a_compDomain_closure_compact V i
    have hW'comp : ∀ j ∈ T, IsCompact (closure (W' j : Set (Rd d))) :=
      fun j _ => l7a_compDomain_closure_compact (extOpen V) j
    have hWV : ∀ i ∈ S, closure (W i : Set (Rd d)) ⊆ V :=
      fun i _ => l7a_compDomain_closure_subset V i
    have hW'U : ∀ j ∈ T, closure (W' j : Set (Rd d)) ⊆ extOpen V :=
      fun j _ => l7a_compDomain_closure_subset (extOpen V) j
    have hF := l7a_finite_locality_core hL6a hL2c hd ξ κ hκ hB2
      hDM εs hεs hεt P h Dh hh hDh hstable V hV z₀ ρ hρ hsph
      S T W W' hWc hW'c hWcomp hW'comp hWV hW'U
    simpa only [G, H, A, B, X, g₀,
      MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, Function.comp_def,
      fieldSigmaRd, fullSigmaRd, famSigmaRd,
      hchainFun] using hF
  have hlim := l7a_condIndepEv_iSup_observation P X hX
    G H A B hG hH hA hB hfinite
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength :=
    (l7a_ae_stable_limit_good hL6a ξ κ hB2 εs hεs hεt
      P h Dh hh hDh hstable).mono (fun _ hω => hω.1)
  let GI : MeasurableSpace Ω := G.comap X
  let AI : MeasurableSpace Ω := (⨆ i, A i).comap X
  let BI : MeasurableSpace Ω := (H ⊔ ⨆ j, B j).comap X
  letI : MeasurableSpace Ω := mΩ
  have hGid : GI = fieldSigmaRd
      (fun ω => l7b_recenter (h ω) ρ z₀) V := by
    simp only [GI, G, X, g₀, fieldSigmaRd,
      MeasurableSpace.comap_comp, Function.comp_def]
  have hAid (i : ι) : (A i).comap X =
      famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i) := by
    simp only [A, X, famSigmaRd, MeasurableSpace.comap_comp,
      Function.comp_def, hchainFun]
  have hBid (j : κ') : (B j).comap X =
      famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j) := by
    simp only [B, X, famSigmaRd, MeasurableSpace.comap_comp,
      Function.comp_def, hchainFun]
  have hHid : H.comap X =
      fullSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) := by
    simp only [H, X, g₀, fullSigmaRd, MeasurableSpace.comap_comp,
      Function.comp_def]
  have hA' : famSigmaRd (rescFam ξ h Dh z₀ ρ) V ≤ aeClosure P AI := by
    refine (l7a_rescFamSigma_le_iSup_compDomain ξ h Dh z₀ ρ V).trans ?_
    refine iSup_le fun i => ?_
    have hstep : famSigmaRd (rescFam ξ h Dh z₀ ρ) (W i) ≤
        aeClosure P (famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i)) := by
      change famSigmaRd (l7b_intFam ξ h Dh ρ z₀) (W i) ≤ _
      exact l7b_intSigma_le_ae_chain hlen ρ z₀ (W i).isOpen
    have hsource : famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i) ≤ AI := by
      rw [← hAid i]
      exact MeasurableSpace.comap_mono (le_iSup A i)
    exact hstep.trans (aeClosure_mono hsource)
  have hB' : fullSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) ⊔
      famSigmaRd (rescFam ξ h Dh z₀ ρ) (extOpen V) ≤
      aeClosure P BI := by
    apply sup_le
    · have hs : fullSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) ≤ BI := by
        rw [← hHid]
        exact MeasurableSpace.comap_mono le_sup_left
      exact hs.trans (le_aeClosure _)
    · refine (l7a_rescFamSigma_le_iSup_compDomain ξ h Dh z₀ ρ
        (extOpen V)).trans ?_
      refine iSup_le fun j => ?_
      have hstep : famSigmaRd (rescFam ξ h Dh z₀ ρ) (W' j) ≤
          aeClosure P (famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j)) := by
        change famSigmaRd (l7b_intFam ξ h Dh ρ z₀) (W' j) ≤ _
        exact l7b_intSigma_le_ae_chain hlen ρ z₀ (W' j).isOpen
      have hsource : famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j) ≤ BI := by
        rw [← hBid j]
        exact MeasurableSpace.comap_mono ((le_iSup B j).trans le_sup_right)
      exact hstep.trans (aeClosure_mono hsource)
  rw [← hGid]
  exact LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hlim hA' hB'

end HigherDimLQGMetric
