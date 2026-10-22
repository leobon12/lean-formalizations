import HigherDimLQGMetric.Locality.LimitIndep
import HigherDimLQGMetric.Locality.ClippedMark
import HigherDimLQGMetric.Locality.SecondMarkedLaw
import HigherDimLQGMetric.Locality.SecondTrunc
import HigherDimLQGMetric.Locality.SecondConsistency
import HigherDimLQGMetric.Locality.StableGood

/-! The finite connected-domain locality statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_finite_locality_core
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ) (hL2c : L2c_trunc)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ q : ℝ, DGZ.DGZHyp d κ ξ q ∧
      DGZ.RealEpsAdapterShape d κ ξ q)
    (hDM : DMarkovRd)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    (V : TopologicalSpace.Opens (Rd d)) (hV : IsNiceOpen V)
    (z₀ : Rd d) (ρ : ℝ) (hρ : 0 < ρ)
    (hsph : Metric.sphere z₀ ρ ⊆ V)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (hWc : ∀ i ∈ S, IsPreconnected (W i : Set (Rd d)))
    (hW'c : ∀ j ∈ T, IsPreconnected (W' j : Set (Rd d)))
    (hWcomp : ∀ i ∈ S, IsCompact (closure (W i : Set (Rd d))))
    (hW'comp : ∀ j ∈ T, IsCompact (closure (W' j : Set (Rd d))))
    (hWV : ∀ i ∈ S, closure (W i : Set (Rd d)) ⊆ V)
    (hW'U : ∀ j ∈ T, closure (W' j : Set (Rd d)) ⊆ extOpen V) :
    LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) V)
      (⨆ i ∈ S, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i))
      (fullSigmaRd (fun ω => l7b_recenter (h ω) ρ z₀) ⊔
        ⨆ j ∈ T, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j)) P := by
  let g : Ω → DistRd d := fun ω => l7b_recenter (h ω) ρ z₀
  obtain ⟨H, hHc, hHm, hind, hdet₀⟩ :=
    hDM d hd P h hh.1 V z₀ ρ hV.1 hρ hsph
  have hdet := hdet₀ hV.2
  obtain ⟨φ, hφsup, hφc, K, hK, F, hFm, hFsup, _,
    R, hRm, hRae, Φ, hΦm, hΦeq, m, hm⟩ :=
    l7a_stage_finite_with_versions hd κ hκ ξ εs hεs hεt
      P h hh.1 V z₀ ρ S T W W' hWc hW'c
      hWcomp hW'comp hWV hW'U H hHc hHm hind
  obtain ⟨K', hK', Ψ, hΨm, hΨsupp, hΨeq⟩ :=
    l7a_exists_clipped_mark h ρ z₀ K hK F hFsup V Φ hΦm
      (fun ω => by
        simpa only [Function.comp_def] using
          (congrArg Prod.fst (congrFun hΦeq ω)).symm)
  let ε' : ℕ → ℝ := fun n => εs (n + m)
  have hε' (n : ℕ) : 0 < ε' n := hεs (n + m)
  have hε'0 : Tendsto ε' atTop (𝓝 0) :=
    hεt.comp (tendsto_add_atTop_nat m)
  have hshift : StrictMono (fun n : ℕ => n + m) := by
    intro a b hab
    exact Nat.add_lt_add_right hab m
  have hstable' : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ ε' (h ω) n) (fun ω => (Dh ω).1) := by
    simpa only [ε', lfppSeq] using
      (l6c_stable_subseq P h
        (fun n ω => lfppSeq κ ξ εs (h ω) n)
        (fun ω => (Dh ω).1) hstable (fun n => n + m) hshift)
  have hstage (n : ℕ) : Indep
      (fieldSigmaRd g V ⊔
        MeasurableSpace.comap
          (fun ω => l7a_stageArray hd κ hκ ξ (hε' n) S W hWc (g ω))
          inferInstance)
      (MeasurableSpace.comap R inferInstance ⊔
        MeasurableSpace.comap
          (fun ω => l7a_stageArray hd κ hκ ξ (hε' n) T W' hW'c
            (g ω - ofCont (F ω))) inferInstance) P := by
    simpa only [ε', g, l7b_recenter, l7a_stageArray_sigma] using hm n
  obtain ⟨ns, hns, E, mE, hEsb, Q, hQ, Z, Zlim,
    hZm, hZlimm, hZlaw, hZc⟩ :=
    l7a_exists_second_coupling hL6a hL2c hd ξ κ hκ hB2
      ε' hε' hε'0 P h Dh hh hDh hstable' ρ z₀ F
      Ψ hΨm hΨeq K' hK' hΨsupp S T W W' hWc hW'c
  letI : MeasurableSpace E := mE
  letI : StandardBorelSpace E := hEsb
  letI : IsProbabilityMeasure Q := hQ
  obtain ⟨hstageBase, hbase, hgoodBase⟩ :=
    l7a_second_marked_limit_law hL6a hd ξ κ hκ hB2
      ε' hε' hε'0 P h Dh hh hDh hstable'
      ρ z₀ F Ψ hΨm hΨeq S T W W' hWc hW'c
      ns hns Q Z Zlim hZm hZlimm hZlaw hZc
  obtain ⟨hgraph₁, hgraph₂⟩ :=
    l7a_ae_second_stage_arrays hd ξ κ hκ ε' hε' P h hh
      ρ z₀ F Ψ hΨm hΨeq S T W W' hWc hW'c
      ns Q Z hZm hZlaw
  obtain ⟨τ, hτ, hb₁, hb₂⟩ :=
    l7a_second_two_trunc_subseq hd ξ κ hκ hL2c
      ε' hε' hε'0 P h Dh hh hDh Ψ hΨm K' hK' hΨsupp
      S T W W' ns hns Q Z Zlim hZm hZlimm
      hstageBase hbase hZc hgoodBase
  have hcons := l7a_second_internal_consistency hd ξ κ hκ
    (fun n => ε' (ns n)) (fun n => hε' (ns n))
    S T W W' hWc hW'c Q Z Zlim hZc hgoodBase
    hgraph₁ hgraph₂ τ hτ hb₁ hb₂
  have hInd := l7a_second_limit_indep hd ξ κ hκ ε' hε'
    P h hh V z₀ ρ F Ψ hΨm hΨeq R Φ hΦm hΦeq
    S T W W' hWc hW'c hstage ns Q Z Zlim hZm hZlimm hZlaw hZc
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength :=
    (l7a_ae_stable_limit_good hL6a ξ κ hB2 εs hεs hεt
      P h Dh hh hDh hstable).mono (fun _ hω => hω.1)
  exact l7a_finite_locality_of_coupling ξ P h Dh hh.1.measurable hDh
    hlen V z₀ ρ F Ψ hΨm hΨeq R Φ hΦm hΦeq hFm
    (fun ω => restrictTo (extOpen V) (g ω) - ofFunOn (extOpen V) (H ω))
    hRae hdet S T W W' Q
    (fun e => (Zlim e).1) (measurable_fst.comp hZlimm)
    (fun e => (Zlim e).2.1)
    (measurable_fst.comp (measurable_snd.comp hZlimm))
    (fun e => (Zlim e).2.2)
    (measurable_snd.comp (measurable_snd.comp hZlimm))
    hbase hcons hInd

end HigherDimLQGMetric
