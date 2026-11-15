import InteractingSLE.Spec.Sec5.Aux61RestartInstInherited
import InteractingSLE.Spec.Sec5.Aux61RestartAccess

/-!
# The fresh continuation in the actual restart chart

Packet PROVE-AUX61-R1, ruling R71. The normalization on the entire recorded
own collar transfers to the actual future curve by the original own-chart
access theorem. Every compact interior simple continuation consequently has a
continuous driver, without an unbounded-continuation assumption.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

/-- Normalize the actual fresh continuation using the retained own collar,
then map out each compact pre-contact segment. A lift correction leaves every
hypothesis here unchanged, since it changes only the derivative lift. -/
theorem exists_driver_of_history_restart_chart
    {Ω : Type*} {U : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ} {r : ℝ≥0} {t : ℝ}
    (hUc : ∀ ω, Continuous fun u => U u ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω)) (hrt : (r : ℝ) < t)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hown : ∀ ω, (c ω).dom ≤ (ownHistoryChart U r ω).dom)
    (hseed : ∀ ω, Tendsto ((c ω).1 ∘ (ownHistoryChart U r ω).2.1)
      (𝓝[H] 0) (𝓝 0))
    (hi : ∀ ω, InjOn (η ω) (Ioc (r : ℝ) t))
    (hnew : ∀ ω, MapsTo (η ω) (Ioc (r : ℝ) t) (c ω).dom) (ω : Ω) :
    Tendsto ((c ω).1 ∘ η ω) (𝓝[>] (r : ℝ)) (𝓝 0) ∧
      ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ,
        σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 (t - r)) ∧ ContinuousOn σ (Icc 0 (t - r)) ∧
          ∀ u ∈ Icc 0 (t - r), 0 ≤ σ u ∧
            fwdHull W (σ u) = landingSlit ((c ω).1 ∘ η ω) r 0 '' Ioc 0 u ∧
            IsMapOut (landingSlit ((c ω).1 ∘ η ω) r 0 '' Ioc 0 u)
              (fun z => fwdMap W (σ u) z + W (σ u)) := by
  have hW := Chart.continuous_rpath_of_continuous (hUc ω)
  have hW0 := Chart.rpath_zero_of (hU0 ω)
  have hηown : ∀ᶠ u in 𝓝[>] (r : ℝ), η ω u ∈ H \ fwdHull (Ito.rpath (U · ω)) r := by
    filter_upwards [Ioc_mem_nhdsGT hrt] with u hu
    have h : η ω u ∈ ((ownHistoryChart U r ω).dom : Set ℂ) := hown ω (hnew ω hu)
    rwa [coe_dom_ownHistoryChart hUc hU0] at h
  have hlim := tendsto_own_chart_at_restart hW hW0 (hη ω) r.coe_nonneg hηown
  have hηlim : Tendsto ((c ω).1 ∘ η ω) (𝓝[>] (r : ℝ)) (𝓝 0) := by
    refine ((hseed ω).comp hlim).congr' (hηown.mono fun u hu => ?_)
    change (c ω).1 (fwdMapInv (Ito.rpath (U · ω)) r
      (fwdMap (Ito.rpath (U · ω)) r (η ω u))) = (c ω).1 (η ω u)
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 r.coe_nonneg hu]
  refine ⟨hηlim, exists_driver_of_charted_continuation
    ⟨(c ω).1, Sec7.Lemma71E.isConformalBijection_fwd (hc ω)⟩ hrt
    ((hη ω).2.1.mono ?_) (hi ω) (hnew ω) hηlim⟩
  intro u hu
  exact r.coe_nonneg.trans hu.1.le

end InteractingSLE.Sec5.Aux61Restart
