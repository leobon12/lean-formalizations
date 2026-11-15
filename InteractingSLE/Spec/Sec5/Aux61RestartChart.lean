import InteractingSLE.Spec.Sec5.Aux61RestartPath
import InteractingSLE.Spec.Sec5.Aux61RestartPrimeEnd

/-!
# The simple continuation in a restart chart with the original target

Packet PROVE-AUX61-R1; ruling R71. Access limits are expressed in the prime-end
approach filters. Their change-of-chart rule is the existing real Möbius rule.
The continuous Loewner driver is obtained only on compact pre-contact segments.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- A prime-end approach is independent of the chart used to describe its mark.
This also covers approaches to the original target at infinity. -/
theorem tendsto_comp_of_primeEnd_eq {α : Type*} {D : Set ℂ} (hDo : IsOpen D)
    {ψ φ : HChart D} {p q : OnePoint ℝ}
    (heq : PrimeEnd.mk φ q = PrimeEnd.mk ψ p) {g : α → ℂ} {l : Filter α}
    (hgD : ∀ᶠ u in l, g u ∈ D)
    (hg : Tendsto (ψ.1 ∘ g) l (PrimeEnd.approachH p)) :
    Tendsto (φ.1 ∘ g) l (PrimeEnd.approachH q) := by
  obtain ⟨a, b, c, d, hdet, hmap⟩ := ψ.exists_realMobius hDo φ
  have hmark := PrimeEnd.mk_mobiusBdry hdet hmap p
  have hpq := PrimeEnd.mk_injective φ (hmark.trans heq.symm)
  have hlim := (PrimeEnd.tendsto_realMobius_approachH hdet p).comp hg
  rw [hpq] at hlim
  exact hlim.congr' (hgD.mono fun u hu => (hmap hu).symm)

/-- A simple continuation from a landed current access, in a chosen half-plane
chart, has a continuous driver on every compact part before its next contact. -/
theorem exists_driver_of_charted_continuation {D : Set ℂ} (ψ : HChart D)
    {η : ℝ → ℂ} {r t : ℝ} (hrt : r < t) (hc : ContinuousOn η (Ioc r t))
    (hi : InjOn η (Ioc r t)) (hD : MapsTo η (Ioc r t) D)
    (haccess : Tendsto (ψ.1 ∘ η) (𝓝[>] r) (𝓝 0)) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ,
      σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 (t - r)) ∧ ContinuousOn σ (Icc 0 (t - r)) ∧
        ∀ u ∈ Icc 0 (t - r), 0 ≤ σ u ∧
          QuantumZipper.fwdHull W (σ u) = landingSlit (ψ.1 ∘ η) r 0 '' Ioc 0 u ∧
          IsMapOut (landingSlit (ψ.1 ∘ η) r 0 '' Ioc 0 u)
            (fun z => QuantumZipper.fwdMap W (σ u) z + W (σ u)) := by
  exact exists_driver_of_landing_slit hrt (ψ.2.1.continuousOn.comp hc hD)
    (ψ.injOn.comp hi hD) (ψ.mapsTo.comp hD) (by simpa only [ofReal_zero] using haccess)

/-- The retained component's chart fixes the actual current access and the
original target, and maps every compact part of the fresh continuation out by
a continuous driver. The access is supplied in any chart of that component;
it is transported to the normalized chart by the prime-end change-of-chart law.
-/
theorem exists_restart_chart_and_driver {K : Set ℂ} {η : ℝ → ℂ} {r t : ℝ} {b : ℂ}
    (hr : 0 ≤ r) (hrt : r < t) (hKo : IsOpen (H \ K))
    (hKu : ∀ z ∈ LocalSets.lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion K) z))
    (hc : ContinuousOn η (Icc 0 t)) (hi : InjOn η (Icc 0 t)) (h0 : η 0 = 0)
    (hb : b ∈ retainedDomain K η r)
    (hnew : MapsTo η (Ioc r t) (restartComponent K η r b))
    (ψ : HChart (restartComponent K η r b)) (p : OnePoint ℝ)
    (target : PrimeEnd (restartComponent K η r b))
    (hne : PrimeEnd.mk ψ p ≠ target)
    (haccess : Tendsto (ψ.1 ∘ η) (𝓝[>] r) (PrimeEnd.approachH p)) :
    ∃ φ : HChart (restartComponent K η r b),
      PrimeEnd.mk φ (0 : ℝ) = PrimeEnd.mk ψ p ∧ PrimeEnd.mk φ OnePoint.infty = target ∧
      Tendsto (φ.1 ∘ η) (𝓝[>] r) (𝓝 0) ∧
      ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ,
        σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 (t - r)) ∧ ContinuousOn σ (Icc 0 (t - r)) ∧
          ∀ u ∈ Icc 0 (t - r), 0 ≤ σ u ∧
            QuantumZipper.fwdHull W (σ u) = landingSlit (φ.1 ∘ η) r 0 '' Ioc 0 u ∧
            IsMapOut (landingSlit (φ.1 ∘ η) r 0 '' Ioc 0 u)
              (fun z => QuantumZipper.fwdMap W (σ u) z + W (σ u)) := by
  have hcr := hc.mono (Icc_subset_Icc_right hrt.le)
  obtain ⟨φ, hseed, htarget⟩ :=
    exists_restart_targetChart hr hKo hKu hcr h0 hb (PrimeEnd.mk ψ p) target hne
  have hnew' : ∀ᶠ u in 𝓝[>] r, η u ∈ restartComponent K η r b :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hrt) fun u hu => hnew hu
  have hlim := tendsto_comp_of_primeEnd_eq (isOpen_retainedDomain hKo hcr).connectedComponentIn
    hseed hnew' haccess
  have hlim0 : Tendsto (φ.1 ∘ η) (𝓝[>] r) (𝓝 0) :=
    hlim.mono_right nhdsWithin_le_nhds
  refine ⟨φ, hseed, htarget, hlim0, exists_driver_of_charted_continuation φ hrt
    (hc.mono ?_) (hi.mono ?_) hnew hlim0⟩
  all_goals intro u hu; exact ⟨hr.trans hu.1.le, hu.2⟩

end InteractingSLE.Sec5.Aux61Restart
