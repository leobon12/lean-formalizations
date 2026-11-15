import InteractingSLE.Spec.Sec5.Aux61RestartMeas
import InteractingSLE.Spec.Sec5.Aux61RestartChart

/-!
# Measurable normalization at the current access and original target

Packet PROVE-AUX61-R1; ruling R71. The two recorded approach sequences must
approach distinct prime ends of the actual retained component. This is genuine
marking data; Euclidean convergence alone would not specify the correct access.
Given that data, the existing measurable two-point chart supplies the forward
map, inverse, and derivative-argument lift.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

open LocalSets
open Sec7.Lemma71E

/-- Two recorded sequences approach distinct prime ends. The describing chart
is arbitrary; the conclusion is the normalized zero/infinity chart. -/
theorem exists_normalized_chart_of_approaches {D : Set ℂ} (hDo : IsOpen D)
    {x y : ℕ → ℂ} (hxD : ∀ n, x n ∈ D) (hyD : ∀ n, y n ∈ D)
    (hpair : ∃ ψ : HChart D, ∃ p q : OnePoint ℝ, p ≠ q ∧
      Tendsto (ψ.1 ∘ x) atTop (PrimeEnd.approachH p) ∧
      Tendsto (ψ.1 ∘ y) atTop (PrimeEnd.approachH q)) :
    ∃ φ : ℂ → ℂ, IsConformalBijection φ D H ∧
      Tendsto (φ ∘ x) atTop (𝓝 0) ∧ Tendsto (fun n => ‖φ (y n)‖) atTop atTop := by
  obtain ⟨ψ, p, q, hpq, hx, hy⟩ := hpair
  have hne : PrimeEnd.mk ψ p ≠ PrimeEnd.mk ψ q := fun heq =>
    hpq (PrimeEnd.mk_injective ψ heq)
  obtain ⟨φ, hseed, htarget⟩ :=
    exists_hChart_marking hDo ψ (PrimeEnd.mk ψ p) (PrimeEnd.mk ψ q) hne
  have h0 := tendsto_comp_of_primeEnd_eq hDo hseed (Eventually.of_forall hxD) hx
  have hinf := tendsto_comp_of_primeEnd_eq hDo htarget (Eventually.of_forall hyD) hy
  exact ⟨φ.1, φ.2, h0.mono_right nhdsWithin_le_nhds,
    tendsto_norm_cobounded_atTop.comp (hinf.mono_right inf_le_left)⟩

/-- The measurable half-plane restart chart, including a continuous derivative
logarithm, from recorded approaches to the current access and original target.
The remaining marking hypothesis states prime-end convergence explicitly.
No determination theorem or conditional independence is used. -/
theorem exists_measurable_restart_targetChart_of_approaches
    {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ} {η : Ω → ℝ → ℂ}
    {r : ℝ} (hr : 0 ≤ r) (hKo : ∀ ω, IsOpen (H \ K ω))
    (hKu : ∀ ω z, z ∈ lowerUnion (K ω) →
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    (hKm : ∀ c ρ, MeasurableSet {ω | closedBall c ρ ⊆ H \ K ω})
    (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 r)) (h0 : ∀ ω, η ω 0 = 0)
    (hm : ∀ t ∈ Icc 0 r, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) {N : Ω → ℕ} (hN : Measurable N)
    (hb : ∀ ω, e (N ω) ∈ retainedDomain (K ω) (η ω) r)
    {Nx Ny : ℕ → Ω → ℕ} (hNx : ∀ n, Measurable (Nx n)) (hNy : ∀ n, Measurable (Ny n))
    (hxD : ∀ n ω, e (Nx n ω) ∈ restartComponent (K ω) (η ω) r (e (N ω)))
    (hyD : ∀ n ω, e (Ny n ω) ∈ restartComponent (K ω) (η ω) r (e (N ω)))
    (hpair : ∀ ω, ∃ ψ : HChart (restartComponent (K ω) (η ω) r (e (N ω))),
      ∃ p q : OnePoint ℝ, p ≠ q ∧
        Tendsto (fun n => ψ.1 (e (Nx n ω))) atTop (PrimeEnd.approachH p) ∧
        Tendsto (fun n => ψ.1 (e (Ny n ω))) atTop (PrimeEnd.approachH q)) :
    ∃ c : Ω → Chart,
      (∀ ω, (c ω).IsConformal) ∧
      (∀ ω, ((c ω).dom : Set ℂ) = restartComponent (K ω) (η ω) r (e (N ω))) ∧
      (∀ ω, IsConformalBijection (c ω).1
        (restartComponent (K ω) (η ω) r (e (N ω))) H) ∧
      (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) ∧
      (∀ ω, ∃ L : ℂ → ℂ, IsDerivLog (c ω).1 L
        (restartComponent (K ω) (η ω) r (e (N ω))) ∧
          ∀ z ∈ restartComponent (K ω) (η ω) r (e (N ω)), (c ω).2.2 z = (L z).im) ∧
      (∀ ω, Tendsto (fun n => (c ω).1 (e (Nx n ω))) atTop (𝓝 0) ∧
        Tendsto (fun n => ‖(c ω).1 (e (Ny n ω))‖) atTop atTop) := by
  have hprops := fun ω => restartComponent_properties hr (hKo ω) (hKu ω) (hc ω) (h0 ω) (hb ω)
  have hUm := measurableSet_closedBall_subset_retainedDomain hr hKm hc hm
  have hCm := measurableSet_closedBall_subset_component
    (fun ω => isOpen_retainedDomain (hKo ω) (hc ω)) hUm hN hb
  have hnorm := fun ω => exists_normalized_chart_of_approaches (hprops ω).1
    (fun n => hxD n ω) (fun n => hyD n ω) (hpair ω)
  obtain ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, hlimits, _hunique⟩ :=
    exists_measurable_twoPointChart (fun ω => (hprops ω).1) (fun ω => (hprops ω).2.1)
      (fun ω => (hprops ω).2.2.1) (fun ω => (hprops ω).2.2.2) hCm he
      hNx hNy hxD hyD hnorm
  exact ⟨c, hconf, hdom, hbij, hdm, hfm, hlm, hlc, hL, hlimits⟩

end InteractingSLE.Sec5.Aux61Restart
