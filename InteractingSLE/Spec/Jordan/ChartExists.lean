/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Chart
import InteractingSLE.Spec.Sec6.Aux36Jordan
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Existence of domain charts; Jordan domains

Packet PROVE-JORDANCPL. Specification p. 2: a conformal coordinate comes with "the chosen analytic logarithm of
`ψ′`"; "boundary markings used in conformal maps are prime ends. Their Euclidean realizations require the stated
boundary-extension hypotheses, automatic for Jordan domains."

## Main results

* `IsDerivLog.congr_of_eqOn`: an analytic logarithm of `ψ′` is one of `φ′` when `φ = ψ` on the open set;
* **`exists_isDomainChart_of_isConformalBijection`**: every conformal bijection `ψ : D → ℍ` of an open `D ⊆ ℍ` is
  the forward map of a chart of `D` (inverse `invFunOn ψ D`; the lift is `Im` of an analytic logarithm of `ψ′`,
  obtained from a logarithm of `(ψ⁻¹)′` on the simply connected `ℍ` and the inverse-lift rule `L_ψ = −L_{ψ⁻¹} ∘ ψ`);
* **`exists_isDomainChart_of_isJordanCurve`**: a bounded Jordan domain `D ⊆ ℍ` with two boundary points `x₀, y₀` has
  a chart whose inverse extends continuously to `ℍ̄`, and whose prime ends at `0` and `∞` are realized at `y₀` and
  `x₀` (from PROVE-AUX36-41C's Jordan coordinate `Sec6.exists_jordanCoord`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function Bornology
open QuantumZipper (H Hbar isOpen_H)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric.JordanMap (IsJordanCurve)

namespace InteractingSLE

/-- An analytic logarithm of `ψ′` on an open set is one of `φ′` if `φ = ψ` there. -/
theorem IsDerivLog.congr_of_eqOn {ψ φ L : ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D) (hL : IsDerivLog ψ L D)
    (he : EqOn ψ φ D) : IsDerivLog φ L D :=
  ⟨hL.1, fun z hz => by
    rw [hL.2 z hz]
    exact (Filter.eventuallyEq_of_mem (hDo.mem_nhds hz) he).deriv_eq⟩

/-- **Every conformal bijection of an open `D ⊆ ℍ` onto `ℍ` is the forward map of a chart of `D`**, with inverse
`invFunOn ψ D` and a lift `Im L` for an analytic logarithm `L` of `ψ′`. -/
theorem exists_isDomainChart_of_isConformalBijection {D : Set ℂ} {ψ : ℂ → ℂ} (hDo : IsOpen D) (hDH : D ⊆ H)
    (hψ : IsConformalBijection ψ D H) : ∃ c : Chart, c.1 = ψ ∧ c.2.1 = invFunOn ψ D ∧ IsDomainChart D c := by
  set inv := invFunOn ψ D with hinv
  have hinv_mem : ∀ w ∈ H, inv w ∈ D := fun w hw => (invFunOn_pos (hψ.2.surjOn hw)).1
  have hψinv : ∀ w ∈ H, ψ (inv w) = w := fun w hw => (invFunOn_pos (hψ.2.surjOn hw)).2
  have hinvψ : ∀ z ∈ D, inv (ψ z) = z := fun z hz => hψ.2.injOn.leftInvOn_invFunOn hz
  have hdiff : DifferentiableOn ℂ inv H := by
    have h := SmallGammaGeodesics.CC.differentiableOn_leftInv hDo hψ.1 hψ.2.injOn hinvψ
    rwa [hψ.2.image_eq] at h
  have hinj : InjOn inv H := fun w₁ hw₁ w₂ hw₂ he => by rw [← hψinv w₁ hw₁, he, hψinv w₂ hw₂]
  have himg : inv '' H = D := by
    refine Subset.antisymm (fun _ ⟨w, hw, he⟩ => he ▸ hinv_mem w hw) fun z hz =>
      ⟨ψ z, hψ.2.mapsTo hz, hinvψ z hz⟩
  -- a logarithm `M` of `inv′` on the simply connected `ℍ`, and the inverse lift `−M ∘ ψ`
  obtain ⟨M, hM⟩ := exists_isDerivLog isOpen_H isSimplyConnected_H hdiff
    fun w hw => QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_H hdiff hinj hw
  have hinvbij : IsConformalBijection inv H D := ⟨hdiff, himg ▸ hinj.bijOn_image⟩
  have hL := hM.invFunOn isOpen_H hinvbij
  have heq : EqOn (invFunOn inv H) ψ D := fun z hz => by
    obtain ⟨w, hw, rfl⟩ := himg.symm ▸ hz
    rw [hinj.leftInvOn_invFunOn hw, hψinv w hw]
  have hLψ : IsDerivLog ψ (fun z => -M (invFunOn inv H z)) D := hL.congr_of_eqOn hDo heq
  refine ⟨(ψ, inv, fun z => (-M (invFunOn inv H z)).im), rfl, rfl,
    ⟨hdiff, fun w hw => hDH (hinv_mem w hw), hψinv⟩, himg, _, hLψ, fun _ _ => rfl⟩

/-- **Charts of a bounded Jordan domain** `D ⊆ ℍ` with boundary points `x₀, y₀`: a chart of `D` whose inverse extends
continuously to `ℍ̄` (with values in `D̄ \ {x₀}`), and whose prime ends marked by `0` and `∞` are realized at `y₀`
and at `x₀` (Specification p. 2: Euclidean realizations are "automatic for Jordan domains"). -/
theorem exists_isDomainChart_of_isJordanCurve {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) (hDH : connectedComponentIn Γᶜ p ⊆ H) {x₀ y₀ : ℂ}
    (hx₀ : x₀ ∈ Γ) (hy₀ : y₀ ∈ Γ) (hxy : x₀ ≠ y₀) :
    ∃ (c : Chart) (hc : IsDomainChart (connectedComponentIn Γᶜ p) c),
      (∃ ψinv : ℂ → ℂ, ContinuousOn ψinv Hbar ∧
        MapsTo ψinv Hbar (closure (connectedComponentIn Γᶜ p) \ {x₀}) ∧ EqOn c.2.1 ψinv H) ∧
      (PrimeEnd.mk hc.hChart ((0 : ℝ) : OnePoint ℝ)).IsRealizedAt y₀ ∧
      (PrimeEnd.mk hc.hChart OnePoint.infty).IsRealizedAt x₀ := by
  set D := connectedComponentIn Γᶜ p with hDdef
  have hHb : ∀ w ∈ H, w ∈ Hbar := fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt hw
  have hDo : IsOpen D :=
    (Foundations.Schoenflies.isCompact_of_isJordanCurve hΓ).isClosed.isOpen_compl.connectedComponentIn
  have hfrontΓ : frontier D = Γ := (Foundations.Schoenflies.jordan_split hΓ hp hb).1
  obtain ⟨ψ, ψinv, hψc, hψm, hic, him, hiψ, hψi, hψ, hΓre, hy0, hψx⟩ :=
    Sec6.exists_jordanCoord hΓ hp hb hx₀ hy₀
  obtain ⟨c, hc1, hc2, hc⟩ := exists_isDomainChart_of_isConformalBijection hDo hDH hψ
  have hfront : frontier D ⊆ Γ := hfrontΓ.le
  -- `ψinv` maps `ℍ` into `D`, and agrees there with the chart inverse
  have him_H : ∀ w ∈ H, ψinv w ∈ D := by
    intro w hw
    have hm := him (hHb w hw)
    by_contra hnot
    have hfr : ψinv w ∈ frontier D := ⟨hm.1, by rw [hDo.interior_eq]; exact hnot⟩
    have hre := hΓre (ψinv w) ⟨hfront hfr, hm.2⟩
    rw [hψi w (hHb w hw)] at hre
    exact (ne_of_gt hw) hre
  have heqH : EqOn c.2.1 ψinv H := fun w hw => by
    rw [hc2]
    have h1 : ψ (ψinv w) = w := hψi w (hHb w hw)
    have h2 := hψ.2.injOn.leftInvOn_invFunOn (him_H w hw)
    rw [← h2, h1]
  have hhc : hc.hChart.1 = ψ := hc1
  refine ⟨c, hc, ⟨ψinv, hic, him, heqH⟩, ⟨hc.hChart, _, rfl, ?_⟩, ⟨hc.hChart, _, rfl, ?_⟩⟩
  · -- the prime end at `0` is realized at `y₀ = ψinv 0`
    rw [PrimeEnd.approachH_coe, hhc, ← hc2]
    have hy₀cl : y₀ ∈ closure D \ {x₀} :=
      ⟨(hfrontΓ.symm ▸ hy₀ : y₀ ∈ frontier D).1, hxy.symm⟩
    have hval : ψinv ((0 : ℝ) : ℂ) = y₀ := by
      rw [Complex.ofReal_zero, ← hy0, hiψ y₀ hy₀cl]
    have h0 : ((0 : ℝ) : ℂ) ∈ Hbar := by simp [Hbar]
    have ht : Tendsto ψinv (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 y₀) :=
      hval ▸ (hic _ h0).mono_left (nhdsWithin_mono _ hHb)
    exact ht.congr' (eventually_nhdsWithin_of_forall fun w hw => (heqH hw).symm)
  · -- the prime end at `∞` is realized at `x₀`: off a ball around `x₀`, `ψ` is bounded on the compact `D̄`
    rw [PrimeEnd.approachH_infty, hhc, ← hc2, Metric.tendsto_nhds]
    intro ε hε
    have hK : IsCompact (closure D) := hb.isCompact_closure
    set K := closure D ∩ (Metric.ball x₀ ε)ᶜ with hKdef
    have hKc : IsCompact K := hK.inter_right Metric.isOpen_ball.isClosed_compl
    have hKsub : K ⊆ closure D \ {x₀} := fun z hz =>
      ⟨hz.1, fun he => hz.2 (by rw [mem_singleton_iff.1 he]; exact Metric.mem_ball_self hε)⟩
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hψc.mono hKsub)
    have hev : ∀ᶠ w in cobounded ℂ, M < ‖w‖ := tendsto_norm_cobounded_atTop.eventually_gt_atTop M
    filter_upwards [mem_inf_of_left hev, mem_inf_of_right (mem_principal_self H)] with w hw hwH
    by_contra hd
    have hwK : c.2.1 w ∈ K := ⟨subset_closure (hc.inv_mem hwH), fun hb' => hd (Metric.mem_ball.1 hb')⟩
    have hb' := hM _ hwK
    rw [heqH hwH, hψi w (hHb w hwH)] at hb'
    exact absurd hw (not_lt.2 hb')

end InteractingSLE
