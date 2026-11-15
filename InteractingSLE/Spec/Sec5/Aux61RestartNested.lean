import InteractingSLE.Spec.Sec5.Aux61RestartAccess
import InteractingSLE.Spec.Sec5.Aux61RestartChart

/-!
# The original-target restart driver in a nested-hull coordinate

Packet PROVE-AUX61-R1; ruling R71. This assembles the own-chart access and
finite-slit driver results. The larger hull `B` is the filling of the retained
sets in a coordinate with the original target at infinity. Its complement must
be the selected target component. The half-disc condition states exactly that
the current access is in this component.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Restart

/-- The restart chart and driver from the actual own inverse-chart collar in
the original target component. The positive-time continuation is a simple slit;
the target is the same hydrodynamic prime end as that of the retained hull. -/
theorem exists_restart_driver_of_nested_hulls {W : ℝ → ℝ} {η : ℝ → ℂ} {r t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hr : 0 ≤ r) (hrt : r < t) {B : Set ℂ} (hB : IsHPHull B)
    (hAB : fwdHull W r ⊆ B) (hi : InjOn η (Ioc r t))
    (hnew : MapsTo η (Ioc r t) (H \ B))
    (hcollar : ∃ δ > 0, MapsTo (fwdMapInv W r) (ball 0 δ ∩ H) (H \ B)) :
    ∃ (ψ φ : HChart (H \ B)) (x : ℝ), IsMapOut B ψ.1 ∧
      PrimeEnd.mk φ (0 : ℝ) = PrimeEnd.mk ψ (x : OnePoint ℝ) ∧
      PrimeEnd.mk φ OnePoint.infty = PrimeEnd.mk ψ OnePoint.infty ∧
      Tendsto (φ.1 ∘ η) (𝓝[>] r) (𝓝 0) ∧
      ∃ U : ℝ → ℝ, Continuous U ∧ U 0 = 0 ∧ ∃ σ : ℝ → ℝ,
        σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 (t - r)) ∧ ContinuousOn σ (Icc 0 (t - r)) ∧
          ∀ u ∈ Icc 0 (t - r), 0 ≤ σ u ∧
            fwdHull U (σ u) = landingSlit (φ.1 ∘ η) r 0 '' Ioc 0 u ∧
            IsMapOut (landingSlit (φ.1 ∘ η) r 0 '' Ioc 0 u)
              (fun z => fwdMap U (σ u) z + U (σ u)) := by
  have hA := isHPHull_fwdHull hW hr
  have hg := isMapOut_fwdMap hW hW0 hr
  have hF := isConformalBijection_fwdMapInv hW hW0 hr
  obtain ⟨ψ, x, hψ, haccess⟩ := exists_chart_access_of_nested_hulls hA hB hAB hg
    hF.2.mapsTo (a := W r) (fun w hw => by
      rw [QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hr hw]) hcollar
  have hηevent : ∀ᶠ u in 𝓝[>] r, η u ∈ H \ B :=
    Filter.mem_of_superset (Ioc_mem_nhdsGT hrt) fun u hu => hnew hu
  have hηown : ∀ᶠ u in 𝓝[>] r, η u ∈ H \ fwdHull W r :=
    hηevent.mono fun u hu => ⟨hu.1, fun ha => hu.2 (hAB ha)⟩
  have hown := tendsto_own_chart_at_restart hW hW0 hη hr hηown
  have hψη : Tendsto (ψ.1 ∘ η) (𝓝[>] r) (PrimeEnd.approachH (x : OnePoint ℝ)) := by
    refine (haccess.comp hown).congr' ?_
    filter_upwards [hηown] with u hu
    simp only [Function.comp_apply, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hr hu]
  have hne : PrimeEnd.mk ψ (x : OnePoint ℝ) ≠ PrimeEnd.mk ψ OnePoint.infty := by
    intro heq
    have := PrimeEnd.mk_injective ψ heq
    simp only [OnePoint.coe_ne_infty] at this
  obtain ⟨φ, hseed, htarget⟩ := exists_hChart_marking hB.isOpen ψ
    (PrimeEnd.mk ψ (x : OnePoint ℝ)) (PrimeEnd.mk ψ OnePoint.infty) hne
  have hφlim : Tendsto (φ.1 ∘ η) (𝓝[>] r) (𝓝 0) :=
    (tendsto_comp_of_primeEnd_eq hB.isOpen hseed hηevent hψη).mono_right nhdsWithin_le_nhds
  refine ⟨ψ, φ, x, hψ, hseed, htarget, hφlim,
    exists_driver_of_charted_continuation φ hrt (hη.2.1.mono ?_) hi hnew hφlim⟩
  intro u hu
  exact hr.trans hu.1.le

end InteractingSLE.Sec5.Aux61Restart
