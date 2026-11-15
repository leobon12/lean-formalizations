/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdentBoundary
import LQGMetric.Complex.HarmonicComp

/-!
# The remaining analytic obligation and the finite-boundary uniqueness argument

Packet PROVE-G7A-MEANIDENT. `AliveGreenRegularityStatement` is an explicit
UNPROVED analytic input: the Dirichlet correction of a smooth compactly
supported function on the active domain is bounded harmonic and attains its
continuous boundary values in the inverse chart. Its source is restricted to
the active domain. The comparison theorem below discharges the geometric,
finite-word boundary and uniqueness steps from this input.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Restart.FlowLocalityGen
open FlowStopIdentCMI

/-- The active-domain Green potential of the cutoff's Laplacian density. -/
def aliveGreenPot (F : CMCut) (w : ℝ → ℝ) (t : ℝ) : ℂ → ℝ :=
  GB7a.greenPot w ((H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f)) t

/-- The harmonic Dirichlet correction, expressed in the inverse chart. -/
def greenCorrection (F : CMCut) (w : ℝ → ℝ) (t : ℝ) (Ψ : ℂ → ℂ) (ξ : ℂ) : ℝ :=
  F.f (Ψ ξ) - aliveGreenPot F w t (Ψ ξ)

/-- **Unproved analytic input**, isolated from the finite-word identity.
This is the classical Green Dirichlet representation for a smooth compact
cutoff on a Loewner domain admitting a continuous inverse-chart extension.
It neither assumes a mean identity nor requires the source to avoid the hull. -/
def AliveGreenRegularityStatement : Prop :=
  ∀ w : ℝ → ℝ, Continuous w → w 0 = 0 → ∀ t : ℝ, 0 ≤ t →
    ∀ (F : CMCut) (Ψ : ℂ → ℂ), EqOn Ψ (fwdMapInv w t) H → ContinuousOn Ψ Hbar →
      InnerProductSpace.HarmonicOnNhd (greenCorrection F w t Ψ) H ∧
        Bornology.IsBounded (greenCorrection F w t Ψ '' H) ∧
        ∀ x : ℝ, Tendsto (greenCorrection F w t Ψ) (𝓝[H] (x : ℂ)) (𝓝 (F.f (Ψ x)))

/-- The finite-word mean comparison from active-domain Green regularity.
The marks may be swallowed: only their geometric images occur in `h`. -/
theorem geomArgSum_ident_of_greenRegularity (hreg : AliveGreenRegularityStatement)
    {ι : Type*} [Fintype ι] {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {t : ℝ} (ht : 0 < t) {η : ℝ → ℂ} (hη : ContinuousOn η (Icc 0 t))
    (hfill : fwdHull w t = fillH (η '' Icc 0 t))
    (p c : ι → ℝ) (c₀ : ℝ) (hp : ∀ j, p j ≠ 0)
    (hseed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0)
    {N : Set ℂ} (hNo : IsOpen N) (h0N : (0 : ℂ) ∈ N)
    (hηN : ∀ s ∈ Icc 0 t, η s ∈ N) (F : CMCut) {q h : ℂ → ℝ}
    (hq : InnerProductSpace.HarmonicOnNhd q H) (hqb : Bornology.IsBounded (q '' H))
    (hqa : EqOn q (GB7a.argSum0 p c c₀) H)
    (hh : InnerProductSpace.HarmonicOnNhd h H) (hhb : Bornology.IsBounded (h '' H))
    (hha : EqOn h (GB7a.argSum0 (fun j => geomImage w t (p j)) c c₀) H)
    (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z) {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    h (fwdMap w t z) = q z - F.f z + aliveGreenPot F w t z := by
  classical
  obtain ⟨Ψ, hΨeq, hΨc, hΨR⟩ := GB7a.exists_extension_of_trace hw hw0 ht.le hη hfill
  obtain ⟨hC, hCb, hClim⟩ := hreg w hw hw0 t ht.le F Ψ hΨeq hΨc
  have hΨH : MapsTo Ψ H H := fun ξ hξ => by
    rw [hΨeq hξ]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht.le hξ).1
  have hΨd : DifferentiableOn ℂ Ψ H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hw hw0 ht.le).congr hΨeq
  have hqΨ : InnerProductSpace.HarmonicOnNhd (fun ξ => q (Ψ ξ)) H :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hq hΨd hΨH
  set R : ℂ → ℝ := fun ξ => h ξ + greenCorrection F w t Ψ ξ - q (Ψ ξ) with hRdef
  have hRh : InnerProductSpace.HarmonicOnNhd R H := (hh.add hC).sub hqΨ
  obtain ⟨Bh, hBh⟩ := isBounded_iff_forall_norm_le.1 hhb
  obtain ⟨BC, hBC⟩ := isBounded_iff_forall_norm_le.1 hCb
  obtain ⟨Bq, hBq⟩ := isBounded_iff_forall_norm_le.1 hqb
  have hRb : Bornology.IsBounded (R '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨Bh + BC + Bq, ?_⟩
    rintro _ ⟨ξ, hξ, rfl⟩
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add (hBh _ ⟨ξ, hξ, rfl⟩) (hBC _ ⟨ξ, hξ, rfl⟩))
        (hBq _ ⟨Ψ ξ, hΨH hξ, rfl⟩)))
  let E : Finset ℝ := Finset.univ.image (fun j => geomImage w t (p j))
  have hlim : ∀ x : ℝ, x ∉ E → Tendsto (fun ξ => R ξ - (0 : ℝ))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    have hxp : ∀ j, x ≠ geomImage w t (p j) := fun j he =>
      hx (Finset.mem_image.2 ⟨j, Finset.mem_univ _, he.symm⟩)
    have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    have hΨlim : Tendsto Ψ (𝓝[H] (x : ℂ)) (𝓝 (Ψ x)) :=
      ((hΨc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
    have hhcongr : h =ᶠ[𝓝[H] (x : ℂ)]
        GB7a.argSum0 (fun j => geomImage w t (p j)) c c₀ := by
      filter_upwards [self_mem_nhdsWithin] with ξ hξ using hha hξ
    by_cases hA : ∃ a : ℝ, Ψ x = a ∧ ∃ u, IsForwardSol w (a : ℂ) t u
    · obtain ⟨a, hΨa, u, hu⟩ := hA
      have hut := chart_eq_of_extension_eq_of_alive hw hw0 ht.le hΨeq hΨc hΨa hu
      have hpa : ∀ j, a ≠ p j := by
        intro j he
        have hg : (geomImage w t (p j) : ℂ) = u t := by
          unfold geomImage
          split_ifs with hj
          · exact (geomL_eq_fwdMap hw hw0 ht.le hj (he ▸ hu)).trans
              (Zhan.fwdMap_ofReal_eq hw ht.le (he ▸ hu))
          · have hj0 := hp j
            exact (geomR_eq_fwdMap hw hw0 ht.le
              (lt_of_le_of_ne (not_lt.1 hj) hj0.symm) (he ▸ hu)).trans
              (Zhan.fwdMap_ofReal_eq hw ht.le (he ▸ hu))
        exact hxp j (Complex.ofReal_injective (hg.trans hut)).symm
      have hhlim := (tendsto_geomArgSum_of_alive hw hw0 ht.le p c c₀ hu hut hxp).congr' hhcongr.symm
      have hΨwithin : Tendsto Ψ (𝓝[H] (x : ℂ)) (𝓝[H] (a : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hΨa ▸ hΨlim, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ξ hξ using hΨH hξ
      have hqlim := (tendsto_argSum0 p c c₀ a hpa).comp hΨwithin
      have hqcongr : (fun ξ => GB7a.argSum0 p c c₀ (Ψ ξ)) =ᶠ[𝓝[H] (x : ℂ)]
          fun ξ => q (Ψ ξ) := by
        filter_upwards [self_mem_nhdsWithin] with ξ hξ using (hqa (hΨH hξ)).symm
      have hFzero : F.f (Ψ x) = 0 := by
        rw [hΨa]
        have ho := F.odd (a : ℂ)
        rw [Complex.conj_ofReal] at ho
        linarith
      have hc := hClim x
      rw [hFzero] at hc
      have hl := (hhlim.add hc).sub (hqlim.congr' hqcongr)
      simp only [add_zero, sub_self] at hl
      simpa only [hRdef, sub_zero] using hl
    · have hΨN := extension_mem_buffer_of_not_alive hw hw0 ht.le hη hfill h0N hηN hΨeq hΨc hΨR hA
      have hb := geom_seed_bounds_of_not_alive hw hw0 ht.le hΨeq hΨc hA
      have hhlim := (tendsto_geomArgSum_of_seed_bounds hw ht.le p c c₀ hp hseed
        hb.1 hb.2 hxp).congr' hhcongr.symm
      have hqFlim : Tendsto (fun ξ => q (Ψ ξ)) (𝓝[H] (x : ℂ)) (𝓝 (F.f (Ψ x))) := by
        have hFcont := F.smooth.continuous.tendsto (Ψ x)
        have heq : (fun ξ => F.f (Ψ ξ)) =ᶠ[𝓝[H] (x : ℂ)] fun ξ => q (Ψ ξ) := by
          filter_upwards [hΨlim (hNo.mem_nhds hΨN), self_mem_nhdsWithin] with ξ hξN hξ
          exact hFq _ hξN (hΨH hξ)
        exact (hFcont.comp hΨlim).congr' heq
      have hl := (hhlim.add (hClim x)).sub hqFlim
      simp only [zero_add, sub_self] at hl
      simpa only [hRdef, sub_zero] using hl
  have hzero : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (0 : ℝ)) H :=
    fun _ _ => InnerProductSpace.harmonicAt_const 0
  have heq := eqOn_of_tendsto_sub_H E hRh hzero hRb
    (isBounded_iff_forall_norm_le.2 ⟨0, by rintro _ ⟨ξ, _, rfl⟩; simp only [norm_zero, le_refl]⟩) hlim
  have hfz := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht.le hz
  have hzΨ : Ψ (fwdMap w t z) = z := by
    rw [hΨeq hfz, QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 ht.le hz]
  have hzR := heq hfz
  change h (fwdMap w t z) + (F.f (Ψ (fwdMap w t z)) -
    aliveGreenPot F w t (Ψ (fwdMap w t z))) - q (Ψ (fwdMap w t z)) = 0 at hzR
  rw [hzΨ] at hzR
  linarith

end InteractingSLE.Restart.FlowLocalityGen
