/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinClock

/-!
# The relative surviving domain is the selected target component

PROVE-R7-GAPEQ. Adapt the landed Aux. 41 range argument to a single component of
`C ∩ D_s` adhering to the pocket target. Other ambient components may survive in forbidden
outer bulges. The conformal image identity requires no connectedness of all of `C ∩ D_s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec7.R7GapEqGeo

open Sec6 R7StopIn R7GapEqFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The target-component form of (GC2).** A component of the ambient surviving part of
the pocket which adheres to its target maps exactly to the surviving relative domain.
The proof generalizes the landed contained-pocket `image_inter_domain` argument. -/
theorem image_target_component (hP : IsErasurePocket η C x₀ y₀ τ σ)
    (hη : IsLoewnerTrace W η)
    (hCH : C ⊆ H) (hψ : IsJordanCoord C x₀ y₀ ψ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (pocketClock η C τ σ σ)) {q : ℂ} {E : Set ℂ}
    (hE : E = connectedComponentIn (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) q)
    (hxcl : x₀ ∈ closure E) :
    ψ '' E = H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u) := by
  let s := pocketFibre η C τ σ u
  let ζ := fun v => ψ (erasedPath η C τ σ v)
  let D := H \ fwdHull W s
  have hs0 : 0 ≤ s := hP.nonneg.trans (hP.fibre_mem u).1
  have hsub : Icc (0 : ℝ) u ⊆ Ico 0 (pocketClock η C τ σ σ) :=
    fun v hv => ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hCsub : C ⊆ closure C \ {x₀} := fun z hz =>
    ⟨subset_closure hz, fun he => hP.notMem_x (he ▸ hz)⟩
  have hζc : ContinuousOn ζ (Icc 0 u) := hψ.1.comp
    (hP.continuousOn_erasedPath.mono fun v hv => ⟨hv.1, hv.2.trans hu.2.le⟩)
    fun v hv => hP.erasedPath_mem (hsub hv)
  have hζ0 : ζ 0 = 0 := by
    dsimp [ζ]
    rw [hP.erasedPath_zero]
    exact hψ.2.2.2.2.2.1
  have hcpt : IsCompact (ζ '' Icc 0 u) := isCompact_Icc.image_of_continuousOn hζc
  have hEC : E ⊆ C ∩ D := hE ▸ connectedComponentIn_subset _ _
  have hpre : IsPreconnected E := hE ▸ isPreconnected_connectedComponentIn
  have hGC2 := hP.erasedPath_image_inter (u := u) ⟨hu.1, hu.2.le⟩
  have hfwd : ψ '' E ⊆ H \ fillH (ζ '' Icc 0 u) := by
    refine subset_H_diff_fillH_of_isPreconnected hcpt.isBounded
      (hpre.image _ (hψ.1.mono fun z hz => hCsub (hEC hz).1)) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψ.2.2.2.1.2.mapsTo (hEC hz).1, fun hcl => ?_⟩
      rw [hcpt.isClosed.closure_eq] at hcl
      obtain ⟨v, hv, hvz⟩ := hcl
      have hzv : erasedPath η C τ σ v = z :=
        hψ.2.1 (hP.erasedPath_mem (hsub hv)) (hCsub (hEC hz).1) hvz
      have hzR : z ∈ η '' Icc 0 s := by
        have hm : z ∈ erasedPath η C τ σ '' Icc 0 u ∩ C := ⟨⟨v, hv, hzv⟩, (hEC hz).1⟩
        rw [hGC2] at hm
        exact hm.1
      exact (hEC hz).2.2 (mem_fwdHull_of_mem_trace hη hs0 (hEC hz).2.1 hzR)
    · intro hb
      have : (𝓝[E] x₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
      have ht : Tendsto ψ (𝓝[E] x₀) (cobounded ℂ) := hψ.2.2.2.2.2.2.mono_left
        (nhdsWithin_mono _ fun z hz => hCsub (hEC hz).1)
      obtain ⟨z, hzb, hz⟩ := ((ht.eventually (isBounded_def.1 hb)).and self_mem_nhdsWithin).exists
      exact hzb ⟨z, hz, rfl⟩
  refine Subset.antisymm hfwd ?_
  let e := QuantumZipper.CA.univalentOPH hP.isOpen hψ.2.2.2.1.1 hψ.2.2.2.1.2.injOn
  have htarget : e.target = H := by
    dsimp only [e]
    rw [QuantumZipper.CA.univalentOPH_target]
    exact hψ.2.2.2.1.2.image_eq
  have hsymmC : MapsTo e.symm H C := fun w hw => by
    have hm := e.map_target (htarget ▸ hw)
    dsimp only [e] at hm
    rwa [QuantumZipper.CA.univalentOPH_source] at hm
  have hψe : ∀ w ∈ H, ψ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hP.isOpen hψ.2.2.2.1.1 hψ.2.2.2.1.2.injOn
      (by rw [hψ.2.2.2.1.2.image_eq]; exact hw)
  have hK : IsHPHull (fillH (ζ '' Icc 0 u)) :=
    YuanCharacterisation.isHPHull_fillH_image hζc hu.1 hζ0
  let P := e.symm '' (H \ fillH (ζ '' Icc 0 u))
  have hPpre : IsPreconnected P := hK.isConnected.isPreconnected.image _
    ((htarget ▸ e.continuousOn_symm).mono sdiff_subset)
  have hPC : P ⊆ C := by rintro _ ⟨w, hw, rfl⟩; exact hsymmC hw.1
  have hPR : Disjoint P (η '' Icc 0 s) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hR
    have hm : e.symm w ∈ η '' Icc 0 s ∩ C := ⟨hR, hsymmC hw.1⟩
    rw [← hGC2] at hm
    obtain ⟨⟨v, hv, hve⟩, -⟩ := hm
    have hwζ : w ∈ ζ '' Icc 0 u := ⟨v, hv, by dsimp [ζ]; rw [hve, hψe w hw.1]⟩
    exact hw.2 ⟨hw.1, Or.inl (subset_closure hwζ)⟩
  obtain ⟨z₀, hz₀⟩ : E.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    rw [hn, closure_empty] at hxcl
    exact hxcl
  have hz₀P : z₀ ∈ P := ⟨ψ z₀, hfwd ⟨z₀, hz₀, rfl⟩,
    QuantumZipper.CA.univalentOPH_symm_apply_apply hP.isOpen hψ.2.2.2.1.1
      hψ.2.2.2.1.2.injOn (hEC hz₀).1⟩
  have hPD : P ⊆ D := subset_domain_of_isPreconnected hη hs0 hPpre (hPC.trans hCH)
    hPR hz₀P (hEC hz₀).2
  have hPE : P ⊆ E := by
    rw [hE, connectedComponentIn_eq (hE ▸ hz₀)]
    exact hPpre.subset_connectedComponentIn hz₀P fun z hz => ⟨hPC hz, hPD hz⟩
  intro w hw
  exact ⟨e.symm w, hPE ⟨w, hw, rfl⟩, hψe w hw.1⟩

end InteractingSLE.Sec7.R7GapEqGeo
