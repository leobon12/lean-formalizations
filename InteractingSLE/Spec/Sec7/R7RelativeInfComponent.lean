/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfClock

/-!
# The selected infinite component is the relative surviving domain

PROVE-R7-GAPEQ. Adapt the landed target-component GC2 proof. At infinity the
selected component is unbounded, and the proper pocket coordinate takes it to
an unbounded set. Other surviving physical components are not identified with it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- GC2 identifies the relative domain with the conformal image of any unbounded
surviving pocket component. No connectedness of the whole surviving pocket is used. -/
theorem image_unbounded_component (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η)
    (hCH : C ⊆ H) (hψ : IsJordanCoordInf C y₀ ψ)
    {u : ℝ} (hu : u ∈ Ico (0 : ℝ) (clockEnd η C τ)) {q : ℂ} {E : Set ℂ}
    (hE : E = connectedComponentIn (C ∩ (H \ fwdHull W (pocketFibreInf η C τ u))) q)
    (hunb : ¬ IsBounded E) :
    ψ '' E = H \ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u) := by
  let s := pocketFibreInf η C τ u
  let ζ := fun v => ψ (erasedPathInf η C τ v)
  let D := H \ fwdHull W s
  have hs0 : 0 ≤ s := hP.fibre_nonneg hu
  have hsub : Icc (0 : ℝ) u ⊆ Ico 0 (clockEnd η C τ) :=
    fun v hv => ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hCsub : C ⊆ closure C := subset_closure
  have hζc : ContinuousOn ζ (Icc 0 u) := hψ.1.comp
    (hP.continuousOn_erasedPath.mono hsub)
    fun v hv => hP.erasedPath_mem (hsub hv)
  have hζ0 : ζ 0 = 0 := by
    dsimp [ζ]
    rw [hP.erasedPath_zero]
    exact hψ.2.2.2.2.2.1
  have hcpt : IsCompact (ζ '' Icc 0 u) := isCompact_Icc.image_of_continuousOn hζc
  have hEC : E ⊆ C ∩ D := hE ▸ connectedComponentIn_subset _ _
  have hpre : IsPreconnected E := hE ▸ isPreconnected_connectedComponentIn
  have hGC2 := hP.erasedPath_image_inter hu
  have hfwd : ψ '' E ⊆ H \ fillH (ζ '' Icc 0 u) := by
    refine subset_H_diff_fillH_of_isPreconnected hcpt.isBounded
      (hpre.image _ (hψ.1.mono fun z hz => hCsub (hEC hz).1)) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψ.2.2.2.1.2.mapsTo (hEC hz).1, fun hcl => ?_⟩
      rw [hcpt.isClosed.closure_eq] at hcl
      obtain ⟨v, hv, hvz⟩ := hcl
      have hzv : erasedPathInf η C τ v = z :=
        hψ.2.1 (hP.erasedPath_mem (hsub hv)) (hCsub (hEC hz).1) hvz
      have hzR : z ∈ η '' Icc 0 s := by
        have hm : z ∈ erasedPathInf η C τ '' Icc 0 u ∩ C := ⟨⟨v, hv, hzv⟩, (hEC hz).1⟩
        rw [hGC2] at hm
        exact hm.1
      exact (hEC hz).2.2 (mem_fwdHull_of_mem_trace hη hs0 (hEC hz).2.1 hzR)
    · intro hb
      have hne : (cobounded ℂ ⊓ 𝓟 E).NeBot := by
        refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
        by_contra hn
        rw [not_nonempty_iff_eq_empty] at hn
        have hUb : IsBounded Uᶜ := isBounded_def.2 (by rwa [compl_compl])
        refine hunb (hUb.subset fun z hz hzU => ?_)
        have hm : z ∈ U ∩ E := ⟨hzU, hz⟩
        rw [hn] at hm
        exact hm
      have ht : Tendsto ψ (cobounded ℂ ⊓ 𝓟 E) (cobounded ℂ) :=
        hψ.2.2.2.2.2.2.mono_left (inf_le_inf_left _
          (principal_mono.2 fun z hz => subset_closure (hEC hz).1))
      obtain ⟨z, hzb, hz⟩ := ((ht.eventually (isBounded_def.1 hb)).and
        (eventually_inf_principal.2 (Eventually.of_forall fun z hz => hz))).exists
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
  obtain ⟨z₀, hz₀, -⟩ := R7EndFace.exists_norm_gt_of_not_isBounded hunb 0
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

end InteractingSLE.Sec7.R7RelativeInf
