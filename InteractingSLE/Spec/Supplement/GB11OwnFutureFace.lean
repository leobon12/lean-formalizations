/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11OwnFutureDomain

/-!
# GB11: the precise current-Jordan-face input and its analytic consequence

The remaining geometric input is the source's current-Jordan-face assertion
(specification pp. 556–557): the compactified ambient image of the active pocket is
a Jordan domain. It is kept explicitly as an unproved input, rather than asserted
as a theorem. The conditional result below proves all subsequent analytic steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The current face is a Jordan domain after a compactification regular on `ℍ̄`.
This predicate records geometric data, and makes no assertion of their existence. -/
def IsCurrentJordanFace (W : ℝ → ℝ) (C : Set ℂ) (t : ℝ) : Prop :=
  ∃ Γ : Set ℂ, LQGMetric.JordanMap.IsJordanCurve Γ ∧ ∃ p ∈ Γᶜ,
    connectedComponentIn Γᶜ p = mu '' ownDomain W C t

/-- **Unproved geometric input:** GB11's current Jordan face, including walls that
meet the original real boundary and unbounded pockets. All GB11 premises are retained. -/
def GB11CurrentJordanFaceStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      IsCurrentJordanFace (fun r : ℝ => W' r.toNNReal) C t

/-- GB11's continuous relative own futures, conditional only on the geometric current
Jordan face. The ambient own future, its confinement, and compatibility of the boundary
extension with the relative point are proved here. -/
theorem gb11RelOwnFutureStatement_of_currentJordanFace
    (hface : GB11CurrentJordanFaceStatement) : GB11RelOwnFutureStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
    T hT hT0 ζ hrel hζc hζ0
  set τ := entryTime γ αR s₂
  set σ := GB11.firstVisit γ (αR s₁)
  set W : ℝ → ℝ := fun r => W' r.toNNReal
  set η : ℝ → ℂ := fun r => γ r.toNNReal
  set tt : ℝ → ℝ≥0 := fun u => τ + u.toNNReal
  have hW : Continuous W := hW'.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simpa only [W, Real.toNNReal_zero] using hW'0
  have hη : IsLoewnerTrace W η := isLoewnerTrace_of_isGeneratingTrace hγ
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hB.1)
    (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := by
    obtain ⟨z, -, -, -, hz⟩ := hC
    rw [hz]
    exact connectedComponentIn_subset _ _
  have hPC : αR s₁ ∉ C := fun h => (hCsub h).2 (Or.inl ⟨s₁, rfl⟩)
  obtain ⟨E, ψ, G, k, hpc, hEcl, -, hψE, -, hψinf, -, hcase⟩ :=
    exists_pocketData hB.1 hB.2.1 hB.2.2.1 hC hs hc hxC
  have hptc := continuousOn_relPt hpc hEcl hψE hψinf
  have htt : ∀ u ∈ Icc (0 : ℝ) T, ((tt u : ℝ≥0) : ℝ) = (τ : ℝ) + u := by
    intro u hu
    change ((τ + u.toNNReal : ℝ≥0) : ℝ) = (τ : ℝ) + u
    rw [NNReal.coe_add, Real.coe_toNNReal _ hu.1]
  have htσ : ∀ u ∈ Icc (0 : ℝ) T, (tt u : ℝ≥0∞) < σ := fun u hu =>
    coe_add_lt_of_mem_horizon ⟨hu.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hu.2) hT.2⟩
  have hτt : ∀ u, τ ≤ tt u := fun u => le_self_add
  have hdom : ∀ u ∈ Icc (0 : ℝ) T, γ (tt u) ∈ relDomBar C E (αR s₁) := by
    intro u hu
    by_cases h0 : γ (tt u) = 0
    · refine Or.inl ⟨h0, ?_⟩
      rcases hcase with ⟨hE', -⟩ | ⟨-, hs₂⟩
      · exact hE'
      · exact absurd h0 (trace_ne_zero_of_isBounded hγc (hs.entry hs₂).2.2 hD (hτt u) (htσ u hu))
    · refine Or.inr ⟨h0, hTr _ (hτt u) (htσ u hu) h0, fun hQ => ?_⟩
      have : σ ≤ (tt u : ℝ≥0∞) := iInf₂_le (tt u) ⟨h0, hQ⟩
      exact absurd (htσ u hu) (not_lt.2 this)
  have hζpt : ∀ u ∈ Icc (0 : ℝ) T, ζ u = relPt E ψ k (γ (tt u)) := fun u hu =>
    eq_relPt_of_tendsto hpc hc hCH hPC hptc (hrel u hu).1 (hdom u hu) (hrel u hu).2
  obtain ⟨ζ', hrel', -, -, hfill', -⟩ := exists_relCurve hW' hW'0 hγ hB hC hs hc hxC hE hTr hD hT
  have hζeq : EqOn ζ ζ' (Icc 0 T) := by
    intro u hu
    exact (hζpt u hu).trans
      (eq_relPt_of_tendsto hpc hc hCH hPC hptc (hrel' u hu).1 (hdom u hu) (hrel' u hu).2).symm
  intro s hsT
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hsT.1, hsT.2.le⟩
  have hfill : fillH (ζ '' Icc 0 s) = relHull W' c C τ s := by
    rw [image_congr (fun u hu => hζeq ⟨hu.1, hu.2.trans hsT.2.le⟩)]
    exact hfill' s hsI
  set a : ℝ := (τ : ℝ) + s
  set δ : ℝ → ℂ := fun u => trMap W a ((τ : ℝ) + u) 0
  have ha : 0 ≤ a := add_nonneg τ.2 hsT.1
  have hδc : ContinuousOn δ (Icc s T) :=
    (YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 ha).comp
      (continuousOn_const.add continuousOn_id)
      (fun u hu => show a ≤ (τ : ℝ) + u from add_le_add le_rfl hu.1)
  have hδH : MapsTo δ (Icc s T) Hbar := fun u hu =>
    YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 ha
      (show a ≤ (τ : ℝ) + u from add_le_add le_rfl hu.1)
  have hfδ : ∀ u ∈ Icc s T, trMap W 0 a (δ u) = γ (tt u) := by
    intro u hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hsT.1.trans hu.1, hu.2⟩
    change trMap W 0 a (trMap W a ((τ : ℝ) + u) 0) = γ (tt u)
    rw [Sec6.traceMapOut_trMap_zero hη hW hW0 ha
      (show a ≤ (τ : ℝ) + u from add_le_add le_rfl hu.1)]
    change γ (((τ : ℝ) + u).toNNReal) = γ (tt u)
    rw [← htt u huT, Real.toNNReal_coe]
  have hδO : MapsTo δ (Icc s T) (closure (ownDomain W C a)) := by
    intro u hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hsT.1.trans hu.1, hu.2⟩
    refine Sec6.ownFuture_mem_closure_face hη hW hW0 (isOpen_relDom hCo hCH) ha
      (fun r har hrC hrH => ⟨hrH, ?_⟩) ?_
    · rw [Sec6.traceMapOut_trMap_zero hη hW hW0 ha har]
      exact hrC
    · have hvisit := mem_closure_later_visits hD (s := a) (a := tt u)
        (by rw [htt u huT]; exact add_le_add le_rfl hu.1) (hτt u) (htσ u huT)
      rwa [htt u huT] at hvisit
  obtain ⟨Γ, hΓ, p, hp, hF⟩ := hface W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC
    hE hTr hD (tt s) (hτt s) (htσ s hsI)
  rw [htt s hsI] at hF
  set F := connectedComponentIn Γᶜ p
  have hFsub : MapsTo muInv F (ownDomain W C a) := by
    rw [show F = mu '' ownDomain W C a from hF]
    exact (isConformalBijection_muInv_ownDomain W C a).2.mapsTo
  have hf : IsConformalBijection (fun w => trMap W 0 a (muInv w)) F
      (relDom C \ fwdHull W a) := by
    have h := isConformalBijection_comp (isConformalBijection_trMap_ownDomain hW hW0 ha hCH)
      (isConformalBijection_muInv_ownDomain W C a)
    rwa [← hF] at h
  have hrelMap : IsConformalBijection (relMapC c) (relDom C \ fwdHull W a)
      (H \ fillH (ζ '' Icc 0 s)) := by
    rw [hfill]
    change IsConformalBijection (relMapC c) (relDom C \ fwdHull W a)
      (H \ relMapC c '' (fwdHull W a ∩ relDom C))
    rw [H_diff_relHull_eq hc]
    exact ⟨(differentiableOn_relMapC hc hCo hCH).mono sdiff_subset,
      ((injOn_relMapC hc).mono sdiff_subset).bijOn_image⟩
  have hq : IsConformalBijection (relPt E ψ k) (relDom C \ fwdHull W a)
      (H \ fillH (ζ '' Icc 0 s)) :=
    ⟨hrelMap.1.congr (fun w hw => relPt_eq_relMapC hpc hc hCH hw.1),
      hrelMap.2.congr (fun w hw => (relPt_eq_relMapC hpc hc hCH hw.1).symm)⟩
  set f : ℂ → ℂ := fun w => relPt E ψ k (trMap W 0 a (muInv w))
  have hfc : ∀ u ∈ Icc s T, ContinuousWithinAt f F (mu (δ u)) := by
    intro u hu
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hsT.1.trans hu.1, hu.2⟩
    have hμ0 := mu_ne_zero_of_mem_Hbar (hδH hu)
    have hμc : ContinuousWithinAt muInv F (mu (δ u)) :=
      (continuousOn_muInv.continuousAt (isOpen_compl_singleton.mem_nhds hμ0)).continuousWithinAt
    have htc := YuanSimpleApprox.trMap_continuousOn hη hW hW0 (a := 0) le_rfl ha
    have hχc : ContinuousWithinAt (fun w => trMap W 0 a (muInv w)) F (mu (δ u)) := by
      have htc' : ContinuousWithinAt (trMap W 0 a) Hbar (muInv (mu (δ u))) := by
        rw [muInv_mu]
        exact htc _ (hδH hu)
      exact htc'.comp hμc (fun w hw => H_subset_Hbar (hFsub hw).1)
    have hpt' : ContinuousWithinAt (relPt E ψ k) (relDomBar C E (αR s₁))
        (trMap W 0 a (muInv (mu (δ u)))) := by
      rw [muInv_mu, hfδ u hu]
      exact hptc _ (hdom u huT)
    exact hpt'.comp (f := fun w => trMap W 0 a (muInv w)) hχc
      (fun w hw => relDom_subset_relDomBar hCH hPC (hFsub hw).2)
  have hμδc : ContinuousOn (fun u => mu (δ u)) (Icc s T) := continuousOn_mu_Hbar.comp hδc hδH
  have hμδF : MapsTo (fun u => mu (δ u)) (Icc s T) (closure F) := by
    intro u hu
    rw [show F = mu '' ownDomain W C a from hF]
    exact ((continuousOn_mu_Hbar _ (hδH hu)).mono
      (fun w hw => H_subset_Hbar hw.1)).mem_closure_image (hδO hu)
  obtain ⟨β, hβc, hβH, hβ⟩ := exists_lift_of_jordan_face hΓ hp
    (by change IsBounded F; rw [hF]; exact isBounded_mu_ownDomain W C a) hsT.1
    (hζc.mono (Icc_subset_Icc_right hsT.2.le))
    (fun u hu => (hrel u ⟨hu.1, hu.2.trans hsT.2.le⟩).1) hζ0
    (isConformalBijection_comp hq hf) hμδc hμδF hfc
  refine ⟨β, hβc, hβH, fun u hu => ?_⟩
  rw [hβ u hu]
  change relPt E ψ k (trMap W 0 a (muInv (mu (δ u)))) = ζ u
  rw [muInv_mu, hfδ u hu]
  exact (hζpt u ⟨hsT.1.trans hu.1, hu.2⟩).symm

/-- The existing GB11 local-growth reduction with the sole remaining geometric input. -/
theorem gb11RelLocalGrowthStatement_of_currentJordanFace
    (hface : GB11CurrentJordanFaceStatement) : GB11RelLocalGrowthStatement :=
  gb11RelLocalGrowthStatement_of_ownFuture (gb11RelOwnFutureStatement_of_currentJordanFace hface)

/-- The relative parametrization with the sole remaining current-face input. -/
theorem gb11RelParamStatement_of_currentJordanFace
    (hface : GB11CurrentJordanFaceStatement) : GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_ownFuture (gb11RelOwnFutureStatement_of_currentJordanFace hface)

end InteractingSLE.Theorem14.GB11Chart
