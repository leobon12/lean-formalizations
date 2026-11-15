/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux40FullErase
import InteractingSLE.Spec.Sec6.Aux36Jordan
import InteractingSLE.Spec.Sec6.Aux41
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# Aux. lemmas 40–41 in full: the erased path in the Jordan coordinate

Specification §6.2, **Aux.** lemma 40 (conditions (a), (b) of Proposition 6.12, p. 204) and
**Aux.** lemma 41 ((RG1)–(RG5), pp. 204–206), with ruling R41's Proposition 1.6
(`ig1_ztip_elimination.txt` L276–L320). For the pocket of `IsReversePocket`, a Jordan coordinate
`ψ : C̄ \ {x₀} → ℍ̄` of `C` with `ψ(y₀) = 0`, `ψ(x₀) = ∞` (`IsJordanCoord`; one exists,
`IsReversePocket.exists_isJordanCoord`), and the pause-free erased path `ζ = ψ ∘ γ̂_C`:

* `IsReversePocket.image_inter_domain`: **(GC2) in the Jordan coordinate**:
  `ψ(C ∩ D_{fR(u)}) = ℍ \ fill(ζ([0, u]))`;
* `IsReversePocket.drivingCriterionA`, `IsReversePocket.drivingCriterionB`: **Aux. lemma 40 (a),
  (b)**;
* `IsReversePocket.hasContinuousOwnFuture`: **(RG1)–(RG5)**: after every erased prefix the future of
  `ζ` lifts continuously through the inverse of the relative mapping-out function;
* `IsReversePocket.aux41`: **Aux. lemma 41**: a continuous Loewner driving function up to the
  terminal capacity time, and the uniform simple approximations of Proposition 6.12.

All results assume Aux. lemma 37's conclusion (`AttachmentConstancy`), the named input whose proof
needs the field comparison.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.YuanCharacterisation (invExt HasContinuousOwnFuture)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- A **Jordan coordinate** of a Jordan domain `C` with `x₀ ↦ ∞` and `y₀ ↦ 0` (Aux. lemma 41:
"Let `ψ : C → ℍ` be the Jordan coordinate with `ψ(y₀) = 0` and `ψ(x₀) = ∞`"): a conformal bijection
`C → ℍ` extending continuously and injectively to `C̄ \ {x₀}` with values in `ℍ̄`, real on
`∂C \ {x₀}`, `ψ(y₀) = 0`, and `ψ → ∞` at `x₀`. -/
def IsJordanCoord (C : Set ℂ) (x₀ y₀ : ℂ) (ψ : ℂ → ℂ) : Prop :=
  ContinuousOn ψ (closure C \ {x₀}) ∧ InjOn ψ (closure C \ {x₀}) ∧
    MapsTo ψ (closure C \ {x₀}) Hbar ∧ IsConformalBijection ψ C H ∧
    (∀ z ∈ frontier C \ {x₀}, (ψ z).im = 0) ∧ ψ y₀ = 0 ∧
    Tendsto ψ (𝓝[closure C \ {x₀}] x₀) (cobounded ℂ)

/-- An unbounded preconnected subset of `ℍ \ B̄` (`B` bounded) lies in `ℍ \ fill(B)`. -/
theorem subset_H_diff_fillH_of_isPreconnected {B P : Set ℂ} (hB : IsBounded B)
    (hP : IsPreconnected P) (hPB : P ⊆ H \ closure B) (hPu : ¬ IsBounded P) :
    P ⊆ H \ fillH B := by
  obtain ⟨R, hR, hBR⟩ := exists_closure_subset_ball hB
  rw [H_diff_fillH hR hBR]
  obtain ⟨p, hpP, hpR⟩ : ∃ p ∈ P, R ≤ ‖p‖ := by
    by_contra h
    push Not at h
    exact hPu (isBounded_ball.subset fun p hp => mem_ball_zero_iff.2 (h p hp))
  have hp0 := mem_connectedComponentIn_of_le_norm hR hBR (hPB hpP).1 hpR
  rw [connectedComponentIn_eq hp0]
  exact hP.subset_connectedComponentIn hpP hPB

/-- The inverse boundary extension `invExt K` of the filling `K` of a path from `0` is continuous on
`ℍ̄` and inverts the mapping-out function on `ℍ \ K`. -/
theorem invExt_facts {ζ : ℝ → ℂ} {u : ℝ} (hu : 0 ≤ u) (hc : ContinuousOn ζ (Icc 0 u))
    (hH : MapsTo ζ (Icc 0 u) Hbar) (h0 : ζ 0 = 0) :
    ContinuousOn (invExt (fillH (ζ '' Icc 0 u))) Hbar ∧
      ∀ z ∈ H \ fillH (ζ '' Icc 0 u), invExt (fillH (ζ '' Icc 0 u))
        (ConformalImage.mapOut (fillH (ζ '' Icc 0 u)) z) = z := by
  obtain ⟨F, hF, -, heq⟩ := YuanCharacterisation.exists_isBdryExt_invExt hu hc hH h0
  refine ⟨hF.continuousOn.congr heq, fun z hz => ?_⟩
  have hgz := hF.isMapOut.1.2.mapsTo hz
  rw [heq (QuantumZipper.H_subset_Hbar hgz)]
  obtain ⟨h1, h2⟩ := hF.mem _ hgz
  exact hF.isMapOut.1.2.injOn h1 hz h2

namespace IsReversePocket

variable {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}

/-! ### The Jordan coordinate of the pocket -/

/-- The boundary of the pocket is a Jordan curve. -/
theorem isJordanCurve_frontier (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    LQGMetric.JordanMap.IsJordanCurve (frontier C) := by
  rw [hP.frontier_eq]
  refine Sec7.isJordanCurve_image_union hP.cont₁ hP.cont₂ hP.inj₁ hP.inj₂ hP.junction.symm
    hP.seed.symm ?_
  rintro z ⟨⟨v, hv, rfl⟩, ⟨v', hv', h⟩⟩
  rcases eq_or_lt_of_le hv.2 with h1 | h1
  · exact Or.inr (by rw [h1]; rfl)
  · have hv'1 : v' < 1 := by
      refine lt_of_le_of_ne hv'.2 fun h' => ?_
      rw [h', hP.seed] at h
      exact h1.ne (hP.inj₁ hv ⟨zero_le_one, le_rfl⟩ h.symm)
    exact Or.inl (hP.arms_eq ⟨hv.1, h1⟩ ⟨hv'.1, hv'1⟩ h.symm)

/-- **The pocket has a Jordan coordinate** with `x₀ ↦ ∞`, `y₀ ↦ 0` (`exists_jordanCoord`). -/
theorem exists_isJordanCoord (hP : IsReversePocket W η C α₁ α₂ β τ σ) :
    ∃ ψ : ℂ → ℂ, IsJordanCoord C (α₁ 0) (α₁ 1) ψ := by
  obtain ⟨p, hp⟩ := hP.isConnected.nonempty
  have hCeq := connectedComponentIn_compl_frontier_eq hP.isOpen hP.isConnected hp
  have hpΓ : p ∈ (frontier C)ᶜ := by
    rw [← hCeq] at hp; exact connectedComponentIn_subset _ _ hp
  have hx₀ : α₁ 0 ∈ frontier C := by
    rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hy₀ : α₁ 1 ∈ frontier C := by
    rw [hP.frontier_eq]; exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  obtain ⟨ψ, ψinv, hc, hmaps, -, -, hψinvψ, -, hconf, hreal, hy, ht⟩ :=
    exists_jordanCoord hP.isJordanCurve_frontier hpΓ (by rw [hCeq]; exact hP.isBounded) hx₀ hy₀
  rw [hCeq] at hc hmaps hψinvψ hconf ht
  refine ⟨ψ, hc, fun z hz z' hz' h => ?_, hmaps, hconf, hreal, hy, ht⟩
  rw [← hψinvψ z hz, h, hψinvψ z' hz']

/-! ### The erased path in the Jordan coordinate -/

variable {ψ : ℂ → ℂ}

theorem continuousOn_ζ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    ContinuousOn (fun v => ψ (erasedPath η C τ σ v)) (Ico 0 (pocketClock η C τ σ σ)) :=
  hψ.1.comp ((hP.continuousOn_erasedPath hAC).mono Ico_subset_Icc_self)
    fun _ hv => hP.erasedPath_mem hv

theorem mapsTo_ζ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    MapsTo (fun v => ψ (erasedPath η C τ σ v)) (Ico 0 (pocketClock η C τ σ σ)) Hbar :=
  fun _ hv => hψ.2.2.1 (hP.erasedPath_mem hv)

theorem ζ_zero (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) : ψ (erasedPath η C τ σ 0) = 0 := by
  rw [hP.erasedPath_zero hAC]; exact hψ.2.2.2.2.2.1

/-- The domain part `C ∩ D_s` of the pocket at a chart time `s ∈ [τ, σ)` is preconnected (it is the
image of the central face), and adheres to `x₀`. -/
theorem inter_domain_props (hP : IsReversePocket W η C α₁ α₂ β τ σ) {s : ℝ} (hτs : τ ≤ s)
    (hsσ : s < σ) : IsPreconnected (C ∩ (H \ fwdHull W s)) ∧
      α₁ 0 ∈ closure (C ∩ (H \ fwdHull W s)) := by
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  obtain ⟨Γ, hΓJ, hΓH, hiff⟩ := hP.exists_face hτs hsσ
  obtain ⟨-, -, -, -, -, -, -, hpre, -⟩ := jordan_sides hΓJ hΓH
  have heq : C ∩ (H \ fwdHull W s) = trMap W 0 s '' innerSide Γ := by
    ext z
    constructor
    · rintro ⟨hzC, hzD⟩
      rw [← trMap_zero_image_H hW hW0 hs0] at hzD
      obtain ⟨w, hw, rfl⟩ := hzD
      exact ⟨w, (hiff w hw).1 hzC, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have hwH := innerSide_subset_H hΓJ hΓH hw
      refine ⟨(hiff w hwH).2 hw, ?_⟩
      rw [← trMap_zero_image_H hW hW0 hs0]; exact ⟨w, hwH, rfl⟩
  refine ⟨heq ▸ hpre.image _ ((YuanSimpleApprox.trMap_continuousOn hP.trace hW hW0 le_rfl
    hs0).mono fun w hw => QuantumZipper.H_subset_Hbar (innerSide_subset_H hΓJ hΓH hw)), ?_⟩
  obtain ⟨-, -, hD, -, -⟩ := hP.chart hτs hsσ (Or.inl rfl)
  have hxD := hD 0 ⟨le_rfl, (hP.chart hτs hsσ (Or.inl rfl)).1⟩
  have hxC : α₁ 0 ∈ closure C := by
    have : α₁ 0 ∈ frontier C := by
      rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    exact frontier_subset_closure this
  exact (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs0).closure_inter ⟨hxC, hxD⟩

/-- **(GC2) in the Jordan coordinate** (Specification p. 206: "By (GC2), the physical target
component is `E_s`"): `ψ(C ∩ D_{fR(u)}) = ℍ \ fill(ζ([0, u]))` for `u ∈ [0, ℓ(σ))`. -/
theorem image_inter_domain (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (pocketClock η C τ σ σ)) :
    ψ '' (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) =
      H \ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u) := by
  have hψ' := hψ
  obtain ⟨hψc, hψi, hψH, hψconf, -, -, hψt⟩ := hψ'
  set s := pocketFibre η C τ σ u with hsdef
  set ζ : ℝ → ℂ := fun v => ψ (erasedPath η C τ σ v) with hζdef
  set D := H \ fwdHull W s with hDdef
  have hτs : τ ≤ s := (hP.fibre_mem u).1
  have hsσ : s < σ := hP.fibre_lt_σ hu
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hsub : Icc 0 u ⊆ Ico 0 (pocketClock η C τ σ σ) := fun v hv => ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hcpt : IsCompact (ζ '' Icc 0 u) :=
    isCompact_Icc.image_of_continuousOn ((hP.continuousOn_ζ hAC hψ).mono hsub)
  obtain ⟨hpre, hxcl⟩ := hP.inter_domain_props hτs hsσ
  have hGC2 := hP.erasedPath_image_inter (u := u) ⟨hu.1, hu.2.le⟩
  have hCsub : C ⊆ closure C \ {α₁ 0} := fun z hz =>
    ⟨subset_closure hz, fun h => by
      have hx : α₁ 0 ∈ frontier C := by
        rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      rw [mem_singleton_iff.1 h] at hz
      exact hx.2 (by rw [hP.isOpen.interior_eq]; exact hz)⟩
  -- (⊆): `ψ(C ∩ D_s)` is preconnected, unbounded and misses `ζ([0, u])`
  have hfwd : ψ '' (C ∩ D) ⊆ H \ fillH (ζ '' Icc 0 u) := by
    refine subset_H_diff_fillH_of_isPreconnected hcpt.isBounded
      (hpre.image _ (hψc.mono fun z hz => hCsub hz.1)) ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨hψconf.2.mapsTo hz.1, fun hcl => ?_⟩
      rw [hcpt.isClosed.closure_eq] at hcl
      obtain ⟨v, hv, hvz⟩ := hcl
      have hzv : erasedPath η C τ σ v = z :=
        hψi (hP.erasedPath_mem (hsub hv)) (hCsub hz.1) hvz
      have hzR : z ∈ η '' Icc 0 s := by
        have := hGC2 ▸ (show z ∈ erasedPath η C τ σ '' Icc 0 u ∩ C from ⟨⟨v, hv, hzv⟩, hz.1⟩)
        exact this.1
      exact hz.2.2 (mem_fwdHull_of_mem_trace hP.trace hs0 hz.2.1 hzR)
    · intro hb
      have hne : (𝓝[C ∩ D] α₁ 0).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
      have ht' : Tendsto ψ (𝓝[C ∩ D] α₁ 0) (cobounded ℂ) :=
        hψt.mono_left (nhdsWithin_mono _ fun z hz => hCsub hz.1)
      obtain ⟨z, hzb, hz⟩ := ((ht'.eventually (isBounded_def.1 hb)).and
        self_mem_nhdsWithin).exists
      exact hzb ⟨z, hz, rfl⟩
  refine Subset.antisymm hfwd ?_
  -- (⊇): pull `ℍ \ fill(ζ([0, u]))` back by the holomorphic inverse of `ψ`
  set e := QuantumZipper.CA.univalentOPH hP.isOpen hψconf.1 hψconf.2.injOn with hedef
  have htarget : e.target = H := by
    rw [hedef, QuantumZipper.CA.univalentOPH_target]; exact hψconf.2.image_eq
  have hsymmC : MapsTo e.symm H C := fun w hw => by
    have := e.map_target (htarget ▸ hw)
    rwa [hedef, QuantumZipper.CA.univalentOPH_source] at this
  have hψe : ∀ w ∈ H, ψ (e.symm w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hP.isOpen hψconf.1 hψconf.2.injOn
      (by rw [hψconf.2.image_eq]; exact hw)
  have hK : IsHPHull (fillH (ζ '' Icc 0 u)) :=
    YuanCharacterisation.isHPHull_fillH_image ((hP.continuousOn_ζ hAC hψ).mono hsub) hu.1
      (hP.ζ_zero hAC hψ)
  set P := e.symm '' (H \ fillH (ζ '' Icc 0 u)) with hPdef
  have hPpre : IsPreconnected P :=
    hK.isConnected.isPreconnected.image _ ((htarget ▸ e.continuousOn_symm).mono sdiff_subset)
  have hPC : P ⊆ C := by rintro _ ⟨w, hw, rfl⟩; exact hsymmC hw.1
  have hPR : Disjoint P (η '' Icc 0 s) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ hR
    have hmem : e.symm w ∈ η '' Icc 0 s ∩ C := ⟨hR, hsymmC hw.1⟩
    rw [← hGC2] at hmem
    obtain ⟨⟨v, hv, hve⟩, -⟩ := hmem
    have : w ∈ ζ '' Icc 0 u := ⟨v, hv, by simp only [hζdef, hve, hψe w hw.1]⟩
    exact hw.2 ⟨hw.1, Or.inl (subset_closure this)⟩
  -- a point of `P` in `D_s`
  obtain ⟨z₀, hz₀⟩ : (C ∩ D).Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at hxcl
    exact hxcl
  have hz₀P : z₀ ∈ P := ⟨ψ z₀, hfwd ⟨z₀, hz₀, rfl⟩,
    QuantumZipper.CA.univalentOPH_symm_apply_apply hP.isOpen hψconf.1 hψconf.2.injOn hz₀.1⟩
  have hPD := subset_domain_of_isPreconnected hP.trace hs0 hPpre (hPC.trans hP.subset_H) hPR
    hz₀P hz₀.2
  intro w hw
  exact ⟨e.symm w, ⟨hsymmC hw.1, hPD ⟨w, hw, rfl⟩⟩, hψe w hw.1⟩

/-- Every retained point after the chart time `s = fR(u)` adheres to `C ∩ D_s`. -/
theorem erasedPath_mem_closure_inter (hP : IsReversePocket W η C α₁ α₂ β τ σ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < pocketClock η C τ σ σ) :
    erasedPath η C τ σ v ∈ closure (C ∩ (H \ fwdHull W (pocketFibre η C τ σ u))) := by
  set s := pocketFibre η C τ σ u with hsdef
  set b := pocketFibre η C τ σ v with hbdef
  have hsb : s ≤ b := hP.monotone_fibre huv
  have hb0 : 0 ≤ b := hP.nonneg.trans (hP.fibre_mem v).1
  have hbcl := hP.mem_closure_of_right (hP.fibre_lt_σ ⟨hu.trans huv, hv⟩)
    (hP.clock_lt_of_fibre ⟨hu.trans huv, hv.le⟩)
  have hsub : {t | b < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hb0.trans ht.1.le
  have hc : ContinuousWithinAt η {t | b < t ∧ η t ∈ C} b :=
    (hP.trace.2.1 b (mem_Ici.2 hb0)).mono hsub
  refine closure_minimal ?_ isClosed_closure (hc.mem_closure_image hbcl)
  rintro _ ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := hb0.trans ht.1.le
  have hcl := trace_mem_closure_domain hP.trace hP.continuous_W hP.W_zero ht0
  have hDD : H \ fwdHull W t ⊆ H \ fwdHull W s := fun z hz =>
    ⟨hz.1, fun h => hz.2 (fwdHull_mono' (hsb.trans ht.1.le) h)⟩
  exact hP.isOpen.inter_closure ⟨ht.2, closure_mono hDD hcl⟩

/-- **Aux. lemma 40, condition (a)** of Proposition 6.12 in the Jordan coordinate: the future of `ζ`
stays in the closure of the unbounded component `ℍ \ fill(ζ([0, t]))`. -/
theorem drivingCriterionA (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {S : ℝ}
    (hS : S < pocketClock η C τ σ σ) :
    DrivingCriterionA (fun v => ψ (erasedPath η C τ σ v)) S := by
  intro t ht
  rw [← hP.image_inter_domain hAC hψ ⟨ht.1.le, ht.2.trans hS⟩]
  rintro _ ⟨v, hv, rfl⟩
  have hvσ : v < pocketClock η C τ σ σ := hv.2.trans_lt hS
  have hmem := hP.erasedPath_mem_closure_inter ht.1.le hv.1.le hvσ
  have hCsub : C ⊆ closure C \ {α₁ 0} := fun z hz =>
    ⟨subset_closure hz, fun h => by
      have hx : α₁ 0 ∈ frontier C := by
        rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      rw [mem_singleton_iff.1 h] at hz
      exact hx.2 (by rw [hP.isOpen.interior_eq]; exact hz)⟩
  have hc : ContinuousWithinAt ψ (C ∩ (H \ fwdHull W (pocketFibre η C τ σ t)))
      (erasedPath η C τ σ v) :=
    (hψ.1 _ (hP.erasedPath_mem ⟨ht.1.le.trans hv.1.le, hvσ⟩)).mono fun z hz => hCsub hz.1
  exact hc.mem_closure_image hmem

/-- **Aux. lemma 40, condition (b)** of Proposition 6.12 in the Jordan coordinate: no nontrivial
interval of `ζ` lies in its earlier range together with `ℝ`. -/
theorem drivingCriterionB (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {S : ℝ} (hS : S < pocketClock η C τ σ σ) :
    DrivingCriterionB (fun v => ψ (erasedPath η C τ σ v)) S := by
  intro t ht
  set A := {u ∈ Ioo t S | ψ (erasedPath η C τ σ u) ∈ (fun v => ψ (erasedPath η C τ σ v)) ''
    Icc 0 t ∨ (ψ (erasedPath η C τ σ u)).im = 0} with hAdef
  by_contra hne
  obtain ⟨v₀, hv₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 isOpen_interior v₀ hv₀
  have hball : ∀ v, |v - v₀| < ε → v ∈ A := fun v hv =>
    interior_subset (hεA (by rw [mem_ball, Real.dist_eq]; exact hv))
  set v₁ := v₀ - ε / 2 with hv₁
  set v₂ := v₀ + ε / 2 with hv₂
  have hA₁ := hball v₁ (by rw [hv₁, abs_of_neg (by linarith)]; linarith)
  have hA₂ := hball v₂ (by rw [hv₂, abs_of_pos (by linarith)]; linarith)
  have hσ₂ : v₂ < pocketClock η C τ σ σ := hA₂.1.2.trans hS
  have h0₁ : 0 ≤ v₁ := ht.1.le.trans hA₁.1.1.le
  set a₁ := pocketFibre η C τ σ v₁ with ha₁
  set a₂ := pocketFibre η C τ σ v₂ with ha₂
  have hℓ₁ := hP.clock_fibre ⟨h0₁, (show v₁ < v₂ by linarith).le.trans hσ₂.le⟩
  have hℓ₂ := hP.clock_fibre ⟨h0₁.trans (by linarith), hσ₂.le⟩
  have ha₁₂ : a₁ < a₂ := by
    by_contra h
    push Not at h
    have := hP.monotone_clock h
    rw [hℓ₁, hℓ₂] at this
    linarith
  obtain ⟨t₀, ht₀, ht₀I⟩ := hP.exists_mem_of_clock_lt ha₁₂ (by rw [hℓ₁, hℓ₂]; linarith)
  obtain ⟨δ, hδ, hδI⟩ := Metric.isOpen_iff.1 hP.isOpen_visitSet t₀ ht₀I
  set l := max (t₀ - δ) a₁ with hl
  set r := min (t₀ + δ) a₂ with hr
  have hlt : l < t₀ := max_lt (by linarith) ht₀.1
  have htr : t₀ < r := lt_min (by linarith) ht₀.2
  have hJ : ∀ x, l < x → x < r → x ∈ visitSet η C τ σ := fun x hlx hxr => hδI (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (t₀ - δ) a₁]
    · linarith [min_le_left (t₀ + δ) a₂])
  set c := (l + t₀) / 2 with hc
  set d := (t₀ + r) / 2 with hd
  have hcd : c < d := by rw [hc, hd]; linarith
  have hc0 : 0 ≤ c := hP.nonneg.trans ((hJ c (by rw [hc]; linarith) (by rw [hc]; linarith)).1.1.le)
  have hsub : η '' Icc c d ⊆ η '' Icc 0 c := by
    rintro _ ⟨t', ht', rfl⟩
    have ht'I := hJ t' (by rw [hc] at ht'; linarith [ht'.1]) (by rw [hd] at ht'; linarith [ht'.2])
    have hal : a₁ ≤ l := le_max_right _ _
    have hlo : pocketClock η C τ σ a₁ < pocketClock η C τ σ t' := hP.clock_lt_of_mem
      (t := (l + c) / 2) (by rw [hc]; linarith) (by rw [hc] at ht'; linarith [ht'.1])
      (hJ _ (by rw [hc]; linarith) (by rw [hc]; linarith))
    have hhi : pocketClock η C τ σ t' < pocketClock η C τ σ a₂ := hP.clock_lt_of_mem
      (t := (d + r) / 2) (by rw [hd] at ht'; linarith [ht'.2]) (by
        have : r ≤ a₂ := min_le_right _ _
        rw [hd]; linarith) (hJ _ (by rw [hd]; linarith) (by rw [hd]; linarith))
    rw [hℓ₁] at hlo
    rw [hℓ₂] at hhi
    set w := pocketClock η C τ σ t' with hw
    have hwA := hball w (by rw [abs_lt]; constructor <;> linarith)
    have hfw : pocketFibre η C τ σ w = t' := hP.fibre_clock_of_mem ht'I
    have hηC : η t' ∈ C := ht'I.2
    have hCsub : ∀ z ∈ C, z ∈ closure C \ {α₁ 0} := fun z hz =>
      ⟨subset_closure hz, fun h => by
        have hx : α₁ 0 ∈ frontier C := by
          rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
        rw [mem_singleton_iff.1 h] at hz
        exact hx.2 (by rw [hP.isOpen.interior_eq]; exact hz)⟩
    rcases hwA.2 with ⟨w', hw', hψw⟩ | him
    · simp only [erasedPath, hfw] at hψw
      have heq : erasedPath η C τ σ w' = η t' := hψ.2.1
        (hP.erasedPath_mem ⟨hw'.1, hw'.2.trans_lt (ht.2.trans hS)⟩) (hCsub _ hηC) hψw
      have hmem : η t' ∈ erasedPath η C τ σ '' Icc 0 t ∩ C := ⟨⟨w', hw', heq⟩, hηC⟩
      rw [hP.erasedPath_image_inter ⟨ht.1.le, (ht.2.trans hS).le⟩] at hmem
      obtain ⟨t'', ht'', he⟩ := hmem.1
      have hft : pocketFibre η C τ σ t ≤ a₁ := hP.monotone_fibre hA₁.1.1.le
      exact ⟨t'', ⟨ht''.1, ht''.2.trans (hft.trans (hal.trans (by rw [hc]; linarith)))⟩, he⟩
    · simp only [erasedPath, hfw] at him
      exact absurd him (ne_of_gt (hψ.2.2.2.1.2.1 hηC))
  exact not_image_subset_of_lt hP.trace hP.continuous_W hP.W_zero hc0 hcd hsub

/-- Strict growth of the relative fillings (Specification p. 206, "The relative hulls are strictly
increasing"), from conditions (a) and (b). -/
theorem strictMonoOn_fillH_ζ (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {S : ℝ}
    (hS : S < pocketClock η C τ σ σ) :
    StrictMonoOn (fun t => fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 t)) (Icc 0 S) :=
  strictMonoOn_fillH_of_drivingCriteria ((hP.continuousOn_ζ hAC hψ).mono fun _ hv =>
    ⟨hv.1, hv.2.trans_lt hS⟩) (hP.drivingCriterionA hAC hψ hS) (hP.drivingCriterionB hψ hS)

/-- On `[u, S]` the fibre endpoints of the clock restricted to `[fR(u), fR(S)]` are those in
`[τ, σ]`. -/
theorem fibreRight_restrict (hP : IsReversePocket W η C α₁ α₂ β τ σ) {u S v : ℝ} (hu : 0 ≤ u)
    (hS : S < pocketClock η C τ σ σ) (hv : v ∈ Icc u S) :
    fibreRight (pocketClock η C τ σ) (pocketFibre η C τ σ u) (pocketFibre η C τ σ S) v =
      pocketFibre η C τ σ v := by
  have hv0 : 0 ≤ v := hu.trans hv.1
  have hℓs := hP.clock_fibre ⟨hu, (hv.1.trans hv.2).trans hS.le⟩
  have hℓv := hP.clock_fibre ⟨hv0, hv.2.trans hS.le⟩
  have hvA : pocketFibre η C τ σ v ∈ {t ∈ Icc (pocketFibre η C τ σ u) (pocketFibre η C τ σ S) |
      pocketClock η C τ σ t ≤ max v (pocketClock η C τ σ (pocketFibre η C τ σ u))} :=
    ⟨⟨hP.monotone_fibre hv.1, hP.monotone_fibre hv.2⟩, by rw [hℓv]; exact le_max_left _ _⟩
  refine le_antisymm (csSup_le ⟨_, hvA⟩ fun t ht => ?_) (le_csSup ⟨_, fun t ht => ht.1.2⟩ hvA)
  rw [hℓs, max_eq_left hv.1] at ht
  exact le_fibreRight ⟨(hP.fibre_mem u).1.trans ht.1.1, ht.1.2.trans (hP.fibre_mem S).2⟩
    (by rw [clock_τ, max_eq_left hv0]; exact ht.2)

/-- **(RG1)–(RG5)** (Specification pp. 204–206; ruling R41's Proposition 1.6): after every erased
prefix `ζ([0, u])`, `u < S < ℓ(σ)`, the future `ζ|[u, S]` lifts continuously through the inverse of
the relative mapping-out function: `β(v) = Φ̄_s(Δ_s(v))`, `s = fR(u)`, with
`Φ_s = G_u ∘ ψ ∘ f̄_s` the conformal map of the central face `F_s` onto `ℍ` and `Δ_s` the collapsed
own-mapped future. This is condition (ii) of [Yua22, Theorem 1.1] (`HasContinuousOwnFuture`). -/
theorem hasContinuousOwnFuture (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {S : ℝ}
    (hS : S < pocketClock η C τ σ σ) :
    HasContinuousOwnFuture (fun v => ψ (erasedPath η C τ σ v)) S := by
  intro u hu
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  set ζ : ℝ → ℂ := fun v => ψ (erasedPath η C τ σ v) with hζdef
  set s := pocketFibre η C τ σ u with hsdef
  set S' := pocketFibre η C τ σ S with hS'def
  have huσ : u < pocketClock η C τ σ σ := hu.2.trans hS
  have hτs : τ ≤ s := (hP.fibre_mem u).1
  have hsσ : s < σ := hP.fibre_lt_σ ⟨hu.1, huσ⟩
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hℓs : pocketClock η C τ σ s = u := hP.clock_fibre ⟨hu.1, huσ.le⟩
  have hℓS' : pocketClock η C τ σ S' = S := hP.clock_fibre ⟨hu.1.trans hu.2.le, hS.le⟩
  have hsS' : s ≤ S' := hP.monotone_fibre hu.2.le
  have hS'σ : S' < σ := hP.fibre_lt_σ ⟨hu.1.trans hu.2.le, hS⟩
  have hsubu : Icc 0 u ⊆ Ico 0 (pocketClock η C τ σ σ) := fun v hv => ⟨hv.1, hv.2.trans_lt huσ⟩
  have hζc : ContinuousOn ζ (Icc 0 u) := (hP.continuousOn_ζ hAC hψ).mono hsubu
  have hζH : MapsTo ζ (Icc 0 u) Hbar := (hP.mapsTo_ζ hψ).mono_left hsubu
  set K := fillH (ζ '' Icc 0 u) with hKdef
  set G := ConformalImage.mapOut K with hGdef
  have hK : IsHPHull K := YuanCharacterisation.isHPHull_fillH_image hζc hu.1 (hP.ζ_zero hAC hψ)
  have hG : IsMapOut K G := ConformalImage.isMapOut_mapOut hK
  obtain ⟨hinvc, hinvG⟩ := invExt_facts hu.1 hζc hζH (hP.ζ_zero hAC hψ)
  have hCsub : C ⊆ closure C \ {α₁ 0} := fun z hz =>
    ⟨subset_closure hz, fun h => by
      have hx : α₁ 0 ∈ frontier C := by
        rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      rw [mem_singleton_iff.1 h] at hz
      exact hx.2 (by rw [hP.isOpen.interior_eq]; exact hz)⟩
  -- the central face `F_s` and the conformal map `Φ_s = G_u ∘ ψ ∘ f̄_s : F_s → ℍ`
  obtain ⟨Γ, hΓJ, hΓH, hiff⟩ := hP.exists_face hτs hsσ
  obtain ⟨⟨x₁, hx₁, hin⟩, hFb, hFfr, -, -, -, -, -, -⟩ := jordan_sides hΓJ hΓH
  set F := innerSide Γ with hFdef
  have hFH : F ⊆ H := innerSide_subset_H hΓJ hΓH
  have hfeq : ∀ w ∈ H, trMap W 0 s w = fwdMapInv W s w := fun w hw => by
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs0 hw, YuanSimpleApprox.shiftDrive_zero_eq hW0,
      sub_zero]
  have himgH := trMap_zero_image_H hW hW0 hs0
  have hf : IsConformalBijection (trMap W 0 s) F (C ∩ (H \ fwdHull W s)) := by
    refine ⟨((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hs0).mono hFH).congr
      fun w hw => hfeq w (hFH hw), fun w hw => ⟨(hiff w (hFH hw)).2 hw,
        himgH ▸ ⟨w, hFH hw, rfl⟩⟩, fun w hw w' hw' h => ?_, fun z hz => ?_⟩
    · rw [hfeq w (hFH hw), hfeq w' (hFH hw')] at h
      exact QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hs0 (hFH hw) (hFH hw') h
    · have hzD := hz.2
      rw [← himgH] at hzD
      obtain ⟨w, hw, rfl⟩ := hzD
      exact ⟨w, (hiff w hw).1 hz.1, rfl⟩
  have hψ' : IsConformalBijection ψ (C ∩ (H \ fwdHull W s)) (H \ K) := by
    refine ⟨hψ.2.2.2.1.1.mono inter_subset_left, ?_⟩
    have := (hψ.2.2.2.1.2.injOn.mono inter_subset_left).bijOn_image
      (s := C ∩ (H \ fwdHull W s))
    rwa [hP.image_inter_domain hAC hψ ⟨hu.1, huσ⟩] at this
  have hΦ := isConformalBijection_comp hG.1 (isConformalBijection_comp hψ' hf)
  have hΦ' : IsConformalBijection (G ∘ (ψ ∘ trMap W 0 s)) (connectedComponentIn Γᶜ x₁) H := by
    rw [← hin]; exact hΦ
  obtain ⟨p, hpΓ, Φ', hΦeq, hΦc, hΦH, hΦt⟩ :=
    exists_bdryExt_of_isConformalBijection hΓJ hx₁ (hin ▸ hFb) hΦ'
  rw [← hin] at hΦeq hΦc hΦH hΦt
  have hpF : p ∉ F := fun h => innerSide_subset_compl h hpΓ
  have hFsub : F ⊆ closure F \ {p} := fun w hw => ⟨subset_closure hw, fun h => hpF (h ▸ hw)⟩
  -- the collapsed own-mapped future `Δ_s`
  set Δ : ℝ → ℂ := fun v => trMap W s (pocketFibre η C τ σ v) 0 with hΔdef
  have hΔc : ContinuousOn Δ (Icc u S) := by
    have h := continuousOn_collapsed_ownFuture hη hW hW0 hP.continuous_clock hP.monotone_clock
      hs0 hsS' (S := S') ?_
    · rw [hℓs, hℓS'] at h
      exact h.congr fun v hv => by
        simp only [hΔdef]
        exact congrArg (fun x => trMap W s x 0) (hP.fibreRight_restrict hu.1 hS hv).symm
    intro a ha b hb hab hℓab hmax
    have hbσ : b < σ := hb.2.trans_lt hS'σ
    obtain ⟨hgap, hbcl, hacl⟩ := hP.maximal_fibre hτs
      (hP.clock_lt_of_fibre ⟨hu.1.trans hu.2.le, hS.le⟩) ha hb hab hbσ hℓab hmax
    have has : s < a := by
      refine lt_of_le_of_ne ha.1 fun h => ?_
      rw [← h] at hℓab
      exact (hP.clock_lt_of_fibre ⟨hu.1, huσ.le⟩ b
        ⟨lt_of_le_of_lt (le_of_eq h) hab, hbσ.le⟩).ne hℓab
    exact (hP.gap_eq hAC hs0 has (hτs.trans ha.1) hab hbσ hgap
      (Or.inr (hacl.resolve_left has.ne')) hbcl).1
  have hfib_s : ∀ v ∈ Icc u S, s ≤ pocketFibre η C τ σ v := fun v hv => hP.monotone_fibre hv.1
  have hfΔ : ∀ v ∈ Icc u S, trMap W 0 s (Δ v) = erasedPath η C τ σ v := fun v hv =>
    traceMapOut_trMap_zero hη hW hW0 hs0 (hfib_s v hv)
  have hΔF : ∀ v ∈ Icc u S, Δ v ∈ closure F := by
    intro v hv
    have hvσ : v < pocketClock η C τ σ σ := hv.2.trans_lt hS
    refine ownFuture_mem_closure_face hη hW hW0 hP.isOpen hs0 (fun t hst htC hδH =>
      (hiff _ hδH).1 (by rw [traceMapOut_trMap_zero hη hW hW0 hs0 hst]; exact htC)) ?_
    refine closure_mono (s := {t | pocketFibre η C τ σ v < t ∧ η t ∈ C})
      (t := {t | s < t ∧ η t ∈ C}) (fun t ht => ⟨(hfib_s v hv).trans_lt ht.1, ht.2⟩) ?_
    exact hP.mem_closure_of_right (hP.fibre_lt_σ ⟨hu.1.trans hv.1, hvσ⟩)
      (hP.clock_lt_of_fibre ⟨hu.1.trans hv.1, hvσ.le⟩)
  have hFHbar : closure F ⊆ Hbar := by
    rw [← closure_H]; exact closure_mono hFH
  have hfc : ContinuousOn (trMap W 0 s) Hbar :=
    YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs0
  have hfC : MapsTo (trMap W 0 s) F (closure C \ {α₁ 0}) := fun w hw =>
    hCsub ((hiff w (hFH hw)).2 hw)
  -- `ψ ∘ f̄_s` is continuous within `F` at every `Δ_s(v)`
  have hgc : ∀ v ∈ Icc u S, ContinuousWithinAt (fun w => ψ (trMap W 0 s w)) F (Δ v) := by
    intro v hv
    have hmem : trMap W 0 s (Δ v) ∈ closure C \ {α₁ 0} := by
      rw [hfΔ v hv]; exact hP.erasedPath_mem ⟨hu.1.trans hv.1, hv.2.trans_lt hS⟩
    exact (hψ.1 _ hmem).comp ((hfc _ (hFHbar (hΔF v hv))).mono fun w hw =>
      QuantumZipper.H_subset_Hbar (hFH hw)) hfC
  -- the pole is not reached
  have hΔp : ∀ v ∈ Icc u S, Δ v ≠ p := by
    intro v hv hvp
    have hpcl : p ∈ closure F := by
      rw [← hFfr] at hpΓ; exact frontier_subset_closure hpΓ
    have : (𝓝[F] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpcl
    obtain ⟨M, hM⟩ := hG.exists_norm_le hK
    have hg := hgc v hv
    rw [hvp] at hg
    set c := ψ (trMap W 0 s p) with hcdef
    have h1 : ∀ᶠ w in 𝓝[F] p, ‖ψ (trMap W 0 s w)‖ < ‖c‖ + 1 := by
      filter_upwards [hg.tendsto.eventually (Metric.ball_mem_nhds c one_pos)] with w hw
      have := norm_sub_norm_le (ψ (trMap W 0 s w)) c
      rw [dist_eq_norm] at hw
      linarith
    have h2 : ∀ᶠ w in 𝓝[F] p, ‖c‖ + 1 + M < ‖(G ∘ (ψ ∘ trMap W 0 s)) w‖ :=
      (tendsto_norm_atTop_iff_cobounded.2 hΦt).eventually (eventually_gt_atTop _)
    obtain ⟨w, ⟨hw1, hw2⟩, hwF⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    have hz : ψ (trMap W 0 s w) ∈ H \ K := hψ'.2.mapsTo (hf.2.mapsTo hwF)
    have := hM _ hz
    simp only [Function.comp_apply] at hw2
    linarith
  refine ⟨fun v => Φ' (Δ v), hΦc.comp hΔc fun v hv => ⟨hΔF v hv, hΔp v hv⟩,
    fun v hv => hΦH ⟨hΔF v hv, hΔp v hv⟩, fun v hv => ?_⟩
  -- the identity `invExt K (Φ̄_s(Δ_s(v))) = ζ(v)`, by uniqueness of limits within `F`
  have : (𝓝[F] (Δ v)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hΔF v hv)
  have hmemp : Δ v ∈ closure F \ {p} := ⟨hΔF v hv, hΔp v hv⟩
  have hc₁ : ContinuousWithinAt (fun w => invExt K (Φ' w)) F (Δ v) :=
    ((hinvc _ (hΦH hmemp)).comp (hΦc _ hmemp) hΦH).mono hFsub
  have heq : ∀ w ∈ F, invExt K (Φ' w) = ψ (trMap W 0 s w) := fun w hw => by
    rw [hΦeq hw]
    exact hinvG _ (hψ'.2.mapsTo (hf.2.mapsTo hw))
  have := tendsto_nhds_unique (hc₁.tendsto.congr' (eventually_nhdsWithin_of_forall heq))
    (hgc v hv).tendsto
  rw [this, hfΔ v hv]

/-- **Aux. lemma 40** (Specification p. 203: "There is a continuous erased path from `y₀` to `x₀`
in `C̄`, obtained by retaining the closure of its interior `C` visits and collapsing the
complementary time intervals. After a continuous time change removing its constant intervals, it
satisfies conditions (a) and (b) of Proposition 6.12 in a Jordan coordinate of `C` with `x₀` at
infinity"), under Aux. lemma 37's attachment constancy: the clock has positive terminal value
`ℓ(σ)`;
the erased path `γ̂_C` is continuous on `[0, ℓ(σ)]` from `y₀` to `x₀` in `C̄`; erasure changes no
range in `C` ((GC2)); and in every Jordan coordinate `ψ` of `C` with `x₀ ↦ ∞`, `y₀ ↦ 0`, the path
`ζ = ψ ∘ γ̂_C` satisfies conditions (a) and (b) on every `[0, S]`, `S < ℓ(σ)`. -/
theorem aux40 (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    0 < pocketClock η C τ σ σ ∧ ContinuousOn (erasedPath η C τ σ) (Icc 0 (pocketClock η C τ σ σ)) ∧
      erasedPath η C τ σ 0 = α₁ 1 ∧ erasedPath η C τ σ (pocketClock η C τ σ σ) = α₁ 0 ∧
      MapsTo (erasedPath η C τ σ) (Icc 0 (pocketClock η C τ σ σ)) (closure C) ∧
      (∀ u ∈ Icc 0 (pocketClock η C τ σ σ),
        erasedPath η C τ σ '' Icc 0 u ∩ C = η '' Icc 0 (pocketFibre η C τ σ u) ∩ C) ∧
      ∀ S < pocketClock η C τ σ σ, DrivingCriterionA (fun v => ψ (erasedPath η C τ σ v)) S ∧
        DrivingCriterionB (fun v => ψ (erasedPath η C τ σ v)) S := by
  refine ⟨hP.clock_σ_pos hAC, hP.continuousOn_erasedPath hAC, hP.erasedPath_zero hAC,
    hP.erasedPath_clock_σ hAC, fun v hv => ?_, fun u hu => hP.erasedPath_image_inter hu,
    fun S hS => ⟨hP.drivingCriterionA hAC hψ hS, hP.drivingCriterionB hψ hS⟩⟩
  rcases lt_or_eq_of_le hv.2 with h | h
  · exact (hP.erasedPath_mem ⟨hv.1, h⟩).1
  · rw [h, hP.erasedPath_clock_σ hAC]
    refine frontier_subset_closure ?_
    rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩

/-- **Aux. lemma 41** (Specification p. 204: "the pause-free erased path `ζ = ψ ∘ γ̂_C` has a
continuous Loewner driving function up to its terminal capacity time. In particular it has the
order-sensitive uniform simple approximations required in Proposition 6.12"), under Aux. lemma 37's
attachment constancy, for every Jordan coordinate `ψ` of `C` with `x₀ ↦ ∞`, `y₀ ↦ 0`: on every
`[0, S']`, `0 < S' < ℓ(σ)`, the fillings of `ζ` are the hulls of a continuous driver `W'` after a
continuous strictly increasing capacity change `σ'`, and `ζ` has the uniform simple approximations
on every `[0, S]`, `S < S'`. -/
theorem aux41 (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {S' : ℝ} (hS'0 : 0 < S')
    (hS' : S' < pocketClock η C τ σ σ) :
    (∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧
      StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
      ∀ t ∈ Icc 0 S', fwdHull W' (σ' t) =
        fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 t)) ∧
      ∀ S < S', HasSimpleApproxOn (fun v => ψ (erasedPath η C τ σ v)) S := by
  have hsub : Icc 0 S' ⊆ Ico 0 (pocketClock η C τ σ σ) := fun v hv => ⟨hv.1, hv.2.trans_lt hS'⟩
  have key := fun {S : ℝ} (hSS' : S < S') =>
    exists_loewner_and_hasSimpleApproxOn_of_hasContinuousOwnFuture hS'0
      ((hP.continuousOn_ζ hAC hψ).mono hsub) (hP.ζ_zero hAC hψ) ((hP.mapsTo_ζ hψ).mono_left hsub)
      (hP.strictMonoOn_fillH_ζ hAC hψ hS') (hP.hasContinuousOwnFuture hAC hψ hS') hSS'
  exact ⟨(key (S := S' / 2) (by linarith)).1, fun S hS => (key hS).2⟩

/-- **Aux. lemmas 40–41, existence form**: the pocket has a Jordan coordinate `ψ` (`x₀ ↦ ∞`,
`y₀ ↦ 0`) in which the erased path has a continuous Loewner driver up to its terminal capacity time
and the uniform simple approximations. -/
theorem exists_aux41 (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    0 < pocketClock η C τ σ σ ∧ ∃ ψ : ℂ → ℂ, IsJordanCoord C (α₁ 0) (α₁ 1) ψ ∧
      ∀ S' ∈ Ioo 0 (pocketClock η C τ σ σ),
        (∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ σ' : ℝ → ℝ, σ' 0 = 0 ∧
          StrictMonoOn σ' (Icc 0 S') ∧ ContinuousOn σ' (Icc 0 S') ∧
          ∀ t ∈ Icc 0 S', fwdHull W' (σ' t) =
            fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 t)) ∧
          ∀ S < S', HasSimpleApproxOn (fun v => ψ (erasedPath η C τ σ v)) S := by
  obtain ⟨ψ, hψ⟩ := hP.exists_isJordanCoord
  exact ⟨hP.clock_σ_pos hAC, ψ, hψ, fun S' hS' => hP.aux41 hAC hψ hS'.1 hS'.2⟩

end IsReversePocket

end InteractingSLE.Sec6
