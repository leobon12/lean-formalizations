/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterCfg
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Theorem R.7's outer pockets: the relative hull set and the relative active domain inside the ambient one

Packet PROVE-HOUTER. Supplement §5.4 (`source/spec/p433-480.md` L976–L997, pp. 473–474): for a mixed or outer pocket
`C`, "`E_s` [is] the component of `C ∖ R_s` incident to `x_C`"; "Outer-tail bulges can remain active in `D_s`". So,
unlike the contained case (`PocketUnionPt.image_inter_domain_ambTime`, Aux. lemma 41's (GC2)), the relative active
domain is in general **not** `C ∩ D_{T(q)}`: the ambient pocket domain keeps the bulges between the outer arm and its
certified frontier. The stop-level statement `R7Pocket.R7PocketStopStatement` leaves the hull sets `F q` free; here they
are chosen as the **relative hull sets**

  `relHull C ψ γ q = ℍ ∖ (C ∩ ψ⁻¹(ℍ ∖ K_q))`,  `K_q` the hull of the traversal's driver at relative capacity `q`,

for which the geometric identity `ψ(C ∩ (ℍ ∖ F q)) = ℍ ∖ K_q` and the openness of `ℍ ∖ F q` hold by construction
(`image_inter_H_diff_relHull`, `isOpen_H_diff_relHull`). The geometric content moves to the following inclusion, used
to transfer the walls' marked union law at the ambient stop to these sets:

* **`mem_domain_of_not_mem_fillH`** (deterministic, face-free): for an erasure pocket `C` (`R7StopIn.IsErasurePocket`)
  of a Loewner trace, a Jordan coordinate `ψ` and an erased time `u < ℓ(σ)`, every `w ∈ C` with `ψ(w)` off the filled
  erased image `fill(ζ([0, u]))` is in the ambient domain `D_{fR(u)}` at the right end of the clock fibre of `u`. Proof:
  the Jordan preimage of the unbounded component of `ℍ ∖ ζ([0, u])` containing `ψ(w)` is preconnected, misses
  `η([0, fR(u)])` by (GC2), and accumulates at the terminal point `x₀ = η(σ)` (the coordinate is bounded away from
  `x₀`); a small half-disc at `x₀` misses `η([0, fR(u)])` (freshness) and meets `D_{fR(u)}` (the tip lies in the
  closure of the domain); so their union lies in `D_{fR(u)}`.
* **`relDomain_subset_domain`**, **`relDomain_subset_domain_ambTime0`**: hence
  `C ∩ ψ⁻¹(ℍ ∖ K_q) ⊆ D_{T(q)} ⊆ D_{T⁰(q)}`.
* The same at infinity (`mem_domain_of_not_mem_fillH_inf`, `relDomain_subset_domain_ambTime0Inf`), where the preimage
  is unbounded.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.HOuter

open Sec6 PocketTraversal Lemma71C R7StopIn

/-! ### The relative hull sets -/

/-- **The relative hull set at relative capacity time `q`**: everything of `ℍ` outside the Jordan preimage
`C ∩ ψ⁻¹(ℍ ∖ K_q)` of the relative active domain, `K_q` the hull of the driver of `γ` at `q`. -/
def relHull (C : Set ℂ) (ψ : ℂ → ℂ) (γ : ℝ → ℂ) (q : ℝ≥0) : Set ℂ :=
  H \ (C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q))

theorem H_diff_relHull {C : Set ℂ} (hCH : C ⊆ H) (ψ : ℂ → ℂ) (γ : ℝ → ℂ) (q : ℝ≥0) :
    H \ relHull C ψ γ q = C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q) := by
  rw [relHull, sdiff_sdiff_right_self]
  exact inter_eq_right.2 (inter_subset_left.trans hCH)

/-- **The geometric identity holds by construction**: `ψ(C ∩ (ℍ ∖ relHull)) = ℍ ∖ K_q`. -/
theorem image_inter_H_diff_relHull {C : Set ℂ} (hCH : C ⊆ H) {ψ : ℂ → ℂ} (hψ : IsConformalBijection ψ C H)
    (γ : ℝ → ℂ) (q : ℝ≥0) :
    ψ '' (C ∩ (H \ relHull C ψ γ q)) = H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q := by
  rw [H_diff_relHull hCH, ← inter_assoc, inter_self, image_inter_preimage, hψ.2.image_eq]
  exact inter_eq_right.2 sdiff_subset

/-- **`ℍ ∖ relHull` is open** below the capacity lifetime of a driven `γ`, for `ψ` continuous on the open `C`. -/
theorem isOpen_H_diff_relHull {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ C)
    {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife γ) :
    IsOpen (H \ relHull C ψ γ q) := by
  rw [H_diff_relHull hCH]
  refine hψc.isOpen_inter_preimage hCo ?_
  rw [hγ.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
  exact InteractingSLE.isOpen_H_diff_fillH
    ((isCompact_Icc.image_of_continuousOn (hγ.continuousOn.mono fun t ht => ht.1)).isBounded)

/-! ### The relative active domain lies in the ambient domain -/

section Bounded

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative active domain lies in the ambient domain** (bounded erasure pocket; deterministic, without the
face description): for `u ∈ [0, ℓ(σ))` and `w ∈ C` with `ψ(w) ∉ fill(ζ([0, u]))`, `ζ = ψ ∘ γ̂_C`, `w` is in
`D_{fR(u)} = ℍ ∖ K_{fR(u)}`. -/
theorem mem_domain_of_not_mem_fillH (hP : IsErasurePocket η C x₀ y₀ τ σ) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hCH : C ⊆ H) (hCb : IsBounded C) (hψ : IsJordanCoord C x₀ y₀ ψ) {u : ℝ}
    (hu : u ∈ Ico 0 (pocketClock η C τ σ σ)) {w : ℂ} (hwC : w ∈ C)
    (hw : ψ w ∉ fillH ((fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u)) :
    w ∈ H \ fwdHull W (pocketFibre η C τ σ u) := by
  obtain ⟨hψc, -, -, hψconf, -, -, -⟩ := hψ
  set s := pocketFibre η C τ σ u with hsdef
  set Z : Set ℂ := (fun v => ψ (erasedPath η C τ σ v)) '' Icc 0 u with hZdef
  have hτs : τ ≤ s := (hP.fibre_mem u).1
  have hsσ : s < σ := hP.fibre_lt_σ hu
  have hs0 : 0 ≤ s := hP.nonneg.trans hτs
  have hGC2 := hP.erasedPath_image_inter (u := u) ⟨hu.1, hu.2.le⟩
  have hCsub : C ⊆ closure C \ {x₀} := fun z hz => ⟨subset_closure hz, fun h => hP.notMem_x (h ▸ hz)⟩
  -- the component of `ψ(w)` in `ℍ ∖ Z̄` is unbounded
  have hwH : ψ w ∈ H := hψconf.2.mapsTo hwC
  have hwZ : ψ w ∉ closure Z := fun h => hw ⟨hwH, Or.inl h⟩
  set V := connectedComponentIn (H \ closure Z) (ψ w) with hVdef
  have hVb : ¬ IsBounded V := fun h => hw ⟨hwH, Or.inr h⟩
  have hVsub : V ⊆ H \ closure Z := connectedComponentIn_subset _ _
  have hVpre : IsPreconnected V := isPreconnected_connectedComponentIn
  have hwV : ψ w ∈ V := mem_connectedComponentIn ⟨hwH, hwZ⟩
  -- its Jordan preimage
  set e := QuantumZipper.CA.univalentOPH hP.isOpen hψconf.1 hψconf.2.injOn with hedef
  have htarget : e.target = H := by
    rw [hedef, QuantumZipper.CA.univalentOPH_target]; exact hψconf.2.image_eq
  have hsymmC : MapsTo e.symm H C := fun v hv => by
    have := e.map_target (htarget ▸ hv)
    rwa [hedef, QuantumZipper.CA.univalentOPH_source] at this
  have hψe : ∀ v ∈ H, ψ (e.symm v) = v := fun v hv =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hP.isOpen hψconf.1 hψconf.2.injOn
      (by rw [hψconf.2.image_eq]; exact hv)
  have hew : e.symm (ψ w) = w :=
    QuantumZipper.CA.univalentOPH_symm_apply_apply hP.isOpen hψconf.1 hψconf.2.injOn hwC
  set Pr := e.symm '' V with hPrdef
  have hPpre : IsPreconnected Pr :=
    hVpre.image _ ((htarget ▸ e.continuousOn_symm).mono fun v hv => (hVsub hv).1)
  have hPC : Pr ⊆ C := by rintro _ ⟨v, hv, rfl⟩; exact hsymmC (hVsub hv).1
  have hwP : w ∈ Pr := ⟨ψ w, hwV, hew⟩
  have hPR : Disjoint Pr (η '' Icc 0 s) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hR
    have hmem : e.symm v ∈ η '' Icc 0 s ∩ C := ⟨hR, hsymmC (hVsub hv).1⟩
    rw [← hGC2] at hmem
    obtain ⟨⟨v', hv', hve⟩, -⟩ := hmem
    have : v ∈ Z := ⟨v', hv', by simp only [hve, hψe v (hVsub hv).1]⟩
    exact (hVsub hv).2 (subset_closure this)
  -- a half-disc at `x₀` missing `η([0, s])`
  have hRc : IsCompact (η '' Icc 0 s) := isCompact_Icc.image_of_continuousOn (hP.cont.mono fun t ht => ht.1)
  have hx₀R : x₀ ∉ η '' Icc 0 s := fun ⟨t, ht, he⟩ =>
    hP.fresh_x ⟨t, ⟨ht.1, ht.2.trans_lt hsσ⟩, he⟩
  obtain ⟨ε, hε, hεR⟩ := Metric.isOpen_iff.1 hRc.isClosed.isOpen_compl x₀ hx₀R
  set B := ball x₀ ε ∩ H with hBdef
  have hBpre : IsPreconnected B :=
    ((convex_ball x₀ ε).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hBR : Disjoint B (η '' Icc 0 s) := Set.disjoint_left.2 fun z hz hzR => hεR hz.1 hzR
  -- `x₀` adheres to the ambient domain at `s`
  have hσ0 : 0 ≤ σ := hP.nonneg_σ
  have hxcl : x₀ ∈ closure (H \ fwdHull W s) := by
    have h := trace_mem_closure_domain hη hW hW0 hσ0
    rw [hP.first_x] at h
    exact closure_mono (sdiff_subset_sdiff_right (WangWu.fwdHull_mono hsσ.le)) h
  obtain ⟨z₀, hz₀D, hz₀d⟩ := Metric.mem_closure_iff.1 hxcl ε hε
  have hz₀ : z₀ ∈ B := ⟨by rw [mem_ball, dist_comm]; exact hz₀d, hz₀D.1⟩
  -- the preimage meets the half-disc: the coordinate is bounded on `C̄ ∖ ball x₀ ε`
  have hKc : IsCompact (closure C \ ball x₀ ε) :=
    (hCb.isCompact_closure).diff isOpen_ball
  have hKsub : closure C \ ball x₀ ε ⊆ closure C \ {x₀} := fun z hz =>
    ⟨hz.1, fun h => hz.2 (by rw [mem_singleton_iff.1 h]; exact mem_ball_self hε)⟩
  obtain ⟨M, hM⟩ := (hKc.image_of_continuousOn (hψc.mono hKsub)).isBounded.subset_closedBall 0
  obtain ⟨v, hvV, hvM⟩ : ∃ v ∈ V, M < ‖v‖ := by
    by_contra hcon
    push Not at hcon
    exact hVb ((isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset fun v hv => by
      rw [mem_closedBall, dist_zero_right]; exact hcon v hv)
  have hyP : e.symm v ∈ Pr := ⟨v, hvV, rfl⟩
  have hyB : e.symm v ∈ B := by
    refine ⟨?_, hCH (hPC hyP)⟩
    by_contra hyb
    have hyK : e.symm v ∈ closure C \ ball x₀ ε := ⟨subset_closure (hPC hyP), hyb⟩
    have h1 := hM ⟨_, hyK, rfl⟩
    rw [hψe v (hVsub hvV).1, mem_closedBall, dist_zero_right] at h1
    exact absurd hvM (not_lt.2 h1)
  -- the union lies in the ambient domain
  have hU : IsPreconnected (Pr ∪ B) := hPpre.union (e.symm v) hyP hyB hBpre
  have hUH : Pr ∪ B ⊆ H := union_subset (hPC.trans hCH) inter_subset_right
  have hUR : Disjoint (Pr ∪ B) (η '' Icc 0 s) := Set.disjoint_union_left.2 ⟨hPR, hBR⟩
  have hsub := Sec6.subset_domain_of_isPreconnected hη hs0 hU hUH hUR (Or.inr hz₀) hz₀D
  exact hsub (Or.inl hwP)

/-- **The relative active domain at relative capacity `q` lies in the ambient domain at `T(q)`** (bounded erasure
pocket, driven relative traversal `γ = relTrav η C τ σ ψ`): `C ∩ ψ⁻¹(ℍ ∖ K_q) ⊆ D_{fR(clockOf ℓ(σ) (capInv γ q))}`. -/
theorem relDomain_subset_domain (hP : IsErasurePocket η C x₀ y₀ τ σ) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hCH : C ⊆ H) (hCb : IsBounded C) (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hγ : IsDrivenCurve (relTrav η C τ σ ψ)) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (relTrav η C τ σ ψ)) :
    C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (relTrav η C τ σ ψ) s.toNNReal) q) ⊆
      H \ fwdHull W (pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) (capInv (relTrav η C τ σ ψ) q))) := by
  have hL := hP.clock_σ_pos
  have h0 : 0 ≤ capInv (relTrav η C τ σ ψ) q := capInv_nonneg _ _
  rintro w ⟨hwC, hwD⟩
  refine mem_domain_of_not_mem_fillH hP hη hW hW0 hCH hCb hψ (clockOf_mem_Ico hL h0) hwC fun hK => hwD.2 ?_
  rw [hγ.fwdHull_segDriver hq0 hq, image_relCurve_Icc _ hL h0]
  exact hK

/-- **The relative active domain lies in the ambient domain at the left fibre end `T⁰(q)`** (ruling R67's stop):
`C ∩ ψ⁻¹(ℍ ∖ K_q) ⊆ D_{T⁰(q)}`, since `T⁰(q) ≤ T(q)` and the hulls increase. -/
theorem relDomain_subset_domain_ambTime0 (hP : IsErasurePocket η C x₀ y₀ τ σ) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hCH : C ⊆ H) (hCb : IsBounded C) (hψ : IsJordanCoord C x₀ y₀ ψ)
    (hγ : IsDrivenCurve (relTrav η C τ σ ψ)) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (relTrav η C τ σ ψ)) :
    C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (relTrav η C τ σ ψ) s.toNNReal) q) ⊆
      H \ fwdHull W (PocketStopWallsFin.ambTime0 η C τ σ ψ q) := by
  refine (relDomain_subset_domain hP hη hW hW0 hCH hCb hψ hγ hq0 hq).trans
    (sdiff_subset_sdiff_right (WangWu.fwdHull_mono ?_))
  have hv := clockOf_mem_Ico hP.clock_σ_pos (capInv_nonneg (relTrav η C τ σ ψ) q)
  exact PocketStopWallsFin.fibreLeft_le_fibreRight hP.continuous_clock hP.lt.le
    (by rw [IsErasurePocket.clock_τ]; exact ⟨hv.1, hv.2.le⟩)

end Bounded

section Inf

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative active domain lies in the ambient domain** (erasure pocket opening at the flow seed): for
`u ∈ [0, ℓ(∞))` and `w ∈ C` with `ψ(w) ∉ fill(ζ([0, u]))`, `w ∈ D_{fR(u)}`. Here the Jordan preimage of the unbounded
component is itself unbounded (the coordinate is bounded on bounded parts of `C̄`). -/
theorem mem_domain_of_not_mem_fillH_inf (hP : IsErasurePocketInf η C y₀ τ) (hη : IsLoewnerTrace W η)
    (hCH : C ⊆ H) (hψ : IsJordanCoordInf C y₀ ψ) {u : ℝ} (hu : u ∈ Ico 0 (clockEnd η C τ)) {w : ℂ}
    (hwC : w ∈ C) (hw : ψ w ∉ fillH ((fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u)) :
    w ∈ H \ fwdHull W (pocketFibreInf η C τ u) := by
  obtain ⟨hψc, -, -, hψconf, -, -, -⟩ := hψ
  set s := pocketFibreInf η C τ u with hsdef
  set Z : Set ℂ := (fun v => ψ (erasedPathInf η C τ v)) '' Icc 0 u with hZdef
  have hs0 : 0 ≤ s := hP.fibre_nonneg hu
  have hGC2 := hP.erasedPath_image_inter hu
  have hwH : ψ w ∈ H := hψconf.2.mapsTo hwC
  have hwZ : ψ w ∉ closure Z := fun h => hw ⟨hwH, Or.inl h⟩
  set V := connectedComponentIn (H \ closure Z) (ψ w) with hVdef
  have hVb : ¬ IsBounded V := fun h => hw ⟨hwH, Or.inr h⟩
  have hVsub : V ⊆ H \ closure Z := connectedComponentIn_subset _ _
  have hVpre : IsPreconnected V := isPreconnected_connectedComponentIn
  have hwV : ψ w ∈ V := mem_connectedComponentIn ⟨hwH, hwZ⟩
  set e := QuantumZipper.CA.univalentOPH hP.isOpen hψconf.1 hψconf.2.injOn with hedef
  have htarget : e.target = H := by
    rw [hedef, QuantumZipper.CA.univalentOPH_target]; exact hψconf.2.image_eq
  have hsymmC : MapsTo e.symm H C := fun v hv => by
    have := e.map_target (htarget ▸ hv)
    rwa [hedef, QuantumZipper.CA.univalentOPH_source] at this
  have hψe : ∀ v ∈ H, ψ (e.symm v) = v := fun v hv =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply hP.isOpen hψconf.1 hψconf.2.injOn
      (by rw [hψconf.2.image_eq]; exact hv)
  have hew : e.symm (ψ w) = w :=
    QuantumZipper.CA.univalentOPH_symm_apply_apply hP.isOpen hψconf.1 hψconf.2.injOn hwC
  set Pr := e.symm '' V with hPrdef
  have hPpre : IsPreconnected Pr :=
    hVpre.image _ ((htarget ▸ e.continuousOn_symm).mono fun v hv => (hVsub hv).1)
  have hPC : Pr ⊆ C := by rintro _ ⟨v, hv, rfl⟩; exact hsymmC (hVsub hv).1
  have hwP : w ∈ Pr := ⟨ψ w, hwV, hew⟩
  have hPR : Disjoint Pr (η '' Icc 0 s) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨v, hv, rfl⟩ hR
    have hmem : e.symm v ∈ η '' Icc 0 s ∩ C := ⟨hR, hsymmC (hVsub hv).1⟩
    rw [← hGC2] at hmem
    obtain ⟨⟨v', hv', hve⟩, -⟩ := hmem
    have : v ∈ Z := ⟨v', hv', by simp only [hve, hψe v (hVsub hv).1]⟩
    exact (hVsub hv).2 (subset_closure this)
  -- the preimage is unbounded
  have hPb : ¬ IsBounded Pr := by
    intro hb
    obtain ⟨ρ, hρ⟩ := hb.subset_closedBall 0
    have hKc : IsCompact (closure C ∩ closedBall 0 ρ) := (isCompact_closedBall 0 ρ).inter_left isClosed_closure
    obtain ⟨M, hM⟩ := (hKc.image_of_continuousOn (hψc.mono inter_subset_left)).isBounded.subset_closedBall 0
    obtain ⟨v, hvV, hvM⟩ : ∃ v ∈ V, M < ‖v‖ := by
      by_contra hcon
      push Not at hcon
      exact hVb ((isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset fun v hv => by
        rw [mem_closedBall, dist_zero_right]; exact hcon v hv)
    have hyP : e.symm v ∈ Pr := ⟨v, hvV, rfl⟩
    have h1 := hM ⟨_, ⟨subset_closure (hPC hyP), hρ hyP⟩, rfl⟩
    rw [hψe v (hVsub hvV).1, mem_closedBall, dist_zero_right] at h1
    exact absurd hvM (not_lt.2 h1)
  exact Sec6.subset_domain_of_not_isBounded hη hs0 hPpre (hPC.trans hCH) hPR hPb hwP

/-- **The relative active domain at relative capacity `q` lies in the ambient domain at `T⁰(q)`** (pocket opening at
the flow seed). -/
theorem relDomain_subset_domain_ambTime0Inf (hP : IsErasurePocketInf η C y₀ τ) (hη : IsLoewnerTrace W η)
    (hCH : C ⊆ H) (hψ : IsJordanCoordInf C y₀ ψ) (hγ : IsDrivenCurve (relTravInf η C τ ψ)) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (relTravInf η C τ ψ)) :
    C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (relTravInf η C τ ψ) s.toNNReal) q) ⊆
      H \ fwdHull W (PocketStopWallsFin.ambTime0Inf η C τ ψ q) := by
  have hL := hP.clockEnd_pos
  have h0 : 0 ≤ capInv (relTravInf η C τ ψ) q := capInv_nonneg _ _
  have hv := clockOf_mem_Ico hL h0
  rintro w ⟨hwC, hwD⟩
  have hw := mem_domain_of_not_mem_fillH_inf (W := W) hP hη hCH hψ hv hwC fun hK => hwD.2 (by
    rw [hγ.fwdHull_segDriver hq0 hq, image_relCurve_Icc _ hL h0]
    exact hK)
  refine (sdiff_subset_sdiff_right (WangWu.fwdHull_mono ?_)) hw
  exact csInf_le ⟨τ, fun _ ht => ht.1⟩ ⟨hP.fibre_mem hv, (hP.clock_fibre hv).ge⟩

end Inf

end InteractingSLE.Sec7.HOuter
