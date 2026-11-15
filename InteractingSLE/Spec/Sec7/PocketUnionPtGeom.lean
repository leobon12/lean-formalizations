/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCouplingMean
import InteractingSLE.Spec.Sec7.PocketTraversalErase

/-!
# The relative active domain of the pocket traversal is the ambient pocket domain at `T(q)`

Packet PROVE-STRIPSYS32. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L213–L224, p. 396):
"Let `q(t)` be the relative half-plane capacity accumulated by the erased prefix, divided by two. […] Its right inverse
`T(s) = inf{t ≥ τ : q(t) > s}` (ER2) is an ambient stopping time […] The relative active domain at `S` is exactly
the target component of `C ∖ R_{T(S)}`."

For the erased counterflow traversal `γ = relCurve (ψ ∘ γ̂_C) L` of a reverse-contained pocket `C` (Aux. lemmas 40–41,
`Sec6.IsReversePocket`, `Sec6.IsReversePocketInf`) in a Jordan coordinate `ψ`, this file names the **ambient time of
the relative capacity time `q`**, `T(q) = fR(clockOf L (capInv γ q))` (`ambTime`, `ambTimeInf`), and proves

* `image_inter_domain_ambTime`, `image_inter_domain_ambTimeInf`: **`ψ(C ∩ D_{T(q)}) = ℍ ∖ K^{rel}_q`**, where
  `D_t = ℍ ∖ fwdHull W t` is the counterflow's active domain and `K^{rel}_q` the hull of the relative driver
  `segDriver γ` at `q` (Aux. lemma 41's (GC2), `Sec6.IsReversePocket.image_inter_domain`, read at the capacity time);
* `inv_image_eq_of_image`: in a conformal chart `c = (ψ, ψ⁻¹, ℓ)` of `C`, the inverse image `c.inv(ℍ ∖ K^{rel}_q)`
  is then the ambient pocket domain `C ∩ D_{T(q)}` itself;
* `connectedComponentIn_subset_inter`: **`C ∩ D_t` is a union of components of `ℍ ∖ K`** for every `K` containing
  the pocket's frontier in `ℍ` and the counterflow hull `fwdHull W t ∩ ℍ`, and meeting `C` only inside the hull (for
  instance `K = m(walls) ∪ hull`, the marked union `A ∪ R_t` of Aux. lemmas 35–36, or `K = (ℍ ∖ C) ∪ hull`, the
  `B ∪ R_t` of Aux. lemma 124).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketUnionPt

open PocketTraversal Lemma71C

/-! ### The ambient time of a relative capacity time -/

/-- **The ambient time of the relative capacity time `q`** (bounded pocket, (ER2)): the right end of the erasure-clock
fibre of the erased time `clockOf L (capInv γ q)`, `γ` the erased traversal in the coordinate `ψ`. -/
def ambTime (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) (q : ℝ) : ℝ :=
  Sec6.pocketFibre η C τ σ (clockOf (Sec6.pocketClock η C τ σ σ)
    (capInv (relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ)) q))

/-- **The ambient time of the relative capacity time `q`** (pocket opening at the flow seed). -/
def ambTimeInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (ψ : ℂ → ℂ) (q : ℝ) : ℝ :=
  Sec6.pocketFibreInf η C τ (clockOf (Sec6.clockEnd η C τ)
    (capInv (relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ)) q))

section Erase

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative active domain is the ambient pocket domain at `T(q)`** (bounded pocket; Aux. lemma 125's
"the relative active domain at `S` is exactly the target component of `C ∖ R_{T(S)}`"):
`ψ(C ∩ D_{T(q)}) = ℍ ∖ K^{rel}_q` for every relative capacity time `q` below the terminal one. -/
theorem image_inter_domain_ambTime (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (hψ : Sec6.IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q <
      capLife (relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ))) :
    ψ '' (C ∩ (H \ fwdHull W (ambTime η C τ σ ψ q))) =
      H \ fwdHull (fun s : ℝ => segDriver
        (relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ)) s.toNNReal) q := by
  set ζ : ℝ → ℂ := fun v => ψ (Sec6.erasedPath η C τ σ v) with hζ
  set L := Sec6.pocketClock η C τ σ σ with hLdef
  have hL : 0 < L := hP.clock_σ_pos hAC
  have hγ : IsDrivenCurve (relCurve ζ L) := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have h0 : 0 ≤ capInv (relCurve ζ L) q := capInv_nonneg _ _
  rw [hγ.fwdHull_segDriver hq0 hq, image_relCurve_Icc ζ hL h0]
  exact hP.image_inter_domain hAC hψ (clockOf_mem_Ico hL h0)

/-- **The relative active domain is the ambient pocket domain at `T(q)`** (pocket opening at the flow seed). -/
theorem image_inter_domain_ambTimeInf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (hψ : Sec6.IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ))) :
    ψ '' (C ∩ (H \ fwdHull W (ambTimeInf η C τ ψ q))) =
      H \ fwdHull (fun s : ℝ => segDriver
        (relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ)) s.toNNReal) q := by
  set ζ : ℝ → ℂ := fun v => ψ (Sec6.erasedPathInf η C τ v) with hζ
  set L := Sec6.clockEnd η C τ with hLdef
  have hL : 0 < L := hP.clockEnd_pos hAC
  have hγ : IsDrivenCurve (relCurve ζ L) := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have h0 : 0 ≤ capInv (relCurve ζ L) q := capInv_nonneg _ _
  rw [hγ.fwdHull_segDriver hq0 hq, image_relCurve_Icc ζ hL h0]
  exact hP.image_inter_domain hAC hψ (clockOf_mem_Ico hL h0)

/-- The ambient active domain at `T(q)` is open (bounded pocket). -/
theorem isOpen_H_diff_fwdHull_ambTime (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (ψ : ℂ → ℂ) (q : ℝ) :
    IsOpen (H \ fwdHull W (ambTime η C τ σ ψ q)) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull hP.continuous_W (hP.nonneg.trans (hP.fibre_mem _).1)

/-- The ambient active domain at `T(q)` is open (pocket opening at the flow seed). -/
theorem isOpen_H_diff_fwdHull_ambTimeInf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (ψ : ℂ → ℂ) (q : ℝ) :
    IsOpen (H \ fwdHull W (ambTimeInf η C τ ψ q)) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull hP.continuous_W
    (hP.nonneg.trans (hP.fibre_mem (clockOf_mem_Ico (hP.clockEnd_pos hAC) (capInv_nonneg _ _))))

end Erase

/-! ### Charts and components -/

section Chart

/-- **The chart inverse of a relative active domain** : if `c = (ψ, ψ⁻¹, ℓ)` is a conformal chart of `C`
(`c.inv(ℍ) = C`, `c.fwd = ψ` on `C`, `ψ` injective on `C`) and `ψ(S) = ℍ ∖ X` for some `S ⊆ C`, then
`c.inv(ℍ ∖ X) = S`. -/
theorem inv_image_eq_of_image {c : Chart} (hc : c.IsConformal) {C : Set ℂ} (hdom : (c.dom : Set ℂ) = C)
    {ψ : ℂ → ℂ} (hfwd : EqOn c.1 ψ C) (hinj : InjOn ψ C) {S X : Set ℂ} (hSC : S ⊆ C) (hS : ψ '' S = H \ X) :
    c.2.1 '' (H \ X) = S := by
  have hinvC : ∀ w ∈ H, c.2.1 w ∈ C := fun w hw => by
    rw [← hdom, hc.coe_dom]
    exact mem_image_of_mem _ hw
  have hψinv : ∀ w ∈ H, ψ (c.2.1 w) = w := fun w hw => by
    rw [← hfwd (hinvC w hw)]
    exact hc.2.2 w hw
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← hS] at hw
    obtain ⟨z', hz', rfl⟩ := hw
    have hwH : ψ z' ∈ H := by
      have : ψ z' ∈ ψ '' S := mem_image_of_mem _ hz'
      rw [hS] at this
      exact this.1
    have : c.2.1 (ψ z') = z' := hinj (hinvC _ hwH) (hSC hz') (hψinv _ hwH)
    rw [this]
    exact hz'
  · intro hz
    have hw : ψ z ∈ H \ X := by
      rw [← hS]
      exact mem_image_of_mem _ hz
    refine ⟨ψ z, hw, ?_⟩
    exact hinj (hinvC _ hw.1) (hSC hz) (hψinv _ hw.1)

/-- **The ambient pocket domain is a union of components of `ℍ ∖ K`**: for `C` open, if `K` contains the
frontier of `C` in `ℍ` and `ℍ ∖ D`, then every component of `ℍ ∖ K` through a point of `C ∩ D` stays in `C ∩ D`. -/
theorem connectedComponentIn_subset_inter {C D K : Set ℂ} (hCo : IsOpen C)
    (hfr : frontier C ∩ H ⊆ K) (hD : H \ D ⊆ K) {z : ℂ} (hz : z ∈ C ∩ D) :
    connectedComponentIn (H \ K) z ⊆ C ∩ D := by
  by_cases hzK : z ∈ H \ K
  swap
  · rw [connectedComponentIn_eq_empty hzK]
    exact empty_subset _
  set Z := connectedComponentIn (H \ K) z with hZ
  have hZsub : Z ⊆ H \ K := connectedComponentIn_subset _ _
  have hZC : Z ⊆ C := by
    refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hCo
      ⟨z, mem_connectedComponentIn hzK, hz.1⟩ ?_
    · rintro x ⟨hxc, hxZ⟩
      by_contra hxC
      have hxfr : x ∈ frontier C := by
        rw [hCo.frontier_eq]
        exact ⟨hxc, hxC⟩
      exact (hZsub hxZ).2 (hfr ⟨hxfr, (hZsub hxZ).1⟩)
  intro x hx
  refine ⟨hZC hx, ?_⟩
  by_contra hxD
  exact (hZsub hx).2 (hD ⟨(hZsub hx).1, hxD⟩)

end Chart

end InteractingSLE.Sec7.PocketUnionPt
