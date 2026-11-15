/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketTraversalErase
import InteractingSLE.Spec.Sec7.Aux125Life

/-!
# The infinite relative lifetime of the erased pocket traversal (Aux. lemma 125)

Packet PROVE-STRIPSYS13. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L224–L232, p. 397):

> If `ζ` were finite, continuity of the complete pocket traversal and the Jordan boundary homeomorphism would give
> `|X_C(s)| → ∞` as `s ↑ ζ`. The preceding bound makes the driver bounded on that finite interval. The elementary
> Loewner rectangle bound then bounds the whole trace prefix, a contradiction. Thus `ζ = ∞`.

PROVE-STRIPSYS7 proved the analytic half (`Aux125.lifetime_eq_top_of_not_isBounded`: a solution of the path equations
of Definition 2.1 before `ζ`, with continuous noise and side totals `≠ −2`, whose hulls before a finite `ζ` are
unbounded, has `ζ = ∞`). This file proves the geometric half for the erased pocket traversal in its Jordan coordinate
(`PocketTraversal.relCurve`) and assembles the two:

* `mem_iUnion_fwdHull_segDriver`: for a driven curve (`PocketTraversal.IsDrivenCurve`), every curve point in `ℍ` lies
  in a hull of the canonical driver `segDriver γ` before the terminal capacity time `capLife γ`;
* `not_isBounded_iUnion_fwdHull_segDriver`: hence these hulls are unbounded when the curve has points of `ℍ` of
  arbitrarily large modulus;
* **`capLife_eq_top_of_driverEq`**: Aux. lemma 125's conclusion `ζ = ∞` for a driven curve whose canonical driver
  solves the path equations before `capLife γ`;
* **`exists_relCurve_mem_H_lt_norm_of_isReversePocket`** (finite junction `x₀`) and
  **`exists_relCurve_mem_H_lt_norm_of_isReversePocketInf`** (junction at `∞`, with the counterflow transient): the
  relative curve `ψ ∘ γ̂_C` has points of `ℍ` of arbitrarily large modulus ("`|X_C(s)| → ∞`"), at the interior visit
  times of the pocket;
* **`capLife_relCurve_eq_top_of_isReversePocket`**, **`capLife_relCurve_eq_top_of_isReversePocketInf`**: the relative
  lifetime of the erased pocket traversal is infinite as soon as its canonical relative driver solves the path
  equations of Definition 2.1 before it (Aux. lemma 122's conclusion) with a continuous noise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex Bornology
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketLife

open Lemma71C PocketTraversal

/-! ### Driven curves: the hulls before the terminal capacity time contain the curve -/

section Driven

variable {γ : ℝ → ℂ}

/-- **Every curve point of `ℍ` lies in a hull of the canonical driver before the terminal capacity time**: for
`u ≥ 0` with `γ(u) ∈ ℍ`, `γ(u) ∈ K_s` for `s = capClock γ u < capLife γ`. -/
theorem mem_iUnion_fwdHull_segDriver (hγ : IsDrivenCurve γ) {u : ℝ} (hu : 0 ≤ u) (huH : γ u ∈ H) :
    γ u ∈ ⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < capLife γ), fwdHull (fun r : ℝ => segDriver γ r.toNNReal) s := by
  have hc0 := hγ.capClock_nonneg hu
  have hlt := hγ.ofReal_capClock_lt hu
  refine mem_iUnion₂.2 ⟨(capClock γ u).toNNReal, hlt, ?_⟩
  rw [Real.coe_toNNReal _ hc0, hγ.fwdHull_segDriver hc0 hlt, hγ.capInv_eq hu]
  exact mem_fillH_of_mem_closure huH (subset_closure ⟨u, ⟨hu, le_rfl⟩, rfl⟩)

/-- **The hulls before the terminal capacity time are unbounded** when the curve has points of `ℍ` of arbitrarily
large modulus. -/
theorem not_isBounded_iUnion_fwdHull_segDriver (hγ : IsDrivenCurve γ)
    (hunb : ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ u ∈ H ∧ M < ‖γ u‖) :
    ¬ IsBounded (⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < capLife γ), fwdHull (fun r : ℝ => segDriver γ r.toNNReal) s) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨u, hu, huH, hMu⟩ := hunb M
  exact absurd (hM _ (mem_iUnion_fwdHull_segDriver hγ hu huH)) (not_le.2 hMu)

/-- **Before a finite terminal capacity time the canonical driver is unbounded** (the contrapositive of the Loewner
rectangle bound, `Aux125.iUnion_fwdHull_subset_closedBall`), when the curve has points of `ℍ` of arbitrarily large
modulus. -/
theorem exists_lt_abs_segDriver (hγ : IsDrivenCurve γ) (hunb : ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ u ∈ H ∧ M < ‖γ u‖)
    (hfin : capLife γ ≠ ⊤) (M : ℝ) : ∃ s : ℝ≥0, (s : ℝ≥0∞) < capLife γ ∧ M < |segDriver γ s| := by
  by_contra hcon
  push Not at hcon
  set T : ℝ≥0 := (capLife γ).toNNReal with hTdef
  have hTe : (T : ℝ≥0∞) = capLife γ := ENNReal.coe_toNNReal hfin
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife γ ↔ t < T := fun t => by rw [← hTe]; exact ENNReal.coe_lt_coe
  have hwc : ContinuousOn (segDriver γ) (Iio T) := hγ.segDriver_spec.2.1.mono fun t ht => (hlt t).2 ht
  have hsub := Aux125.iUnion_fwdHull_subset_closedBall hwc fun t ht => hcon t ((hlt t).2 ht)
  refine not_isBounded_iUnion_fwdHull_segDriver hγ hunb (Metric.isBounded_closedBall.subset fun z hz => hsub ?_)
  obtain ⟨s, hs, hzs⟩ := mem_iUnion₂.1 hz
  exact mem_iUnion₂.2 ⟨s, (hlt s).1 hs, hzs⟩

/-- **Aux. lemma 125's infinite relative lifetime for a driven curve**: if the canonical driver `segDriver γ`, with
force paths `vL`, `vR`, solves the path equations of Definition 2.1 before `capLife γ` (no maximality) with a
continuous noise `b` and both side totals `≠ −2`, and the curve has points of `ℍ` of arbitrarily large modulus, then
`capLife γ = ∞`. -/
theorem capLife_eq_top_of_driverEq (hγ : IsDrivenCurve γ) (hunb : ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ u ∈ H ∧ M < ‖γ u‖)
    {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : Aux125.IsForcePathPre xL xR ρL ρR (segDriver γ) vL vR (capLife γ))
    (hw : Sec2.DriverEq a ρL ρR (segDriver γ) vL vR b (capLife γ)) (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2)
    (hR : ∑ j, ρR j ≠ -2) : capLife γ = ⊤ :=
  Aux125.lifetime_eq_top_of_not_isBounded h hw hb hL hR fun _ => not_isBounded_iUnion_fwdHull_segDriver hγ hunb

/-- **The same, below an SDE lifetime** (`Aux125.lifetime_eq_top_of_le`): if the canonical driver solves Definition 2.1
up to a lifetime `ζ ≥ capLife γ` (for instance the continuation threshold of Aux. lemma 122's evolution) with a
continuous noise, then `capLife γ = ∞`. -/
theorem capLife_eq_top_of_isIntegratedSLEPath (hγ : IsDrivenCurve γ)
    (hunb : ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ u ∈ H ∧ M < ‖γ u‖)
    {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR (segDriver γ) vL vR b ζ) (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2)
    (hR : ∑ j, ρR j ≠ -2) (hle : capLife γ ≤ ζ) : capLife γ = ⊤ :=
  Aux125.lifetime_eq_top_of_le h hb hL hR hle fun _ => not_isBounded_iUnion_fwdHull_segDriver hγ hunb

end Driven

/-! ### The relative curve at the interior visit times -/

section Visit

variable {L : ℝ}

/-- The reparametrization hits every `v ∈ [0, L)`: `clockOf L (v / (L - v)) = v`. -/
theorem clockOf_div_sub (hL : 0 < L) {v : ℝ} (hv : v < L) : clockOf L (v / (L - v)) = v := by
  unfold clockOf
  have h : L - v ≠ 0 := (sub_pos.2 hv).ne'
  have h' : 1 + v / (L - v) = L / (L - v) := by field_simp; ring
  rw [h', div_div_div_cancel_right₀ h, mul_div_cancel₀ _ hL.ne']

theorem div_sub_nonneg {v : ℝ} (hv0 : 0 ≤ v) (hv : v < L) : 0 ≤ v / (L - v) :=
  div_nonneg hv0 (sub_pos.2 hv).le

end Visit

section Pocket

open Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative curve passes through `ψ(η t)` at an interior visit time `t`** (finite junction): with
`L = ℓ(σ)` and `v = ℓ(t)`, at the relative parameter `v / (L − v)`. -/
theorem relCurve_of_mem_visitSet (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) {t : ℝ} (htI : t ∈ visitSet η C τ σ) :
    0 ≤ pocketClock η C τ σ t / (pocketClock η C τ σ σ - pocketClock η C τ σ t) ∧
      relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ)
        (pocketClock η C τ σ t / (pocketClock η C τ σ σ - pocketClock η C τ σ t)) = ψ (η t) := by
  have hL := hP.clock_σ_pos hAC
  have hv0 := hP.clock_nonneg htI.1.1.le
  have hv := hP.clock_lt_clock_σ hAC ⟨htI.1.1.le, htI.1.2⟩
  refine ⟨div_sub_nonneg hv0 hv, ?_⟩
  simp only [relCurve, clockOf_div_sub hL hv, erasedPath, hP.fibre_clock_of_mem htI]

/-- **"`|X_C(s)| → ∞`"** (proof of Aux. lemma 125, finite junction `x₀`): the relative curve of the erased traversal in
a Jordan coordinate `ψ` (`x₀ ↦ ∞`) has points of `ℍ` of arbitrarily large modulus, at interior visit times close to
`σ = T(x₀)`. -/
theorem exists_relCurve_mem_H_lt_norm_of_isReversePocket (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) (M : ℝ) :
    ∃ u, 0 ≤ u ∧ relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) u ∈ H ∧
      M < ‖relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) u‖ := by
  -- near `x₀`, within `C̄ \ {x₀}`, the coordinate has modulus `> M`
  have hev : ∀ᶠ z in 𝓝[closure C \ {α₁ 0}] (α₁ 0), M < ‖ψ z‖ :=
    (tendsto_norm_cobounded_atTop.comp hψ.2.2.2.2.2.2).eventually (eventually_gt_atTop M)
  obtain ⟨ε, hε, hεM⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  -- the trace is near `x₀ = η σ` shortly before `σ`
  have hηc : ContinuousWithinAt η (Ici 0) σ := hP.trace.2.1 σ hP.nonneg_σ
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hηc ε hε
  set a := max τ (σ - δ / 2) with ha
  have haσ : a < σ := max_lt hP.τ_lt_σ (by linarith)
  have hℓ := hP.clock_lt_clock_σ hAC ⟨le_max_left _ _, haσ⟩
  obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt haσ hℓ.ne
  have ht0 : 0 ≤ t := hP.nonneg.trans ((le_max_left _ _).trans ht.1.le)
  have hdt : dist t σ < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith [ht.2])]
    have : σ - δ / 2 ≤ a := le_max_right _ _
    linarith [ht.1]
  have hηt : dist (η t) (α₁ 0) < ε := by
    have := hδε ht0 hdt
    rwa [hP.first_x] at this
  -- `η t ∈ C`, so `η t ≠ x₀ ∈ ∂C`
  have hx₀ : α₁ 0 ∈ frontier C := by
    rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hne : η t ≠ α₁ 0 := fun h => by
    have := hP.isOpen.inter_frontier_eq
    exact (Set.eq_empty_iff_forall_notMem.1 this) (α₁ 0) ⟨h ▸ htI.2, hx₀⟩
  have hMt : M < ‖ψ (η t)‖ := hεM hηt ⟨subset_closure htI.2, hne⟩
  obtain ⟨hu, he⟩ := relCurve_of_mem_visitSet (ψ := ψ) hP hAC htI
  exact ⟨_, hu, he ▸ hψ.2.2.2.1.2.mapsTo htI.2, he ▸ hMt⟩

/-- **The relative lifetime of the erased traversal is infinite** (Aux. lemma 125, finite junction): if the canonical
relative driver solves the path equations of Definition 2.1 before its terminal capacity time with a continuous noise
and side totals `≠ −2` (Aux. lemma 122's conclusion), then the relative curve has infinite capacity lifetime. -/
theorem capLife_relCurve_eq_top_of_isReversePocket (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ)
    {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : Aux125.IsForcePathPre xL xR ρL ρR
      (segDriver (relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ))) vL vR
      (capLife (relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ))))
    (hw : Sec2.DriverEq a ρL ρR
      (segDriver (relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ))) vL vR b
      (capLife (relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ))))
    (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) :
    capLife (relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ)) = ⊤ :=
  capLife_eq_top_of_driverEq (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ)
    (exists_relCurve_mem_H_lt_norm_of_isReversePocket hP hAC hψ) h hw hb hL hR

/-- **The relative curve passes through `ψ(η t)` at an interior visit time `t`** (junction at `∞`): with
`L = ℓ(∞)` and `v = ℓ(t)`, at the relative parameter `v / (L − v)`. -/
theorem relCurve_of_mem_visitSetInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {t : ℝ} (htI : t ∈ visitSetInf η C τ) :
    0 ≤ pocketClockInf η C τ t / (clockEnd η C τ - pocketClockInf η C τ t) ∧
      relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ)
        (pocketClockInf η C τ t / (clockEnd η C τ - pocketClockInf η C τ t)) = ψ (η t) := by
  have hL := hP.clockEnd_pos hAC
  have hv0 := hP.clock_nonneg (le_of_lt htI.1)
  have hv := hP.clock_lt_clockEnd_of_mem htI
  refine ⟨div_sub_nonneg hv0 hv, ?_⟩
  simp only [relCurve, clockOf_div_sub hL hv, erasedPathInf, hP.fibre_clock_of_mem htI]

/-- **"`|X_C(s)| → ∞`"** (proof of Aux. lemma 125, junction at the original target `∞`): if the counterflow is
transient, the relative curve of the erased traversal in a Jordan coordinate at infinity has points of `ℍ` of
arbitrarily large modulus, at late interior visit times. -/
theorem exists_relCurve_mem_H_lt_norm_of_isReversePocketInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop) (M : ℝ) :
    ∃ u, 0 ≤ u ∧ relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ) u ∈ H ∧
      M < ‖relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ) u‖ := by
  -- far out in `C̄`, the coordinate has modulus `> M`
  have hev : ∀ᶠ z in cobounded ℂ ⊓ 𝓟 (closure C), M < ‖ψ z‖ :=
    (tendsto_norm_cobounded_atTop.comp hψ.2.2.2.2.2.2).eventually (eventually_gt_atTop M)
  have hev' : ∀ᶠ t in atTop, η t ∈ closure C → M < ‖ψ (η t)‖ :=
    (tendsto_norm_atTop_iff_cobounded.1 htr).eventually (eventually_inf_principal.1 hev)
  obtain ⟨A, hA⟩ := eventually_atTop.1 hev'
  -- a visit time after `max A τ`
  set A' := max A τ with hA'
  obtain ⟨T, -, hT⟩ := hP.exists_clock_gt (hP.clock_lt_clockEnd hAC (le_max_right A τ))
  have hA'T : A' < T := lt_of_not_ge fun h => absurd (hP.monotone_clock h) (not_le.2 hT)
  obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt hA'T hT.ne
  have hMt : M < ‖ψ (η t)‖ := hA t ((le_max_left _ _).trans ht.1.le) (subset_closure htI.2)
  obtain ⟨hu, he⟩ := relCurve_of_mem_visitSetInf (ψ := ψ) hP hAC htI
  exact ⟨_, hu, he ▸ hψ.2.2.2.1.2.mapsTo htI.2, he ▸ hMt⟩

/-- **The relative lifetime of the erased traversal is infinite** (Aux. lemma 125, junction at `∞`, transient
counterflow): as `capLife_relCurve_eq_top_of_isReversePocket`. -/
theorem capLife_relCurve_eq_top_of_isReversePocketInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : Aux125.IsForcePathPre xL xR ρL ρR
      (segDriver (relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ))) vL vR
      (capLife (relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ))))
    (hw : Sec2.DriverEq a ρL ρR
      (segDriver (relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ))) vL vR b
      (capLife (relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ))))
    (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) :
    capLife (relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ)) = ⊤ :=
  capLife_eq_top_of_driverEq (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ)
    (exists_relCurve_mem_H_lt_norm_of_isReversePocketInf hP hAC hψ htr) h hw hb hL hR

end Pocket

end InteractingSLE.Sec7.PocketLife
