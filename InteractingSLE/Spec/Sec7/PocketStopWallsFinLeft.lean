/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsLaw

/-!
# The pocket's stop at the left end of the erasure fibre (ruling R67)

Packet PROVE-STRIPSYS41 (PROVE-STRIPSYS37 §5.3). Specification §7.4, proof of Aux. lemma 125
(`source/spec/p385-432.md` L213–L224, p. 396) and Aux. lemma 41's (GC2).

The ambient time `T(q) = ambTime` of the relative capacity time `q` is the RIGHT end of the erasure-clock fibre of
the erased time; ruling R67 replaces it, for the field-level statements, by the LEFT end `T⁰(q)` of the same fibre and
transfers back by the deterministic identity `C ∩ D_{T⁰(q)} = C ∩ D_{T(q)}` (the pocket's part of the hull does not
change during an erased excursion). Here:

* `fibreLeft`, `clock_fibreLeft`, `fibreLeft_le_fibreRight`: left ends of clock fibres;
* `inter_eq_of_image` (deterministic topology): two nested domains `D ⊆ D₀` with `C ∩ D₀` preconnected have the same
  trace on `C` when `ψ(C ∩ D) = ℍ ∖ fill(Z)` and `ψ(C ∩ D₀)` misses `Z`;
* **`IsReversePocket.inter_domain_fibreLeft`**, **`IsReversePocketInf.inter_domain_fibreLeftInf`**:
  `C ∩ D_{fL(v)} = C ∩ D_{fR(v)}` for every erased time `v` below the terminal clock value;
* `ambTime0`, `ambTime0Inf`, `stopHull0`, `stopHull0Inf` (the hull at the left end `T⁰(q)`), and
  **`extHullSet_stopHull0`**, **`extHullSet_stopHull0Inf`**: `B ∪ R_{T⁰(q)} = B ∪ R_{T(q)}` for the change pockets;
* **`pocketStopUnionLaw_stopHull_of_stopHull0`** (and `…Inf`): `PocketStopUnionLaw` at `T(q)` from `PocketStopUnionLaw`
  at `T⁰(q)` — its consumers are unchanged.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Bornology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopWallsFin

open QuantumZipper (H fwdHull)

/-! ### Left ends of clock fibres -/

section Fibre

/-- **The left end of the clock fibre** of `v` inside `[τ, S]`: `inf {t ∈ [τ, S] : min v (ℓ S) ≤ ℓ t}` (the value
`v` capped at `ℓ S`, so that the set is nonempty for every `v`). -/
def fibreLeft (ℓ : ℝ → ℝ) (τ S v : ℝ) : ℝ := sInf {t ∈ Icc τ S | min v (ℓ S) ≤ ℓ t}

variable {ℓ : ℝ → ℝ} {τ S : ℝ}

theorem fibreLeft_set_nonempty (hτS : τ ≤ S) (v : ℝ) : {t ∈ Icc τ S | min v (ℓ S) ≤ ℓ t}.Nonempty :=
  ⟨S, ⟨hτS, le_rfl⟩, min_le_right _ _⟩

theorem fibreLeft_set_bddBelow (v : ℝ) : BddBelow {t ∈ Icc τ S | min v (ℓ S) ≤ ℓ t} :=
  ⟨τ, fun _ ht => ht.1.1⟩

theorem fibreLeft_mem_set (hℓ : Continuous ℓ) (hτS : τ ≤ S) (v : ℝ) :
    fibreLeft ℓ τ S v ∈ {t ∈ Icc τ S | min v (ℓ S) ≤ ℓ t} :=
  (isClosed_Icc.inter (isClosed_le continuous_const hℓ)).csInf_mem (fibreLeft_set_nonempty hτS v)
    (fibreLeft_set_bddBelow v)

theorem fibreLeft_mem (hℓ : Continuous ℓ) (hτS : τ ≤ S) (v : ℝ) : fibreLeft ℓ τ S v ∈ Icc τ S :=
  (fibreLeft_mem_set hℓ hτS v).1

theorem fibreLeft_le {v t : ℝ} (ht : t ∈ Icc τ S) (hv : min v (ℓ S) ≤ ℓ t) : fibreLeft ℓ τ S v ≤ t :=
  csInf_le (fibreLeft_set_bddBelow v) ⟨ht, hv⟩

/-- On `[ℓ τ, ℓ S]` the left end of the fibre lies before the right end. -/
theorem fibreLeft_le_fibreRight (hℓ : Continuous ℓ) (hτS : τ ≤ S) {v : ℝ} (hv : v ∈ Icc (ℓ τ) (ℓ S)) :
    fibreLeft ℓ τ S v ≤ Sec6.fibreRight ℓ τ S v :=
  fibreLeft_le (Sec6.fibreRight_mem hℓ hτS v) (by rw [Sec6.clock_fibreRight hℓ hτS hv]; exact min_le_left _ _)

/-- On `[ℓ τ, ℓ S]` the left end of the fibre of `v` lies in the fibre. -/
theorem clock_fibreLeft (hℓ : Continuous ℓ) (hℓm : Monotone ℓ) (hτS : τ ≤ S) {v : ℝ}
    (hv : v ∈ Icc (ℓ τ) (ℓ S)) : ℓ (fibreLeft ℓ τ S v) = v := by
  refine le_antisymm ?_ ?_
  · calc ℓ (fibreLeft ℓ τ S v) ≤ ℓ (Sec6.fibreRight ℓ τ S v) := hℓm (fibreLeft_le_fibreRight hℓ hτS hv)
      _ = v := Sec6.clock_fibreRight hℓ hτS hv
  · have h := (fibreLeft_mem_set hℓ hτS v).2
    rwa [min_eq_left hv.2] at h

/-- **No interior visit inside a fibre**: if the erasure clock of an open visit set takes the same value at `a < b`,
no time of `(a, b)` is a visit. -/
theorem notMem_of_erasureClock_eq {I : Set ℝ} (hI : IsOpen I) {a b : ℝ}
    (hab : Sec6.erasureClock I τ a = Sec6.erasureClock I τ b) {t : ℝ} (ht : t ∈ Ioo a b) : t ∉ I :=
  fun htI => Set.disjoint_left.1 ((Sec6.erasureClock_eq_iff hI (ht.1.trans ht.2)).1 hab) ht htI

/-- If a path continuous at `b > 0` (on `[0, ∞)`) avoids an open set `C` on `(a, b)`, it avoids `C` at `b`. -/
theorem notMem_right_of_notMem_Ioo {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0)) {C : Set ℂ} (hC : IsOpen C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hno : ∀ t ∈ Ioo a b, η t ∉ C) : η b ∉ C := by
  intro hbC
  have hb0 : 0 < b := ha.trans_lt hab
  have hcont : ContinuousAt η b := (hη b hb0.le).continuousAt (Ici_mem_nhds hb0)
  have hev : ∀ᶠ t in 𝓝[<] b, η t ∈ C := nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hC.mem_nhds hbC))
  obtain ⟨t, htC, ht⟩ := (hev.and (Ioo_mem_nhdsLT hab)).exists
  exact hno t ht htC

end Fibre

/-! ### Two nested domains with the same trace on the pocket -/

section Domain

/-- `ℍ ∖ fill(Z)` is unbounded for bounded `Z`. -/
theorem not_isBounded_H_diff_fillH {Z : Set ℂ} (hZ : IsBounded Z) : ¬ IsBounded (H \ fillH Z) := by
  intro hb
  obtain ⟨r, hr⟩ := hZ.closure.subset_closedBall 0
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  set c : ℝ := max (max r R) 0 + 1 with hc
  have hc0 : 0 < c := by positivity
  set z : ℂ := (c : ℂ) * Complex.I with hz
  have hzim : z.im = c := by simp [hz]
  have hnorm : c ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rw [hzim, abs_of_pos hc0] at this
    exact this
  have hzH : z ∈ H := by
    show 0 < z.im
    rw [hzim]
    exact hc0
  have hzf : z ∉ fillH Z := fun h => by
    have h' := mem_closedBall_zero_iff.1 (fillH_subset_closedBall_zero hr h)
    have : r < c := by
      have := le_max_left r R
      have := le_max_left (max r R) 0
      linarith
    linarith
  have h' := mem_closedBall_zero_iff.1 (hR ⟨hzH, hzf⟩)
  have : R < c := by
    have := le_max_right r R
    have := le_max_left (max r R) 0
    linarith
  linarith

/-- **Two nested domains with the same trace on a Jordan domain** (deterministic): for `D ⊆ D₀`, a map `ψ`
injective and continuous on `C` with values in `ℍ`, a compact `Z` with `ψ(C ∩ D) = ℍ ∖ fill(Z)`, `C ∩ D₀`
preconnected and `ψ(C ∩ D₀)` disjoint from `Z`, the traces agree: `C ∩ D₀ = C ∩ D`. -/
theorem inter_eq_of_image {C D₀ D Z : Set ℂ} {ψ : ℂ → ℂ} (hDD : D ⊆ D₀) (hψi : InjOn ψ C)
    (hψc : ContinuousOn ψ C) (hψH : MapsTo ψ C H) (hZ : IsCompact Z) (himg : ψ '' (C ∩ D) = H \ fillH Z)
    (hpre : IsPreconnected (C ∩ D₀)) (hmiss : ∀ z ∈ C ∩ D₀, ψ z ∉ Z) : C ∩ D₀ = C ∩ D := by
  refine Subset.antisymm (fun z hz => ?_) (inter_subset_inter_right C hDD)
  have hsub : ψ '' (C ∩ D₀) ⊆ H \ fillH Z := by
    refine Sec6.subset_H_diff_fillH_of_isPreconnected hZ.isBounded (hpre.image _ (hψc.mono inter_subset_left))
      ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨hψH hw.1, by rw [hZ.isClosed.closure_eq]; exact hmiss w hw⟩
    · intro hb
      refine not_isBounded_H_diff_fillH hZ.isBounded (hb.subset ?_)
      rw [← himg]
      exact image_mono (inter_subset_inter_right C hDD)
  have hz' := hsub (mem_image_of_mem ψ hz)
  rw [← himg] at hz'
  obtain ⟨w, hw, hwz⟩ := hz'
  rw [← hψi hw.1 hz.1 hwz]
  exact hw

end Domain

/-! ### The bounded pocket -/

section Bounded

open Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}

/-- **The left end of the pocket's clock fibre** of the erased time `v`. -/
def pocketFibreLeft (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (v : ℝ) : ℝ := fibreLeft (pocketClock η C τ σ) τ σ v

theorem pocketFibreLeft_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) (v : ℝ) :
    pocketFibreLeft η C τ σ v ∈ Icc τ σ :=
  fibreLeft_mem hP.continuous_clock hP.τ_lt_σ.le v

theorem pocketFibreLeft_le (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) : pocketFibreLeft η C τ σ v ≤ pocketFibre η C τ σ v :=
  fibreLeft_le_fibreRight hP.continuous_clock hP.τ_lt_σ.le (by rw [IsReversePocket.clock_τ]; exact hv)

theorem clock_pocketFibreLeft (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) : pocketClock η C τ σ (pocketFibreLeft η C τ σ v) = v :=
  clock_fibreLeft hP.continuous_clock hP.monotone_clock hP.τ_lt_σ.le (by rw [IsReversePocket.clock_τ]; exact hv)

/-- **No visit to the pocket between the two ends of a fibre**: `η(t) ∉ C` for `t ∈ (fL(v), fR(v)]`. -/
theorem notMem_of_mem_Ioc_fibre (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v : ℝ}
    (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) {t : ℝ}
    (ht : t ∈ Ioc (pocketFibreLeft η C τ σ v) (pocketFibre η C τ σ v)) : η t ∉ C := by
  set a := pocketFibreLeft η C τ σ v with ha
  set b := pocketFibre η C τ σ v with hb
  have hab : a < b := ht.1.trans_le ht.2
  have hτa : τ ≤ a := (pocketFibreLeft_mem hP v).1
  have hbσ : b < σ := hP.fibre_lt_σ hv
  have hclk : pocketClock η C τ σ a = pocketClock η C τ σ b := by
    rw [ha, hb, clock_pocketFibreLeft hP ⟨hv.1, hv.2.le⟩, hP.clock_fibre ⟨hv.1, hv.2.le⟩]
  have hno : ∀ t' ∈ Ioo a b, η t' ∉ C := fun t' ht' ht'C =>
    notMem_of_erasureClock_eq hP.isOpen_visitSet hclk ht'
      ⟨⟨hτa.trans_lt ht'.1, ht'.2.trans hbσ⟩, ht'C⟩
  rcases ht.2.lt_or_eq with htb | htb
  · exact hno t ⟨ht.1, htb⟩
  · rw [htb]
    exact notMem_right_of_notMem_Ioo hP.trace.2.1 hP.isOpen (hP.nonneg.trans hτa) hab hno

/-- **(GC2) at both ends of a fibre** (ruling R67): the pocket's part of the active domain is the same at the left
and at the right end of the clock fibre of every erased time below the terminal clock value,
`C ∩ D_{fL(v)} = C ∩ D_{fR(v)}`. -/
theorem inter_domain_fibreLeft (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {v : ℝ} (hv : v ∈ Ico 0 (pocketClock η C τ σ σ)) :
    C ∩ (H \ fwdHull W (pocketFibreLeft η C τ σ v)) = C ∩ (H \ fwdHull W (pocketFibre η C τ σ v)) := by
  obtain ⟨ψ, hψ⟩ := hP.exists_isJordanCoord
  set s₀ := pocketFibreLeft η C τ σ v with hs₀
  set s := pocketFibre η C τ σ v with hs
  have hs₀s : s₀ ≤ s := pocketFibreLeft_le hP ⟨hv.1, hv.2.le⟩
  have hτs₀ : τ ≤ s₀ := (pocketFibreLeft_mem hP v).1
  have hs₀σ : s₀ < σ := hs₀s.trans_lt (hP.fibre_lt_σ hv)
  have hs₀0 : 0 ≤ s₀ := hP.nonneg.trans hτs₀
  have hCsub : C ⊆ closure C \ {α₁ 0} := fun z hz =>
    ⟨subset_closure hz, fun h => by
      have hx : α₁ 0 ∈ frontier C := by
        rw [hP.frontier_eq]; exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      rw [mem_singleton_iff.1 h] at hz
      exact hx.2 (by rw [hP.isOpen.interior_eq]; exact hz)⟩
  have hsub : Icc 0 v ⊆ Ico 0 (pocketClock η C τ σ σ) := fun w hw => ⟨hw.1, hw.2.trans_lt hv.2⟩
  have hGC2 := hP.erasedPath_image_inter (u := v) ⟨hv.1, hv.2.le⟩
  refine inter_eq_of_image (Z := (fun w => ψ (erasedPath η C τ σ w)) '' Icc 0 v)
    (sdiff_subset_sdiff_right (WangWu.fwdHull_mono hs₀s)) (hψ.2.1.mono hCsub) (hψ.1.mono hCsub)
    (fun z hz => hψ.2.2.2.1.2.mapsTo hz)
    (isCompact_Icc.image_of_continuousOn ((hP.continuousOn_ζ hAC hψ).mono hsub))
    (hP.image_inter_domain hAC hψ hv) (hP.inter_domain_props hτs₀ hs₀σ).1 ?_
  rintro z hz ⟨w, hw, hwz⟩
  have hzw : erasedPath η C τ σ w = z := hψ.2.1 (hP.erasedPath_mem (hsub hw)) (hCsub hz.1) hwz
  have hzR : z ∈ η '' Icc 0 s ∩ C := hGC2 ▸ ⟨⟨w, hw, hzw⟩, hz.1⟩
  obtain ⟨t, ht, htz⟩ := hzR.1
  rcases le_or_gt t s₀ with hts | hts
  · exact hz.2.2 (mem_fwdHull_of_mem_trace hP.trace hs₀0 hz.2.1 ⟨t, ⟨ht.1, hts⟩, htz⟩)
  · exact notMem_of_mem_Ioc_fibre hP hv ⟨hts, ht.2⟩ (htz ▸ hz.1)

end Bounded

/-! ### The pocket opening at the flow seed -/

section Inf

open Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}

/-- **The left end of the pocket's clock fibre** of the erased time `v` (pocket opening at the flow seed). -/
def pocketFibreLeftInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (v : ℝ) : ℝ :=
  sInf {t ∈ Ici τ | v ≤ pocketClockInf η C τ t}

theorem pocketFibreLeftInf_mem_set (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ} (hv : v < clockEnd η C τ) :
    pocketFibreLeftInf η C τ v ∈ {t ∈ Ici τ | v ≤ pocketClockInf η C τ t} := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt hv
  exact (isClosed_Ici.inter (isClosed_le continuous_const hP.continuous_clock)).csInf_mem ⟨T, hτT, hvT.le⟩
    ⟨τ, fun _ ht => ht.1⟩

theorem pocketFibreLeftInf_le (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ} (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    pocketFibreLeftInf η C τ v ≤ pocketFibreInf η C τ v :=
  csInf_le ⟨τ, fun _ ht => ht.1⟩ ⟨hP.fibre_mem hv, (hP.clock_fibre hv).ge⟩

theorem clock_pocketFibreLeftInf (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : pocketClockInf η C τ (pocketFibreLeftInf η C τ v) = v := by
  refine le_antisymm ?_ (pocketFibreLeftInf_mem_set hP hv.2).2
  calc pocketClockInf η C τ (pocketFibreLeftInf η C τ v) ≤ pocketClockInf η C τ (pocketFibreInf η C τ v) :=
        hP.monotone_clock (pocketFibreLeftInf_le hP hv)
    _ = v := hP.clock_fibre hv

/-- **No visit to the pocket between the two ends of a fibre** (pocket opening at the flow seed). -/
theorem notMem_of_mem_Ioc_fibreInf (hP : IsReversePocketInf W η C α₁ α₂ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) {t : ℝ}
    (ht : t ∈ Ioc (pocketFibreLeftInf η C τ v) (pocketFibreInf η C τ v)) : η t ∉ C := by
  set a := pocketFibreLeftInf η C τ v with ha
  set b := pocketFibreInf η C τ v with hb
  have hab : a < b := ht.1.trans_le ht.2
  have hτa : τ ≤ a := (pocketFibreLeftInf_mem_set hP hv.2).1
  have hclk : pocketClockInf η C τ a = pocketClockInf η C τ b := by
    rw [ha, hb, clock_pocketFibreLeftInf hP hv, hP.clock_fibre hv]
  have hno : ∀ t' ∈ Ioo a b, η t' ∉ C := fun t' ht' ht'C =>
    notMem_of_erasureClock_eq hP.isOpen_visitSet hclk ht' ⟨hτa.trans_lt ht'.1, ht'C⟩
  rcases ht.2.lt_or_eq with htb | htb
  · exact hno t ⟨ht.1, htb⟩
  · rw [htb]
    exact notMem_right_of_notMem_Ioo hP.trace.2.1 hP.isOpen (hP.nonneg.trans hτa) hab hno

/-- **(GC2) at both ends of a fibre** (ruling R67; pocket opening at the flow seed):
`C ∩ D_{fL(v)} = C ∩ D_{fR(v)}`. -/
theorem inter_domain_fibreLeftInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {v : ℝ} (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    C ∩ (H \ fwdHull W (pocketFibreLeftInf η C τ v)) = C ∩ (H \ fwdHull W (pocketFibreInf η C τ v)) := by
  obtain ⟨ψ, hψ⟩ := hP.exists_isJordanCoordInf
  set s₀ := pocketFibreLeftInf η C τ v with hs₀
  set s := pocketFibreInf η C τ v with hs
  have hs₀s : s₀ ≤ s := pocketFibreLeftInf_le hP hv
  have hτs₀ : τ ≤ s₀ := (pocketFibreLeftInf_mem_set hP hv.2).1
  have hs₀0 : 0 ≤ s₀ := hP.nonneg.trans hτs₀
  have hsub : Icc 0 v ⊆ Ico 0 (clockEnd η C τ) := fun w hw => ⟨hw.1, hw.2.trans_lt hv.2⟩
  have hGC2 := hP.erasedPath_image_inter hv
  refine inter_eq_of_image (Z := (fun w => ψ (erasedPathInf η C τ w)) '' Icc 0 v)
    (sdiff_subset_sdiff_right (WangWu.fwdHull_mono hs₀s)) (hψ.2.1.mono subset_closure) (hψ.1.mono subset_closure)
    (fun z hz => hψ.2.2.2.1.2.mapsTo hz)
    (isCompact_Icc.image_of_continuousOn (hP.continuousOn_ζ_Icc hAC hψ hv))
    (hP.image_inter_domain hAC hψ hv) (hP.isPreconnected_inter_domain hτs₀) ?_
  rintro z hz ⟨w, hw, hwz⟩
  have hzw : erasedPathInf η C τ w = z := hψ.2.1 (hP.erasedPath_mem (hsub hw)) (subset_closure hz.1) hwz
  have hzR : z ∈ η '' Icc 0 s ∩ C := hGC2 ▸ ⟨⟨w, hw, hzw⟩, hz.1⟩
  obtain ⟨t, ht, htz⟩ := hzR.1
  rcases le_or_gt t s₀ with hts | hts
  · exact hz.2.2 (mem_fwdHull_of_mem_trace hP.trace hs₀0 hz.2.1 ⟨t, ⟨ht.1, hts⟩, htz⟩)
  · exact notMem_of_mem_Ioc_fibreInf hP hv ⟨hts, ht.2⟩ (htz ▸ hz.1)

end Inf

/-! ### The ambient stop at the left end and the hull there -/

section Stop

open PocketTraversal Lemma71C PocketUnionPt

/-- **The ambient time `T⁰(q)` of the relative capacity time `q`** (bounded pocket; ruling R67): the LEFT end of the
erasure-clock fibre of the erased time `clockOf L (capInv γ q)` (`ambTime` is its right end). -/
def ambTime0 (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) (q : ℝ) : ℝ :=
  pocketFibreLeft η C τ σ (clockOf (Sec6.pocketClock η C τ σ σ)
    (capInv (relCurve (fun v => ψ (Sec6.erasedPath η C τ σ v)) (Sec6.pocketClock η C τ σ σ)) q))

/-- **The ambient time `T⁰(q)` of the relative capacity time `q`** (pocket opening at the flow seed). -/
def ambTime0Inf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (ψ : ℂ → ℂ) (q : ℝ) : ℝ :=
  pocketFibreLeftInf η C τ (clockOf (Sec6.clockEnd η C τ)
    (capInv (relCurve (fun v => ψ (Sec6.erasedPathInf η C τ v)) (Sec6.clockEnd η C τ)) q))

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}

/-- **`C ∩ D_{T⁰(q)} = C ∩ D_{T(q)}`** (bounded pocket; ruling R67). -/
theorem inter_domain_ambTime0 (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : Sec6.AttachmentConstancy η C α₁ α₂ τ σ) (ψ : ℂ → ℂ) (q : ℝ) :
    C ∩ (H \ fwdHull W (ambTime0 η C τ σ ψ q)) = C ∩ (H \ fwdHull W (ambTime η C τ σ ψ q)) :=
  inter_domain_fibreLeft hP hAC (clockOf_mem_Ico (hP.clock_σ_pos hAC) (capInv_nonneg _ _))

/-- **`C ∩ D_{T⁰(q)} = C ∩ D_{T(q)}`** (pocket opening at the flow seed; ruling R67). -/
theorem inter_domain_ambTime0Inf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (ψ : ℂ → ℂ) (q : ℝ) :
    C ∩ (H \ fwdHull W (ambTime0Inf η C τ ψ q)) = C ∩ (H \ fwdHull W (ambTimeInf η C τ ψ q)) :=
  inter_domain_fibreLeftInf hP hAC (clockOf_mem_Ico (hP.clockEnd_pos hAC) (capInv_nonneg _ _))

/-- `T⁰(q)` lies in `[τ, σ]` (bounded pocket). -/
theorem ambTime0_mem (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (ψ : ℂ → ℂ) (q : ℝ) :
    ambTime0 η C τ σ ψ q ∈ Icc τ σ :=
  pocketFibreLeft_mem hP _

/-- `T⁰(q) ≥ τ` (pocket opening at the flow seed). -/
theorem le_ambTime0Inf (hP : Sec6.IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : Sec6.AttachmentConstancyInf η C α₁ α₂ τ) (ψ : ℂ → ℂ) (q : ℝ) : τ ≤ ambTime0Inf η C τ ψ q :=
  (pocketFibreLeftInf_mem_set hP (clockOf_mem_Ico (hP.clockEnd_pos hAC) (capInv_nonneg _ _)).2).1

/-- The exterior union `B ∪ F` sees only the pocket's part of the hull. -/
theorem extHullSet_eq_of_inter {C K₀ K : Set ℂ} (h : C ∩ (H \ K₀) = C ∩ (H \ K)) :
    extHullSet C K₀ = extHullSet C K := by
  have key : ∀ {K₁ K₂ : Set ℂ}, C ∩ (H \ K₁) = C ∩ (H \ K₂) → extHullSet C K₁ ⊆ extHullSet C K₂ := by
    intro K₁ K₂ h12 z ⟨hzH, hz⟩
    refine ⟨hzH, ?_⟩
    by_cases hzC : z ∈ C
    · rcases hz with hz | hz
      · exact absurd hzC hz
      · refine Or.inr (by_contra fun hzK => ?_)
        have hz2 : z ∈ C ∩ (H \ K₂) := ⟨hzC, hzH, hzK⟩
        rw [← h12] at hz2
        exact hz2.2.2 hz
    · exact Or.inl hzC
  exact Subset.antisymm (key h) (key h.symm)

end Stop

section Hulls

open PocketTraversal Lemma71C PocketUnionPt WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketSeedOpen PocketStop

variable {Ω : Type*}

/-- **The ambient counterflow hull at `T⁰(q)`** (bounded change pocket; ruling R67). -/
def stopHull0 (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  fwdHull (W ω) (ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q)

/-- **The ambient counterflow hull at `T⁰(q)`** (change pocket opening at the flow seed; ruling R67). -/
def stopHull0Inf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (W : Ω → ℝ → ℝ) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  fwdHull (W ω) (ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q)

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}

/-- The change pocket of a counterflow pocket configuration is a reverse pocket. -/
theorem IsCfPocketConfig.isReversePocket' {R L : ℝ≥0 → ℂ} {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hc : IsCfPocketConfig R L r W η) :
    Sec6.IsReversePocket W η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r) (cfBeta R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) :=
  hc.conf.isReversePocket_of_counterflow (zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded) hc.trace
    hc.continuous_W hc.W_zero hc.revR hc.revL hc.visR

/-- **`B ∪ R_{T⁰(q)} = B ∪ R_{T(q)}`** for the bounded change pocket (ruling R67). -/
theorem extHullSet_stopHull0 {ω : Ω} (hc : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (q : ℝ≥0) :
    extHullSet (cfPocket (R ω) (L ω) r) (stopHull0 R L r W η ψ q ω) =
      extHullSet (cfPocket (R ω) (L ω) r) (stopHull R L r W η ψ q ω) :=
  extHullSet_eq_of_inter (inter_domain_ambTime0 (IsCfPocketConfig.isReversePocket' hc) hc.attach (ψ ω) q)

/-- **`B ∪ R_{T⁰(q)} = B ∪ R_{T(q)}`** for the change pocket opening at the flow seed (ruling R67). -/
theorem extHullSet_stopHull0Inf {ω : Ω} (hc : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (q : ℝ≥0) :
    extHullSet (cfPocket (R ω) (L ω) r) (stopHull0Inf R L r W η ψ q ω) =
      extHullSet (cfPocket (R ω) (L ω) r) (stopHullInf R L r W η ψ q ω) :=
  extHullSet_eq_of_inter (inter_domain_ambTime0Inf hc.isReversePocketInf hc.attach (ψ ω) q)

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketStopUnionLaw` at `T(q)` from `PocketStopUnionLaw` at `T⁰(q)`** (bounded change pocket; ruling R67): the
union law only sees `B ∪ F` on the live event. -/
theorem pocketStopUnionLaw_stopHull_of_stopHull0 {G A : Set Ω}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω)) (hAG : A ⊆ G) {γ : Ω → ℝ → ℂ} {q : ℝ≥0}
    {h₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hU : PocketStopUnionLaw 𝓦 P A γ (fun ω => cfPocket (R ω) (L ω) r) (stopHull0 R L r W η ψ q) h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ (fun ω => cfPocket (R ω) (L ω) r) (stopHull R L r W η ψ q) h₀ q := by
  obtain ⟨E, hE, hloc, heq⟩ := hU
  exact ⟨E, hE, hloc, fun ω hω hq => (heq ω hω hq).trans (extHullSet_stopHull0 (hcfg ω (hAG hω)) q)⟩

/-- **`PocketStopUnionLaw` at `T(q)` from `PocketStopUnionLaw` at `T⁰(q)`** (change pocket opening at the flow seed;
ruling R67). -/
theorem pocketStopUnionLaw_stopHullInf_of_stopHull0Inf {G A : Set Ω}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω)) (hAG : A ⊆ G) {γ : Ω → ℝ → ℂ} {q : ℝ≥0}
    {h₀ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hU : PocketStopUnionLaw 𝓦 P A γ (fun ω => cfPocket (R ω) (L ω) r) (stopHull0Inf R L r W η ψ q) h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ (fun ω => cfPocket (R ω) (L ω) r) (stopHullInf R L r W η ψ q) h₀ q := by
  obtain ⟨E, hE, hloc, heq⟩ := hU
  exact ⟨E, hE, hloc, fun ω hω hq => (heq ω hω hq).trans (extHullSet_stopHull0Inf (hcfg ω (hAG hω)) q)⟩

end Hulls

end InteractingSLE.Sec7.PocketStopWallsFin
