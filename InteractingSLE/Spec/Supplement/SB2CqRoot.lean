/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CqFacts
import InteractingSLE.Spec.Supplement.SB2CqShift
import InteractingSLE.Spec.Supplement.SBS3DuWalk

/-!
# The chain facts of the canonical driver at the relative root (one sample)

Packet PROVE-SB2-CANON, round 5 (`Mz.CanonIdentOn` at `relOff`). At the relative root B's piece `P` (lifetime `L`)
enters the right end `R` of the retained union `Y` at time `τ < L`, and its head `P[0, τ]` lies in `fill Y ∪ ℝ` (it is
in the compact hull of `Y`). The relative curve is the canonical curve `ρ = canonCurve Y x₀ P(τ + ·) (L − τ)`.

* **`fillH_union_of_subset_fill_real`**: a set inside `fill Y ∪ ℝ` adds nothing to `fill (Y ∪ T)` (for compact
  `Y ∪ T ⊆ ℍ̄`), as CORNER's `Dv.fillH_union_of_subset_hullK`;
* **`image_Icc_add_split`**: `P[0, τ + s] = P[0, τ] ∪ P(τ + ·)[0, s]`; **`im_bdVal_nonneg`**: boundary values of B's
  stage chart lie in `ℍ̄`;
* **`chainFacts_root_at`**: `Qx.ChainFacts` at one sample of the root, as `chainFacts_at`, with the chain clause from
  the tail start `τ` (`chainFor_canon_shift`): B's stage hull up to `τ + s` reads into the joint fill
  `fill (Y ∪ P[0, τ + s]) = fill (Y ∪ P(τ + ·)[0, s])`.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Sec7.PocketTraversal Sec7.Lemma71C Exist Exist.Staged Exist.StagedLaw Lu Mx Mz

/-- **A set inside `fill Y ∪ ℝ` adds nothing to the fill of `Y ∪ T`.** -/
theorem fillH_union_of_subset_fill_real {Y S T : Set ℂ} (hc : IsCompact (Y ∪ T)) (hH : ∀ z ∈ Y ∪ T, 0 ≤ z.im)
    (hS : S ⊆ fillH Y ∪ {z | z.im = 0}) : fillH (Y ∪ S ∪ T) = fillH (Y ∪ T) := by
  refine Subset.antisymm ?_ (fillH_mono (union_subset (subset_union_left.trans subset_union_left) subset_union_right))
  have h1 : fillH (Y ∪ S ∪ T) ⊆ fillH (fillH (Y ∪ T) ∪ (Y ∪ S ∪ T)) := fillH_mono subset_union_right
  have h2 : fillH (fillH (Y ∪ T) ∪ (Y ∪ S ∪ T)) = fillH (fillH (Y ∪ T)) := by
    refine Supp9B.fillH_eq_of_subset_union_real subset_union_left ?_
    rintro z (hz | (hz | hz) | hz)
    · exact Or.inl hz
    · by_cases hzH : z ∈ H
      · exact Or.inl (mem_fillH_of_mem_closure hzH (subset_closure (Or.inl hz)))
      · exact Or.inr (le_antisymm (not_lt.1 hzH) (hH z (Or.inl hz)))
    · rcases hS hz with h | h
      · exact Or.inl (fillH_mono subset_union_left h)
      · exact Or.inr h
    · by_cases hzH : z ∈ H
      · exact Or.inl (mem_fillH_of_mem_closure hzH (subset_closure (Or.inr hz)))
      · exact Or.inr (le_antisymm (not_lt.1 hzH) (hH z (Or.inr hz)))
  exact h1.trans (h2 ▸ Lk.fillH_fillH_subset hc)

/-- **The image of `[0, τ + s]` splits at `τ`.** -/
theorem image_Icc_add_split (P : ℝ≥0 → ℂ) (τ s : ℝ≥0) :
    P '' Icc 0 (τ + s) = P '' Icc 0 τ ∪ (fun u => P (τ + u)) '' Icc 0 s := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    by_cases hrτ : r ≤ τ
    · exact Or.inl ⟨r, ⟨bot_le, hrτ⟩, rfl⟩
    · refine Or.inr ⟨r - τ, ⟨bot_le, tsub_le_iff_left.2 hr.2⟩, ?_⟩
      show P (τ + (r - τ)) = P r
      rw [add_tsub_cancel_of_le (not_le.1 hrτ).le]
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨r, ⟨bot_le, hr.2.trans le_self_add⟩, rfl⟩
    · exact ⟨τ + r, ⟨bot_le, add_le_add_right hr.2 τ⟩, rfl⟩

/-- **Boundary values of a domain chart with boundary limits lie in `ℍ̄`.** -/
theorem im_bdVal_nonneg {cℓ : Chart} {B : Set ℂ} (hD : IsDomainChart (H \ fillH B) cℓ)
    (hbl : ∀ x : ℝ, ∃ y : ℂ, Tendsto cℓ.2.1 (𝓝[H] (x : ℂ)) (𝓝 y)) {w : ℂ} (hw0 : 0 ≤ w.im) :
    0 ≤ (LuM.bdVal cℓ w).im := by
  have hcH : ContinuousOn cℓ.2.1 H := hD.isConformal.1.continuousOn
  by_cases hwH : w ∈ H
  · rw [LuM.bdVal_eq_of_mem_H hcH hwH]
    exact le_of_lt (hD.isConformal.2.1 hwH)
  · have hre : w.im = 0 := le_antisymm (not_lt.1 hwH) hw0
    obtain ⟨y, hy⟩ := hbl w.re
    have hwre : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [hre])
    rw [hwre] at hy
    rw [LuM.bdVal_eq_of_tendsto hw0 hy]
    have : (𝓝[H] w).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hw0
    exact ge_of_tendsto ((Complex.continuous_im.tendsto y).comp hy)
      (eventually_nhdsWithin_of_forall fun v hv => le_of_lt (hD.isConformal.2.1 hv))

/-- **The chain facts of the canonical driver at one sample of the relative root.** See the module docstring. -/
theorem chainFacts_root_at (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0))
    (k ℓ : ℕ) {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {ω : Ω}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hD : IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) ℓ)) (Mn.walkStageChart κ b jumps E ℓ ω))
    (hN : WalkIntCanon.IsNormalized (Mn.walkStageChart κ b jumps E ℓ ω)) {gc : ℂ → ℂ}
    (hgct : ∀ q ∈ Hbar, Tendsto (Mn.walkStageChart κ b jumps E ℓ ω).2.1 (𝓝[H] q) (𝓝 (gc q))) {C : ℝ}
    (hgC : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ C)
    (hYc : IsCompact (retY (κ := κ) b jumps E u l k ℓ ω)) (hA : IsHPHull (fillH (retY (κ := κ) b jumps E u l k ℓ ω)))
    (hYH : ∀ z ∈ retY (κ := κ) b jumps E u l k ℓ ω, 0 ≤ z.im)
    (hfill : fillH (K ω) = fillH (retY (κ := κ) b jumps E u l k ℓ ω))
    {τ : ℝ≥0} (hτL : (τ : ℝ≥0∞) < (lowerD b jumps E ω ℓ).2)
    (hhead : Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ)
      (lowerD b jumps E ω ℓ) '' Icc 0 τ ⊆ fillH (retY (κ := κ) b jumps E u l k ℓ ω) ∪ {z | z.im = 0})
    (hpc : ContinuousOn (Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ)) {t | (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2})
    (hdr : IsDrivenCurve (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω) (x₀ ω)
      (fun s => Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        ℓ) (lowerD b jumps E ω ℓ) (τ + s)) ((lowerD b jumps E ω ℓ).2 - τ)))
    (hβc : ContinuousOn (LuM.trOf (lowerD b jumps E ω ℓ)) {t | (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2})
    (hβH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (lowerD b jumps E ω ℓ).2 → 0 ≤ (LuM.trOf (lowerD b jumps E ω ℓ) t).im)
    (he1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < capLife (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω) (x₀ ω)
      (fun s => Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        ℓ) (lowerD b jumps E ω ℓ) (τ + s)) ((lowerD b jumps E ω ℓ).2 - τ)) →
      (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1 t = segDriver (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω)
        (x₀ ω) (fun s => Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ) (τ + s)) ((lowerD b jumps E ω ℓ).2 - τ)) t)
    (he2 : (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2 = capLife (Dv.canonCurve (retY (κ := κ) b jumps E u l k ℓ ω)
      (x₀ ω) (fun s => Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) ℓ) (lowerD b jumps E ω ℓ) (τ + s)) ((lowerD b jumps E ω ℓ).2 - τ)))
    (hcont : ContinuousOn (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω).2}) :
    Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω := by
  set cℓ := Mn.walkStageChart κ b jumps E ℓ ω with hcℓ
  set Y := retY (κ := κ) b jumps E u l k ℓ ω with hY
  set B := SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ
    with hBdef
  set e := Qx.canonDrvAt h12p hκ h c x₀ hKc hKp ω with hedef
  have hBY : B ⊆ Y := subset_union_right
  have hreg : IsRegularDriver e := Mz.isRegularDriver_driverOf h12p hκ _ _
  -- the stage chart's inverse agrees with its boundary map in `ℍ`
  have hcH : ContinuousOn cℓ.2.1 H := hD.isConformal.1.continuousOn
  have hgeq : ∀ q ∈ H, gc q = cℓ.2.1 q := fun q hq => by
    have : (𝓝[H] q).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hq)
    exact tendsto_nhds_unique (hgct q (le_of_lt (show 0 < q.im from hq))) (hcH q hq).tendsto
  have hM : ∀ v ∈ H, ‖cℓ.2.1 v - v‖ ≤ C := fun v hv => by
    rw [← hgeq v hv]; exact hgC v (le_of_lt (show 0 < v.im from hv))
  have hinj : InjOn cℓ.2.1 H := fun v hv w hw hvw => by
    rw [← hD.fwd_inv hv, hvw, hD.fwd_inv hw]
  have hbl : ∀ x : ℝ, ∃ y : ℂ, Tendsto cℓ.2.1 (𝓝[H] (x : ℂ)) (𝓝 y) := fun x =>
    ⟨gc x, hgct x (by simp [Hbar])⟩
  -- the stage version of the canonical chart
  have hdomY : IsDomainChart (H \ Mn.stageRetained cℓ Y) (stageChartOf cℓ (Mo.hullChart (fillH Y) (x₀ ω))) :=
    isDomainChart_stageChartOf hD (Mo.isDomainChart_hullChart hA (x₀ ω)) (fillH_mono hBY)
  -- the post-entry piece
  set P := Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ)
    (lowerD b jumps E ω ℓ) with hPdef
  set L := (lowerD b jumps E ω ℓ).2 with hLdef
  have hL' : L - τ ≠ 0 := (tsub_pos_of_lt hτL).ne'
  have hBL : ∀ S : ℝ≥0, ((τ + S : ℝ≥0) : ℝ≥0∞) < L ↔ (S : ℝ≥0∞) < L - τ := fun S => by
    rw [ENNReal.coe_add]; exact lt_tsub_iff_left.symm
  have hle : ∀ S : ℝ≥0, (S : ℝ≥0∞) ≤ L - τ → ((τ + S : ℝ≥0) : ℝ≥0∞) ≤ L := fun S hS => by
    rw [ENNReal.coe_add]; exact (ENNReal.le_sub_iff_add_le_left ENNReal.coe_ne_top hτL.le).1 hS
  have hpc' : ContinuousOn (fun s => P (τ + s)) {s : ℝ≥0 | (s : ℝ≥0∞) ≤ L - τ} :=
    hpc.comp (continuous_const.add continuous_id).continuousOn fun s hs => hle s hs
  -- B's physical piece is in `ℍ̄`
  have hPH : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ L → 0 ≤ (P r).im := fun r hr => im_bdVal_nonneg hD hbl (hβH r hr)
  have hin : ∀ s : ℝ≥0, (s : ℝ≥0∞) < L - τ → ∀ z ∈ fillH (LuM.trOf (lowerD b jumps E ω ℓ) '' Icc 0 (τ + s)),
      z ∉ fillH (Mn.stageRetained cℓ Y) → cℓ.2.1 z ∈ fillH (Y ∪ (fun s => P (τ + s)) '' Icc 0 s) := by
    intro s hs z hz _
    have hτs := (hBL s).2 hs
    have h := mem_joint_of_mem_fillH_stage hD hM hBY
      (hβc.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hτs.le)
      (fun r _ hrH => (LuM.bdVal_eq_of_mem_H hcH hrH)) (p := P) hz
    have hT : IsCompact ((fun s => P (τ + s)) '' Icc 0 s) :=
      isCompact_Icc.image_of_continuousOn (hpc'.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hs.le)
    have hTH : ∀ z ∈ Y ∪ (fun s => P (τ + s)) '' Icc 0 s, 0 ≤ z.im := by
      rintro z (hz | ⟨r, hr, rfl⟩)
      · exact hYH z hz
      · exact hPH _ (hle r ((ENNReal.coe_le_coe.2 hr.2).trans hs.le))
    rwa [image_Icc_add_split, ← union_assoc, fillH_union_of_subset_fill_real (hYc.union hT) hTH hhead] at h
  have hchain := chainFor_canon_shift (cℓ := cℓ) hYc hA hL' hpc' hdr
    (fun z hz => mem_diff_of_notMem_fillH_stageRetained hD.isConformal hz) hinj hBL hin
    (fun t ht hp => piece_of_mem_diff hD hBY hYc.isClosed hbl (hβH (τ + t) ((hBL t).2 ht).le) hp)
    hreg he1 he2
  refine ⟨hl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfill]; exact hdomY
  · exact Mz.notMem_fillH_stageRetained hN hA.2.1 hdomY
  · rw [hfill]; exact hchain
  · rw [he2]; exact (Lk.capLife_pos_of_driven hdr).ne'
  · exact hcont

end InteractingSLE.Theorem14.SB.Cz
