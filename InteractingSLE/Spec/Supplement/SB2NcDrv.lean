/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcLive
import InteractingSLE.Spec.Supplement.SBS3DuWalk

/-!
# F2b′: B's tail-stage curve is driven in the chart recentred at the right entry value

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). PROVE-R6-CORNER's F2a (`Dv.isDrivenCurve_stage_fin`,
`Dv.isDrivenCurve_stage_top`, `Dv.isDrivenCurve_walkStage_old`) gives a driven canonical stage curve for *some*
offset. The offset of its proof is the right entry value of the canonical package (`Dv.exists_canon_package_pinv`).
F2b′'s chart offset `x₀` must be readable from the retained hull (`entryRead`), so the offset is needed explicitly.
These are CORNER's three proofs verbatim, with the conclusion strengthened to record that the offset makes the
recentred chart a right entry chart (`IsRightEntryChart`, which by `entryRead_eq` pins the offset down):

* `isDrivenCurve_stage_fin_entry`, `isDrivenCurve_stage_top_entry`;
* **`isDrivenCurve_walkStage_old_entry`** (a launch at a stage where the upper prefix's right end is already
  explored).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv

theorem isDrivenCurve_stage_fin_entry {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) {σ : ℝ≥0} {x : ℝ} (hx : β σ = x)
    (hle : ∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ β '' Icc 0 σ → y ≤ x)
    {q : ℝ≥0 → ℂ} {L : ℝ≥0} (hL : 0 < L) (hqc : ContinuousOn q (Icc 0 L)) (hqi : InjOn q (Iio L))
    (hq0 : q 0 = β σ) (hqβ : ∀ t, t ≤ L → q t ∈ β '' Ici σ)
    (hden : ∀ t : ℝ≥0, t < L →
      t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ q t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ x₀ : ℝ, IsRightEntryChart (pA '' Icc 0 1 ∪ β '' Icc 0 σ) (realMax (pA '' Icc 0 1 ∪ β '' Icc 0 σ))
        ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) 0).recenter x₀) ∧
      IsDrivenCurve (canonCurve (pA '' Icc 0 1 ∪ β '' Icc 0 σ) x₀ q L) := by
  set A := pA '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : (x : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hx⟩
  have hRx : realMax X = x := realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hx])
  rw [htL] at hγ
  obtain ⟨φ₀, hφc, hφ0, hφm, hqφ⟩ := exists_timeChange_fin hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hcongr : canonCurve X e q L = canonCurve X e q' L :=
    canonCurve_congr fun t ht => hqφ t (by exact_mod_cast ht)
  have hφS : ∀ t : ℝ≥0, t < L → φ₀ t < φ₀ L := fun t ht => lt_of_strictMonoOn_Iio hφc hφm ht
  have hS : 0 < φ₀ L := by rw [← hφ0]; exact hφS 0 hL
  have hpos : ∀ t : ℝ≥0, 0 < t → t ≤ L → 0 < φ₀ t := fun t ht htL' => by
    rcases htL'.lt_or_eq with h | h
    · rw [← hφ0]; exact hφm hL h ht
    · rw [h]; exact hS
  -- the good times for the canonical chart contain the good times for `A`
  have hgood : {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} ⊆ canonGood X q' (L : ℝ≥0∞) := by
    rintro t' ⟨ht'L, ht'⟩
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      rw [← h, hq0, hx] at ht'
      have him : (0 : ℝ) < ((x : ℝ) : ℂ).im := ht'.1
      simp at him
    have ht'L' : t' ≤ L := by exact_mod_cast ht'L
    refine ⟨ht'L, ?_⟩
    have hq := hqφ t' ht'L'
    rw [hq] at ht'
    exact mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (hpos t' ht'0 ht'L') ht'
  have hdq : ∀ t : ℝ≥0, t < L → t ∈ closure (canonGood X q' (L : ℝ≥0∞)) := fun t ht =>
    closure_mono hgood (hden t ht)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hmaps : MapsTo φ₀ (canonGood X q' (L : ℝ≥0∞)) {s' : ℝ≥0 | γ s' ∈ H} := fun t' ht' =>
    (canon_eq_of_lift_good (ζ := γ ∘ φ₀) hA (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr ht'.2).2
  have hdγ : ∀ s : ℝ≥0, (s : ℝ) < (φ₀ L : ℝ) → s ∈ closure {s' : ℝ≥0 | γ s' ∈ H} := by
    intro s hs
    have hs' : s < φ₀ L := by exact_mod_cast hs
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ L) hφc.continuousOn
      (show s ∈ Icc (φ₀ 0) (φ₀ L) from ⟨by rw [hφ0]; exact bot_le, hs'.le⟩)
    have htL' : t < L := lt_of_le_of_ne ht.2 fun h => (ne_of_lt hs') (by rw [← hts, h])
    rw [← hts]
    exact map_mem_closure hφc (hdq t htL') hmaps
  refine ⟨e, by rw [himg] at hrc; exact hrc, ?_⟩
  rw [hcongr]
  exact isDrivenCurve_canonCurve_of_timeChange hA hgt hgi hgfr hγ.2.1 hγ.2.2.1 hS hL hφc hφm hφ0 hφS hdγ hζl hdq

theorem isDrivenCurve_stage_top_entry {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β) {σ : ℝ≥0} {x : ℝ} (hx : β σ = x)
    (hle : ∀ y : ℝ, (y : ℂ) ∈ pA '' Icc 0 1 ∪ β '' Icc 0 σ → y ≤ x)
    {q : ℝ≥0 → ℂ} (hqc : Continuous q) (hqi : Function.Injective q) (hq0 : q 0 = β σ)
    (hqβ : range q = β '' Ici σ)
    (hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | q t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ x₀ : ℝ, IsRightEntryChart (pA '' Icc 0 1 ∪ β '' Icc 0 σ) (realMax (pA '' Icc 0 1 ∪ β '' Icc 0 σ))
        ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ β '' Icc 0 σ)) 0).recenter x₀) ∧
      IsDrivenCurve (canonCurve (pA '' Icc 0 1 ∪ β '' Icc 0 σ) x₀ q ⊤) := by
  set A := pA '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨p, hpc', hp0', hpH', hpv', himg⟩ := stagePath_pinv hpc hp0 hpH hpv hβ hβ0 σ
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  obtain ⟨e, g, hrc, hgc, hgi, hgt, hgf, hgfr⟩ := exists_canon_package_pinv hpc' hp0' hpH' hpv'
  have hS1X : p '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β := by
    rw [himg]; exact union_subset hS1 ((image_subset_range _ _).trans (range_subset_closedLeftSide β))
  have hrc' : IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1))
      ((Mo.hullChart (fillH (p '' Icc 0 1)) 0).recenter (-(-e))) := by rwa [neg_neg]
  obtain ⟨tL, γ, hγ⟩ := Lk.exists_tailLiftCurve hpc' hp0' hpH' hβ hβ0 hS1X hrc' hgc hgi hgt hgf
  have hA := isHPHull_fillH_path hpc' hp0'
  rw [himg] at hγ hgt hgi hgfr hA
  have hxX : (x : ℂ) ∈ X := Or.inr ⟨σ, ⟨bot_le, le_rfl⟩, hx⟩
  have hRx : realMax X = x := realMax_eq_of_le hXc hxX hle
  have htL : tL = σ := hβ.2.1 (by rw [hγ.1, hRx, hx])
  rw [htL] at hγ
  obtain ⟨φ₀, hφc, hφ0, hφm, hφs, hqφ⟩ := exists_timeChange_top hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hcongr : canonCurve X e q ⊤ = canonCurve X e q' ⊤ := canonCurve_congr fun t _ => hqφ t
  have hgood : {t' : ℝ≥0 | q t' ∈ H \ fillH A} ⊆ canonGood X q' ⊤ := by
    rintro t' ht'
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      have ht0 : q 0 ∈ H \ fillH A := h ▸ ht'
      rw [hq0, hx] at ht0
      have him : (0 : ℝ) < ((x : ℝ) : ℂ).im := ht0.1
      simp at him
    refine ⟨le_top, ?_⟩
    have ht'' : q t' ∈ H \ fillH A := ht'
    rw [hqφ t'] at ht''
    exact mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (by rw [← hφ0]; exact hφm ht'0) ht''
  have hdq : ∀ t : ℝ≥0, t ∈ closure (canonGood X q' ⊤) := fun t => closure_mono hgood (hden t)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hmaps : MapsTo φ₀ (canonGood X q' ⊤) {s' : ℝ≥0 | γ s' ∈ H} := fun t' ht' =>
    (canon_eq_of_lift_good (ζ := γ ∘ φ₀) hA (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr ht'.2).2
  have hdγ : ∀ s : ℝ≥0, s ∈ closure {s' : ℝ≥0 | γ s' ∈ H} := fun s => by
    obtain ⟨t, rfl⟩ := hφs s
    exact map_mem_closure hφc (hdq t) hmaps
  -- the lift is driven
  set γ' : ℝ → ℂ := fun r => γ r.toNNReal with hγ'def
  have hc' : ContinuousOn γ' (Ici 0) := (hγ.2.1.1.comp continuous_real_toNNReal).continuousOn
  have hinj' : InjOn γ' (Ici 0) := fun a ha b hb hab => by
    have := hγ.2.1.2.1 hab
    rw [← Real.coe_toNNReal a ha, ← Real.coe_toNNReal b hb, this]
  have hH' : MapsTo γ' (Ici 0) Hbar := fun r _ => hγ.2.1.2.2.1 r.toNNReal
  have h0' : γ' 0 = 0 := by simp [hγ'def, hγ.2.2.1]
  have hinf' : Tendsto (fun r => ‖γ' r‖) atTop atTop := hγ.2.1.2.2.2.comp tendsto_real_toNNReal_atTop
  have hR : ∀ S : ℝ, interior {r ∈ Ioo (0 : ℝ) S | (γ' r).im = 0} = ∅ := fun S =>
    interior_real_eq_empty_of_dense fun s _ => hdγ s
  have hdr : IsDrivenCurve γ' :=
    ⟨hc', h0', fun S hS => FinRel.exists_localDriver_of_lt hc' hinj' hH' h0' hinf' (hR S) hS le_rfl⟩
  -- the time change on `[0, ∞)`
  set Φ : ℝ → ℝ := fun u => (φ₀ u.toNNReal : ℝ) with hΦdef
  have hΦc : Continuous Φ := NNReal.continuous_coe.comp (hφc.comp continuous_real_toNNReal)
  have hΦm : StrictMonoOn Φ (Ici 0) := fun a ha b hb hab => by
    show (φ₀ a.toNNReal : ℝ) < φ₀ b.toNNReal
    exact_mod_cast hφm ((Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt ha hab)).2 hab)
  have hΦ0 : Φ 0 = 0 := by simp [hΦdef, hφ0]
  have hΦs : ∀ t, 0 ≤ t → Φ '' Icc 0 t = Icc 0 (Φ t) := by
    intro t ht
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨?_, hΦm.monotoneOn hr.1 ht hr.2⟩
      rw [← hΦ0]; exact hΦm.monotoneOn (le_refl (0 : ℝ)) hr.1 hr.1
    · have := intermediate_value_Icc ht hΦc.continuousOn
      rwa [hΦ0] at this
  have hcomp := isDrivenCurve_comp hdr hΦc.continuousOn hΦm hΦ0 hΦs
  refine ⟨e, by rw [himg] at hrc; exact hrc, ?_⟩
  rw [hcongr]
  refine Vk.IsDrivenCurve.congr hcomp fun u hu => ?_
  show γ' (Φ u) = canonVal X e q' ⊤ (if (⊤ : ℝ≥0∞) = ⊤ then u else clockOf (⊤ : ℝ≥0∞).toReal u).toNNReal
  simp only [↓reduceIte]
  rw [canonVal_eq_of_lift (ζ := γ ∘ φ₀) hA (hγ.2.1.1.comp hφc) (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr
    (hdq _)]
  simp [hγ'def, hΦdef]


section Walk

open Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem isDrivenCurve_walkStage_old_entry {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H) :
    ∃ x₀ : ℝ, IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        (realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
        ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
          0).recenter x₀) ∧
      IsDrivenCurve (canonCurve
      (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₀
      (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hndd : stStatus s ≠ GW1Conn.stDead := not_dead_of_launch w D hl'
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  -- the records
  have hM : ∀ i, i < n + 1 → stStatus (ExplState.run κ b jumps w D i) ≠ GW1Conn.stDone := fun i hi hd =>
    hnd (by rw [hs, Lx.run_eq_of_done w D hd n (by omega)]; exact hd)
  have hfin := fin_before_first_done hM
  have hri := recInv_ptRec_run_le hP (N := n) (fun j hj hlj => hfin j (by omega) hlj) hlm hlh
  have hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k := fun k hk => (hri k hk).1
  have hpt : stPt s = stRecR s := by
    rcases (hri n le_rfl).2 with h | h | h
    · exact absurd h hnd
    · exact absurd h hndd
    · exact h
  have hbeyond : ∀ y : ℝ, (y : ℂ) ∈ Pn → y ≤ stPt s := fun y hy => by
    by_contra hlt
    exact notMem_prefix_of_beyond hP hrec hlm hnd (hpt ▸ not_le.1 hlt) hy
  -- the cut of `β` at the seed
  have hPc : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hPp : IsPreconnected Pn := by
    rcases hpinv with h | ⟨p, hp⟩
    · rw [h]; exact isPreconnected_singleton
    · rw [← hp.2.2.2.2]; exact isPreconnected_Icc.image _ hp.1
  have h0P : β 0 ∈ Pn := by
    rw [hβ0]; exact Or.inl (Or.inl (by simp [hw, boundaryWalkSpec]))
  have hPr : Pn ⊆ range β := by
    rw [hβr]; exact statePhysicalSet_subset_physSet (κ := κ) (b := b) (jumps := jumps) (D := D) hlen.le
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℂ, T = pcPt s (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := ⟨_, rfl⟩
  have htipT := htip.trans hTdef.symm
  have hTr : T ⊆ range β := by rw [hβr, ← htipT]; exact tipSet_subset_physSet_launch hl
  have hpcc := continuousOn_pcPt_launch hP hl
  have hTp : IsPreconnected T := hTdef ▸ (WalkSide.isPreconnected_le_ennreal _).image _ hpcc
  have hPT : Pn ∩ T = {((stPt s : ℝ) : ℂ)} := by
    rw [← htipT, inter_comm]; exact tip_inter_old_eq hW hl
  have hinj := pcPt_injOn_launch hP hW hl
  have hq0 := pcPt_zero_launch hP hW hl hpos
  obtain ⟨t₁, ht₁0, ht₁L⟩ : ∃ t₁ : ℝ≥0, 0 < t₁ ∧ (t₁ : ℝ≥0∞) < (D n).2 := by
    obtain ⟨r, hr0, hrL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hpos)
    exact ⟨r, by exact_mod_cast hr0, hrL⟩
  have h0L : ((0 : ℝ≥0) : ℝ≥0∞) < (D n).2 := pos_iff_ne_zero.2 hpos
  have hT2 : ∃ y ∈ T, y ≠ ((stPt s : ℝ) : ℂ) := ⟨pcPt s (D n) t₁, hTdef ▸ ⟨t₁, ht₁L.le, rfl⟩, fun h =>
    (ne_of_gt ht₁0) (hinj ht₁L h0L (h.trans hq0.symm))⟩
  obtain ⟨σ, hσ, hPσ, hTσ⟩ := exists_arc_of_cut hβ hPc hPp h0P hPr hTr hTp hPT hT2
  -- the good times of the piece for `A`
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨-, tR, htR, -, -, -, hright⟩ := Lk.s2HullRight hpc hp0 hpH hβ hβ0 hS1
  have hAH := isHPHull_fillH_path hpc hp0
  have hDom : (Mo.hullChart (fillH A) 0).2.1 '' H = H \ fillH A := (Mo.isDomainChart_hullChart hAH 0).image_eq
  have hden0 := S3.Asm.hgd_of_launch_tailH hP hW hl hAc.isClosed hDom hβ hβ0 hβr htR hR hright (hS3 tR htR)
  have hgoodeq : goodT (Mo.hullChart (fillH A) 0) s (D n) =
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s (D n) t ∈ H \ fillH A} := by
    ext t; simp only [goodT, hDom]
  rw [hgoodeq] at hden0
  -- the largest real point
  have hle : ∀ y : ℝ, (y : ℂ) ∈ A ∪ β '' Icc 0 σ → y ≤ stPt s := by
    rintro y (hy | hy)
    · exact (Lx.le_realMax_of_mem hAc hy).trans (hbeyond _ hR)
    · rw [← hPσ] at hy; exact hbeyond y hy
  have hX : A ∪ Pn = A ∪ β '' Icc 0 σ := by rw [hPσ]
  rw [hX]
  have hq0' : pcPt s (D n) 0 = β σ := by rw [hq0, hσ]
  rcases eq_or_ne (D n).2 ⊤ with htop | hfinL
  · -- the infinite last piece
    rw [htop] at hpcc hinj hden0 hTdef ⊢
    have hqc : Continuous (pcPt s (D n)) := by
      rw [← continuousOn_univ]
      exact hpcc.mono fun t _ => (show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hqi : Function.Injective (pcPt s (D n)) := fun a b' hab =>
      hinj (show (a : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) (show (b' : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) hab
    have hdone : stStatus (ExplState.run κ b jumps w D (n + 1)) = GW1Conn.stDone := by
      by_contra hnd'
      exact fin_of_not_done hnd' hl htop
    have hphys := physSet_walk_eq_of_done (κ := κ) (θ := θ) (b := b) (J := jumps) (D := D) (n := n + 1)
      (Nat.succ_le_of_lt hlen) hdone
    have hsucc := prefixPhysSet_succ_of_launch hl'
    have hqβ : range (pcPt s (D n)) = β '' Ici σ := by
      refine Subset.antisymm ?_ ?_
      · rintro _ ⟨t, rfl⟩; exact hTσ (hTdef ▸ ⟨t, (show (t : ℝ≥0∞) ≤ ⊤ from le_top), rfl⟩)
      · rintro _ ⟨τ, hτ, rfl⟩
        have hmem : β τ ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by
          have := mem_range_self (f := β) τ
          rw [hβr, hphys] at this
          exact this
        rw [hsucc] at hmem
        rcases hmem with hP' | hT'
        · have hP'' : β τ ∈ Pn := hP'
          rw [hPσ] at hP''
          obtain ⟨τ', hτ', he⟩ := hP''
          have := hβ.2.1 he
          have hτσ : τ = σ := le_antisymm (this ▸ hτ'.2) hτ
          rw [hτσ, ← hq0']; exact mem_range_self 0
        · have hT'' : β τ ∈ T := by rw [← htipT]; exact hT'
          rw [hTdef] at hT''
          obtain ⟨t, -, ht⟩ := hT''
          exact ⟨t, ht⟩
    have hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | pcPt s (D n) t' ∈ H \ fillH A} := fun t => by
      have := hden0 (show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
      refine closure_mono (fun t' ht' => ht'.2) this
    exact isDrivenCurve_stage_top_entry hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle hqc hqi hq0' hqβ hden
  · -- a finite piece
    set L := (D n).2.toNNReal with hLdef
    have hLe : ((L : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfinL
    rw [← hLe] at hpcc hinj hden0 hTdef ⊢
    have hLpos : 0 < L := by
      have := pos_iff_ne_zero.2 hpos
      rw [← hLe] at this; exact_mod_cast this
    have hqc : ContinuousOn (pcPt s (D n)) (Icc 0 L) :=
      hpcc.mono fun t ht => (show (t : ℝ≥0∞) ≤ L by exact_mod_cast ht.2)
    have hqi : InjOn (pcPt s (D n)) (Iio L) := fun a ha b' hb hab =>
      hinj (show (a : ℝ≥0∞) < L by exact_mod_cast ha) (show (b' : ℝ≥0∞) < L by exact_mod_cast hb) hab
    have hqβ : ∀ t, t ≤ L → pcPt s (D n) t ∈ β '' Ici σ := fun t ht =>
      hTσ (hTdef ▸ ⟨t, by exact_mod_cast ht, rfl⟩)
    have hden : ∀ t : ℝ≥0, t < L →
        t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ pcPt s (D n) t' ∈ H \ fillH A} := fun t ht =>
      hden0 (show (t : ℝ≥0∞) < L by exact_mod_cast ht)
    exact isDrivenCurve_stage_fin_entry hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle hLpos hqc hqi hq0' hqβ hden

end Walk

end InteractingSLE.Theorem14.SB.Nc
