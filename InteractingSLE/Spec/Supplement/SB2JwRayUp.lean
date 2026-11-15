/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwRay
import InteractingSLE.Spec.Supplement.SB2LwWord
import InteractingSLE.Spec.Supplement.SB2LuLift
import InteractingSLE.Spec.Supplement.SB2MbFill

/-!
# SB2(2): the upper launch chart's ray (item 4a, deterministic)

Packet PROVE-SB2-LIFTSET (round 17). For a run chart `c` of a not finished run whose prefix fill is that of a compact
`A` with real points `≤ R` (the upper launch chart at `R = max (A ∩ ℝ)`):

* **`runRay_facts`** (`SB2LwWord.upper_bdry_facts` with all its intermediate facts): the real boundary values
  `bdryValue c` are continuous and strictly increasing on `(R, ∞)`, tend to the right entry `e` at `R⁺`, are the limits
  of `c.1` from `ℍ`, the boundary map `g` of `c⁻¹` inverts them, and beyond the record they are the real profile;
* **`rayChartLim_of_run`**, **`rayChartInj_of_run`** for `ι = rayMap (bdryValue c) R e` and `m = −e`;
* **`rayCorr_of_run`**: with the state invariant `UState`, the word `β` original beyond the record (`ROrig`), data `b'`
  equal to `β` off a finite set and **the record at most `R`**, `ι` is a ray correspondence between `b` and
  `affData 1 m b'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lh FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The real boundary values of a run chart right of a free `R`.** -/
theorem runRay_facts (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) :
    ContinuousOn (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) (Ioi R) ∧
      InjOn (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) (Ioi R) ∧
      (∀ x : ℝ, R < x → Tendsto (stChart (ExplState.run κ b jumps spec D n)).1 (𝓝[H] (x : ℂ))
        (𝓝 (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n)) x : ℂ))) ∧
      (∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (stChart (ExplState.run κ b jumps spec D n)).2.1 H ∧
        (∀ p ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps spec D n)).2.1 (𝓝[H] p) (𝓝 (g p))) ∧
        ∀ x : ℝ, R < x → g (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n)) x) = x) ∧
      Tendsto (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) (𝓝[>] R)
        (𝓝 (Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)) := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hreg n hnot
  have hcc : c.IsConformal := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
  have hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (Metric.ball (x : ℂ) ρ) M.hull := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := Lx.exists_ball_disjoint_fillH_right hAc fun y hy => lt_of_le_of_lt (hRA y hy) hx
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  obtain ⟨he, hcont, hinv⟩ := Lx.bdryValue_facts_right hcc M hgc hgi hfree
  have hinj : InjOn (Lx.bdryValue c) (Ioi R) := fun x hx y hy hxy => by
    have h1 := hinv x hx
    rw [hxy, hinv y hy] at h1
    exact_mod_cast h1.symm
  obtain ⟨f, hf, hlim⟩ := Lx.isRightEntryValue_runChart spec D hreg n hnot hAc hAf hRA
  have hlim' : Tendsto (Lx.bdryValue c) (𝓝[>] R) (𝓝 (Lx.rightEntry c R)) := by
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := Lx.tendsto_bdryValue (hf x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  exact ⟨hcont, hinj, he, ⟨g, hgc, hgi, hgt, hinv⟩, hlim'⟩

/-- **`RayChartLim` of a run chart.** -/
theorem rayChartLim_of_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) :
    RayChartLim (stChart (ExplState.run κ b jumps spec D n)) R
      (-Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)
      (rayMap (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) R
        (Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)) := by
  obtain ⟨-, -, -, ⟨g, -, -, hgt, hinv⟩, -⟩ := runRay_facts spec D hreg n hnot hAc hAf hRA
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  intro y hy
  rw [rayMap_of_lt hy]
  have e : (((Lx.bdryValue c y - Lx.rightEntry c R) - -Lx.rightEntry c R : ℝ) : ℂ) = (Lx.bdryValue c y : ℂ) := by
    push_cast; ring
  rw [e]
  have h := hgt ((Lx.bdryValue c y : ℝ) : ℂ) (Lw.ofReal_mem_Hbar _)
  rwa [hinv y hy] at h

/-- **`RayChartInj` of a run chart** (the forward chart continuous within `ℍ` at the ray, with real boundary values
the profile beyond the record, and the record at most `R`). -/
theorem rayChartInj_of_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) {x₀ : ℝ} (hS : UState x₀ (ExplState.run κ b jumps spec D n))
    (hrec : stRecR (ExplState.run κ b jumps spec D n) ≤ R) :
    RayChartInj (stChart (ExplState.run κ b jumps spec D n)) R
      (-Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)
      (rayMap (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) R
        (Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)) := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  obtain ⟨-, -, he, ⟨g, hgc, hgi, hgt, hinv⟩, -⟩ := runRay_facts spec D hreg n hnot hAc hAf hRA
  obtain ⟨hconf, hc, -, -, hcontc, -⟩ := hS
  have hval : ∀ x : ℝ, R < x → c.1 x = (Lx.bdryValue c x : ℂ) := fun x hx => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    exact tendsto_nhds_unique ((hcontc x (lt_of_le_of_lt hrec hx)).mono_right nhdsWithin_le_nhds) (he x hx)
  refine rayChartInj_of_continuousWithinAt (ĝ := g) (fun w hw => hconf.2.1 hw) (fun w hw => hconf.2.2 w hw) hgc
    hgi hgt (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · have h1 := (hcontc x (lt_of_le_of_lt hrec hx)).mono_right nhdsWithin_le_nhds
    have h2 : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (c.1 x)) := h1
    exact h2
  · rw [hval x hx, rayMap_of_lt hx]; push_cast; ring
  · rw [rayMap_of_lt hx]
    have e : (((Lx.bdryValue c x - Lx.rightEntry c R) - -Lx.rightEntry c R : ℝ) : ℂ) = (Lx.bdryValue c x : ℂ) := by
      push_cast; ring
    rw [e, hinv x hx]

/-- **The ray correspondence of a run chart** (`UState`, the word original beyond the record, data equal to the word
off a finite set, and the record at most `R`). -/
theorem rayCorr_of_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {R : ℝ}
    (hRA : ∀ y : ℝ, (y : ℂ) ∈ A → y ≤ R) {x₀ : ℝ} (hS : UState x₀ (ExplState.run κ b jumps spec D n))
    (hrec : stRecR (ExplState.run κ b jumps spec D n) ≤ R) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {β : BoundaryWord} (hO : ROrig b jumps β (ExplState.run κ b jumps spec D n)) {b' : ℝ → ℝ} {J' : Finset ℝ}
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hagree : ∀ y ∉ J' ∪ β.jumps, b' y = β.fn y) :
    RayCorr b jumps (affData 1 (-Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R) b')
      (affJumps 1 (-Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R) J') R
      (rayMap (Lx.bdryValue (stChart (ExplState.run κ b jumps spec D n))) R
        (Lx.rightEntry (stChart (ExplState.run κ b jumps spec D n)) R)) := by
  set c := stChart (ExplState.run κ b jumps spec D n) with hcdef
  set a := stRecR (ExplState.run κ b jumps spec D n) with hadef
  obtain ⟨hcont, hinj, he, -, hlim⟩ := runRay_facts spec D hreg n hnot hAc hAf hRA
  obtain ⟨-, hc, hm, -, hcontc, -⟩ := hS
  have heq : ∀ x : ℝ, R < x → Lx.bdryValue c x = rProf c x := fun x hx => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := (hcontc x (lt_of_le_of_lt hrec hx)).mono_right nhdsWithin_le_nhds
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast tendsto_nhds_unique (he x hx) h1
  have hmax : max R a = R := max_eq_left hrec
  have hsm : StrictMonoOn (Lx.bdryValue c) (Ioi R) := by
    refine strictMonoOn_Ioi_of_injOn hcont hinj (a := a) ?_
    rw [hmax]
    intro x hx y hy hxy
    rw [heq x hx, heq y hy]
    exact hm.1 (lt_of_le_of_lt hrec hx) (lt_of_le_of_lt hrec hy) hxy
  have hunb : ∀ M : ℝ, ∃ x, R < x ∧ M < Lx.bdryValue c x := by
    intro M
    obtain ⟨x, hxa, hMx⟩ := hm.2.2 M
    by_cases hRx : R < x
    · exact ⟨x, hRx, by rw [heq x hRx]; exact hMx⟩
    · push Not at hRx
      have hR1 : R < R + 1 := lt_add_one R
      refine ⟨R + 1, hR1, ?_⟩
      rw [heq _ hR1]
      exact hMx.trans (hm.1 hxa (lt_of_le_of_lt hrec hR1) (lt_of_le_of_lt hRx hR1))
  have hdat : ∀ x, R < x → x ∉ jumps → Lx.bdryValue c x ∉ J' ∪ β.jumps → b' (Lx.bdryValue c x) = b x := by
    intro x hx hxJ hxK
    rw [hagree _ hxK, heq x hx]
    rw [heq x hx] at hxK
    exact hO x (lt_of_le_of_lt hrec hx) hxJ (fun h => hxK (Finset.mem_union_right _ h))
  exact rayCorr_of_profile hsm hcont hlim hb hb' hdat hunb

end InteractingSLE.Theorem14.SB.Lk
