/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JaGood

/-!
# SB2(2)'s joint stage induction: F2a at a finite old stage, with the canonical curve's lift

Packet PROVE-SB2-LIFTSET (round 20). CORNER's `Dv.isDrivenCurve_walkStage_old` gives F2a at a stage whose start state
contains `R` with an unnamed offset. Its proof writes the canonical curve as a lift: through the hull chart of
`X = A ∪ β([0, σ])` (offset `e` of CORNER's canonical package) the piece `q = β (σ + φ₀ ·)` lifts to `γ ∘ φ₀`, `γ` the
tail lift of `β` after the cut. **`canon_old_fin`** returns this offset with the lift: the canonical curve is driven
and its values before the end are those of the continuous curve `γ ∘ φ₀` in `ℍ̄` (`Dv.canonVal_eq_of_lift`). This is
what carries F2a to the run chart at a finite stage, including the convergence at `∞` and the values in `ℍ̄`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The canonical values of two curves agreeing up to the lifetime agree. -/
theorem canonVal_congr {X : Set ℂ} {x₀ : ℝ} {q q' : ℝ≥0 → ℂ} {L : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → q t = q' t) (t : ℝ≥0) :
    Dv.canonVal X x₀ q L t = Dv.canonVal X x₀ q' L t := by
  classical
  have hG := Dv.canonGood_congr (X := X) h
  unfold Dv.canonVal
  rw [hG]
  split_ifs with hg
  · rw [h t hg.1]
  · unfold limUnder
    rw [Filter.map_congr (eventually_nhdsWithin_of_forall fun t' ht' => by rw [h t' ht'.1])]

/-- **F2a at a finite old stage, with the canonical curve's lift** (walk level). -/
theorem canon_old_fin {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) (hfin : (D n).2 ≠ ⊤)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hden : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ (e : ℝ) (ζ : ℝ≥0 → ℂ), Continuous ζ ∧ (∀ t, ζ t ∈ Hbar) ∧
      IsDrivenCurve (Dv.canonCurve (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        e (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 →
        Dv.canonVal (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) e
          (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 t = ζ t := by
  classical
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set q := pcPt s (D n) with hqdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨e, g, γ, hA, hgt, hgi, -, hgfr, hγ⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hX : A ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n = X := by rw [hPσ]
  rw [hX]
  -- the finite lifetime
  set L := (D n).2.toNNReal with hLdef
  have hLe : ((L : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfin
  rw [← hLe] at hden ⊢
  have hLpos : 0 < L := by
    have := pos_iff_ne_zero.2 hpos
    rw [← hLe] at this; exact_mod_cast this
  have hpcc := continuousOn_pcPt_launch hP hl
  rw [← hLe] at hpcc
  have hqc : ContinuousOn q (Icc 0 L) := hpcc.mono fun t ht => (show (t : ℝ≥0∞) ≤ L by exact_mod_cast ht.2)
  have hinj := pcPt_injOn_launch hP hW hl
  rw [← hLe] at hinj
  have hqi : InjOn q (Iio L) := fun a ha b' hb hab =>
    hinj (show (a : ℝ≥0∞) < L by exact_mod_cast ha) (show (b' : ℝ≥0∞) < L by exact_mod_cast hb) hab
  have hq0 : q 0 = β σ := by rw [hσ]; exact pcPt_zero_launch hP hW hl hpos
  have hqβ : ∀ t, t ≤ L → q t ∈ β '' Ici σ := fun t ht => hTσ t (by rw [← hLe]; exact_mod_cast ht)
  obtain ⟨φ₀, hφc, hφ0, hφm, hqφ⟩ := Dv.exists_timeChange_fin hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hqq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (L : ℝ≥0∞) → q t = q' t := fun t ht => hqφ t (by exact_mod_cast ht)
  have hφS : ∀ t : ℝ≥0, t < L → φ₀ t < φ₀ L := fun t ht => Dv.lt_of_strictMonoOn_Iio hφc hφm ht
  have hS : 0 < φ₀ L := by rw [← hφ0]; exact hφS 0 hLpos
  have hpos' : ∀ t : ℝ≥0, 0 < t → t ≤ L → 0 < φ₀ t := fun t ht htL' => by
    rcases htL'.lt_or_eq with h | h
    · rw [← hφ0]; exact hφm hLpos h ht
    · rw [h]; exact hS
  -- the good times for the canonical chart contain the good times for `A`
  have hgood : {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (L : ℝ≥0∞) ∧ q t' ∈ H \ fillH A} ⊆ Dv.canonGood X q' (L : ℝ≥0∞) := by
    rintro t' ⟨ht'L, ht'⟩
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      rw [← h, hq0, hσ] at ht'
      have him : (0 : ℝ) < (((stPt s : ℝ) : ℂ)).im := ht'.1
      simp at him
    have ht'L' : t' ≤ L := by exact_mod_cast ht'L
    refine ⟨ht'L, ?_⟩
    rw [hqφ t' ht'L'] at ht'
    exact Dv.mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (hpos' t' ht'0 ht'L') ht'
  have hdq : ∀ t : ℝ≥0, t < L → t ∈ closure (Dv.canonGood X q' (L : ℝ≥0∞)) := fun t ht =>
    closure_mono hgood (hden t (by exact_mod_cast ht))
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hmaps : MapsTo φ₀ (Dv.canonGood X q' (L : ℝ≥0∞)) {s' : ℝ≥0 | γ s' ∈ H} := fun t' ht' =>
    (Dv.canon_eq_of_lift_good (ζ := γ ∘ φ₀) hA (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr ht'.2).2
  have hdγ : ∀ s' : ℝ≥0, (s' : ℝ) < (φ₀ L : ℝ) → s' ∈ closure {s'' : ℝ≥0 | γ s'' ∈ H} := by
    intro s' hs'
    have hs'' : s' < φ₀ L := by exact_mod_cast hs'
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ L) hφc.continuousOn
      (show s' ∈ Icc (φ₀ 0) (φ₀ L) from ⟨by rw [hφ0]; exact bot_le, hs''.le⟩)
    have htL' : t < L := lt_of_le_of_ne ht.2 fun h => (ne_of_lt hs'') (by rw [← hts, h])
    rw [← hts]
    exact map_mem_closure hφc (hdq t htL') hmaps
  have hdr := Dv.isDrivenCurve_canonCurve_of_timeChange hA hgt hgi hgfr hγ.2.1 hγ.2.2.1 hS hLpos hφc hφm hφ0 hφS
    hdγ hζl hdq
  have hζc : Continuous (fun t => γ (φ₀ t)) := hγ.2.1.1.comp hφc
  refine ⟨e, fun t => γ (φ₀ t), hζc, fun t => hγ.2.1.2.2.1 _, ?_, fun t ht => ?_⟩
  · rw [Dv.canonCurve_congr hqq']; exact hdr
  · rw [canonVal_congr hqq']
    exact Dv.canonVal_eq_of_lift hA hζc (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr (hdq t (by exact_mod_cast ht))

end InteractingSLE.Theorem14.SB.Lk
