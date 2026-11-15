/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JyHull

/-!
# SB2(2): the lifted endpoint and the density of the tail's `D`-times

Packet PROVE-SB2-LIFTSET (round 14). Two more facts of `StageGeom` **proved outright** for an actual launched piece
(regular launch, conformal upper chart `c`):

* **`hend_of_launch`**: at a finite positive lifetime `L`, if `L` is a good time (`pcPt L ∈ D`), the lifted endpoint
  is a limit of lifted good points before it (`pcPt` is continuous on `[0, L]`, `D` is open, `c.1` is continuous on
  `D`, and `L > 0` is a limit of earlier times);
* **`hdense_tail_of_good`**: the `D`-times of the tail are dense in the tail times of the piece, given the density of
  the piece's good times before its lifetime (`hgd`), the tail position of its points in `D` and `β₀` a closed
  embedding — so `StageGeom`'s `hdense₁` reduces to `hgd`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- The points of a regularly launched piece are continuous on `[0, e.2]`. -/
theorem continuousOn_pcPt_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    ContinuousOn (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := by
  obtain ⟨g, hgc, -, hval, -⟩ := tipSet_newPc_launch hP hl
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  exact (hgc.comp hα.2.1 fun t ht => im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht).congr
    fun t ht => hval t ht

/-- **The lifted endpoint is a limit of lifted good points before it** (`hend` of `StageGeom`). -/
theorem hend_of_launch {c : Chart} (hcc : c.IsConformal) (m : ℝ)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) :
    ∀ t ∈ goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n), (t : ℝ≥0∞) = (D n).2 →
      liftPt c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t) ∈
        closure ((fun t' => liftPt c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
          (D n) t')) '' (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ∩
            {t' | (t' : ℝ≥0∞) < (D n).2})) := by
  intro t ht heq
  have hpc := continuousOn_pcPt_launch hP hl
  have hp : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ c.2.1 '' H := ht.2
  have hca : ContinuousAt c.1 (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t) := by
    have hdom : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t ∈ (c.dom : Set ℂ) := by
      rw [hcc.coe_dom]; exact hp
    exact (hcc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hdom)).continuousAt
  have hF : ContinuousWithinAt
      (fun t' => liftPt c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t'))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} t :=
    (hca.comp_continuousWithinAt (hpc t ht.1)).add continuousWithinAt_const
  have ht0 : 0 < t := pos_iff_ne_zero.2 fun h => hpos (by rw [← heq, h]; simp)
  have hIK : Iio t ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := fun t' ht' => by
    show (t' : ℝ≥0∞) ≤ (D n).2
    rw [← heq]
    exact ENNReal.coe_le_coe.2 (le_of_lt ht')
  have hS : goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ∩
      {t' | (t' : ℝ≥0∞) < (D n).2} ∈ 𝓝[Iio t] t := by
    have h1 : pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ⁻¹' (c.2.1 '' H) ∈
        𝓝[{t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2}] t :=
      (hpc t ht.1).preimage_mem_nhdsWithin (hcc.isOpen_image.mem_nhds hp)
    filter_upwards [nhdsWithin_mono t hIK h1, self_mem_nhdsWithin] with t' h1' h2'
    refine ⟨⟨hIK h2', h1'⟩, ?_⟩
    show (t' : ℝ≥0∞) < (D n).2
    rw [← heq]
    exact ENNReal.coe_lt_coe.2 h2'
  have hNe : (𝓝[Iio t] t).NeBot := by
    have hI : t ∈ closure (Iio t) := by rw [closure_Iio' (a := t) ⟨0, ht0⟩]; exact mem_Iic.2 le_rfl
    exact mem_closure_iff_nhdsWithin_neBot.1 hI
  have hcl : t ∈ closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ∩
      {t' | (t' : ℝ≥0∞) < (D n).2}) := by
    rw [mem_closure_iff_clusterPt]
    exact hNe.mono (le_inf nhdsWithin_le_nhds (le_principal_iff.2 hS))
  exact (hF.mono fun t' ht' => ht'.1.1).mem_closure_image hcl

/-- **The tail's `D`-times are dense in the piece's tail times** (`hdense₁` of `StageGeom`), from the density of the
good times before the lifetime, the tail position of the piece's points in `D`, and `β₀` proper. -/
theorem hdense_tail_of_good {c : Chart} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {tL : ℝ≥0}
    (htail : (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩ c.2.1 '' H ⊆
      β₀ '' Ici tL)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))) :
    {s | β₀ (tL + s) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2} ⊆
      closure {s | β₀ (tL + s) ∈
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
          (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
          (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 ∩ c.2.1 '' H} := by
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  set T := (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 with hT
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hpc := continuousOn_pcPt_launch hP hl
  set K := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} with hK
  -- every time of the piece is a limit of good times
  have hgK : K ⊆ closure (goodT c s₁ (D n)) := by
    intro t ht
    rcases lt_or_eq_of_le (show (t : ℝ≥0∞) ≤ (D n).2 from ht) with hlt | heq
    · exact hgd hlt
    · have ht0 : 0 < t := pos_iff_ne_zero.2 fun h => hpos (by rw [← heq, h]; simp)
      have hI : t ∈ closure (Iio t) := by rw [closure_Iio' (a := t) ⟨0, ht0⟩]; exact mem_Iic.2 le_rfl
      refine closure_minimal (fun t' ht' => hgd ?_) isClosed_closure hI
      show (t' : ℝ≥0∞) < (D n).2
      rw [← heq]
      exact ENNReal.coe_lt_coe.2 ht'
  -- the piece's points are limits of its points in `D`
  have hTD : T ⊆ closure (T ∩ c.2.1 '' H) := by
    rw [hT, htip]
    rintro _ ⟨t, ht, rfl⟩
    have h1 := ((hpc t ht).mono (show goodT c s₁ (D n) ⊆ K from fun t' h => h.1)).mem_closure_image (hgK ht)
    refine closure_mono ?_ h1
    rintro _ ⟨t', ht', rfl⟩
    exact ⟨⟨t', ht'.1, rfl⟩, ht'.2⟩
  -- transport to the tail times through the closed embedding `β₀`
  have he := isClosedEmbedding_of_isProperCurve hβ
  intro s hs
  set G' := {u : ℝ≥0 | tL ≤ u ∧ β₀ u ∈ T ∩ c.2.1 '' H} with hG'
  have himg : β₀ '' G' = T ∩ c.2.1 '' H := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu.2
    · intro hz
      obtain ⟨u, hu, rfl⟩ := htail hz
      exact ⟨u, ⟨hu, hz⟩, rfl⟩
  have hu : tL + s ∈ closure G' := by
    rw [he.isInducing.closure_eq_preimage_closure_image, himg]
    exact hTD hs
  have hsub : (fun u : ℝ≥0 => u - tL) '' G' ⊆
      {s | β₀ (tL + s) ∈ T ∩ c.2.1 '' H} := by
    rintro _ ⟨u, hu, rfl⟩
    show β₀ (tL + (u - tL)) ∈ T ∩ c.2.1 '' H
    rw [add_tsub_cancel_of_le hu.1]
    exact hu.2
  have hcont : Continuous fun u : ℝ≥0 => u - tL := continuous_id.sub continuous_const
  have h2 := hcont.continuousWithinAt.mem_closure_image hu
  rw [show tL + s - tL = s from add_tsub_cancel_left tL s] at h2
  exact closure_mono hsub h2

end InteractingSLE.Theorem14.SB.Lk
