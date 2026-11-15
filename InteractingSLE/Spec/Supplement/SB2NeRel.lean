/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeAe

/-!
# F2b′'s relative facts: the canonical curve read back to B's piece

Packet PROVE-AUX61-NOJUMP (round 22, component F), deterministic.

* `pcPt_eq_of_runs`: two walk families with the same runs have the same piece at a regular launch;
* **`g_canonCurve_eq`**: a continuous extension `g` of the inverse hull chart (offset `0`) reads the canonical
  relative curve (offset `x₀`) back to B's piece at every relative time;
* `cTime_lt`: relative times are before a finite lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Ne

open Exist Exist.StagedLaw Exist.Staged Restart GW1W LuM Lk Dv Sec7.PocketTraversal GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Two walk families with the same runs have the same piece** at a regular launch. -/
theorem pcPt_eq_of_runs {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hrun : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hR : GW1P.PieceRegular (D ℓ).1 (D ℓ).2) (hR' : GW1P.PieceRegular (D' ℓ).1 (D' ℓ).2) :
    (D ℓ).2 = (D' ℓ).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) (D ℓ) t =
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' ℓ) (D' ℓ) t := by
  have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [← hrun]; exact hl
  have h1 := pieces_run_succ_of_launch hl
  have h2 := pieces_run_succ_of_launch hl'
  rw [hrun (ℓ + 1), hrun ℓ] at h1
  have hx := List.singleton_inj.1 (List.append_cancel_left (h1.symm.trans h2))
  have hL : (D ℓ).2 = (D' ℓ).2 := by
    have := congrArg (fun x => x.2.2) hx
    simpa using this
  have hww : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D ℓ).2 → (D ℓ).1 s = (D' ℓ).1 s := fun s hs => by
    have := congrFun (congrArg (fun x => x.2.1) hx) s
    simp only [min_eq_right (le_top : (D ℓ).2 ≤ ⊤), min_eq_right (le_top : (D' ℓ).2 ≤ ⊤)] at this
    rw [min_eq_left hs, ← hL, min_eq_left hs] at this
    simpa using this
  refine ⟨hL, fun t ht => ?_⟩
  have htr := Nc.trOf_eq_of_eqOn hR hR' le_rfl (hL ▸ le_rfl) hww t ht
  unfold pcPt
  rw [hrun ℓ, htr]

/-- **Relative times are before a finite lifetime.** -/
theorem cTime_lt {L : ℝ≥0∞} (hL : L ≠ ⊤) (hL0 : L ≠ 0) {v : ℝ} (hv : 0 ≤ v) :
    ((Nc.cTime L v : ℝ≥0) : ℝ≥0∞) < L := by
  have hLr : 0 < L.toReal := ENNReal.toReal_pos hL0 hL
  have hr : Nc.rTime L v < L.toReal := by
    unfold Nc.rTime clockOf
    simp only [hL, ↓reduceIte]
    have : v / (1 + v) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  show ENNReal.ofReal (Nc.rTime L v) < L
  exact (ENNReal.ofReal_lt_iff_lt_toReal (Nc.rTime_nonneg hL0 hv) hL).2 hr


section Canon

variable {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

/-- **The canonical curve is in the closed half-plane**, and at good times in `ℍ`. -/
theorem canonCurve_mem_Hbar (hA : IsHPHull (fillH X)) (hL : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L})
    (hdr : IsDrivenCurve (canonCurve X x₀ p L)) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ (canonCurve X x₀ p L v).im := by
  set G : Set ℝ := {v' : ℝ | 0 ≤ v' ∧ Nc.cTime L v' ∈ canonGood X p L} with hG
  have hcl := mem_closure_goodU (x₀ := x₀) hA.2.2.1 hL hpc hdr hv
  have : (𝓝[G] v).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have h1 : Tendsto (canonCurve X x₀ p L) (𝓝[G] v) (𝓝 (canonCurve X x₀ p L v)) :=
    (hdr.continuousOn v hv).tendsto.mono_left (nhdsWithin_mono _ fun v' hv' => hv'.1)
  refine ge_of_tendsto ((Complex.continuous_im.tendsto _).comp h1) (eventually_nhdsWithin_of_forall fun v' hv' => ?_)
  rw [Function.comp_apply, canonCurve_eq_fwd hL hv'.1 hv'.2.2]
  exact le_of_lt (hullChart_fwd_spec hA x₀ hv'.2.2).1

/-- **A continuous extension of the inverse hull chart reads the canonical curve back to the piece.** -/
theorem g_canonCurve_eq (hA : IsHPHull (fillH X)) (hL : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L})
    (hdr : IsDrivenCurve (canonCurve X x₀ p L)) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) {v : ℝ} (hv : 0 ≤ v) :
    g (canonCurve X x₀ p L v + x₀) = p (Nc.cTime L v) := by
  set G : Set ℝ := {v' : ℝ | 0 ≤ v' ∧ Nc.cTime L v' ∈ canonGood X p L} with hG
  have hcl := mem_closure_goodU (x₀ := x₀) hA.2.2.1 hL hpc hdr hv
  have : (𝓝[G] v).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hGs : G ⊆ Ici 0 := fun v' hv' => hv'.1
  have h1 : Tendsto (fun v' => canonCurve X x₀ p L v' + x₀) (𝓝[G] v)
      (𝓝[{z | 0 ≤ z.im}] (canonCurve X x₀ p L v + x₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((hdr.continuousOn v hv).tendsto.mono_left (nhdsWithin_mono _ hGs)).add_const _,
      eventually_nhdsWithin_of_forall fun v' hv' => ?_⟩
    show 0 ≤ (canonCurve X x₀ p L v' + (x₀ : ℂ)).im
    simpa using canonCurve_mem_Hbar hA hL hpc hdr hv'.1
  have hmem : 0 ≤ (canonCurve X x₀ p L v + (x₀ : ℂ)).im := by
    simpa using canonCurve_mem_Hbar hA hL hpc hdr hv
  have h2 := (hgc _ hmem).tendsto.comp h1
  have h3 : Tendsto (fun v' => p (Nc.cTime L v')) (𝓝[G] v) (𝓝 (p (Nc.cTime L v))) := by
    have hct : Tendsto (Nc.cTime L) (𝓝[G] v) (𝓝 (Nc.cTime L v)) :=
      (Nc.continuousOn_cTime v hv).tendsto.mono_left (nhdsWithin_mono _ hGs)
    have hev : ∀ᶠ v' in 𝓝[G] v, Nc.cTime L v' ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} :=
      eventually_nhdsWithin_of_forall fun v' hv' => Nc.cTime_le hL hv'.1
    exact (hpc _ (Nc.cTime_le hL hv)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hct, hev⟩)
  have h4 : ∀ v' ∈ G, g (canonCurve X x₀ p L v' + x₀) = p (Nc.cTime L v') := by
    intro v' hv'
    have hf := hullChart_fwd_spec hA 0 hv'.2.2
    have he : canonCurve X x₀ p L v' + x₀ = (Mo.hullChart (fillH X) 0).1 (p (Nc.cTime L v')) := by
      rw [canonCurve_eq_fwd hL hv'.1 hv'.2.2, Mo.hullChart_fwd, Mo.hullChart_fwd]
      push_cast; ring
    rw [he, hgi hf.1]
    exact hf.2
  exact tendsto_nhds_unique (h2.congr' (eventually_nhdsWithin_of_forall h4)) h3

end Canon

end InteractingSLE.Theorem14.SB.Ne
