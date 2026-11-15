/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JbStep

/-!
# SB2(2)'s joint stage induction: the infinite last stage

Packet PROVE-SB2-LIFTSET (round 20). At an old stage whose actual piece is infinite (the walk's last piece):

* **`canonVal_eq_of_lift_shift`**: with a continuous lift `ζ` for the hull-chart offset `e`, the canonical values at
  any offset `x₀` are `ζ + (e − x₀)` on the closure of the good times;
* **`canon_old_top`** (walk level): F2a's canonical curve at its offset is the lift `γ ∘ φ₀` of CORNER's time change
  (the offsets agree since both curves start at `0`); the lift is transient, and the canonical curve's capacity
  lifetime is infinite (`capLife_root_top` with the hull chart of `A ∪ β([0, σ])` as the upper chart: the capacity of
  the prefix with the piece's initial part grows like twice its time, `hcap_prefix_piece`);
* **`stage_inf_of_canon`** (curve level): drivenness and `StageRelInfP` of the run-chart stage curve;
* **`relChart_bound_of_lt`**: the relative run chart's boundary map within bounded distance of the identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

/-- **The canonical values at any offset from a continuous lift at the offset `e`.** -/
theorem canonVal_eq_of_lift_shift {X : Set ℂ} (hA : IsHPHull (fillH X)) {e : ℝ} {q ζ : ℝ≥0 → ℂ}
    (hζc : Continuous ζ) (hζH : ∀ t, 0 ≤ (ζ t).im)
    (hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (ζ t - ((-e : ℝ) : ℂ))) (𝓝 (q t)))
    {g : ℂ → ℂ} (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q)))
    (hgi : EqOn g (Mo.hullChart (fillH X) 0).2.1 H) (hgfr : MapsTo g (Hbar \ H) (frontier (H \ fillH X)))
    {L : ℝ≥0∞} {t : ℝ≥0} (ht : t ∈ closure (Dv.canonGood X q L)) (x₀ : ℝ) :
    Dv.canonVal X x₀ q L t = ζ t + ((e - x₀ : ℝ) : ℂ) := by
  classical
  have hval : ∀ t' ∈ Dv.canonGood X q L,
      (Mo.hullChart (fillH X) x₀).1 (q t') = ζ t' + ((e - x₀ : ℝ) : ℂ) := fun t' ht' => by
    have h := (Dv.canon_eq_of_lift_good hA hζH hζl hgt hgi hgfr ht'.2).1
    rw [Mo.hullChart_fwd] at h ⊢
    rw [← h]; push_cast; ring
  unfold Dv.canonVal
  split_ifs with hg
  · exact hval t hg
  · have hne : (𝓝[Dv.canonGood X q L] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 ht
    have hlim : Tendsto (fun t' => (Mo.hullChart (fillH X) x₀).1 (q t')) (𝓝[Dv.canonGood X q L] t)
        (𝓝 (ζ t + ((e - x₀ : ℝ) : ℂ))) :=
      (((hζc.tendsto t).add_const _).mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun t' ht' => (hval t' ht').symm)
    exact hlim.limUnder_eq

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The relative run chart's boundary map stays within bounded distance of the identity** (pieces launched before
`n` regular). -/
theorem relChart_bound_of_lt {θ : ℝ} {D : ℕ → Drv} {n : ℕ}
    (hreg : ∀ k < n, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2)) :
    ∃ C : ℝ, ∀ p ∈ Hbar,
      ‖extendFrom H (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 p - p‖ ≤ C := by
  obtain ⟨-, hfib⟩ := runChart_facts_of_lt (boundaryWalkSpec b jumps θ true) (D := D) (n := n) hreg
  obtain ⟨f, C, hf, hC, -⟩ := hfib
  refine ⟨C, fun p hp => ?_⟩
  have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
  have he : extendFrom H (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 p = f p :=
    (hf p hp).limUnder_eq
  rw [he]; exact hC p hp

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **One lockstep stage with an infinite piece, from F2a** (curve level). -/
theorem stage_inf_of_canon {s₂ : ExplState} {e₂ : Drv} {X : Set ℂ} {q : ℝ≥0 → ℂ} {x₀ x₁ : ℝ}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : Supp9B.IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH' : ∀ w ∈ H, c.2.1 w ∈ H) (hoff : BdryOff c)
    (hPc : ContinuousOn q {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤})
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤}, q t ∈ β₀ '' Ici tL)
    (hgood : goodTp c q ⊤ = Dv.canonGood X q ⊤) (hF : IsDrivenCurve (Dv.canonCurve X x₀ q ⊤))
    (hΦ : ∀ z ∈ H \ fillH X, (stChart s₂).1 (c.1 z + (m : ℂ)) = (Mo.hullChart (fillH X) x₁).1 z)
    (hΦd : (Mo.physRelChart c (stChart s₂) m).2.1 '' H = H \ fillH X)
    {w₀ : ℂ} (hw₀ : ∀ s, β₀ (tL + s) = q 0 → γ s = w₀)
    (hcw₀ : ContinuousWithinAt (stChart s₂).1 H w₀) (hz₀ : (stChart s₂).1 w₀ = 0)
    {ζ : ℝ≥0 → ℂ} (hζH : ∀ t, ζ t ∈ Hbar) (hζtr : Tendsto (fun t => ‖ζ t‖) atTop atTop)
    (hcv : ∀ t, Dv.canonVal X x₀ q ⊤ t = ζ t) (htop : capLife (Dv.canonCurve X x₀ q ⊤) = ⊤)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} ⊆ closure (goodTp c q ⊤))
    (he₂ : e₂.2 = capLife (stCurvep c m q ⊤ s₂)) (hreg : IsRegularDriver e₂)
    (hB₂ : HasBdryLimits (stChart s₂).2.1) {C : ℝ}
    (hC₂ : ∀ p ∈ Hbar, ‖extendFrom H (stChart s₂).2.1 p - p‖ ≤ C)
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H) :
    IsDrivenCurve (stCurvep c m q ⊤ s₂) ∧ StageRelInfP c m q ⊤ s₂ e₂ ∧
      Tendsto (fun u => ‖stCurvep c m q ⊤ s₂ u‖) atTop atTop ∧ capLife (stCurvep c m q ⊤ s₂) = ⊤ := by
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ hPc htl
  have h0mem : ((0 : ℝ≥0) : ℝ≥0∞) ≤ ⊤ := le_top
  have hGsub : goodTp c q ⊤ ∩ {t | (t : ℝ≥0∞) < ⊤} ⊆ goodTp c q ⊤ := inter_subset_left
  have h0 : Tendsto (relValp c m q s₂) (𝓝[goodTp c q ⊤ ∩ {t | (t : ℝ≥0∞) < ⊤}] 0) (𝓝 0) := by
    have h := tendsto_relValp_of_tail hγ hcH hc1 hoff hσc hσ hGsub h0mem (hw₀ (σ 0) (hσ 0 h0mem)) hcw₀
    rwa [hz₀] at h
  have hne := neBot_good_zero (L := ⊤) ENNReal.top_ne_zero hgd
  obtain ⟨hdr, heq⟩ := isDrivenCurve_stCurvep_of_canon hΦ hgood hF h0 hne
  have hrep : ∀ u : ℝ, stCurvep c m q ⊤ s₂ u = ζ u.toNNReal := fun u => by
    rw [heq]
    unfold Dv.canonCurve
    simp only [↓reduceIte]
    exact hcv _
  have htr : Tendsto (fun u => ‖stCurvep c m q ⊤ s₂ u‖) atTop atTop := by
    simp only [hrep]
    exact hζtr.comp tendsto_real_toNNReal_atTop
  have htop' : capLife (stCurvep c m q ⊤ s₂) = ⊤ := by rw [heq]; exact htop
  have hHbar : ∀ u, 0 ≤ u → stCurvep c m q ⊤ s₂ u ∈ Hbar := fun u _ => by rw [hrep]; exact hζH _
  have hoffX : ∀ t ∈ goodTp c q ⊤, q t ∉ fillH X := fun t ht => by
    rw [hgood] at ht; exact ht.2.2
  have hdom := stage_dom_of_phys hΦd hc1 hcH' hc₂ hoffX
  exact ⟨hdr, stageRelInfP_of hdr he₂ hreg htop' htr hHbar hB₂ hC₂ hcH₂ hc1₂ hdom, htr, htop'⟩

end InteractingSLE.Theorem14.SB.Lk
