/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveChart
import InteractingSLE.Spec.Sec5.Aux22ChartE

/-!
# Lemma GW1's active-word classification: a right threshold (deterministic)

Packet PROVE-T14-GW1W. Lemma GW1, proof (`source/spec/p577-624.md` L949–L951, p. 618–619): for a lower-extreme piece
with an admissible left word, "a lower-extreme continuation threshold can occur only on its right side". Along one
path:

* `stopWord_le_of_collision`: if the right marks read from the record sit at the limit gaps `v^R₀ − w₀` and the right
  colliding group has weight sum `≤ −2`, the stop word is low just right of `0`;
* **`lowStart_of_goodStopPath`**: on a good stop path with an admissible left word, the threshold at a finite positive
  lifetime is on the right, so the stop word is low just right of `0`;
* **`rightLim_le_of_lowStart`**: then the original outward height at the new right record is low (the first condition
  of (GW1.3));
* **`launch_ne_thr_false`**: a launch in a state with a right profile does not end at a new left record when a
  positive real point of its chart is hit at a finite positive lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

section Collision

variable {κ : ℝ}

/-- **The stop word is low just right of the seed** when the right colliding group has weight sum `≤ −2`. -/
theorem stopWord_le_of_collision (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {w₀ : ℝ}
    {vR₀ : Fin (flowLineNR c.fn c.jumps 0) → ℝ}
    (hpos : ∀ j, markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) = vR₀ j - w₀) (hge : ∀ j, w₀ ≤ vR₀ j)
    (hsum : ∑ j ∈ univ.filter (fun j => vR₀ j = w₀), flowLineRhoR κ c.fn c.jumps 0 θ j ≤ -2) :
    ∃ ε > 0, ∀ z ∈ Ioo (0 : ℝ) ε, (stopWord κ (c, θ, r)).fn z + θ * chiC κ ≤ -sleLambda κ := by
  classical
  set G : Finset ℝ := insert 1 ((univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) => vR₀ j ≠ w₀)).image
    (fun j => vR₀ j - w₀)) with hG
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  have hGpos : ∀ x ∈ G, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact one_pos
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact sub_pos.2 (lt_of_le_of_ne (hge j) (Ne.symm (Finset.mem_filter.1 hj).2))
  refine ⟨G.min' hGne, hGpos _ (G.min'_mem hGne), fun z hz => ?_⟩
  have hord := isMarkOrder_stopWord c r
  have hpR : ∀ j : Fin (flowLineNR c.fn c.jumps 0),
      markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) = vR₀ j - w₀ := fun j => by
    rw [padFL_fst_snd_fin]; exact hpos j
  have hfar : ∀ j : Fin (flowLineNR c.fn c.jumps 0), vR₀ j ≠ w₀ → G.min' hGne ≤ vR₀ j - w₀ := fun j hj =>
    G.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)))
  -- `z` is not a jump of the stop word
  have hzJ : z ∉ (stopWord κ (c, θ, r)).jumps := by
    intro hzJ'
    obtain ⟨k, hk, hkz⟩ := BoundaryWord.mem_jumps.1 hzJ'
    have hk' : k < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0 := hk
    change cumMax (rawPos (flowLineNL c.fn c.jumps 0)
      (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))) k = z at hkz
    rw [cumMax_rawPos hord hk'] at hkz
    unfold rawPos at hkz
    split_ifs at hkz with h1 h2
    · have := hord.2.1 (flowLineNL c.fn c.jumps 0 - 1 - k) (by omega)
      linarith [hz.1]
    · linarith [hz.1]
    · have e := hpR ⟨k - flowLineNL c.fn c.jumps 0 - 1, by omega⟩
      change markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 (k - flowLineNL c.fn c.jumps 0 - 1)) = z at hkz
      change markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 (k - flowLineNL c.fn c.jumps 0 - 1)) = _ at e
      by_cases hj : vR₀ ⟨k - flowLineNL c.fn c.jumps 0 - 1, by omega⟩ = w₀
      · rw [hj, sub_self] at e
        rw [e] at hkz
        linarith [hz.1]
      · have := hfar _ hj
        rw [← e, hkz] at this
        linarith [hz.2]
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hord hzJ hz.1.ne'
  change (forceWord κ _ _ _ _ _ _ _).fn z + _ ≤ _
  rw [h1]
  unfold forceBoundaryData
  simp only [not_lt.2 hz.1.le, ↓reduceIte]
  have hset : univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
      markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) ≤ z) =
      univ.filter (fun j => vR₀ j = w₀) := Finset.filter_congr fun j _ => by
    rw [hpR j]
    constructor
    · intro hle
      by_contra hj
      have := hfar j hj
      linarith [hz.2]
    · intro hj
      rw [hj, sub_self]
      exact hz.1.le
  rw [hset, Finset.sum_congr rfl (fun j _ => padFL_snd_snd_fin κ θ c.fn c.jumps j)]
  have hl := Sec4.sleLambda_pos hκ
  change sleLambda κ * (1 + ∑ j ∈ univ.filter (fun j => vR₀ j = w₀), flowLineRhoR κ c.fn c.jumps 0 θ j) -
    θ * chiC κ + θ * chiC κ ≤ -sleLambda κ
  nlinarith

/-- **A right threshold on a good stop path** (Lemma GW1, (GW1.1)): with an admissible left word, at a finite positive
lifetime the colliding group is on the right, so the stop word is low just right of `0`. -/
theorem lowStart_of_goodStopPath (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) ⊤ e vL vR B)
    (hL : ∀ y, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ < sleLambda κ) :
    ∃ ε > 0, ∀ z ∈ Ioo (0 : ℝ) ε, (stopWord κ (c, θ, recOf ⊤ e)).fn z + θ * chiC κ ≤ -sleLambda κ := by
  have hfin : min ⊤ e.2 ≠ ⊤ := hgp.2.2.2.2.1
  set T : ℝ≥0 := (min ⊤ e.2).toNNReal with hTdef
  have hTe : (T : ℝ≥0∞) = e.2 := by rw [hTdef, ENNReal.coe_toNNReal hfin, min_eq_right le_top]
  have hTpos : 0 < T := hgp.stop_pos hTe
  obtain ⟨w₀, vL₀, vR₀, hlim⟩ := hgp.2.1 T hTpos hTe
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hth⟩ := hgp.1
  have hthr := hth T hTpos hTe w₀ vL₀ vR₀ hlim
  have hfp := hgp.1.isForcePath
  have := Sec2.IsForcePath.neBot_nhdsLT hTpos
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < e.2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hTe]; exact_mod_cast ht
  have hw : Tendsto e.1 (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hvR : ∀ j, Tendsto (fun t => vR j t) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds j
  -- the left colliding group is admissible
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineL hκ c.isPiecewiseConstantBoundaryData hL
  have hanti : StrictAnti (flowLineXL c.fn c.jumps 0) := fun i j hij => GW0.flowLineXL_lt c.fn c.jumps 0 hij
  have hLs : -2 < ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), flowLineRhoL κ c.fn c.jumps 0 θ i := by
    have h' := Sec4.neg_two_lt_sum_collision (v₀ := -vL₀) (w₀ := -w₀) hcc
      (fun i j hij => neg_le_neg (hanti.antitone hij)) hgc
      (fun i j hij => neg_le_neg (le_of_tendsto_of_tendsto (hvL j) (hvL i)
        (hev.mono fun t ht => hfp.antitone_vL ht hij)))
      (fun i => neg_le_neg (le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)))
      (fun i j hij => by
        have e' : i = j := hanti.injective (neg_injective hij)
        rw [e'])
    simpa only [Pi.neg_apply, neg_inj] using h'
  have hR := hthr.resolve_left (not_le.2 hLs)
  -- the right marks read from the record
  obtain ⟨s, -, hs, hsT⟩ := exists_seq_strictMono_tendsto' hTpos
  have hsζ : ∀ n, ((s n : ℝ≥0) : ℝ≥0∞) < e.2 := fun n => by rw [← hTe]; exact_mod_cast (hs n).2
  have hsT' : Tendsto s atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall fun n => (hs n).2⟩
  have hpos : ∀ j, markPos (rdrv (recOf ⊤ e)) (rtime (recOf ⊤ e)) (flowLineXR c.fn c.jumps 0 j) =
      vR₀ j - w₀ := fun j => by
    have h1 := hgp.tendsto_right j hsζ hsT
    have h2 : Tendsto (fun n => vR j (s n) - e.1 (s n)) atTop (𝓝 (vR₀ j - w₀)) :=
      ((hvR j).comp hsT').sub (hw.comp hsT')
    exact tendsto_nhds_unique h1 h2
  have hge : ∀ j, w₀ ≤ vR₀ j := fun j =>
    le_of_tendsto_of_tendsto hw (hvR j) (hev.mono fun t ht => hfp.w_le_vR ht j)
  exact stopWord_le_of_collision hκ c θ (recOf ⊤ e) hpos hge hR

end Collision

/-! ### The original height at a right threshold -/

section Record

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The original outward height at the new right record is low** when the threshold word is low just right of `0`
(the first condition of (GW1.3)). -/
theorem rightLim_le_of_lowStart {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ : ExplState} (hs₁ : RProf s₁)
    (hO : ROrig b jumps γ s₁) {ε : ℝ} (hε : 0 < ε)
    (hlow : ∀ z ∈ Ioo (0 : ℝ) ε, γ.fn z + θ * chiC κ ≤ -sleLambda κ) :
    rightLim b (stRecR s₁) + θ * chiC κ ≤ -sleLambda κ := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs₁
  set q := stRecR s₁ with hq
  set m := rProf (stChart s₁) with hmdef
  obtain ⟨hi, hqhi, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb q
  set x₁ := (q + hi) / 2 with hx₁
  have hx₁q : q < x₁ := by linarith
  have hx₁hi : x₁ < hi := by linarith
  set δ := min ε (m x₁) with hδ
  have hδpos : 0 < δ := lt_min hε (hpos x₁ hx₁q)
  obtain ⟨x₂, hx₂q, hmx₂⟩ := RProf.exists_eq ⟨hc, hm, hpos, hsmall⟩ (half_pos hδpos)
  rw [← hmdef] at hmx₂
  have hx₂x₁ : x₂ < x₁ := by
    by_contra h
    push Not at h
    have := hm.1.monotoneOn hx₁q hx₂q h
    have : δ ≤ m x₁ := min_le_right _ _
    linarith
  have hc₂ : ContinuousAt m x₂ := hm.2.1.continuousAt (Ioi_mem_nhds hx₂q)
  have hP : ∀ᶠ x' in 𝓝 x₂, x' < hi ∧ m x' < ε := by
    have h1 := hc₂.eventually (gt_mem_nhds (show m x₂ < ε by
      rw [hmx₂]; linarith [min_le_left ε (m x₁)]))
    filter_upwards [gt_mem_nhds (hx₂x₁.trans hx₁hi), h1] with x' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨x', hx'q, hx'J, hmx'J, hx'hi, hmx'ε⟩ := exists_near_avoid hm.1 hx₂q jumps γ.jumps hP
  have h1 := hO x' hx'q hx'J hmx'J
  have h2 := hlow (m x') ⟨hpos x' hx'q, hmx'ε⟩
  rw [h1, hconst x' ⟨hx'q, hx'hi⟩] at h2
  exact h2

/-- **A launch does not end at a new left record** when, at a finite positive lifetime, a positive real point of its
chart is hit (the state having a right profile). -/
theorem launch_ne_thr_false {s : ExplState} (hs : RProf s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hhit : D.2 ≠ ⊤ → D.2 ≠ 0 → ∃ y : ℝ, 0 < y ∧
      (∀ r < stopTime ⊤ D, ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) (stopTime ⊤ D) u) :
    stStatus (ExplState.launch s k D θ ⊤) ≠ stThr (some false) := by
  by_cases htop : D.2 = ⊤
  · have hmin : min ⊤ D.2 = ⊤ := by rw [htop]; rfl
    rw [(launch_eq_of_top s k D θ ⊤ hmin).2.2.2.2.1]
    simp
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top htop)
  rw [hst]
  unfold lStatus
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 le_top))]
  by_cases h0 : D.2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    split <;> simp
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
  obtain ⟨y, hy, hyb, hyd⟩ := hhit htop h0
  obtain ⟨x, hx, hmx⟩ := RProf.exists_eq hs hy
  have hhx : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
    refine ⟨x, hx, (lHit_iff hs.1 ⊤ D x).2 ⟨?_, ?_⟩⟩ <;> rw [hmx]
    · exact hyb
    · exact hyd
  rw [ite_eq_left_of_eq_true _ _ (eq_true hhx)]
  simp

end Record

end GW1W

end Theorem14

end InteractingSLE
