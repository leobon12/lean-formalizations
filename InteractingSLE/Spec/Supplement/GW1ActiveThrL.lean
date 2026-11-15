/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveChartL

/-!
# Lemma GW1's active-word classification: a left threshold (deterministic)

Packet PROVE-T14-GW1W. The mirror of `GW1ActiveThr` for the left walk ("Reflection gives the left boundary walk",
Lemma GW1, p. 618), plus the fact that the frozen `ExplState.launch` needs for the left walk: **no positive point of
the chart is swallowed** at a finite threshold of a piece with an admissible right word (GW6's argument for the first
piece, `GW1Conn.ae_status_run_one_ne_left`, here for an arbitrary path):

* `stopWord_ge_of_collision`, **`highStart_of_goodStopPath`**: at a left threshold the stop word is high just left
  of `0`;
* **`leftLim_ge_of_highStart`**: then the original outward height at the new left record is high;
* **`no_hit_right_of_tendsto`**: with an admissible right word the colliding group at a finite positive lifetime is on
  the left, the two seeds have separated, the right seed gap stays open, and every positive point alive before the
  lifetime is alive at it.
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

section CollisionL

variable {κ : ℝ}

/-- **The stop word is high just left of the seed** when the left colliding group has weight sum `≤ −2`. -/
theorem stopWord_ge_of_collision (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {w₀ : ℝ}
    {vL₀ : Fin (flowLineNL c.fn c.jumps 0) → ℝ}
    (hpos : ∀ i, markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) = vL₀ i - w₀) (hle : ∀ i, vL₀ i ≤ w₀)
    (hsum : ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), flowLineRhoL κ c.fn c.jumps 0 θ i ≤ -2) :
    ∃ ε > 0, ∀ z ∈ Ioo (-ε) (0 : ℝ), sleLambda κ ≤ (stopWord κ (c, θ, r)).fn z + θ * chiC κ := by
  classical
  set G : Finset ℝ := insert 1 ((univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) => vL₀ i ≠ w₀)).image
    (fun i => w₀ - vL₀ i)) with hG
  have hGne : G.Nonempty := Finset.insert_nonempty _ _
  have hGpos : ∀ x ∈ G, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact one_pos
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      exact sub_pos.2 (lt_of_le_of_ne (hle i) (Finset.mem_filter.1 hi).2)
  refine ⟨G.min' hGne, hGpos _ (G.min'_mem hGne), fun z hz => ?_⟩
  have hord := isMarkOrder_stopWord c r
  have hpL : ∀ i : Fin (flowLineNL c.fn c.jumps 0),
      markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) = vL₀ i - w₀ := fun i => by
    rw [padFL_fst_fst_fin]; exact hpos i
  have hfar : ∀ i : Fin (flowLineNL c.fn c.jumps 0), vL₀ i ≠ w₀ → G.min' hGne ≤ w₀ - vL₀ i := fun i hi =>
    G.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)))
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
    · have e := hpL ⟨flowLineNL c.fn c.jumps 0 - 1 - k, by omega⟩
      change markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 (flowLineNL c.fn c.jumps 0 - 1 - k)) = z
        at hkz
      change markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 (flowLineNL c.fn c.jumps 0 - 1 - k)) = _
        at e
      by_cases hi : vL₀ ⟨flowLineNL c.fn c.jumps 0 - 1 - k, by omega⟩ = w₀
      · rw [hi, sub_self] at e
        rw [e] at hkz
        linarith [hz.2]
      · have := hfar _ hi
        rw [← hkz] at hz
        rw [e] at hz
        linarith [hz.1]
    · linarith [hz.2]
    · have := hord.2.2.2 (k - flowLineNL c.fn c.jumps 0 - 1) (by omega)
      linarith [hz.2]
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hord hzJ hz.2.ne
  change _ ≤ (forceWord κ _ _ _ _ _ _ _).fn z + _
  rw [h1]
  unfold forceBoundaryData
  simp only [hz.2, ↓reduceIte]
  have hset : univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
      z < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) =
      univ.filter (fun i => vL₀ i = w₀) := Finset.filter_congr fun i _ => by
    rw [hpL i]
    constructor
    · intro hlt
      by_contra hi
      have := hfar i hi
      linarith [hz.1]
    · intro hi
      rw [hi, sub_self]
      exact hz.2
  rw [hset, Finset.sum_congr rfl (fun i _ => padFL_snd_fst_fin κ θ c.fn c.jumps i)]
  have hl := Sec4.sleLambda_pos hκ
  change sleLambda κ ≤ -sleLambda κ * (1 + ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), flowLineRhoL κ c.fn c.jumps 0 θ i) -
    θ * chiC κ + θ * chiC κ
  nlinarith

/-- **A left threshold on a good stop path** (the mirror of `lowStart_of_goodStopPath`): with an admissible right
word, at a finite positive lifetime the colliding group is on the left, so the stop word is high just left of `0`. -/
theorem highStart_of_goodStopPath (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) ⊤ e vL vR B)
    (hR : ∀ y, 0 < y → y ∉ c.jumps → -sleLambda κ < c.fn y + θ * chiC κ) :
    ∃ ε > 0, ∀ z ∈ Ioo (-ε) (0 : ℝ), sleLambda κ ≤ (stopWord κ (c, θ, recOf ⊤ e)).fn z + θ * chiC κ := by
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
  -- the right colliding group is admissible
  obtain ⟨cc, hcc, hgc⟩ := GW1Conn.exists_hasGroupEndSums_flowLineR hκ c.isPiecewiseConstantBoundaryData hR
  have hmono : StrictMono (flowLineXR c.fn c.jumps 0) := fun i j hij => GW0.flowLineXR_lt c.fn c.jumps 0 hij
  have hRs : -2 < ∑ j ∈ univ.filter (fun j => vR₀ j = w₀), flowLineRhoR κ c.fn c.jumps 0 θ j :=
    Sec4.neg_two_lt_sum_collision hcc hmono.monotone hgc
      (fun i j hij => le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij))
      (fun i => le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i))
      (fun i j hij => by rw [hmono.injective hij])
  have hL := hthr.resolve_right (not_le.2 hRs)
  obtain ⟨s, -, hs, hsT⟩ := exists_seq_strictMono_tendsto' hTpos
  have hsζ : ∀ n, ((s n : ℝ≥0) : ℝ≥0∞) < e.2 := fun n => by rw [← hTe]; exact_mod_cast (hs n).2
  have hsT' : Tendsto s atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall fun n => (hs n).2⟩
  have hpos : ∀ i, markPosL (rdrv (recOf ⊤ e)) (rtime (recOf ⊤ e)) (flowLineXL c.fn c.jumps 0 i) =
      vL₀ i - w₀ := fun i => by
    have h1 := hgp.tendsto_left i hsζ hsT
    have h2 : Tendsto (fun n => vL i (s n) - e.1 (s n)) atTop (𝓝 (vL₀ i - w₀)) :=
      ((hvL i).comp hsT').sub (hw.comp hsT')
    exact tendsto_nhds_unique h1 h2
  have hle : ∀ i, vL₀ i ≤ w₀ := fun i =>
    le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
  exact stopWord_ge_of_collision hκ c θ (recOf ⊤ e) hpos hle hL

end CollisionL

/-! ### The original height at a left threshold; no right hit -/

section RecordL

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The original outward height at the new left record is high** when the threshold word is high just left of `0`
(the mirror of `rightLim_le_of_lowStart`). -/
theorem leftLim_ge_of_highStart {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ : ExplState} (hs₁ : LProf s₁)
    (hO : LOrig b jumps γ s₁) {ε : ℝ} (hε : 0 < ε)
    (hhigh : ∀ z ∈ Ioo (-ε) (0 : ℝ), sleLambda κ ≤ γ.fn z + θ * chiC κ) :
    sleLambda κ ≤ leftLim b (stRecL s₁) + θ * chiC κ := by
  set q := stRecL s₁ with hq
  set m := lProf (stChart s₁) with hmdef
  obtain ⟨lo, hloq, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb q
  set u₁ := (-q + -lo) / 2 with hu₁
  have hu₁q : -q < u₁ := by linarith
  have hu₁lo : u₁ < -lo := by linarith
  set δ := min ε (m u₁) with hδ
  have hδpos : 0 < δ := lt_min hε (hs₁.2.2.1 u₁ hu₁q)
  obtain ⟨u₂, hu₂q, hmu₂⟩ := LProf.exists_eq hs₁ (half_pos hδpos)
  rw [← hmdef] at hmu₂
  have hu₂u₁ : u₂ < u₁ := by
    by_contra h
    push Not at h
    have := hs₁.2.1.1.monotoneOn hu₁q hu₂q h
    have : δ ≤ m u₁ := min_le_right _ _
    linarith
  set x₂ := -u₂ with hx₂
  have hx₂q : x₂ < q := by linarith
  have hx₂lo : lo < x₂ := by linarith
  have hmx₂ : rProf (stChart s₁) x₂ = -(δ / 2) := by
    have : m u₂ = -rProf (stChart s₁) (-u₂) := lProf_eq _ _
    rw [hx₂]; linarith
  have hc₂ : ContinuousAt (rProf (stChart s₁)) x₂ := by
    have hcl : ContinuousAt (lProf (stChart s₁)) (-x₂) :=
      hs₁.2.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
    have : rProf (stChart s₁) = fun y => -lProf (stChart s₁) (-y) := by
      funext y; rw [lProf_eq, neg_neg, neg_neg]
    rw [this]
    exact (hcl.comp (by simpa using continuous_neg.continuousAt (x := x₂))).neg
  have hP : ∀ᶠ x' in 𝓝 x₂, lo < x' ∧ -ε < rProf (stChart s₁) x' := by
    have h1 := hc₂.eventually (lt_mem_nhds (show -ε < rProf (stChart s₁) x₂ by
      rw [hmx₂]; linarith [min_le_left ε (m u₁)]))
    filter_upwards [lt_mem_nhds hx₂lo, h1] with x' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨x', hx'q, hx'J, hmx'J, hx'lo, hmx'ε⟩ := exists_near_avoid_left hs₁.strictMonoOn hx₂q jumps γ.jumps hP
  have h1 := hO x' hx'q hx'J hmx'J
  have h2 := hhigh (rProf (stChart s₁) x') ⟨hmx'ε, hs₁.neg hx'q⟩
  rw [h1, hconst x' ⟨hx'lo, hx'q⟩] at h2
  exact h2

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **No positive point is swallowed at a finite threshold when the right word is admissible** (Lemma GW1 reflected;
GW6's argument for the first piece, for an arbitrary path): the left seed collides, the seeds have separated, and the
right seed gap stays open. -/
theorem no_hit_right_of_tendsto (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {c : ℝ} (hc : -2 < c)
    (hxR : StrictMono xR) (hR : Sec4.HasGroupEndSums c ρR xR) {iL : Fin nL} {iR : Fin nR} (hxL0 : xL iL = 0)
    (hxR0 : xR iR = 0) (hiL : ∀ i, iL ≤ i) {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ} (hUc : Continuous U)
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {y : ℝ} (hy : 0 < y)
    (halive : ∀ r : ℝ, r < T → ∃ u, IsForwardSol U (y : ℂ) r u) : ∃ u, IsForwardSol U (y : ℂ) T u := by
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hζ]; exact_mod_cast ht
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds i
  have hRs : -2 < ∑ i ∈ univ.filter (fun i => vR₀ i = w₀), ρR i :=
    Sec4.neg_two_lt_sum_collision hc hxR.monotone hR
      (fun i j hij => le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => h.monotone_vR ht hij))
      (fun i => le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => h.w_le_vR ht i))
      (fun i j hij => by rw [hxR.injective hij])
  have hLs := hthr.resolve_right (not_le.2 hRs)
  obtain ⟨i, hi⟩ : ∃ i, vL₀ i = w₀ := by
    by_contra hn
    push Not at hn
    have he : univ.filter (fun i => vL₀ i = w₀) = ∅ := Finset.filter_eq_empty_iff.2 fun i _ => hn i
    rw [he, Finset.sum_empty] at hLs
    linarith
  have hvL0 : vL₀ iL = w₀ := by
    refine le_antisymm (le_of_tendsto_of_tendsto (hvL iL) hw (hev.mono fun t ht => h.vL_le_w ht iL)) ?_
    rw [← hi]
    exact le_of_tendsto_of_tendsto (hvL i) (hvL iL) (hev.mono fun t ht => h.antitone_vL ht (hiL i))
  have hsep := GW1Conn.lt_of_tendsto_marks h (iL := iL) (iR := iR) (by rw [hxL0, hxR0]) hT hζ (hvL iL) (hvR iR)
  exact GW1Conn.exists_isForwardSol_of_tendsto_gap h hxR0 hT hζ (g := vR₀ iR - w₀) (by linarith)
    ((hvR iR).sub hw) hUc hU hy halive

end RecordL

end GW1W

end Theorem14

end InteractingSLE
