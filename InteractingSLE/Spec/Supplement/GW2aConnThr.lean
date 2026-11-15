/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aConnMove
import InteractingSLE.Spec.Supplement.GW1ActiveThrL

/-!
# GW2a's connectors: thresholds of an ordinary piece of an arbitrary program

Packet PROVE-GW2A-CONN. Lemma GW2a (supplement p. 623): "A finite threshold cannot be an old incoming point. Its
physical endpoint is therefore an untouched original-real record on the indicated outward side." For a piece of an
arbitrary program the left word need not be admissible (the walks of Lemma GW1 have this, and
`GW1W.lowStart_of_goodStopPath` uses it); instead:

* `sums_of_right_hit` (deterministic, any force path): if at a finite positive lifetime a positive real point is
  swallowed, the colliding right group is inadmissible (`≤ −2`) and the left seed did not collide. If the left group
  were inadmissible it would contain the left seed, the seeds have separated (`GW1Conn.lt_of_tendsto_marks`), so the
  right seed gap stays open and every positive point survives (`GW1Conn.exists_isForwardSol_of_tendsto_gap`); the
  right group is then nonempty, so it contains the right seed, and the seeds' separation keeps the left seed open;
* `sums_of_left_hit`: the mirror, by reflection of the path;
* `stopWord_facts_right` / `stopWord_facts_left`: on a good stop path stopped at its lifetime with such a hit, the stop
  word is low just right of `0` (the threshold's low start) and equals the left side height `−λ − θχ` just left of `0`
  (the mirror: high just left of `0`, `λ − θχ` just right of `0`) — the seed of a later launch at the threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-! ### The colliding groups at a hit -/

section Path

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **At a right hit the right group is inadmissible and the left seed is open.** -/
theorem sums_of_right_hit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {iL : Fin nL} {iR : Fin nR}
    (hxL0 : xL iL = 0) (hxR0 : xR iR = 0) (hiL : ∀ i, iL ≤ i) (hiR : ∀ i, iR ≤ i) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ} (hUc : Continuous U)
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {y : ℝ} (hy : 0 < y)
    (halive : ∀ r : ℝ, r < T → ∃ u, IsForwardSol U (y : ℂ) r u) (hdead : ¬ ∃ u, IsForwardSol U (y : ℂ) T u) :
    (∑ i ∈ univ.filter (fun i => vR₀ i = w₀), ρR i ≤ -2) ∧ vL₀ iL < w₀ := by
  have := Sec2.IsForcePath.neBot_nhdsLT hT
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hζ]; exact_mod_cast ht
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds i
  have hsep := GW1Conn.lt_of_tendsto_marks h (iL := iL) (iR := iR) (by rw [hxL0, hxR0]) hT hζ (hvL iL) (hvR iR)
  have hLs : -2 < ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), ρL i := by
    by_contra hle
    push Not at hle
    obtain ⟨i, hi⟩ : ∃ i, vL₀ i = w₀ := by
      by_contra hn
      push Not at hn
      have he : univ.filter (fun i => vL₀ i = w₀) = ∅ := Finset.filter_eq_empty_iff.2 fun i _ => hn i
      rw [he, Finset.sum_empty] at hle
      linarith
    have hvL0 : vL₀ iL = w₀ := by
      refine le_antisymm (le_of_tendsto_of_tendsto (hvL iL) hw (hev.mono fun t ht => h.vL_le_w ht iL)) ?_
      rw [← hi]
      exact le_of_tendsto_of_tendsto (hvL i) (hvL iL) (hev.mono fun t ht => h.antitone_vL ht (hiL i))
    exact hdead (GW1Conn.exists_isForwardSol_of_tendsto_gap h hxR0 hT hζ (g := vR₀ iR - w₀) (by linarith)
      ((hvR iR).sub hw) hUc hU hy halive)
  have hRs := hthr.resolve_left (not_le.2 hLs)
  refine ⟨hRs, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, vR₀ j = w₀ := by
    by_contra hn
    push Not at hn
    have he : univ.filter (fun j => vR₀ j = w₀) = ∅ := Finset.filter_eq_empty_iff.2 fun j _ => hn j
    rw [he, Finset.sum_empty] at hRs
    linarith
  have hvR0 : vR₀ iR = w₀ := by
    refine le_antisymm ?_ (le_of_tendsto_of_tendsto hw (hvR iR) (hev.mono fun t ht => h.w_le_vR ht iR))
    rw [← hj]
    exact le_of_tendsto_of_tendsto (hvR iR) (hvR j) (hev.mono fun t ht => h.monotone_vR ht (hiR j))
  linarith

/-- **At a left hit the left group is inadmissible and the right seed is open** (the mirror of
`sums_of_right_hit`, by reflection). -/
theorem sums_of_left_hit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {iL : Fin nL} {iR : Fin nR}
    (hxL0 : xL iL = 0) (hxR0 : xR iR = 0) (hiL : ∀ i, iL ≤ i) (hiR : ∀ i, iR ≤ i) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) {U : ℝ → ℝ} (hUc : Continuous U)
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {y : ℝ} (hy : y < 0)
    (halive : ∀ r : ℝ, r < T → ∃ u, IsForwardSol U (y : ℂ) r u) (hdead : ¬ ∃ u, IsForwardSol U (y : ℂ) T u) :
    (∑ i ∈ univ.filter (fun i => vL₀ i = w₀), ρL i ≤ -2) ∧ w₀ < vR₀ iR := by
  have hlim' : Tendsto (fun t => ((-w) t, fun i => -vR i t, fun i => -vL i t)) (𝓝[<] T)
      (𝓝 (-w₀, fun i => -vR₀ i, fun i => -vL₀ i)) := by
    have hcont : Continuous fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) =>
        (-p.1, fun i => -p.2.2 i, fun i => -p.2.1 i) := by fun_prop
    exact (hcont.tendsto _).comp hlim
  have hthr' : ForceWord.ThresholdCondition ρR ρL (-w₀) (fun i => -vR₀ i) (fun i => -vL₀ i) :=
    Sec2.thresholdCondition_neg_iff.2 hthr
  have hal : ∀ r : ℝ, r < T → ∃ u, IsForwardSol (-U) (((-y : ℝ)) : ℂ) r u := fun r hr => by
    rw [alive_neg_iff, neg_neg]
    exact halive r hr
  have hde : ¬ ∃ u, IsForwardSol (-U) (((-y : ℝ)) : ℂ) T u := by
    rw [alive_neg_iff, neg_neg]
    exact hdead
  obtain ⟨h1, h2⟩ := sums_of_right_hit h.reflect (iL := iR) (iR := iL) (by simp [hxR0]) (by simp [hxL0]) hiR hiL hT
    hζ hlim' hthr' hUc.neg (fun r hr hrT => by simp [hU r hr hrT]) (by linarith : (0 : ℝ) < -y) hal hde
  refine ⟨?_, by linarith⟩
  simpa only [neg_inj] using h1

end Path

/-! ### The stop word at a threshold -/

section Word

variable {κ : ℝ}

/-- **The stop word equals the left side height just left of `0`** when every left mark ends strictly left of the
driver (the left seed did not collide). -/
theorem stopWord_eq_left_of_open (c : BoundaryWord) (θ : ℝ) (r : RecData) {w₀ : ℝ}
    {vL₀ : Fin (flowLineNL c.fn c.jumps 0) → ℝ}
    (hpos : ∀ i, markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) = vL₀ i - w₀) {ε : ℝ}
    (hε : ∀ i, vL₀ i - w₀ ≤ -ε) :
    ∀ z ∈ Ioo (-ε) (0 : ℝ), z ∉ (stopWord κ (c, θ, r)).jumps →
      (stopWord κ (c, θ, r)).fn z = -sleLambda κ - θ * chiC κ := by
  intro z hz hzJ
  have hord := isMarkOrder_stopWord c r
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hord hzJ hz.2.ne
  change (forceWord κ _ _ _ _ _ _ _).fn z = _
  rw [h1]
  unfold forceBoundaryData
  simp only [hz.2, ↓reduceIte]
  have hset : univ.filter (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
      z < markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
    rw [padFL_fst_fst_fin, hpos i]
    linarith [hε i, hz.1]
  rw [hset, Finset.sum_empty, add_zero, mul_one]
  rfl

/-- **The stop word equals the right side height just right of `0`** when every right mark ends strictly right of the
driver (the mirror of `stopWord_eq_left_of_open`). -/
theorem stopWord_eq_right_of_open (c : BoundaryWord) (θ : ℝ) (r : RecData) {w₀ : ℝ}
    {vR₀ : Fin (flowLineNR c.fn c.jumps 0) → ℝ}
    (hpos : ∀ j, markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) = vR₀ j - w₀) {ε : ℝ}
    (hε : ∀ j, ε ≤ vR₀ j - w₀) :
    ∀ z ∈ Ioo (0 : ℝ) ε, z ∉ (stopWord κ (c, θ, r)).jumps →
      (stopWord κ (c, θ, r)).fn z = sleLambda κ - θ * chiC κ := by
  intro z hz hzJ
  have hord := isMarkOrder_stopWord c r
  have h1 := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hord hzJ
    hz.1.ne'
  change (forceWord κ _ _ _ _ _ _ _).fn z = _
  rw [h1]
  unfold forceBoundaryData
  simp only [not_lt.2 hz.1.le, ↓reduceIte]
  have hset : univ.filter (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
      markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) ≤ z) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun j _ => ?_
    rw [padFL_fst_snd_fin, hpos j]
    linarith [hε j, hz.2]
  rw [hset, Finset.sum_empty, add_zero, mul_one]
  rfl

theorem flowLineXL_zero (b : ℝ → ℝ) (J : Finset ℝ) :
    flowLineXL b J 0 ⟨0, Nat.succ_pos _⟩ = 0 := rfl

theorem flowLineXR_zero (b : ℝ → ℝ) (J : Finset ℝ) :
    flowLineXR b J 0 ⟨0, Nat.succ_pos _⟩ = 0 := rfl

/-- The common setting of a good stop path stopped at its lifetime: the stop is the lifetime, it is positive, the
path has a limit state satisfying the threshold condition, the record driver is the driver before the stop, and the
marks read from the record are the limits of the gaps. -/
theorem goodStopPath_data {c : BoundaryWord} {θ : ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) t e vL vR B) (hle : e.2 ≤ t) :
    ∃ T : ℝ≥0, (T : ℝ≥0∞) = e.2 ∧ 0 < T ∧ rtime (recOf t e) = T ∧
      (∀ r : ℝ, 0 ≤ r → r < T → rdrv (recOf t e) r = e.1 r.toNNReal) ∧
      ∃ (w₀ : ℝ) (vL₀ : Fin (flowLineNL c.fn c.jumps 0) → ℝ) (vR₀ : Fin (flowLineNR c.fn c.jumps 0) → ℝ),
        Tendsto (fun s => (e.1 s, fun i => vL i s, fun i => vR i s)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) w₀ vL₀ vR₀ ∧
        (∀ j, markPos (rdrv (recOf t e)) (rtime (recOf t e)) (flowLineXR c.fn c.jumps 0 j) = vR₀ j - w₀) ∧
        (∀ i, markPosL (rdrv (recOf t e)) (rtime (recOf t e)) (flowLineXL c.fn c.jumps 0 i) = vL₀ i - w₀) ∧
        (∀ j, w₀ ≤ vR₀ j) ∧ (∀ i, vL₀ i ≤ w₀) := by
  have hfin : min t e.2 ≠ ⊤ := hgp.2.2.2.2.1
  set T : ℝ≥0 := (min t e.2).toNNReal with hTdef
  have hmin : min t e.2 = e.2 := min_eq_right hle
  have hTe : (T : ℝ≥0∞) = e.2 := by rw [hTdef, ENNReal.coe_toNNReal hfin, hmin]
  have hTpos : 0 < T := hgp.stop_pos hTe
  have hrt : rtime (recOf t e) = T := by rw [rtime_recOf_coe]
  obtain ⟨w₀, vL₀, vR₀, hlim⟩ := hgp.2.1 T hTpos hTe
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hth⟩ := hgp.1
  have hthr := hth T hTpos hTe w₀ vL₀ vR₀ hlim
  have hfp := hgp.1.isForcePath
  have := Sec2.IsForcePath.neBot_nhdsLT hTpos
  have hev : ∀ᶠ t' : ℝ≥0 in 𝓝[<] T, (t' : ℝ≥0∞) < e.2 := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [← hTe]; exact_mod_cast ht'
  have hw : Tendsto e.1 (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL : ∀ i, Tendsto (fun t' => vL i t') (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hvR : ∀ j, Tendsto (fun t' => vR j t') (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds j
  obtain ⟨s, -, hs, hsT⟩ := exists_seq_strictMono_tendsto' hTpos
  have hsζ : ∀ n, ((s n : ℝ≥0) : ℝ≥0∞) < e.2 := fun n => by rw [← hTe]; exact_mod_cast (hs n).2
  have hsT' : Tendsto s atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall fun n => (hs n).2⟩
  refine ⟨T, hTe, hTpos, hrt, fun r hr hrT => ?_, w₀, vL₀, vR₀, hlim, hthr, fun j => ?_, fun i => ?_,
    fun j => le_of_tendsto_of_tendsto hw (hvR j) (hev.mono fun t' ht' => hfp.w_le_vR ht' j),
    fun i => le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t' ht' => hfp.vL_le_w ht' i)⟩
  · exact rdrv_recOf_eq hgp.2.2.1 hgp.2.2.2.1 hfin (by rw [hrt]; exact hrT.le)
  · have h1 := hgp.tendsto_right j hsζ hsT
    have h2 : Tendsto (fun n => vR j (s n) - e.1 (s n)) atTop (𝓝 (vR₀ j - w₀)) :=
      ((hvR j).comp hsT').sub (hw.comp hsT')
    exact tendsto_nhds_unique h1 h2
  · have h1 := hgp.tendsto_left i hsζ hsT
    have h2 : Tendsto (fun n => vL i (s n) - e.1 (s n)) atTop (𝓝 (vL₀ i - w₀)) :=
      ((hvL i).comp hsT').sub (hw.comp hsT')
    exact tendsto_nhds_unique h1 h2

/-- **The stop word at a right threshold** (any program): on a good stop path stopped at its lifetime at which a
positive point is swallowed, the stop word is low just right of `0` and equals `−λ − θχ` just left of `0`. -/
theorem stopWord_facts_right (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) t e vL vR B) (hle : e.2 ≤ t)
    {y : ℝ} (hy : 0 < y) (hal : ∀ r < rtime (recOf t e), ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) r u)
    (hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) (rtime (recOf t e)) u) :
    (∃ ε > 0, ∀ z ∈ Ioo (0 : ℝ) ε, (stopWord κ (c, θ, recOf t e)).fn z + θ * chiC κ ≤ -sleLambda κ) ∧
    (∃ ε > 0, ∀ z ∈ Ioo (-ε) (0 : ℝ), z ∉ (stopWord κ (c, θ, recOf t e)).jumps →
      (stopWord κ (c, θ, recOf t e)).fn z = -sleLambda κ - θ * chiC κ) := by
  obtain ⟨T, hTe, hTpos, hrt, hU, w₀, vL₀, vR₀, hlim, hthr, hpR, hpL, hge, hleL⟩ := goodStopPath_data hgp hle
  have hfp := hgp.1.isForcePath
  rw [hrt] at hal hde
  obtain ⟨hR, hsep⟩ := sums_of_right_hit hfp (iL := ⟨0, Nat.succ_pos _⟩) (iR := ⟨0, Nat.succ_pos _⟩)
    (flowLineXL_zero _ _) (flowLineXR_zero _ _) (fun i => Nat.zero_le _) (fun j => Nat.zero_le _) hTpos hTe hlim
    hthr (continuous_rdrv _) hU hy hal hde
  refine ⟨stopWord_le_of_collision hκ c θ (recOf t e) hpR hge hR, w₀ - vL₀ ⟨0, Nat.succ_pos _⟩, by linarith,
    stopWord_eq_left_of_open c θ (recOf t e) hpL fun i => ?_⟩
  have := Sec2.IsForcePath.neBot_nhdsLT hTpos
  have hev : ∀ᶠ t' : ℝ≥0 in 𝓝[<] T, (t' : ℝ≥0∞) < e.2 := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [← hTe]; exact_mod_cast ht'
  have hvL : ∀ i, Tendsto (fun t' => vL i t') (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    tendsto_pi_nhds.1 hlim.snd_nhds.fst_nhds i
  have hmono := le_of_tendsto_of_tendsto (hvL i) (hvL ⟨0, Nat.succ_pos _⟩)
    (hev.mono fun t' ht' => hfp.antitone_vL ht' (Nat.zero_le _ : (⟨0, Nat.succ_pos _⟩ : Fin _) ≤ i))
  linarith

/-- **The stop word at a left threshold** (the mirror of `stopWord_facts_right`): high just left of `0`, equal to
`λ − θχ` just right of `0`. -/
theorem stopWord_facts_left (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) t e vL vR B) (hle : e.2 ≤ t)
    {y : ℝ} (hy : y < 0) (hal : ∀ r < rtime (recOf t e), ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) r u)
    (hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) (rtime (recOf t e)) u) :
    (∃ ε > 0, ∀ z ∈ Ioo (-ε) (0 : ℝ), sleLambda κ ≤ (stopWord κ (c, θ, recOf t e)).fn z + θ * chiC κ) ∧
    (∃ ε > 0, ∀ z ∈ Ioo (0 : ℝ) ε, z ∉ (stopWord κ (c, θ, recOf t e)).jumps →
      (stopWord κ (c, θ, recOf t e)).fn z = sleLambda κ - θ * chiC κ) := by
  obtain ⟨T, hTe, hTpos, hrt, hU, w₀, vL₀, vR₀, hlim, hthr, hpR, hpL, hge, hleL⟩ := goodStopPath_data hgp hle
  have hfp := hgp.1.isForcePath
  rw [hrt] at hal hde
  obtain ⟨hL, hsep⟩ := sums_of_left_hit hfp (iL := ⟨0, Nat.succ_pos _⟩) (iR := ⟨0, Nat.succ_pos _⟩)
    (flowLineXL_zero _ _) (flowLineXR_zero _ _) (fun i => Nat.zero_le _) (fun j => Nat.zero_le _) hTpos hTe hlim
    hthr (continuous_rdrv _) hU hy hal hde
  have := Sec2.IsForcePath.neBot_nhdsLT hTpos
  have hev : ∀ᶠ t' : ℝ≥0 in 𝓝[<] T, (t' : ℝ≥0∞) < e.2 := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    rw [← hTe]; exact_mod_cast ht'
  have hvR : ∀ j, Tendsto (fun t' => vR j t') (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    tendsto_pi_nhds.1 hlim.snd_nhds.snd_nhds j
  refine ⟨?_, vR₀ ⟨0, Nat.succ_pos _⟩ - w₀, by linarith, stopWord_eq_right_of_open c θ (recOf t e) hpR fun j => ?_⟩
  · exact stopWord_ge_of_collision hκ c θ (recOf t e) hpL hleL hL
  · have hmono := le_of_tendsto_of_tendsto (hvR ⟨0, Nat.succ_pos _⟩) (hvR j)
      (hev.mono fun t' ht' => hfp.monotone_vR ht' (Nat.zero_le _ : (⟨0, Nat.succ_pos _⟩ : Fin _) ≤ j))
    linarith

/-- **At a right hit the left seed stays open**, read from the record: `markPosL(0) < 0`. -/
theorem markPosL_neg_of_right_hit {c : BoundaryWord} {θ : ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) t e vL vR B) (hle : e.2 ≤ t)
    {y : ℝ} (hy : 0 < y) (hal : ∀ r < rtime (recOf t e), ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) r u)
    (hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) (rtime (recOf t e)) u) :
    markPosL (rdrv (recOf t e)) (rtime (recOf t e)) 0 < 0 := by
  obtain ⟨T, hTe, hTpos, hrt, hU, w₀, vL₀, vR₀, hlim, hthr, -, hpL, -, -⟩ := goodStopPath_data hgp hle
  have hfp := hgp.1.isForcePath
  rw [hrt] at hal hde
  obtain ⟨-, hsep⟩ := sums_of_right_hit hfp (iL := ⟨0, Nat.succ_pos _⟩) (iR := ⟨0, Nat.succ_pos _⟩)
    (flowLineXL_zero _ _) (flowLineXR_zero _ _) (fun i => Nat.zero_le _) (fun j => Nat.zero_le _) hTpos hTe hlim
    hthr (continuous_rdrv _) hU hy hal hde
  have h := hpL ⟨0, Nat.succ_pos _⟩
  rw [flowLineXL_zero] at h
  linarith

/-- **At a left hit the right seed stays open**: `markPos(0) > 0`. -/
theorem markPos_pos_of_left_hit {c : BoundaryWord} {θ : ℝ} {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {vL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → ℝ}
    {B : ℝ≥0 → ℝ}
    (hgp : IsGoodStopPath κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) t e vL vR B) (hle : e.2 ≤ t)
    {y : ℝ} (hy : y < 0) (hal : ∀ r < rtime (recOf t e), ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) r u)
    (hde : ¬ ∃ u, IsForwardSol (rdrv (recOf t e)) (y : ℂ) (rtime (recOf t e)) u) :
    0 < markPos (rdrv (recOf t e)) (rtime (recOf t e)) 0 := by
  obtain ⟨T, hTe, hTpos, hrt, hU, w₀, vL₀, vR₀, hlim, hthr, hpR, -, -, -⟩ := goodStopPath_data hgp hle
  have hfp := hgp.1.isForcePath
  rw [hrt] at hal hde
  obtain ⟨-, hsep⟩ := sums_of_left_hit hfp (iL := ⟨0, Nat.succ_pos _⟩) (iR := ⟨0, Nat.succ_pos _⟩)
    (flowLineXL_zero _ _) (flowLineXR_zero _ _) (fun i => Nat.zero_le _) (fun j => Nat.zero_le _) hTpos hTe hlim
    hthr (continuous_rdrv _) hU hy hal hde
  have h := hpR ⟨0, Nat.succ_pos _⟩
  rw [flowLineXR_zero] at h
  linarith

end Word

end GW2aConn

end Theorem14

end InteractingSLE
