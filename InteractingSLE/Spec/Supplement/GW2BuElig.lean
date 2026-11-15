/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsLife
import InteractingSLE.Spec.Supplement.GW2BuStmt

/-!
# The exit before the stage life, from the flowed base word and the contact clause (one sample)

Packet PROVE-GW2-BUF (round 18; eligibility at one sample). The base word is GEOM2's flowed root word
`stageWord W₀ θ N (pastOf cf R b N)`, with the stage start `S = b N` and `R` equal to the canonical driver `Wc` on
`[0, S]`. The root word's positive jumps are at most `xR ≥ 0`, its negative ones at least `xL ≤ 0`. The contact
clause is `GapVanishes` of `xR` (or of `−xL` for the reflected driver) at the relative life `L > S`. A death clock
`d < L` carries a stage threshold. Then the cell exit plus the start is below `min (L, d)`.

* `rightImg_rp_congr` (the flowed root bounds read on `Wc`);
* **`cellStop_add_lt_life_cond`**: `cellStop_add_lt_life` with the contact clause needed only when the contact comes
  before the death (the death family's versions exhaust the pre-contact clock only below the death);
* **`exit_add_lt_life_of_flow`**: step A (`stageWord_jump_le`/`_ge`) and `cellStop_add_lt_life_cond`;
* `labelL_zero_eq_junctionR`, `labelR_zero_eq_junctionL` (GEOM2's root-word bounds are the junctions).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist.StagedLaw MartChar.RealFlow Sec5.CrossCond.StagedRepLater GW2TipSystem
  GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach

/-- Two drivers agreeing on `[0, S]` have the same flowed image at `S`. -/
theorem rightImg_rp_congr {R Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) {S : ℝ≥0}
    (hag : ∀ q : ℝ≥0, q ≤ S → R q = Wc q) (x : ℝ) :
    rightImg (rp R) x S = rightImg (rp Wc) x S ∧ rp R S = rp Wc S ∧
      rightImg (fun v => -rp R v) x S = rightImg (fun v => -rp Wc v) x S := by
  have hEq : ∀ v ∈ Icc (0 : ℝ) S, rp R v = rp Wc v := fun v hv =>
    hag v.toNNReal (Real.toNNReal_le_iff_le_coe.2 hv.2)
  refine ⟨Supp8.GB6.rightImg_congr (continuous_rp hWc) S.coe_nonneg hEq, hEq _ ⟨S.coe_nonneg, le_rfl⟩, ?_⟩
  exact Supp8.GB6.rightImg_congr (w' := fun v => -rp Wc v) (continuous_rp hWc).neg S.coe_nonneg
    fun v hv => by simp only [hEq v hv]

section Cell

variable {κ : ℝ} (f : NearCrossingFamily.{u} κ) (cell : RecData → NearCell) (posL posR : RecData → ℕ → ℝ)
  {y : RecData}

/-- **The exit before the stage life, the contact clause only when the contact comes first** (successor of
`cellStop_add_lt_life`: with the death family the versions exhaust the pre-contact clock only below the death). -/
theorem cellStop_add_lt_life_cond (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {base : BoundaryWord} {θ : ℝ} {scale c : ℝ≥0} (hc : 0 < c)
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) (m : ℕ)
    (hP : GW2Sdf.PresentsO κ (GW2Rd.upW (θ * chiC κ) base) scale flip f.xL (f.ρLs m) f.xR (f.ρRs m))
    (hmL : f.mL ≤ f.nL - 1) (hmR : f.mR ≤ f.nR - 1) {cap : ℝ≥0} (hcap : 0 < cap)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (S : ℝ≥0)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) (GW2Rd.stgDrv Wc S)) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {xR xL : ℝ} (hjR : ∀ z ∈ base.jumps, 0 < z → z ≤ rightImg (rp Wc) xR S - rp Wc S)
    (hjL : ∀ z ∈ base.jumps, z < 0 → -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ z) {L : ℝ}
    (hSL : (S : ℝ) < L) {d : ℝ≥0∞}
    (hcon : ENNReal.ofReal L ≤ d →
      (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧ rightImg (rp Wc) xR t - rp Wc t < δ) ∨
      ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, (S : ℝ) < t ∧ t < L ∧
        rightImg (fun v => -rp Wc v) (-xL) t - -rp Wc t < δ)
    (hdeath : d < ENNReal.ofReal L → ∃ u : ℝ≥0, (S : ℝ≥0∞) + u = d ∧
      StageThreshold κ (GW2Rd.upW (θ * chiC κ) base) (GW2Rd.stgDrv Wc S) u) :
    cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc S) + S <
      min (ENNReal.ofReal L) d := by
  set E := cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc S) with hEdef
  have hjR' : ∀ z ∈ (GW2Rd.upW (θ * chiC κ) base).jumps, 0 < z → z ≤ rightImg (rp Wc) xR S - rp Wc S := hjR
  have hjL' : ∀ z ∈ (GW2Rd.upW (θ * chiC κ) base).jumps, z < 0 →
      -rightImg (fun v => -rp Wc v) (-xL) S - rp Wc S ≤ z := hjL
  rcases lt_or_ge d (ENNReal.ofReal L) with hdL | hdL
  · obtain ⟨u, hu, hthr⟩ := hdeath hdL
    have hlt : E < u := cellStop_lt_of_stage_threshold f cell posL posR hsh hL hR hc hsc flip m hP hcap
      (GW2Rd.continuous_stgDrv hWc S) h0 u hthr
    rw [min_eq_right hdL.le, ← hu, add_comm (S : ℝ≥0∞)]
    exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hlt
  · have hcont : E < ENNReal.ofReal (L - S) :=
      cellStop_lt_of_contact f cell posL posR hsh hL hR hc hsc flip m hP hmL hmR hcap hWc S h0 hjR' hjL' (hcon hdL)
    have hL' : ENNReal.ofReal L = ENNReal.ofReal (L - S) + (S : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by linarith) S.coe_nonneg]
      congr 1
      ring
    rw [min_eq_left hdL, hL']
    exact ENNReal.add_lt_add_right ENNReal.coe_ne_top hcont

/-- **The exit before the stage life, from the flowed base word and the contact clause.** -/
theorem exit_add_lt_life_of_flow (hsh : famShapeB f = (cell y).1) (hL : ∀ i : Fin f.nL, f.xL i = posL y i)
    (hR : ∀ j : Fin f.nR, f.xR j = posR y j) {θ : ℝ} {scale c : ℝ≥0} (hc : 0 < c)
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) (m : ℕ)
    (W₀ : RecData → BoundaryWord) (θs : ℕ → ℝ) (cf : RecData) {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0)
    {b : ℕ → ℝ≥0} (hb : Monotone b) (hb0 : b 0 = 0) (N : ℕ)
    (hP : GW2Sdf.PresentsO κ (GW2Rd.upW (θ * chiC κ)
      (GW2JDetR5.stageWord (κ := κ) W₀ θs N (GW2Wm.pastOf cf R b N))) scale flip f.xL (f.ρLs m) f.xR (f.ρRs m))
    (hmL : f.mL ≤ f.nL - 1) (hmR : f.mR ≤ f.nR - 1) {cap : ℝ≥0} (hcap : 0 < cap)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hag : ∀ q : ℝ≥0, q ≤ b N → R q = Wc q)
    (h0 : GW2Sdg.imgState f.xL f.xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) (GW2Rd.stgDrv Wc (b N))) 0 ∈
      cellBuf (famShapeB f, (cell y).2.1, (cell y).2.2))
    {xR xL : ℝ} (hxR : 0 ≤ xR) (hxL : xL ≤ 0) (hjR₀ : ∀ z ∈ (W₀ cf).jumps, 0 < z → z ≤ xR)
    (hjL₀ : ∀ z ∈ (W₀ cf).jumps, z < 0 → xL ≤ z) {L : ℝ} (hSL : ((b N : ℝ≥0) : ℝ) < L)
    {d : ℝ≥0∞} (hcon : ENNReal.ofReal L ≤ d → GapVanishes (rp Wc) xR L ∨ GapVanishes (fun q => -rp Wc q) (-xL) L)
    (hdeath : d < ENNReal.ofReal L → ∃ u : ℝ≥0, ((b N : ℝ≥0) : ℝ≥0∞) + u = d ∧
      StageThreshold κ (GW2Rd.upW (θ * chiC κ) (GW2JDetR5.stageWord (κ := κ) W₀ θs N (GW2Wm.pastOf cf R b N)))
        (GW2Rd.stgDrv Wc (b N)) u) :
    cellStop cell posL posR (c ^ 2) (GW2Sdy.nearSign flip * c) cap (y, GW2Rd.stgDrv Wc (b N)) + (b N : ℝ≥0∞) <
      min (ENNReal.ofReal L) d := by
  set base := GW2JDetR5.stageWord (κ := κ) W₀ θs N (GW2Wm.pastOf cf R b N) with hbase
  obtain ⟨hR1, hR2, -⟩ := rightImg_rp_congr hWc hag xR
  obtain ⟨-, -, hL3⟩ := rightImg_rp_congr hWc hag (-xL)
  have hjR : ∀ z ∈ base.jumps, 0 < z → z ≤ rightImg (rp Wc) xR (b N) - rp Wc (b N) := fun z hz hz0 => by
    have := stageWord_jump_le W₀ θs cf hRc hR0 hb hb0 hxR hjR₀ N z hz hz0
    rwa [hR1, hR2] at this
  have hjL : ∀ z ∈ base.jumps, z < 0 → -rightImg (fun v => -rp Wc v) (-xL) (b N) - rp Wc (b N) ≤ z :=
    fun z hz hz0 => by
      have := stageWord_jump_ge W₀ θs cf hRc hR0 hb hb0 hxL hjL₀ N z hz hz0
      rwa [hL3, hR2] at this
  have hcon' : ENNReal.ofReal L ≤ d → (∀ δ : ℝ, 0 < δ → ∃ t : ℝ, ((b N : ℝ≥0) : ℝ) < t ∧ t < L ∧
        rightImg (rp Wc) xR t - rp Wc t < δ) ∨
      ∀ δ : ℝ, 0 < δ → ∃ t : ℝ, ((b N : ℝ≥0) : ℝ) < t ∧ t < L ∧
        rightImg (fun v => -rp Wc v) (-xL) t - -rp Wc t < δ := fun hLd => by
    rcases hcon hLd with h | h
    · exact Or.inl fun δ hδ => h δ hδ _ hSL
    · exact Or.inr fun δ hδ => h δ hδ _ hSL
  exact cellStop_add_lt_life_cond f cell posL posR hsh hL hR hc hsc flip m hP hmL hmR hcap hWc (b N) h0 hjR hjL hSL
    hcon' hdeath

end Cell

/-- **GEOM2's left-mark bound of the root word is the right junction.** -/
theorem labelL_zero_eq_junctionR {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    GW2Wm.labelL U s 0 = Supp8.GB6.junctionR U s := by
  unfold GW2Wm.labelL Supp8.GB6.junctionR Supp8.GB6.baseL
  rw [Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hU hU0 hs le_rfl, neg_zero]

/-- **GEOM2's right-mark bound of the root word is the left junction.** -/
theorem labelR_zero_eq_junctionL {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    GW2Wm.labelR U s 0 = Supp8.GB6.junctionL U s := by
  unfold GW2Wm.labelR Supp8.GB6.junctionL Supp8.GB6.baseR
  rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hU hU0 hs le_rfl]

end InteractingSLE.Theorem14.GW2Bh
