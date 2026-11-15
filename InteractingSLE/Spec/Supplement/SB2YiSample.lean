/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YhSample
import InteractingSLE.Spec.Supplement.SB2YiGood
import InteractingSLE.Spec.Supplement.SB2YiSeed
import InteractingSLE.Spec.Supplement.SB2YiCap
import InteractingSLE.Spec.Supplement.SB2YiStage0
import InteractingSLE.Spec.Supplement.SB2YiShift

/-!
# `Om.IsStageS2` at a pure piece entry, in the post-head chart, at one sample

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3). **`isStageS2_root`**: at a pure piece entry (B's piece at stage `n`
visits `R = max (A ∩ ℝ)`, not yet explored, first at `τE > 0`), at a B-time `t ∈ (τE, ζ)`, GEOM2's S2 record for

* the post-head chart `(stage chart).loewner (headDrv e τE) (headTime e τE)` (B's stage chart followed by the Loewner
  map of the head `B[0, τE]`; the capped run's chart, `SB2YiCap`);
* the canonical chart `Mo.hullChart (fill X) x₀` of the retained union `X = A ∪ P_n` (`x₀` its right entry at `R`);
* the shifted stopped driver `shiftDrive (headDrv e t) τE` and the time `headTime e t − τE`;
* a relative version with tail start `τE`: clock `a` with `a τE = 0 < a t < ∞`, and the trace identity
  `ηV (a s) = Φ.1 (pc s)` for `τE ≤ s ≤ t` with `pc s` in `Φ`'s domain.

The proof is `Sx.isStageS2_tail`'s with the post-head chart: its seed facts at `R` (`post_seed_facts`, the fresh tip),
the tail read through `f_τE` (`shift_facts`), the root geometry (`root_good_facts`). Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **GEOM2's S2 record at a pure piece entry, in the post-head chart, at one sample.** -/
theorem isStageS2_root {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hRnew : (realMax (pA '' Icc 0 1) : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ
      true) D n))
    (hRtip : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
      (D n) t = (realMax (pA '' Icc 0 1) : ℂ))
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    {t : ℝ≥0} (hτt : (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA ''
      Icc 0 1))) < t) (htζ : (t : ℝ≥0∞) < (D n).2) (htip : LP.traceAt t (D n).1 ∈ H) {x₀ : ℝ}
    (hent : IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
      (realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ((Mo.hullChart
      (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) 0).recenter x₀))
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0) {a : ℝ≥0 → ℝ≥0∞} (hac : Continuous a)
    (ham : Monotone a) (hazero : a (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1))) = 0) (hat : 0 < a t) (hatop : a t ≠ ⊤) {ηV : ℝ → ℂ}
    (hηV : IsLoewnerTrace (fun s : ℝ => W s.toNNReal) ηV)
    (hlink : ∀ s : ℝ≥0, s ≤ t → (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (realMax (pA '' Icc 0 1))) ≤ s → pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s ∈
      ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
      x₀).dom : Set ℂ) →
      ηV (a s).toReal = (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ
        true) D n)) x₀).1 (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s)) :
    Om.IsStageS2 ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner (headDrv (D n)
      (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA '' Icc 0 1))))
      (headTime (D n) (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax (pA
      '' Icc 0 1)))))
      (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) x₀)
        (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) (shiftDrive
        (headDrv (D n) t) (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax
        (pA '' Icc 0 1))))
      (headTime (D n) t - (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (realMax
        (pA '' Icc 0 1)))) (fun s : ℝ => W s.toNNReal) ((a t).toNNReal : ℝ) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  set X := A ∪ Pn with hXdef
  set R := realMax A with hRdef
  set τE := visitTime s (D n) R with hτEdef
  set c := stChart s with hc
  set Φ := Mo.hullChart (fillH X) x₀ with hΦ
  obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hpos : (D n).2 ≠ 0 := ne_bot_of_gt htζ
  have hPR : GW1P.PieceRegular (D n).1 (D n).2 := by
    have h := hP n c' θ' hl'
    rwa [Lx.instrTime_boundaryWalk_of_launch hl', min_eq_right le_top] at h
  have hshlt : (τE : ℝ≥0∞) < (D n).2 := lt_trans (ENNReal.coe_lt_coe.2 hτt) htζ
  -- the root geometry, the stage seed and the stage chart
  obtain ⟨hsh0, hsh, hshmin, hheadK, hY1, hXc, hXh, hRx, hXle, ⟨gX, hgX, hgXf⟩, hden, hstR⟩ :=
    root_good_facts hP hW hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hRnew hRtip hshlt hS3
  obtain ⟨hbeyond, es, gc, Cc, hes, hes0, hgc, hgcc, hCc, -, -, -⟩ := stage_seed_all hP hlm hlh hl
  obtain ⟨-, -, -, -, hcD, hY, -, -, -, -, -⟩ := stageChart_facts w D hP n hnd
  have hPc : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hfreeY : ∀ x : ℝ, stPt s < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH Pn) := fun x hx =>
    Lx.exists_ball_disjoint_fillH_right hPc fun y hy => lt_of_le_of_lt (hbeyond y hy) hx
  have hcont1 : ContinuousOn c.2.1 H := hcD.isConformal.1.continuousOn
  have hgi : EqOn gc c.2.1 H := fun z hz => by
    have hzb : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hz)
    have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H hzb
    exact tendsto_nhds_unique (hgc z hzb)
      (((hcont1 z hz).continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  -- the trace of the piece
  have hgen := isGeneratingTrace_trOf hPR
  have hcont0 : ContinuousOn (D n).1 {r : ℝ≥0 | (r : ℝ≥0∞) < (D n).2} :=
    hPR.2.1.mono fun r (hr : (r : ℝ≥0∞) < (D n).2) => (show (r : ℝ≥0∞) ≤ (D n).2 from hr.le)
  have htrH : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (D n).2 → trOf (D n) r ∈ Hbar := fun r hr =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen hcont0 hPR.1 hr
  have hpcEq : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (D n).2 → pcPt s (D n) r = gc (trOf (D n) r) := fun r hr =>
    LuM.bdVal_eq_of_tendsto (htrH r hr) (hgc _ (htrH r hr))
  have hrealK : ∀ y : ℝ, (y : ℂ) ∈ hullK A → y ≤ R := by
    intro y hy
    rcases hy with h | ⟨y', hy', he⟩
    · exact absurd h.1 (by simp [QuantumZipper.H])
    · rw [← Complex.ofReal_injective he]; exact hy'.2
  -- the post-head chart
  obtain ⟨s₀'', LY'', gcc, Ccc, hccD, hY'', hmo'', hLY'', hl'', hgcc', hCcc⟩ := cap_chart_facts hP hl' hgcc hgi hshlt
  set Pc := statePhysicalSet 0 s ∪ gc '' (trOf (D n) '' Icc 0 τE) with hPcdef
  have hPcK : Pc ⊆ hullK A := by
    rintro z (hz | ⟨_, ⟨r, hr, rfl⟩, rfl⟩)
    · exact hY1 hz
    · have hrζ : (r : ℝ≥0∞) ≤ (D n).2 := (ENNReal.coe_le_coe.2 hr.2).trans hshlt.le
      rw [← hpcEq r hrζ]
      exact hheadK r hr.2
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  have hAH : ∀ z ∈ A, 0 ≤ z.im := by rintro _ ⟨r, hr, rfl⟩; exact hpH r hr
  have hYB'' : fillH Pc ⊆ fillH X := by
    have h := Dv.fillH_union_of_subset_hullK hAc hAH hPcK
    intro z hz
    have : z ∈ fillH (A ∪ Pc) := fillH_mono subset_union_right hz
    rw [h] at this
    exact fillH_mono subset_union_left this
  have hPcc : IsCompact Pc := by
    refine hPc.union ?_
    have hαc : IsCompact (trOf (D n) '' Icc 0 τE) := isCompact_Icc.image_of_continuousOn
      (hgen.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hshlt.le)
    refine hαc.image_of_continuousOn (hgcc.mono ?_)
    rintro _ ⟨r, hr, rfl⟩
    exact htrH r ((ENNReal.coe_le_coe.2 hr.2).trans hshlt.le)
  have hfreeY'' : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH Pc) := fun x hx =>
    Lx.exists_ball_disjoint_fillH_right hPcc fun y hy => lt_of_le_of_lt (hrealK y (hPcK hy)) hx
  set cc := c.loewner (headDrv (D n) τE) (headTime (D n) τE) with hccdef
  have hex : ∀ x : ℝ, ∃ L : ℝ, R < x → Tendsto cc.1 (𝓝[H] (x : ℂ)) (𝓝 (L : ℂ)) := by
    intro x
    by_cases hx : R < x
    · obtain ⟨ρ, hρ, hd⟩ := hfreeY'' x hx
      obtain ⟨L, hL⟩ := exists_tendsto_fwd_of_hull (Ψ := cc) hY'' hmo'' (a := -s₀'')
        (fun z _ => by simp) hρ hd
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose ecc hecc using hex
  have hhT : headTime (D n) τE = (τE : ℝ) := by
    unfold headTime; rw [min_eq_left hshlt.le, ENNReal.toNNReal_coe]
  have hhTt : headTime (D n) t = (t : ℝ) := by
    unfold headTime; rw [min_eq_left htζ.le, ENNReal.toNNReal_coe]
  -- the stopped drivers
  have hτ0 : 0 < τE := hsh0
  obtain ⟨hwτc', hwτ0', -⟩ := stopTrace_facts hPR hτ0 hshlt
  have hwτc : Continuous (headDrv (D n) τE) := hwτc'
  have hwτ0 : headDrv (D n) τE 0 = 0 := hwτ0'
  have ht0 : 0 < t := lt_of_le_of_lt (zero_le) hτt
  obtain ⟨hwtc, hwt0, ηt, hηt, hηteq⟩ := stopTrace_facts hPR ht0 htζ
  have hheadEq : ∀ r ∈ Icc (0 : ℝ) τE, headDrv (D n) τE r = frozenDrive (D n).1 τE r := by
    intro r hr
    unfold headDrv frozenDrive
    rw [min_eq_left hshlt.le, min_eq_left (show r ≤ (τE : ℝ) from hr.2)]
    rw [show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ⊓ (τE : ℝ≥0∞) = (r.toNNReal : ℝ≥0∞) from
      min_eq_left (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2))]
    rfl
  have hfrc : Continuous (frozenDrive (D n).1 τE) := continuous_frozenDrive (hPR.2.1.mono fun r (hr : r ≤ (τE :
    ℝ).toNNReal) =>
    show (r : ℝ≥0∞) ≤ (D n).2 by rw [Real.toNNReal_coe] at hr; exact (ENNReal.coe_le_coe.2 hr).trans hshlt.le)
  have hfr0 : frozenDrive (D n).1 τE 0 = 0 := by simp [frozenDrive, hPR.1]
  have hcomp : ∀ v ∈ H, cc.2.1 v = c.2.1 (fwdMapInv (frozenDrive (D n).1 τE) τE v) := fun v hv => by
    show c.2.1 (fwdMapInv (headDrv (D n) τE) (headTime (D n) τE) v) = _
    rw [hhT, LP.fwdMapInv_eq_of_eqOn_Icc hwτc hfrc hwτ0 hfr0 τE.coe_nonneg hheadEq hv]
  have hRtip' : gc (trOf (D n) τE) = R := by rw [← hpcEq τE hshlt.le]; exact hsh
  have hhead' : ∀ r : ℝ≥0, r < τE → ∀ P : ℝ, gc (trOf (D n) r) = P → P < R := by
    intro r hr P hP
    have hrζ : (r : ℝ≥0∞) ≤ (D n).2 := (ENNReal.coe_le_coe.2 hr.le).trans hshlt.le
    have hK := hheadK r hr.le
    rw [hpcEq r hrζ, hP] at hK
    refine lt_of_le_of_ne (hrealK P hK) fun he => ?_
    have := hshmin r hrζ (by rw [hpcEq r hrζ, hP, he])
    exact absurd hr (not_lt.2 this)
  obtain ⟨hecc0, hgcc0, hgpos'', hgre''⟩ := post_seed_facts hcD hes hfreeY hgc hes0 hgcc hCc hgen hPR.1 hPR.2.1
    hτ0 hshlt hstR hRtip' hhead' hccD hcomp hecc hfreeY'' hgcc' hCcc
  -- the canonical chart's boundary map
  have hΦinv : ∀ y, Φ.2.1 y = (Mo.hullChart (fillH X) 0).2.1 (y + (x₀ : ℂ)) := fun y => by
    simp only [hΦ, Mo.hullChart_inv, Complex.ofReal_zero, add_zero]
  have hgΦ : ∀ p ∈ Hbar, Tendsto Φ.2.1 (𝓝[H] p) (𝓝 (gX (p + (x₀ : ℂ)))) := fun p hp => by
    have hsh' : Tendsto (fun y : ℂ => y + (x₀ : ℂ)) (𝓝[H] p) (𝓝[H] (p + (x₀ : ℂ))) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun y hy => by
          have hy' : 0 < y.im := hy
          show 0 < (y + (x₀ : ℂ)).im
          simpa using hy'⟩
    have hp' : p + (x₀ : ℂ) ∈ Hbar := by
      have hp'' : 0 ≤ p.im := hp
      show 0 ≤ (p + (x₀ : ℂ)).im
      simpa using hp''
    exact ((hgX _ hp').comp hsh').congr fun y => (hΦinv y).symm
  have hgΦf : ∀ z, ((fun p : ℂ => gX (p + (x₀ : ℂ))) ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite := fun z => by
    have := (hgXf z).preimage (f := fun p : ℂ => p + (x₀ : ℂ)) (add_left_injective _).injOn
    refine this.subset ?_
    rintro p ⟨hp, hpim⟩
    refine ⟨hp, ?_⟩
    show 0 ≤ (p + (x₀ : ℂ)).im
    simpa using hpim
  -- the free line and the normalization of the relative chart
  have hfree := free_pullHull hgcc' hgpos'' hXc hXle
  have hentΦ : ∃ eΦ : ℝ → ℝ, (∀ x : ℝ, R < x → Tendsto Φ.1 (𝓝[H] (x : ℂ)) (𝓝 (eΦ x : ℂ))) ∧
      Tendsto eΦ (𝓝[>] R) (𝓝 0) := by
    obtain ⟨-, ⟨eΦ, heΦ, heΦ0⟩, -, -⟩ := hent
    rw [hRx] at heΦ heΦ0
    refine ⟨eΦ, fun x hx => ?_, heΦ0⟩
    have hfun : Φ.1 = ((Mo.hullChart (fillH X) 0).recenter x₀).1 := by
      funext z
      simp only [hΦ, Chart.recenter, Mo.hullChart_fwd, Complex.ofReal_zero, sub_zero]
    rw [hfun]
    exact heΦ x hx
  have hnorm := norm_pullChart hccD.isConformal hgcc' hgpos'' hgre'' hentΦ
  -- the version's trace, reflected, and its clock read from `τE`
  set ηr : ℝ → ℂ := fun r => LP.reflectC (ηV r) with hηrdef
  have hηr : IsLoewnerTrace (fun r => -(fun s : ℝ => W s.toNNReal) r) ηr :=
    Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hηV
  have hWc' : Continuous fun s : ℝ => W s.toNNReal := hWc.comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
  set sB : ℝ := (t : ℝ) - τE with hsBdef
  have hsB : 0 < sB := by rw [hsBdef]; exact sub_pos.2 (by exact_mod_cast hτt)
  set bt : ℝ → ℝ≥0 := fun r => ((τE : ℝ) + r).toNNReal with hbtdef
  have hbt : ∀ r ∈ Icc (0 : ℝ) sB, τE ≤ bt r ∧ bt r ≤ t := fun r hr => by
    refine ⟨(Real.le_toNNReal_iff_coe_le (by linarith [hr.1, τE.coe_nonneg])).2 (by linarith [hr.1]), ?_⟩
    exact (Real.toNNReal_le_iff_le_coe).2 (by linarith [hr.2])
  have hbtz : bt 0 = τE := by simp [hbtdef]
  have hbts : bt sB = t := by simp [hbtdef, hsBdef]
  set τm : ℝ → ℝ := fun r => (a (bt r)).toReal with hτmdef
  have hfinA : ∀ r ∈ Icc (0 : ℝ) sB, a (bt r) ≠ ⊤ := fun r hr => ne_top_of_le_ne_top hatop (ham (hbt r hr).2)
  have hbtc : Continuous bt := continuous_real_toNNReal.comp (continuous_const.add continuous_id)
  have hτc : ContinuousOn τm (Icc 0 sB) :=
    ENNReal.continuousOn_toReal.comp (hac.comp hbtc).continuousOn fun r hr => hfinA r hr
  have hτ0' : τm 0 = 0 := by simp only [hτmdef, hbtz, hazero, ENNReal.toReal_zero]
  have hτs : τm sB = ((a t).toNNReal : ℝ) := by simp only [hτmdef, hbts]; rfl
  have hu : (0 : ℝ) < ((a t).toNNReal : ℝ) := ENNReal.toReal_pos hat.ne' hatop
  have hηrH : ∀ r ∈ Icc (0 : ℝ) sB, 0 ≤ (ηr (τm r)).im := fun r hr => by
    have h := GW2TipSystem.Gm.loewnerTrace_mem_Hbar hηV hWc' hW0' (ENNReal.toReal_nonneg (a := a (bt r)))
    have h' : 0 ≤ (ηV (τm r)).im := h
    simpa [hηrdef, LP.reflectC] using h'
  -- B's tail in the post-head chart
  set ηs : ℝ → ℂ := fun r => LP.reflectC (ηt r) with hηsdef
  have hηs : IsLoewnerTrace (headDrv (D n) t) ηs := by
    have h := Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hηt
    have e : (-fun x : ℝ => -(D n).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) (D n).2)).toNNReal) =
        headDrv (D n) t := by funext x; simp [headDrv]
    rwa [e] at h
  have hηseq : ∀ r ∈ Icc (0 : ℝ) t, ηs r = trOf (D n) r.toNNReal := fun r hr => by
    simp only [hηsdef, hηteq r hr, LP.reflectC_reflectC]
  have hinj := pcPt_injOn_launch hP hW hl
  have hltζ : ∀ r ∈ Icc (0 : ℝ) t, ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2)) htζ
  have htrinj : InjOn (trOf (D n)) {r : ℝ≥0 | (r : ℝ≥0∞) < (D n).2} := fun r₁ h₁ r₂ h₂ he =>
    hinj h₁ h₂ (by unfold pcPt; rw [he])
  have hηsinj : InjOn ηs (Icc 0 t) := by
    intro r₁ h₁ r₂ h₂ he
    rw [hηseq r₁ h₁, hηseq r₂ h₂] at he
    exact (Real.toNNReal_eq_toNNReal_iff h₁.1 h₂.1).1 (htrinj (hltζ r₁ h₁) (hltζ r₂ h₂) he)
  have hτtle : (τE : ℝ) ≤ t := by exact_mod_cast hτt.le
  obtain ⟨hγ, -, hγinj, hγgood⟩ := shift_facts hηs hwtc hwt0 τE.coe_nonneg hτtle hηsinj
  set γ := InteractingSLE.loewnerTip (shiftDrive (headDrv (D n) t) τE) with hγdef
  set η'' : ℝ → ℂ := fun u => LP.reflectC (γ u) with hη''def
  have hη'' : IsLoewnerTrace (fun r => -(shiftDrive (headDrv (D n) t) τE) r) η'' :=
    Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hγ
  have hwBc : Continuous (shiftDrive (headDrv (D n) t) τE) := QuantumZipper.RS.continuous_shiftDrive hwtc _
  have hwB0 : shiftDrive (headDrv (D n) t) τE 0 = 0 := InteractingSLE.shiftDrive_zero _ _
  have hηinj'' : InjOn η'' (Icc 0 sB) := by
    intro u₁ h₁ u₂ h₂ he
    have he' : γ u₁ = γ u₂ := by
      have := congrArg LP.reflectC he
      simpa only [hη''def, LP.reflectC_reflectC] using this
    exact hγinj h₁ h₂ he'
  have hbtη : ∀ r ∈ Icc (0 : ℝ) sB, ηs ((τE : ℝ) + r) = trOf (D n) (bt r) := fun r hr =>
    hηseq _ ⟨by linarith [hr.1, τE.coe_nonneg], by linarith [hr.2]⟩
  have hηH'' : η'' sB ∈ H := by
    have htipH : ηs ((τE : ℝ) + sB) ∈ H := by
      rw [hbtη sB ⟨hsB.le, le_rfl⟩, hbts, ← LP.traceAt_eq_of_isGeneratingTrace hgen hcont0 hPR.1 htζ]
      exact htip
    exact LP.reflectC_mem_H_iff.2 (hγgood sB hsB le_rfl htipH).1
  -- the good times
  set G : Set ℝ := {r | r ∈ Icc (0 : ℝ) sB ∧ pcPt s (D n) (bt r) ∈ H \ fillH X} with hGdef
  have hGs : G ⊆ Icc 0 sB := fun r hr => hr.1
  have hGd0 : Ico (0 : ℝ) sB ⊆ closure G := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have hrt : ((τE + r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) htζ
      have : ((τE + r.toNNReal : ℝ≥0) : ℝ) ≤ t := by
        rw [NNReal.coe_add, Real.coe_toNNReal r hr0]; linarith [hr.2]
      exact_mod_cast this
    have h1 := hden r.toNNReal hrt
    have h2 := map_mem_closure NNReal.continuous_coe h1 (mapsTo_image _ _)
    rw [Real.coe_toNNReal r hr0] at h2
    have h3 := isOpen_Iio.inter_closure ⟨hr.2, h2⟩
    refine closure_mono ?_ h3
    rintro _ ⟨hlt, t', ⟨-, ht'g⟩, rfl⟩
    refine ⟨⟨NNReal.coe_nonneg t', hlt.le⟩, ?_⟩
    have : bt (t' : ℝ) = τE + t' := by simp only [hbtdef, ← NNReal.coe_add, Real.toNNReal_coe]
    rw [this]; exact ht'g
  have hGd : Icc (0 : ℝ) sB ⊆ closure G := by
    have h := closure_minimal hGd0 isClosed_closure
    rwa [closure_Ico (ne_of_lt hsB)] at h
  have hYo : IsOpen (H \ fillH Pn) := hY.2.2.1
  have hPnX : fillH Pn ⊆ fillH X := fillH_mono subset_union_right
  have hgoodtr : ∀ r ∈ G, trOf (D n) (bt r) ∈ H ∧ pcPt s (D n) (bt r) = c.2.1 (trOf (D n) (bt r)) := fun r hr => by
    have hle : ((bt r : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := (ENNReal.coe_le_coe.2 (hbt r hr.1).2).trans htζ.le
    have hgY : LuM.bdVal c (trOf (D n) (bt r)) ∈ H \ fillH Pn := ⟨hr.2.1, fun h => hr.2.2 (hPnX h)⟩
    exact trOf_mem_H_of_good hcD hYo hgc (htrH _ hle) hgY
  have hGpos : ∀ r ∈ G, 0 < r := fun r hr => by
    refine lt_of_le_of_ne hr.1.1 fun h => ?_
    have h' := hr.2.1
    rw [← h, hbtz] at h'
    have : (0 : ℝ) < (pcPt s (D n) τE).im := h'
    rw [show pcPt s (D n) τE = (R : ℂ) from hsh] at this
    simp at this
  have hγG : ∀ r ∈ G, γ r ∈ H ∧ fwdMap (headDrv (D n) t) τE (trOf (D n) (bt r)) = γ r := fun r hr => by
    have h := hγgood r (hGpos r hr) (by rw [← hsBdef]; exact (hGs hr).2)
      (by rw [hbtη r (hGs hr)]; exact (hgoodtr r hr).1)
    rw [hbtη r (hGs hr)] at h
    exact h
  have hnoarc : interior {r ∈ Ioo (0 : ℝ) sB | (η'' r).im = 0} = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun r hr => ?_
    obtain ⟨V, hVsub, hVo, hrV⟩ := mem_interior.1 hr
    have hrI : r ∈ Icc (0 : ℝ) sB := Ioo_subset_Icc_self (hVsub hrV).1
    obtain ⟨g, hgV, hgG⟩ := mem_closure_iff.1 (hGd hrI) V hVo hrV
    have hg := hVsub hgV
    have him : (η'' g).im = 0 := hg.2
    have hH := LP.reflectC_mem_H_iff.2 (hγG g hgG).1
    exact (ne_of_gt hH) him
  -- the clock is strictly increasing
  have hΦD : IsDomainChart (H \ fillH X) Φ := Mo.isDomainChart_hullChart hXh x₀
  have hdom : (Φ.dom : Set ℂ) = H \ fillH X := Mo.coe_dom_hullChart hXh x₀
  have hlinkG : ∀ r ∈ G, ηV (τm r) = Φ.1 (pcPt s (D n) (bt r)) := fun r hr =>
    hlink (bt r) (hbt r hr.1).2 (hbt r hr.1).1 (by rw [hdom]; exact hr.2)
  have hbtζ : ∀ r ∈ Icc (0 : ℝ) sB, ((bt r : ℝ≥0) : ℝ≥0∞) < (D n).2 := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hbt r hr).2) htζ
  have hbtinj : InjOn bt (Icc 0 sB) := fun r₁ h₁ r₂ h₂ he => by
    have := (Real.toNNReal_eq_toNNReal_iff (by linarith [h₁.1, τE.coe_nonneg])
      (by linarith [h₂.1, τE.coe_nonneg])).1 he
    linarith
  have hτm : StrictMonoOn τm (Icc 0 sB) := by
    intro r₁ h₁ r₂ h₂ hlt
    have hmono : ∀ x y, x ∈ Icc (0 : ℝ) sB → y ∈ Icc (0 : ℝ) sB → x ≤ y → τm x ≤ τm y := fun x y _ hy hxy =>
      ENNReal.toReal_mono (hfinA y hy) (ham (Real.toNNReal_le_toNNReal (by linarith)))
    refine lt_of_le_of_ne (hmono r₁ r₂ h₁ h₂ hlt.le) fun heq => ?_
    have hI : ∀ x ∈ Ioo r₁ r₂, x ∈ Icc (0 : ℝ) sB := fun x hx => ⟨h₁.1.trans hx.1.le, hx.2.le.trans h₂.2⟩
    have hconst : ∀ x ∈ Ioo r₁ r₂, τm x = τm r₁ := fun x hx =>
      le_antisymm (heq ▸ hmono x r₂ (hI x hx) h₂ hx.2.le) (hmono r₁ x h₁ (hI x hx) hx.1.le)
    have hm : (r₁ + r₂) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
    obtain ⟨g₁, hg₁, hg₁G⟩ := mem_closure_iff.1 (hGd (hI _ hm)) (Ioo r₁ r₂) isOpen_Ioo hm
    have hm' : (g₁ + r₂) / 2 ∈ Ioo g₁ r₂ := ⟨by linarith [hg₁.2], by linarith [hg₁.2]⟩
    have hsub : Ioo g₁ r₂ ⊆ Ioo r₁ r₂ := Ioo_subset_Ioo_left hg₁.1.le
    obtain ⟨g₂, hg₂, hg₂G⟩ := mem_closure_iff.1 (hGd (hI _ (hsub hm'))) (Ioo g₁ r₂) isOpen_Ioo hm'
    have he : Φ.1 (pcPt s (D n) (bt g₁)) = Φ.1 (pcPt s (D n) (bt g₂)) := by
      rw [← hlinkG g₁ hg₁G, ← hlinkG g₂ hg₂G, hconst g₁ hg₁, hconst g₂ (hsub hg₂)]
    have he' : pcPt s (D n) (bt g₁) = pcPt s (D n) (bt g₂) := by
      rw [← hΦD.inv_fwd hg₁G.2, he, hΦD.inv_fwd hg₂G.2]
    have h' := hinj (hbtζ g₁ (hGs hg₁G)) (hbtζ g₂ (hGs hg₂G)) he'
    have := hbtinj (hGs hg₁G) (hGs hg₂G) h'
    linarith [hg₂.1]
  -- the relative chart and the link at the good times
  obtain ⟨_, _, _, -, -, -, -, -, hcr, -⟩ :=
    stageChartPkg hccD hY'' hXh hYB'' hmo'' hLY'' hl'' hgcc' hCcc hgΦ hgΦf hfree hnorm
  have hcrc : ContinuousOn (Lf.reflChart (Mn.pullChart cc Φ)).2.1 H := hcr.1.isConformal.1.continuousOn
  have heqτt : ∀ r ∈ Icc (0 : ℝ) τE, headDrv (D n) τE r = headDrv (D n) t r := by
    intro r hr
    unfold headDrv
    have h1 : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (τE : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hr.2)
    have h2 : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) := h1.trans (ENNReal.coe_le_coe.2 hτt.le)
    rw [min_eq_left (le_min h1 (h1.trans hshlt.le)), min_eq_left (le_min h2 (h2.trans htζ.le))]
  have hlinkT : ∀ r ∈ G,
      Tendsto (Lf.reflChart (Mn.pullChart cc Φ)).2.1 (𝓝[H] (ηr (τm r))) (𝓝 (η'' r)) := fun r hr => by
    obtain ⟨htrH', hpcE⟩ := hgoodtr r hr
    have hpt : ηr (τm r) = LP.reflectC (Φ.1 (pcPt s (D n) (bt r))) := by
      simp only [hηrdef, hlinkG r hr]
    have hwH : ηr (τm r) ∈ H := by rw [hpt]; exact LP.reflectC_mem_H_iff.2 (hΦD.fwd_mem hr.2)
    have hval : (Lf.reflChart (Mn.pullChart cc Φ)).2.1 (ηr (τm r)) = η'' r := by
      rw [hpt]
      show Supp9B.refl (fwdMap (headDrv (D n) τE) (headTime (D n) τE)
          (c.1 (Φ.2.1 (Supp9B.refl (LP.reflectC (Φ.1 (pcPt s (D n) (bt r)))))))) = LP.reflectC (γ r)
      rw [Lf.refl_eq_reflectC, LP.reflectC_reflectC, hΦD.inv_fwd hr.2, hpcE, hcD.fwd_inv htrH', hhT,
        fwdMap_eq_of_eqOn τE.coe_nonneg heqτt, (hγG r hr).2]
    have h := ((hcrc _ hwH).continuousAt (QuantumZipper.isOpen_H.mem_nhds hwH)).tendsto
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  rw [hhTt]
  exact isStageS2_of_dense hccD hY'' hXh hYB'' hmo'' hLY'' hl'' hgcc' hCcc hgΦ hgΦf hfree hnorm hWc' hW0' hηr
    hsB hu hτc hτm hτ0' hτs hηrH hwBc hwB0 hη'' hηinj'' hnoarc hηH'' hGs hGd hlinkT

end InteractingSLE.Theorem14.SB.Sx
