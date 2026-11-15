/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoEntry
import InteractingSLE.Spec.Supplement.GW1Bookkeep
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Restart.ClockTrace
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov
import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Spec.Supplement.GW1ActiveChart
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber
import InteractingSLE.Spec.Supplement.GW1WalkExitStage
import InteractingSLE.Spec.Supplement.GW1WalkExitRestart
import InteractingSLE.Spec.Supplement.SBLuChart
import InteractingSLE.Spec.Supplement.SB2LoAE
import InteractingSLE.Spec.Supplement.GW1ActiveRun
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.SBLuPath
import InteractingSLE.Spec.Supplement.SB2NcBase
import InteractingSLE.Spec.Supplement.SB2NcWalk
import InteractingSLE.Spec.Supplement.SB2NcGeo
import InteractingSLE.Spec.Supplement.GW1WalkExitLaw
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# D34's left heights: the free real points between two seeds of B's walk are admissible

Worker PROVE-SB2-F3LAW (round 3, handoff §R2.7 item 4, input (iii)). Between B's seed `p` at stage `ℓ` and its next
seed `p'` at stage `ℓ + 2`, the real points that are free in the retained hull of stage `ℓ + 2` are the connector's:

* up to the landing point `q` they are not free: B's piece is a simple arc from `p` to `q` (GW1's `PieceSimpleAt`),
  a point off it is adherent to its fill (`YuanCharacterisation.mem_closure_fillH_of_lt_of_lt`), a point on it is a
  limit of its points in `ℍ` (the generating trace visits `ℍ` densely, `IsGeneratingTrace.exists_mem_H`);
* on `(q, p')` the original heights are low: the exit at `ℓ` is classified (GW1's `ClassifiedExit`, a low outward
  height at `q`) and `p'` is the first restart mark (`GW1W.contStep_thr_true`), so `GW1W.add_le_neg_of_connector`.

Low heights are admissible for the lower flow (`b − (π/2)χ ≤ −λ < λ`).

* `not_free_of_pieceSimpleAt`, `connector_low`, `free_between_seeds_low` (deterministic, one run);
* **`ae_free_between_seeds`** (almost surely, from Theorems 1.2/1.3 via NOJUMP's `Nc.ae_walkGood`, `Nc.ae_retGeom`
  and GW1's `GW1W.exists_witness_right`, `GW1WalkExit.ae_classifiedExit_right`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw GW1Bookkeep

/-- **The real points between the two ends of a simple piece are not free in the fill of any set containing it.**
A point off the piece is adherent to its fill (`YuanCharacterisation.mem_closure_fillH_of_lt_of_lt`); a point on it is
a limit of points of the piece in `ℍ` (the generating trace visits `ℍ` at a dense set of times). -/
theorem not_free_of_pieceSimpleAt {c : Chart} (hc : c.IsConformal) {W : ℝ≥0 → ℝ} {T : ℝ≥0} {old : Set ℂ}
    {q₀ q₁ : ℝ} (h : PieceSimpleAt c W (T : ℝ≥0∞) old q₀ q₁) {X : Set ℂ}
    (hX : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal) (T : ℝ≥0∞) ⊆ X)
    {x : ℝ} (hq₀x : q₀ < x) (hxq₁ : x ≤ q₁) {ρ : ℝ} (hρ : 0 < ρ) :
    ¬ Disjoint (ball (x : ℂ) ρ) (fillH X) := by
  obtain ⟨f, α, C, hf, -, hmaps, hW0, hWc, hgen, -, -, hStart, hEnd, -⟩ := h
  have hEnd' : f (α T) = (q₁ : ℂ) := by have := hEnd ENNReal.coe_ne_top; rwa [ENNReal.toNNReal_coe] at this
  have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < (T : ℝ≥0∞)} :=
    hWc.mono fun s (hs : (s : ℝ≥0∞) < (T : ℝ≥0∞)) => show (s : ℝ≥0∞) ≤ (T : ℝ≥0∞) from le_of_lt hs
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen hWlt hW0 ht
  have htip := CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWc hW0 fun t ht => hf _ (hαH t ht)
  -- `f` is the boundary extension of the inverse chart, continuous on `ℍ̄`
  have hfext : ∀ p ∈ Hbar, f p = extendFrom H c.2.1 p := fun p hp =>
    (extendFrom_eq (by rw [closure_H]; exact hp) (hf p hp)).symm
  have hfc : ContinuousOn f Hbar := by
    have := continuousOn_extendFrom (A := H) (B := Hbar) (f := c.2.1) (by rw [closure_H])
      fun p hp => ⟨f p, hf p hp⟩
    exact this.congr fun p hp => hfext p hp
  have hfH : ∀ p ∈ H, f p = c.2.1 p := fun p hp => by
    have hcont : ContinuousAt c.2.1 p :=
      (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hp)).continuousAt
    have : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hp)
    exact tendsto_nhds_unique (hf p (show (0 : ℝ) ≤ p.im from le_of_lt hp)) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  -- the path on `[0, T]`
  set ζ : ℝ → ℂ := fun t => f (α t.toNNReal) with hζ
  have hζc : ContinuousOn ζ (Icc 0 (T : ℝ)) := by
    refine hfc.comp ((hgen.2.1.comp continuous_real_toNNReal.continuousOn) fun t ht => ?_) fun t ht => ?_
    · show ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (T : ℝ≥0∞)
      exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 ht.2)
    · exact hαH _ (by exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 ht.2))
  have hζm : MapsTo ζ (Icc 0 (T : ℝ)) Hbar := fun t ht => hmaps _ (hαH _ (by
    exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 ht.2)))
  have hT0 : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl, T.2⟩
  have hTT : (T : ℝ) ∈ Icc 0 (T : ℝ) := ⟨T.2, le_rfl⟩
  have hζ0 : ζ 0 = (q₀ : ℂ) := by simp only [hζ, Real.toNNReal_zero]; exact hStart
  have hζT : ζ T = (q₁ : ℂ) := by simp only [hζ, Real.toNNReal_coe]; exact hEnd'
  have himg : ζ '' Icc 0 (T : ℝ) ⊆ X := by
    rintro _ ⟨t, ht, rfl⟩
    apply hX
    rw [htip]
    exact ⟨α t.toNNReal, ⟨t.toNNReal, by exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 ht.2), rfl⟩, rfl⟩
  by_cases hx : (x : ℂ) ∈ ζ '' Icc 0 (T : ℝ)
  · -- a point of the piece: a limit of its points in `ℍ`
    obtain ⟨t₀, ht₀, hζt₀⟩ := hx
    have ht₀pos : 0 < t₀ := by
      rcases eq_or_lt_of_le ht₀.1 with h0 | h0
      · exfalso; rw [← h0, hζ0] at hζt₀; exact absurd (Complex.ofReal_injective hζt₀) (ne_of_lt hq₀x)
      · exact h0
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hζc t₀ ht₀) ρ hρ
    set a : ℝ≥0 := (max (t₀ - δ / 2) 0).toNNReal with ha
    have hab : a < t₀.toNNReal := by
      rw [ha, Real.toNNReal_lt_toNNReal_iff ht₀pos]
      exact max_lt (by linarith) ht₀pos
    obtain ⟨s, hs, hsH⟩ := IsGeneratingTrace.exists_mem_H hgen hWlt hW0 hab
      (by exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 ht₀.2))
    have hs1 : t₀ - δ / 2 ≤ (s : ℝ) := by
      have h1 : (a : ℝ) < (s : ℝ) := hs.1
      have h2 : (a : ℝ) = max (t₀ - δ / 2) 0 := Real.coe_toNNReal _ (le_max_right _ _)
      linarith [le_max_left (t₀ - δ / 2) 0]
    have hs2 : (s : ℝ) < t₀ := by
      have h1 : (s : ℝ) < ((t₀.toNNReal : ℝ≥0) : ℝ) := hs.2
      rwa [Real.coe_toNNReal _ ht₀.1] at h1
    have hsI : (s : ℝ) ∈ Icc 0 (T : ℝ) := ⟨s.2, by linarith [ht₀.2]⟩
    have hdist : dist (s : ℝ) t₀ < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hclose := hδc hsI hdist
    rw [hζt₀] at hclose
    have hζs : ζ s = c.2.1 (α s) := by
      simp only [hζ, Real.toNNReal_coe]
      exact hfH _ hsH
    have hζsH : ζ s ∈ H := by rw [hζs]; exact hc.dom_subset (hc.inv_mem_dom hsH)
    have hζsX : ζ s ∈ X := himg ⟨s, hsI, rfl⟩
    intro hdisj
    exact Set.disjoint_left.1 hdisj (by rw [mem_ball]; exact hclose)
      ⟨hζsH, Or.inl (subset_closure hζsX)⟩
  · have hcl := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hζc hζm hT0 hTT
      (by rw [hζ0]; simp) (by rw [hζT]; simp) (by rw [hζ0]; simpa using hq₀x) ?_ hx
    · intro hdisj
      have hmem := Metric.mem_closure_iff.1 hcl ρ hρ
      obtain ⟨z, hz, hzd⟩ := hmem
      exact Set.disjoint_left.1 hdisj (by rw [mem_ball, dist_comm]; exact hzd) (fillH_mono himg hz)
    · rw [hζT]
      simp only [Complex.ofReal_re]
      exact lt_of_le_of_ne hxq₁ fun h => hx ⟨T, hTT, by rw [hζT, h]⟩

open PiecewiseConstantBoundaryData (rightLim jumpSet) in
/-- **The connector is low**: between a state with a low outward height and the first restart mark after it, the
original heights are low (`GW1W.add_le_neg_of_connector` with the restart set). -/
theorem connector_low {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {s : ExplState} (hbad : rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ)
    (hC : (GW1W.restartSet κ b jumps s).Nonempty) {x : ℝ} (hsx : stPt s < x)
    (hxw : x < (GW1W.restartSet κ b jumps s).min' hC) (hxJ : x ∉ jumps) :
    b x + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  refine GW1W.add_le_neg_of_connector hb hbad (fun z hz hqz hzw => ?_) hsx hxw hxJ
  by_contra hgt
  have hz' : z ∈ GW1W.restartSet κ b jumps s := Finset.mem_filter.2 ⟨hz, hqz, lt_of_not_ge hgt⟩
  exact (not_le.2 hzw) ((GW1W.restartSet κ b jumps s).min'_le z hz')

/-- **Free points between two seeds of the boundary walk are connector points, with low original heights** (one
run): at a launching stage `ℓ` whose next flow stage `ℓ + 2` launches, with a classified exit at `ℓ`, GW1's piece facts,
and regular launches, every real point strictly between the two seeds that has a ball missing the fill of a set
containing the walk's prefix through `ℓ + 2` is right of the landing point, hence on the connector. -/
theorem free_between_seeds_low {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hl2 : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none)
    (hCE : GW1WalkExit.ClassifiedExit κ b true (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)))
    (hchain : SB.Lk.WalkChainFacts κ b jumps θ D)
    (hP : SB.LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hpin : ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) : ℝ) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ))
    {X : Set ℂ} (hX : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 2) ⊆ X) {x : ℝ}
    (hpx : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) < x)
    (hxp' : x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 2)))
    (hfree : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH X)) (hxJ : x ∉ jumps) :
    b x + θ * QuantumZipper.chiC κ ≤ -sleLambda κ := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s₀ := ExplState.run κ b jumps w D ℓ with hs₀
  set s₁ := ExplState.run κ b jumps w D (ℓ + 1) with hs₁
  set s₂ := ExplState.run κ b jumps w D (ℓ + 2) with hs₂
  obtain ⟨⟨c, θ'⟩, hlc⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨⟨c₂, θ₂⟩, hlc₂⟩ := Option.ne_none_iff_exists'.1 hl2
  have hnd₂ : stStatus s₂ ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hlc₂
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hl
  obtain ⟨-, hlen2⟩ := GW1W.even_of_launches_walk hl2
  have hcont : s₂ = ExplState.contStep κ b jumps s₁ none true :=
    GW1W.run_succ_walk_cont (by omega) (by omega)
  have hnd₁ : stStatus s₁ ≠ GW1Conn.stDone := fun hd => hnd₂ (by
    rw [hcont, GW1WalkChain.contStep_of_done hd]; exact hd)
  -- the classified exit: an outward threshold with a low outward height
  obtain ⟨hFE, hbad⟩ := hCE
  have hbad' := hbad hnd₁
  rcases hFE with hd | ⟨-, hthr⟩
  · exact absurd hd hnd₁
  have hθ' : θ' = θ := by
    have h1 := (eq_launch_of_launches w D hlc).1
    rw [(SB.Nc.flow_of_launch hl).2] at h1
    have h2 := Option.some_injective _ h1
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h2
    exact h2.1.symm
  have hang : stAngle s₁ = θ := by
    obtain ⟨-, he, -⟩ := eq_launch_of_launches w D hlc
    rw [hs₁, he, GW1W.instrTime_walk hl, hθ']
    exact GW1WalkExit.angle_launch _ _ _ _
  simp only [GW1WalkExit.BadOutwardHeight, ite_true] at hbad'
  -- the continuation reaches the first restart mark
  have hcs : ExplState.contStep κ b jumps s₁ none true =
      if hC : (GW1W.restartSet κ b jumps s₁).Nonempty then
        ExplState.moveAlong s₁ true ((GW1W.restartSet κ b jumps s₁).min' hC) true
      else ExplState.moveToEnd s₁ true := by
    rcases hthr with h | ⟨h, hR⟩
    · exact GW1W.contStep_thr_true b jumps s₁ h true
    · exact GW1W.contStep_thr_none_right b jumps s₁ h (by simpa using hR)
  by_cases hC : (GW1W.restartSet κ b jumps s₁).Nonempty
  swap
  · exfalso
    rw [dite_eq_right_iff.2 (fun h => absurd h hC)] at hcs
    exact hnd₂ (by rw [hcont, hcs]; exact SB.LuM.stStatus_moveToEnd s₁ true)
  rw [dite_eq_left_of_eq_true (eq_true hC)] at hcs
  have hp' : stPt s₂ = (GW1W.restartSet κ b jumps s₁).min' hC := by
    rw [hcont, hcs, GW1W.stPt_moveAlong]
  -- points up to the landing point are not free
  have hq : stPt s₁ < x := by
    by_contra hle
    push Not at hle
    obtain ⟨ρ, hρ, hdisj⟩ := hfree
    obtain ⟨-, he, hcc⟩ := eq_launch_of_launches w D hlc
    have hc : c.IsConformal := by rw [hcc]; exact SB.LuM.isConformal_runChart_of_reg w hP ℓ
    have hinstr : instrTime w ℓ = ⊤ := GW1W.instrTime_walk hl
    have hfin : (D ℓ).2 ≠ ⊤ := fun htop => hnd₁ (by
      rw [hs₁, he, hinstr]
      exact (launch_eq_of_top _ ℓ (D ℓ) θ' ⊤ (by rw [htop, min_self])).2.2.2.2.1)
    set T : ℝ≥0 := (D ℓ).2.toNNReal with hT
    have hST : min (instrTime w ℓ) (D ℓ).2 = (T : ℝ≥0∞) := by
      rw [hinstr, min_eq_right le_top, hT, ENNReal.coe_toNNReal hfin]
    have hPS := hchain.1 ℓ c θ' hlc hpin
    rw [hST] at hPS
    have hsub := GW1Z.tipSet_subset_prefixPhysSet_succ (κ := κ) (b := b) (jumps := jumps) w D hlc
    rw [hST] at hsub
    have hX' := hsub.trans ((GW1Z.prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps) w D (ℓ + 1)).trans
      hX)
    exact not_free_of_pieceSimpleAt hc hPS hX' hpx hle hρ hdisj
  rw [← hang]
  exact connector_low hb hbad' hC hq (by rw [← hp']; exact hxp') hxJ

open MeasureTheory in
open LQGMetric (DistOn) in
/-- **The free points between two seeds of B's walk are admissible** (almost surely): on B's stage event at `ℓ` with
a launch at `ℓ + 2`, every real point strictly between the two seeds with a ball missing the retained hull `A₁'` of
stage `ℓ + 2` (F2b′'s `A₁' 0 = fill (A ∪ B_{<ℓ+2})`) and off the jumps has left weight `> −2` for the lower flow. -/
theorem ae_free_between_seeds.{u} (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {A₁' : Ω → Set ℂ} (hA' : ∀ᵐ ω ∂P, A₁' ω = Mf.fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ω) :
    ∀ᵐ ω ∂P, ω ∈ Ms.stageEvent κ b jumps E u l k ℓ →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none →
      ∀ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) < x →
        x < stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (ℓ + 2)) →
        (∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (A₁' ω)) → x ∉ jumps →
        b x + -(Real.pi / 2) * QuantumZipper.chiC κ < sleLambda κ := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hwbc : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set Er := StagedReg.regFam E w with hEr
  have hamb := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ'
  have hCE : ∀ᵐ ω ∂P, ∀ n, (ExplState.run κ b jumps w (fun j => Er j ω) (n + 1)).2.2.2.1 n ≠ none →
      GW1WalkExit.ClassifiedExit κ b true (ExplState.run κ b jumps w (fun j => Er j ω) n)
        (ExplState.run κ b jumps w (fun j => Er j ω) (n + 1)) := by
    refine ae_all_iff.2 fun n => ?_
    obtain ⟨β, Y, hW, hI⟩ := GW1W.exists_witness_right hκ hb hh (hE' w hwbc) (hreg' w) hamb.1 n
    exact GW1WalkExit.ae_classifiedExit_right hκ hb hh (hE' w hwbc) (hreg' w) hW
      (hI.mono fun ω hω hl => ⟨(hω hl).1, (hω hl).2.1⟩)
  by_cases hℓ₂ : ℓ + 2 < w.2.2.length
  swap
  · refine Eventually.of_forall fun ω _ hω => absurd (SB.Nc.flow_of_launch hω).1 hℓ₂
  filter_upwards [SB.Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft,
    SB.Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k (ℓ + 2) hℓ₂, hA', hCE, hrun w hwbc]
    with ω hg hgeo hAω hCω hrω hev hl2 x hpx hxp' hfree hxJ
  have hgω := hg hev.1
  obtain ⟨-, -, -, -, hfill⟩ := hgeo hl2
  have hA'eq : A₁' ω = fillH (SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω) := hAω.trans hfill
  have hl := hev.2
  have hnd : stStatus (ExplState.run κ b jumps w (fun i => E w i ω) ℓ) ≠ GW1Conn.stDone := by
    obtain ⟨⟨c, θ'⟩, hlc⟩ := Option.ne_none_iff_exists'.1 hl
    exact WalkIntRunChron.not_done_of_launch w _ hlc
  have hCℓ : GW1WalkExit.ClassifiedExit κ b true (ExplState.run κ b jumps w (fun i => E w i ω) ℓ)
      (ExplState.run κ b jumps w (fun i => E w i ω) (ℓ + 1)) := by
    have h1 := hCω ℓ (by rw [hrω]; exact hl)
    rwa [hrω, hrω] at h1
  have hX : SB.prefixPhysSet κ b jumps w (fun i => E w i ω) (ℓ + 2) ⊆
      SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω := subset_union_right
  have hfree' : ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) (fillH (SB.Nc.retX κ b jumps E u l k (ℓ + 2) ω)) := by
    rw [← hA'eq]; exact hfree
  have hlow := free_between_seeds_low hb hl hl2 hCℓ hgω.chain hgω.reg (hgω.pinv ℓ hnd).2 hX hpx hxp' hfree' hxJ
  have hl0 := Sec4.sleLambda_pos hκ
  linarith

end InteractingSLE.Theorem14.SB.Fo
