/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CgData

/-!
# SB2(2)'s zero clause over the corrected bundle

Packet PROVE-SB2-CONDFIN (round 2). **`sb2LowerZeroClauseWStatement`**: `Cf.SB2LowerZeroClauseWStatement` PROVED
(Theorems 1.2–1.3) — almost surely under the retained kernel, every relative stage `j ≥ 1` that launches has positive
lifetime, for every family with `ClauseTW` (the bundle's run inputs and start disjunction suffice; `StageFactsAS` is not
used). Per sample (`relPos_of_runInputsW`), at a launched relative stage `j` (even, so `j ≥ 2`):

* the matched actual stage `j + o` launches (`actual_launch_of_lifts_arcW` / `_pieceW`, which need no positivity at
  `j ≥ 2`; at an infinite start piece the relative walk is done after its root);
* it is before the actual walk's end `N + o` (`RunInputs''.done`), so it has `FlowSt R` (`Mn.flowSt_of_start`),
  launches from an arc mark with an admissible seed (`Mn.arcM_of_flowSt_launch`), and the run inputs' `piece` field
  gives the lift relation of the actual piece and relative stage `j`;
* the actual piece has positive lifetime (the start's `nz₁`) and dense good times, so its lift is not of lifetime `0`
  (`Mn.pos_of_liftRel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Cg

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn LuM GW1W GW1Bookkeep
open Sec7.PocketTraversal Sec7.Lemma71C

section Sample

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}

/-- **The matched actual launch at a relative stage `j ≥ 2`** (no positivity needed). -/
theorem actual_launch_ge_two (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputsW κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    ∀ j, 2 ≤ j → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + o + 1)).2.2.2.1 (j + o) ≠ none := by
  intro j hj hl
  rcases hS with hA | hPV
  · exact actual_launch_of_lifts_arcW hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hreg₂ hA.zero₀ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁ hA.nz₁ hR.piece hR.two_le hR.len hR.len₁ hR.len₂
      hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head hW₁ hβp hγp hD hβ0
      hR.trLift j hj hl
  · have hlen' : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
        i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hPV.len.1; omega, hPV.len.2⟩
      · exact hR.len i h2 hiN
    by_cases htop : (D₁ o).2 = ⊤
    · exfalso
      have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
      have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
        rw [run_one_walk]
        exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
      obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl' (done_of_le hdone1 (by omega))
    have hP := hPV.toPieceStart htop
    exact actual_launch_of_lifts_pieceW hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero
      hP.hitR hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hreg₂ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁
      hP.nz₁ hR.piece hR.two_le hlen' hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head
      hC.tail hC.ray hP.head hW₁ hβp hγp hD hβ0 hR.trLift j hj hl

/-- **The zero clause at one sample**: every relative stage `j ≥ 1` that launches has positive lifetime. -/
theorem relPos_of_runInputsW (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputsW κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    {c : Chart} {A : Set ℂ}
    (hgd : ∀ i, 2 ≤ i →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + o)).2} ⊆
        closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o)) (D₁ (i + o))))
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A) :
    ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ), 1 ≤ j →
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j = some (c₁, θ') →
      (D₂ j).2 ≠ 0 := by
  intro j c₁ θ' hj1 hl₂'
  have hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none := by
    rw [hl₂']; exact Option.some_ne_none _
  have hev : j % 2 = 0 := (GW1W.even_of_launches_walk hl₂).1
  have hj : 2 ≤ j := by omega
  have hl₁ := actual_launch_ge_two hι hC hR hreg₂ hP₁ hW₁ hlm₁ hlh₁ hallow hexit₁ hβp hγp hβ0 hD hS j hj hl₂
  have ho : o % 2 = 0 := by rcases hS with hA | hPV; exacts [hA.even, hPV.even]
  have hnz : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0 := by
    rcases hS with hA | hPV
    · exact hA.nz₁
    · exact fun k hk => hPV.nz₁ k (by omega)
  -- the start piece is finite (otherwise the relative walk stops after its root)
  have hS' : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤) := by
    rcases hS with hA | hPV
    · exact Or.inl hA
    · refine Or.inr ⟨hPV, fun htop => ?_⟩
      have h2top : (D₂ 0).2 = ⊤ := hPV.top.2 htop
      have hdone1 : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) = stDone := by
        rw [run_one_walk]
        exact (launch_eq_of_top _ 0 (D₂ 0) θ ⊤ (by rw [h2top, min_self])).2.2.2.2.1
      exact WalkIntRunChron.not_done_of_launch _ D₂ hl₂' (done_of_le hdone1 (by omega))
  -- the stage is before the actual walk's end
  have hjN : j < N := by
    by_contra hge
    push Not at hge
    obtain ⟨⟨c', θ''⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
    exact WalkIntRunChron.not_done_of_launch _ D₁ hl₁' (done_of_le hR.done (by omega))
  have hF := flowSt_of_start hP₁ hlm₁ hlh₁ hR.fin₁ hR.len₁ hR.two_le ho hnz hS' (j + o) (by omega) (by omega)
    (by omega)
  obtain ⟨harc, hadm⟩ := arcM_of_flowSt_launch (hR.len j hj hjN).1 (by omega) hF hl₁
  have hLift := hR.piece j hj hjN (by simp [hev]) harc hadm
  exact pos_of_liftRel hP₁ hW₁ hl₁ (hnz (j + o) (by omega) hl₁) (hgd j hj hl₁) hβr hK hDom hγp.2.1 hLift

end Sample

/-- **SB2(2)'s zero clause over the corrected bundle, PROVED** (`Cf.SB2LowerZeroClauseWStatement`; Theorems 1.2–1.3).
-/
theorem sb2LowerZeroClauseWStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : Cf.SB2LowerZeroClauseWStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    Lk.sb2LowerArcsIci h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft, hβex]
    with ω₀ hH₀ hA₀ hX₀ hI₀ hC₀ hZ₀ hU₀ hK₀ hD₀ hβ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm EL _ hELr hae _
  obtain ⟨-, -, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hZ₀ c θ hlaunch b' J' h' hb' hT' hG',
    hK₀ c θ hlaunch b' J' h' hb' hT' hG', hD₀ c θ hlaunch b' J' h' hb' hT' hG', hβ₀]
    with ω hω hHω hAω hXω hIω hCω hZω hKω hDω hβω
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hCω β₀ hβ hβ0 hβr
  obtain ⟨ι, hι, hlim, hray, hS'⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have htail := Mn.tailArc_of_bundle hβ hβr hγ.1 hhead hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hS'
  have hC : CurveInputsW κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  intro j c₁ θ' hj hl₂'
  rcases hS' with ⟨N, hR, hS'⟩ | ⟨hP, htop⟩
  · have hDc : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    exact relPos_of_runInputsW hι hC hR (fun j => hELr j ω) hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1)
      (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hDc hS' (hDω β₀ hβ hβ0 hβr tL hγ.1) hβr
      (hKω β₀ hβ hβ0 hβr tL hγ.1) hDom j c₁ θ' hj hl₂'
  · exfalso
    have h2top := hP.top.2 htop
    have hdone1 : stStatus (ExplState.run κ (affData 1 m b') (affJumps 1 m J')
        (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) (fun i => EL i ω) 1) = stDone := by
      rw [run_one_walk]
      exact (launch_eq_of_top _ 0 (EL 0 ω) (-(Real.pi / 2)) ⊤ (by rw [h2top, min_self])).2.2.2.2.1
    exact WalkIntRunChron.not_done_of_launch _ (fun i => EL i ω) hl₂' (done_of_le hdone1 (by omega))

end InteractingSLE.Theorem14.SB.Cg
