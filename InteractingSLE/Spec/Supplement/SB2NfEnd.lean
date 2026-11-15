/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeAe
import InteractingSLE.Spec.Supplement.SB2WfSwal
import InteractingSLE.Spec.Supplement.SB2MbFill

/-!
# F2b′'s root: a piece through a real point beyond the record ends beyond it

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). At a pure piece entry, B's piece at the root stage starts at
its record `R_B` and visits `R = max (A ∩ ℝ) > R_B` at time `sh`. Its endpoint at a finite lifetime is a real point `x`
right of `R_B` (`Ne.ae_walk_phys`); the root's relative facts need `x > R`.

**`end_right_of_visit`** (deterministic): in the state chart the piece is `g ∘ α` for a generating trace `α`. A real
point right of the record has a unique preimage on the positive half-line (`Ne.not_two_sides` against the right
profile `rProf`), and the profile is increasing; so `α sh = rProf R` and `α L = rProf x`. If `α L < α sh`, then `α L`
lies under the trace before `sh` (`Lk.mem_closure_fillH_image_iff`) and is swallowed untouched, so it is not the
endpoint (`Wf.gen_end_ne_of_mem_closure_fill`).

**`ae_walk_end_right`**: the almost-sure form along B's regularized family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Exist Exist.Staged Exist.StagedLaw GW1W Ne

section Det

variable {s : ExplState} {g : ℂ → ℂ} {α p : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {L : ℝ≥0}

/-- A trace point read back to a real point right of the record is the right profile of that point. -/
theorem eq_rProf_of_readback (hRP : RProf s) (hcc : (stChart s).IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H)
    (himg : (stChart s).2.1 '' H ⊆ H) {C₁ C₂ : ℝ} (hprop : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    (hg0 : g 0 = stRecR s) (hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x)
    (hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H)
    {z : ℂ} (hz : 0 ≤ z.im) {x : ℝ} (hx : stRecR s < x) (hgz : g z = x) : z = (rProf (stChart s) x : ℂ) := by
  -- `z` is real
  have hzr : z.im = 0 := by
    by_contra hne
    have hzH : z ∈ H := lt_of_le_of_ne hz (Ne.symm hne)
    have h1 : g z ∈ H := by rw [hgi hzH]; exact himg ⟨z, hzH, rfl⟩
    rw [hgz] at h1
    have : (0 : ℝ) < ((x : ℝ) : ℂ).im := h1
    simp at this
  have hze : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzr])
  have hpos := hRP.2.2.1 x hx
  have hg1 : g (rProf (stChart s) x : ℂ) = x := by rw [← hRP.1.eq_ofReal]; exact hrec x hx
  -- `z` is on the positive side
  have hz0 : 0 < z.re := by
    rcases lt_trichotomy z.re 0 with hlt | heq | hgt
    · exfalso
      obtain ⟨r, hr, hfr⟩ := hfree x hx
      exact not_two_sides hcc hgc hgi hprop hg0 (ne_of_gt hx) hr hfr hlt hpos (by rw [← hze]; exact hgz) hg1
    · exfalso
      have : g 0 = x := by rw [← hgz, hze, heq, Complex.ofReal_zero]
      rw [hg0] at this
      exact (ne_of_lt hx) (by exact_mod_cast this)
    · exact hgt
  -- the profile is onto the positive half-line and read back to its point
  obtain ⟨x', hx', hx'e⟩ := hRP.exists_eq hz0
  have hgx' : g (z.re : ℂ) = x' := by rw [← hx'e, ← hRP.1.eq_ofReal]; exact hrec x' hx'
  have hxx : x' = x := by
    have h1 : g (z.re : ℂ) = x := by rw [← hze]; exact hgz
    have := hgx'.symm.trans h1
    exact_mod_cast this
  rw [hze, ← hx'e, hxx]

/-- **A piece through a real point beyond the record ends beyond it** (deterministic, in the state chart). -/
theorem end_right_of_visit (hRP : RProf s) (hcc : (stChart s).IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H)
    (himg : (stChart s).2.1 '' H ⊆ H) {C₁ C₂ : ℝ} (hprop : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    (hg0 : g 0 = stRecR s) (hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x)
    (hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H)
    (hα : IsGeneratingTrace w L α) (hw : ContinuousOn w {r | (r : ℝ≥0∞) < L}) (hw0 : w 0 = 0)
    (hαH : ∀ t : ℝ≥0, t ≤ L → 0 ≤ (α t).im) (hval : ∀ t : ℝ≥0, t ≤ L → p t = g (α t))
    {sh : ℝ≥0} (hshL : sh < L) {R' : ℝ} (hR' : stRecR s < R') (hpsh : p sh = R')
    {x : ℝ} (hpx : p L = x) (hxB : stRecR s < x) (hvis : ∀ t : ℝ≥0, t ≤ sh → p t ≠ x) : R' < x := by
  have hsh := eq_rProf_of_readback hRP hcc hgc hgi himg hprop hg0 hrec hfree (hαH sh hshL.le) hR'
    ((hval sh hshL.le).symm.trans hpsh)
  have hL := eq_rProf_of_readback hRP hcc hgc hgi himg hprop hg0 hrec hfree (hαH L le_rfl) hxB
    ((hval L le_rfl).symm.trans hpx)
  have hmono := hRP.2.1.1
  refine (hmono.lt_iff_lt hR' hxB).1 ?_
  by_contra hle
  rw [not_lt] at hle
  -- the endpoint is not on the trace before `sh`
  have hnot : α L ∉ α '' Icc 0 sh := by
    rintro ⟨t, ht, he⟩
    refine hvis t ht.2 ?_
    rw [hval t (ht.2.trans hshL.le), he, ← hval L le_rfl, hpx]
  have hlt : rProf (stChart s) x < rProf (stChart s) R' := by
    refine lt_of_le_of_ne hle fun h => hnot ⟨sh, ⟨bot_le, le_rfl⟩, ?_⟩
    rw [hsh, hL, h]
  -- the curve stopped at `sh`
  set α' : ℝ≥0 → ℂ := fun t => α (min t sh) with hα'
  have hαc : ContinuousOn α (Icc 0 L) := hα.2.1.mono fun t ht => ENNReal.coe_le_coe.2 ht.2
  have hα'c : Continuous α' :=
    hαc.comp_continuous (continuous_id.min continuous_const) fun t => ⟨bot_le, (min_le_right _ _).trans hshL.le⟩
  have hα'H : ∀ t, α' t ∈ Hbar := fun t => hαH _ ((min_le_right _ _).trans hshL.le)
  have himg' : α' '' Icc 0 sh = α '' Icc 0 sh := by
    refine image_congr fun t ht => ?_
    simp only [hα', min_eq_left ht.2]
  have h0 : α' 0 = ((0 : ℝ) : ℂ) := by simp only [hα', zero_min, hα.1, Complex.ofReal_zero]
  have hxpos := hRP.2.2.1 x hxB
  have hmem : ((rProf (stChart s) x : ℝ) : ℂ) ∈ closure (fillH (α' '' Icc 0 sh)) := by
    refine (Lk.mem_closure_fillH_image_iff hα'c hα'H (zero_le : (0 : ℝ≥0) ≤ sh) h0 hxpos ?_).2
      ⟨sh, ⟨bot_le, le_rfl⟩, ?_, ?_⟩
    · rw [himg', ← hL]; exact hnot
    · simp only [hα', min_self, hsh, Complex.ofReal_im]
    · simp only [hα', min_self, hsh, Complex.ofReal_re]; exact hlt
  rw [himg', ← hL] at hmem
  exact Wf.gen_end_ne_of_mem_closure_fill hα hw hw0 hshL hnot hmem rfl

end Det

section Ae

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

open Restart LuM Lk

/-- **A piece through a real point beyond the record ends beyond it**, almost surely at a walk launch (regularized
family). -/
theorem ae_walk_end_right (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      0 < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
      ∀ (sh : ℝ≥0) (R' : ℝ), (sh : ℝ≥0∞) < (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 →
        stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) < R' →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) sh = R' →
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ≠ ⊤ → ∀ x : ℝ,
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2.toNNReal = x →
        x ∈ origBadR κ b (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)) → R' < x := by
  classical
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  have hprog : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  set Ew := StagedReg.regFam E w with hEwdef
  have hEw := hE' w hprog
  have hRw : StagedPiecesRegular κ b jumps P w Ew := WalkLaw.stagedPiecesRegular_regHist (hER _ hprog)
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ := by
    have := WalkCapBlock.ambientSideBound_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ' true
    simpa [WalkCapBlock.AmbientSideBound] using this
  obtain ⟨β, Y, hW, hInv⟩ := Wf.exists_witness_right_lwoj hκ hκ4 (ψ := 0) (u := 0)
    (show -(Real.pi / 2) < (0 : ℝ) by linarith [Real.pi_pos]) hb hh hEw (hreg' w) hRw hamb ℓ
  filter_upwards [hInv, Wf.ae_stage_avoid hκ hκ4 hb hh hEw (hreg' w) hRw hW,
    ae_stage_tip hκ hκ4 hb hh hEw (hreg' w) hRw hW,
    GW1WalkExit.ae_walkStageData_right hκ hb hh hEw (hreg' w) hamb, hRw,
    GW1W.regLaunches_of_stagedPiecesRegular hRw, ae_walk_phys h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ] with ω hInvω hAvω
    hTipω hsω hrω hRLω hphω hl hz
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => Ew j ω with hD
  set s := ExplState.run κ b jumps w D ℓ with hs
  have hP : ∀ j c θ', (ExplState.run κ b jumps w D (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (D j).1 (min (instrTime w j) (D j).2) :=
    fun j c θ' hl' => hrω j θ' _ c (eq_launch_of_launches _ _ hl').1 hl'
  have hX := (GW1WalkExit.walk_recordGeometry hκ hb D (fun j => hreg' w j ω) hsω hP).2 ℓ hl
  have hB := GW1Ext.rawRecordBound_of_launch hκ hb D (fun j => hreg' w j ω) hsω hP hl
  obtain ⟨hRP, hpt, hext⟩ : RProf s ∧ stPt s = stRecR s ∧
      ∀ x, stRecR s < x → extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) = (x : ℂ) := hX.1
  obtain ⟨hleft, -, hO⟩ := (hInvω hl).1
  obtain ⟨hseed', havoid⟩ := hAvω hl
  have hseed := hseed' hz
  obtain ⟨htip, hmark⟩ := hTipω hl hz
  have hcc := isConformal_runChart_of_reg w hRLω ℓ
  have hcb := (GW1P.isClosed_pieces_run w D hRLω ℓ).1
  obtain ⟨g, hgc, hgi, ⟨C₁, C₂, -, hprop⟩, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hPR := pieceRegular_of_launch hRLω hl
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 → 0 ≤ (trOf (D ℓ) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hval : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D ℓ).2 → pcPt s (D ℓ) t = g (trOf (D ℓ) t) := fun t ht =>
    bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))
  have hg0 : g 0 = stRecR s := by
    have h1 := GW1WalkFinish.boundary_limit_of_exteriorRecord (GW1WalkFinish.hasBdryLimits_chart_run w D hP ℓ) hX.1
    have h2 := hgt 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    rw [tendsto_nhds_unique h2 h1, hpt]
  have hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x := fun x hx => by
    have hmem : (0 : ℝ) ≤ ((stChart s).1 (x : ℂ)).im := by rw [hRP.1 x]
    have : (𝓝[H] ((stChart s).1 (x : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H hmem
    have h1 : g ((stChart s).1 (x : ℂ)) = extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) :=
      ((hgt _ hmem).limUnder_eq).symm
    rw [h1]
    exact hext x hx
  have hnd : stStatus s ≠ GW1Conn.stDone := by
    obtain ⟨⟨c₀, θ₀⟩, hc₀⟩ := Option.ne_none_iff_exists'.1 hl
    exact WalkIntRunChron.not_done_of_launch _ _ hc₀
  have hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H := by
    intro x hx
    rw [Lk.image_runChart_walk_eq hRLω (fin_of_later_launch hl)]
    have hpc : IsCompact (SB.prefixPhysSet κ b jumps w D ℓ) := Lx.isCompact_prefixPhysSet_run w D hP ℓ hnd
    obtain ⟨ρ, hρ, hd⟩ := ball_disjoint_fillH_right hpc fun y hy => lt_of_le_of_lt (by
      have := hB y hy
      simpa [GW1WalkFinish.sideCoord, GW1WalkExit.outwardRecord] using this) hx
    exact ⟨ρ, hρ, fun z hz hdz => ⟨hz, fun hzF => Set.disjoint_left.1 hd (mem_ball.2 hdz) hzF⟩⟩
  have himg : (stChart s).2.1 '' H ⊆ H := by
    rw [Lk.image_runChart_walk_eq hRLω (fin_of_later_launch hl)]; exact diff_subset
  obtain ⟨-, -, hav, -⟩ := hphω hl hz
  intro sh R' hshL hR' hpsh hLt x hpx hxbad
  have hLe : (((D ℓ).2.toNNReal : ℝ≥0) : ℝ≥0∞) = (D ℓ).2 := ENNReal.coe_toNNReal hLt
  have hα' : IsGeneratingTrace (D ℓ).1 (((D ℓ).2.toNNReal : ℝ≥0) : ℝ≥0∞) (trOf (D ℓ)) := by rw [hLe]; exact hα
  have hw : ContinuousOn (D ℓ).1 {r : ℝ≥0 | (r : ℝ≥0∞) < (((D ℓ).2.toNNReal : ℝ≥0) : ℝ≥0∞)} := by
    rw [hLe]; exact hPR.2.1.mono fun r (hr : (r : ℝ≥0∞) < (D ℓ).2) => (show (r : ℝ≥0∞) ≤ (D ℓ).2 from hr.le)
  have hshL' : sh < (D ℓ).2.toNNReal := by rw [← ENNReal.coe_lt_coe, hLe]; exact hshL
  have hle : ∀ t : ℝ≥0, t ≤ (D ℓ).2.toNNReal → (t : ℝ≥0∞) ≤ (D ℓ).2 := fun t ht => by
    rw [← hLe]; exact ENNReal.coe_le_coe.2 ht
  refine end_right_of_visit hRP hcc hgc hgi himg hprop hg0 hrec hfree hα' hw hPR.1 (fun t ht => hαH t (hle t ht))
    (fun t ht => hval t (hle t ht)) hshL' hR' hpsh hpx hxbad.1 fun t ht hpt => ?_
  have htL : (t : ℝ≥0∞) < (D ℓ).2 := (ENNReal.coe_le_coe.2 ht).trans_lt hshL
  exact hav t htL x hpt hxbad.1 (subset_closure hxbad)

end Ae

end InteractingSLE.Theorem14.SB.Nf
