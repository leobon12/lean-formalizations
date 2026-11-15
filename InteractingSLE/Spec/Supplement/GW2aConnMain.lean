/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aConnLaw
import InteractingSLE.Spec.Supplement.GW2aConnBR6
import InteractingSLE.Spec.Supplement.GW2aStepConn
import InteractingSLE.Spec.Supplement.GW2aStepWire
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# GW2a's connectors: BR6 forcing in the conditional world — `GW2aConnectorForcingStatement` PROVED

Packet PROVE-GW2A-CONN. Lemma GW2a (supplement p. 624): "For a right threshold the proposed connector has
`H + θχ ≤ −λ ⟹ H ≤ −λ − θχ ≤ −Λ`. Its outward conditional counterflow sums are consequently at most `d` by the BW2
calculation, while the whole conditional word is admissible. BR6 forces the entire connector and its reverse first
visits".

**`gw2aConnectorForcingStatement_of_theorem13`**: PROVE-GW2A-STEP's named input `GW2aStep.GW2aConnectorForcingStatement`
from Theorem 1.3 (at the universe of the probability space and at universe `0`, the latter for Lemma GW0's forward
implication). The argument, at almost every sample `ω₀` whose instruction `k` records a connector:

1. the state `s` after `k` instructions is alive and, by GW1's classification for arbitrary programs (`exists_inv`),
   the field read in the state chart is, under the regular conditional law `ν` given the retained past, a GFF with an
   explicit word `β` satisfying the run invariant `Inv β s`: on the untouched original rays the word read in the chart
   is the original word, the chart is a good real profile there, the current point is the outward record with the
   profile tending to `0` there, and the outward original height is low;
2. the connector is low (`add_le_neg_of_connector`), so the word is low on the chart image `(0, m x)` of the connector
   (`low_word_of_rConn`; the mirror on the left);
3. BR6 sufficiency in the world `ν` (`ae_trace_eq_of_low_right/left`, for any centred counterflow of the conditional
   field with infinite lifetime: the counterflow word is admissible by GW0) gives a visit of the chart point `m q` of
   every rational connector point `q` and of the chart point of the new current point;
4. a chart visit of `m q` is a physical visit of `q` through the chart's boundary extension (`bdry_eq_of_chartReadsAt`,
   `GW2aPiece.tipAt_trans_of_ne_zero`), and the connector is the closure of its rational points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap H Hbar)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### Deterministic facts -/

/-- **The chart's boundary extension at an untouched real point is the point itself.** -/
theorem bdry_eq_of_chartReadsAt {c : Chart} {f : ℂ → ℂ} (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p)))
    {y : ℝ} (hy : ChartReadsAt c y) (hreal : (c.1 y).im = 0) : f (c.1 y) = y := by
  obtain ⟨h1, h2⟩ := hy
  have hp : Tendsto c.1 (𝓝[H] (y : ℂ)) (𝓝[H] (c.1 y)) :=
    tendsto_nhdsWithin_iff.2 ⟨h1, h2.mono fun z hz => hz.1⟩
  have hmem : c.1 y ∈ Hbar := by
    show 0 ≤ (c.1 y).im
    rw [hreal]
  have hcomp : Tendsto (fun z => c.2.1 (c.1 z)) (𝓝[H] (y : ℂ)) (𝓝 (f (c.1 y))) := (hc _ hmem).comp hp
  have hid : Tendsto (fun z => c.2.1 (c.1 z)) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (h2.mono fun z hz => hz.2.symm)
  have := GW1P.neBot_nhdsWithin_H (p := (y : ℂ)) (by show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im; simp)
  exact tendsto_nhds_unique hcomp hid

/-- A step that records a connector is a boundary continuation. -/
theorem contStep_of_arcs_ne (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hne : (ExplState.run κ b jumps spec D (k + 1)).2.1 ≠ (ExplState.run κ b jumps spec D k).2.1) :
    ∃ (vStop : Option ℝ) (pref : Bool), ExplState.run κ b jumps spec D (k + 1) =
      ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) vStop pref := by
  rw [run_succ] at hne ⊢
  cases hk : spec.2.2[k]? with
  | none => rw [hk] at hne; exact absurd rfl hne
  | some ins =>
    rw [hk] at hne
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · exact absurd (GW2aCont.arcs_flowStep (κ := κ) (b := b) spec.2.1 _ k (D k) θ t) hne
    · exact ⟨none, pref, rfl⟩
    · exact ⟨some v, pref, rfl⟩

theorem isLive_of_rStart {s : ExplState} (h : RStart κ b s) : IsLive s := by
  rcases h with h | ⟨h, -⟩ | h <;>
    exact ⟨fun hT => by rcases hT with hT | hT <;> (change stStatus s = _ at hT; rw [h] at hT; simp [stThr] at hT),
      by rw [h]; simp [stThr]⟩

theorem isLive_of_lStart {s : ExplState} (h : LStart κ b s) : IsLive s := by
  rcases h with h | ⟨h, -⟩ | h <;>
    exact ⟨fun hT => by rcases hT with hT | hT <;> (change stStatus s = _ at hT; rw [h] at hT; simp [stThr] at hT),
      by rw [h]; simp [stThr]⟩

theorem rConn_of_rStart {β : BoundaryWord} {s : ExplState} (hI : Inv κ b jumps β s) (h : RStart κ b s) :
    RConn κ b s := by
  rcases h with h | ⟨h, hlow⟩ | h
  · exact (hI.2.2.1 h).1
  · rcases hI.2.2.2.2.2.2 h with ⟨h0, -⟩ | hadm
    · exact rConn_of_ready h0 hlow
    · exact absurd hlow (not_le.2 hadm.2)
  · exact hI.2.2.2.2.1 h

theorem lConn_of_lStart {β : BoundaryWord} {s : ExplState} (hI : Inv κ b jumps β s) (h : LStart κ b s) :
    LConn κ b s := by
  rcases h with h | ⟨h, hhigh⟩ | h
  · exact (hI.2.2.2.1 h).1
  · rcases hI.2.2.2.2.2.2 h with ⟨-, h0⟩ | hadm
    · exact lConn_of_ready h0 hhigh
    · exact absurd hhigh (not_le.2 hadm.1)
  · exact hI.2.2.2.2.2.1 h

theorem stAngle_setDead (s : ExplState) : stAngle (setDead s) = stAngle s := rfl

theorem stAngle_moveToEnd (s : ExplState) (r : Bool) : stAngle (ExplState.moveToEnd s r) = stAngle s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stAngle_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    stAngle (ExplState.launch s k D θ t) = θ := by
  by_cases h : min t D.2 = ⊤
  · exact (launch_eq_of_top s k D θ t h).2.1
  · exact (launch_eq_of_ne_top s k D θ t h).2.1

/-- **The angle of every state of a boundary-continued program lies in `[−π/2, π/2]`.** -/
theorem stAngle_run_mem (spec : ExplSpec) (hp : IsBoundaryContinuedProgram spec.2.2)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, stAngle (ExplState.run κ b jumps spec D k) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  | 0 => by
    change (0 : ℝ) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
    constructor <;> linarith [Real.pi_pos]
  | k + 1 => by
    have ih := stAngle_run_mem spec hp D k
    rw [run_succ]
    cases hk : spec.2.2[k]? with
    | none => exact ih
    | some ins =>
      simp only
      rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
      · change stAngle (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t) ∈ _
        rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t
          with e | e | e <;> rw [e]
        · exact ih
        · exact ih
        · rw [stAngle_launch]
          exact hp θ t (List.mem_of_getElem? hk)
      all_goals
        first
        | (change stAngle (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref) ∈ _
           rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) none pref
             with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e]
           · exact ih
           · exact ih
           · rw [stAngle_moveAlong]; exact ih
           · rw [stAngle_moveToEnd]; exact ih)
        | (change stAngle (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref) ∈ _
           rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) (some v)
             pref with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e]
           · exact ih
           · exact ih
           · rw [stAngle_moveAlong]; exact ih
           · rw [stAngle_moveToEnd]; exact ih)

theorem subset_closure_rat_inter {A U : Set ℝ} (hU : IsOpen U) (hA : A ⊆ closure U) :
    A ⊆ closure (U ∩ range ((↑) : ℚ → ℝ)) := by
  have h1 : U ⊆ closure (U ∩ range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast.open_subset_closure_inter hU
  calc A ⊆ closure U := hA
    _ ⊆ closure (closure (U ∩ range ((↑) : ℚ → ℝ))) := closure_mono h1
    _ = closure (U ∩ range ((↑) : ℚ → ℝ)) := closure_closure

/-! ### BR6 forcing at one sample -/

section Forcing

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **BR6 forcing of a connector in a world whose field has the classified word** (GW2a, p. 624). Let `ν` be a
probability measure under which the field `h'` read in the chart of the state `s` is a GFF with a word `β` satisfying
the run invariant at `s`, and let `Wk` be any centred counterflow of `h'` with infinite lifetime. If the boundary
continuation from `s` records a connector, then almost surely every point of the connector is a limit of physical
tips of `Wk` (read through the chart and the inversion), and the chart image of the new current point, if the history
is still alive, is a tip of `Wk`. -/
theorem forcing_at (hT13 : Exist.Theorem13Statement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u}) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) {ν : Measure Ω} [IsProbabilityMeasure ν]
    {h' : Ω → DistOn upperHalfPlaneOpens} {β : BoundaryWord} (hh' : IsGFFWithBoundaryData ν h' β.fn β.jumps)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ ν h' Wk ζk)
    (hζ : ∀ᵐ ω ∂ν, ζk ω = ⊤) {s : ExplState} (hI : Inv κ b jumps β s)
    (hθ : stAngle s ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto (stChart s).2.1 (𝓝[H] p) (𝓝 (f p))) (vStop : Option ℝ) (pref : Bool)
    (hne : (ExplState.contStep κ b jumps s vStop pref).2.1 ≠ s.2.1) :
    ∀ᵐ ω ∂ν, (∀ y ∈ GW2aCont.newArc s (ExplState.contStep κ b jumps s vStop pref),
        (y : ℂ) ∈ closure {z : ℂ | ∃ r : ℝ≥0,
          ((stChart s).trans infinitySourceChart).tipAt (fun t => Wk t ω) r z}) ∧
      (¬ IsTerminal (ExplState.contStep κ b jumps s vStop pref) →
        (((((stChart s).1 (stPt (ExplState.contStep κ b jumps s vStop pref) : ℂ)).re : ℝ) : ℂ)) ∈
          infinitySourceChart.tipSet (fun t => Wk t ω) ⊤) := by
  have hcf' := hcf
  obtain ⟨b'', J'', h'', -, -, hfl⟩ := hcf'
  have hk : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hk hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  set c := stChart s with hcdef
  set γ := GW2aSingle.chosenTrace Wk ζk with hγdef
  have hpos := hI.1.2.1.2
  have hneg : ∀ q, q < stRecL s → rProf c q < 0 := fun q hq => rProf_neg_of_lProf hI.1.2.2.1.2 hq
  -- a chart visit of `m q` is a physical tip at `q`
  have htip : ∀ ω, IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω) → Continuous (fun t => Wk t ω) → Wk 0 ω = 0 →
      ∀ q : ℝ, stRecR s < q ∨ q < stRecL s → rProf c q ≠ 0 → ∀ t, γ ω t = -((rProf c q : ℂ))⁻¹ →
        (c.trans infinitySourceChart).tipAt (fun t => Wk t ω) t (q : ℂ) := by
    intro ω hγω hWc hW0 q hq hq0 t ht
    have hne' : γ ω t ≠ 0 := by
      rw [ht, neg_ne_zero]
      exact inv_ne_zero (Complex.ofReal_ne_zero.2 hq0)
    have h1 := GW2aPiece.tipAt_trans_of_ne_zero hf hγω hWc hW0 hne'
    have h2 : -(γ ω t)⁻¹ = c.1 q := by rw [ht, inv_neg, inv_inv, neg_neg, hI.1.1.eq_ofReal q]
    rw [h2, bdry_eq_of_chartReadsAt hf (hI.1.2.2.2.2.2 q hq) (hI.1.1 q)] at h1
    exact h1
  -- a chart visit gives a point of the inverted tip set
  have hset : ∀ ω, IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω) → Continuous (fun t => Wk t ω) → Wk 0 ω = 0 →
      ∀ v : ℝ, v ≠ 0 → ∀ t, γ ω t = -((v : ℂ))⁻¹ → (v : ℂ) ∈ infinitySourceChart.tipSet (fun t => Wk t ω) ⊤ := by
    intro ω hγω hWc hW0 v hv t ht
    rw [CounterflowRange.tipSet_infinitySourceChart_top hγω hWc hW0]
    refine ⟨t, ?_, ?_⟩
    · rw [ht, neg_ne_zero]
      exact inv_ne_zero (Complex.ofReal_ne_zero.2 hv)
    · rw [ht, inv_neg, inv_inv, neg_neg]
  have hreg : ∀ᵐ ω ∂ν, IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω) ∧ Continuous (fun t => Wk t ω) ∧
      Wk 0 ω = 0 := by
    filter_upwards [hγ, hζ, hdrv] with ω hγω hζω hdω
    rw [hζω] at hγω hdω
    refine ⟨hγω.1, ?_, hdω.1⟩
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  rcases contStep_arc_cases s vStop pref hne with ⟨hst, he⟩ | ⟨hst, he⟩
  · -- rightward
    have hRC := rConn_of_rStart hI hst
    rw [he]
    have hlowq : ∀ q, stPt s < q → (∀ y, stPt s < y → y < q → y ∉ jumps →
        b y + stAngle s * chiC κ ≤ -sleLambda κ) →
        ∀ᵐ ω ∂ν, ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
      intro q hq hlowb
      have hqR : stRecR s < q := by rw [← hRC.1]; exact hq
      exact ae_trace_eq_of_low_right hT13 hGW0 hκ hκ4 β.isPiecewiseConstantBoundaryData hh' hcf hζ (hpos q hqR)
        (low_word_of_rConn hκ hκ4 hI.1 hRC hθ.1 hqR hlowb)
    rcases rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s vStop with ⟨x, mk, hx, hpx, hj, -⟩ | ⟨hx, hall⟩
    · rw [hx, GW2aCont.newArc_moveAlong]
      have hlowb : ∀ y, stPt s < y → y < x → y ∉ jumps → b y + stAngle s * chiC κ ≤ -sleLambda κ :=
        fun y hy hyx hyJ => add_le_neg_of_connector hb hRC.2.2 hj hy hyx hyJ
      have hq : ∀ q : ℚ, ∀ᵐ ω ∂ν, (q : ℝ) ∈ Ioo (stPt s) x → ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
        intro q
        by_cases hqI : (q : ℝ) ∈ Ioo (stPt s) x
        · filter_upwards [hlowq q hqI.1 fun y hy hyq hyJ => hlowb y hy (hyq.trans hqI.2) hyJ] with ω hω _
            using hω
        · exact Eventually.of_forall fun ω h => absurd h hqI
      filter_upwards [ae_all_iff.2 hq, hlowq x hpx hlowb, hreg] with ω hqω hxω hrω
      refine ⟨fun y hy => ?_, fun _ => ?_⟩
      · simp only [↓reduceIte] at hy
        have hyc : y ∈ closure (Ioo (stPt s) x ∩ range ((↑) : ℚ → ℝ)) :=
          subset_closure_rat_inter isOpen_Ioo (closure_Ioo hpx.ne).symm.subset hy
        refine map_mem_closure Complex.continuous_ofReal hyc ?_
        rintro _ ⟨hqI, q, rfl⟩
        obtain ⟨t, ht⟩ := hqω q hqI
        have hqR : stRecR s < q := by rw [← hRC.1]; exact hqI.1
        exact ⟨t, htip ω hrω.1 hrω.2.1 hrω.2.2 q (Or.inl hqR) (hpos q hqR).ne' t ht⟩
      · rw [stPt_moveAlong]
        obtain ⟨t, ht⟩ := hxω
        have hxR : stRecR s < x := by rw [← hRC.1]; exact hpx
        exact hset ω hrω.1 hrω.2.1 hrω.2.2 _ (hpos x hxR).ne' t ht
    · rw [hx, GW2aCont.newArc_moveToEnd]
      have hq : ∀ q : ℚ, ∀ᵐ ω ∂ν, stPt s < (q : ℝ) → ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
        intro q
        by_cases hqI : stPt s < (q : ℝ)
        · filter_upwards [hlowq q hqI fun y hy hyq hyJ =>
            add_le_neg_of_connector hb hRC.2.2 (fun z hz hpz _ => hall z hz hpz) hy hyq hyJ] with ω hω _
            using hω
        · exact Eventually.of_forall fun ω h => absurd h hqI
      filter_upwards [ae_all_iff.2 hq, hreg] with ω hqω hrω
      refine ⟨fun y hy => ?_, fun hT => absurd (isTerminal_moveToEnd' s true) hT⟩
      simp only [↓reduceIte] at hy
      have hyc : y ∈ closure (Ioi (stPt s) ∩ range ((↑) : ℚ → ℝ)) :=
        subset_closure_rat_inter isOpen_Ioi (closure_Ioi (stPt s)).symm.subset hy
      refine map_mem_closure Complex.continuous_ofReal hyc ?_
      rintro _ ⟨hqI, q, rfl⟩
      obtain ⟨t, ht⟩ := hqω q hqI
      have hqR : stRecR s < q := by rw [← hRC.1]; exact hqI
      exact ⟨t, htip ω hrω.1 hrω.2.1 hrω.2.2 q (Or.inl hqR) (hpos q hqR).ne' t ht⟩
  · -- leftward
    have hLC := lConn_of_lStart hI hst
    rw [he]
    have hhighq : ∀ q, q < stPt s → (∀ y, q < y → y < stPt s → y ∉ jumps →
        sleLambda κ ≤ b y + stAngle s * chiC κ) →
        ∀ᵐ ω ∂ν, ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
      intro q hq hhighb
      have hqL : q < stRecL s := by rw [← hLC.1]; exact hq
      exact ae_trace_eq_of_low_left hT13 hGW0 hκ hκ4 β.isPiecewiseConstantBoundaryData hh' hcf hζ (hneg q hqL)
        (high_word_of_lConn hκ hκ4 hI.1 hLC hθ.2 hqL hhighb)
    rcases lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s vStop with ⟨x, mk, hx, hxp, hj, -⟩ | ⟨hx, hall⟩
    · rw [hx, GW2aCont.newArc_moveAlong]
      have hhighb : ∀ y, x < y → y < stPt s → y ∉ jumps → sleLambda κ ≤ b y + stAngle s * chiC κ :=
        fun y hxy hy hyJ => le_add_of_connector hb hLC.2.2 hj hxy hy hyJ
      have hq : ∀ q : ℚ, ∀ᵐ ω ∂ν, (q : ℝ) ∈ Ioo x (stPt s) → ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
        intro q
        by_cases hqI : (q : ℝ) ∈ Ioo x (stPt s)
        · filter_upwards [hhighq q hqI.2 fun y hy hyq hyJ => hhighb y (hqI.1.trans hy) hyq hyJ] with ω hω _
            using hω
        · exact Eventually.of_forall fun ω h => absurd h hqI
      filter_upwards [ae_all_iff.2 hq, hhighq x hxp hhighb, hreg] with ω hqω hxω hrω
      refine ⟨fun y hy => ?_, fun _ => ?_⟩
      · simp only [Bool.false_eq_true, ↓reduceIte] at hy
        have hyc : y ∈ closure (Ioo x (stPt s) ∩ range ((↑) : ℚ → ℝ)) :=
          subset_closure_rat_inter isOpen_Ioo (closure_Ioo hxp.ne).symm.subset hy
        refine map_mem_closure Complex.continuous_ofReal hyc ?_
        rintro _ ⟨hqI, q, rfl⟩
        obtain ⟨t, ht⟩ := hqω q hqI
        have hqL : (q : ℝ) < stRecL s := by rw [← hLC.1]; exact hqI.2
        exact ⟨t, htip ω hrω.1 hrω.2.1 hrω.2.2 q (Or.inr hqL) (hneg q hqL).ne t ht⟩
      · rw [stPt_moveAlong]
        obtain ⟨t, ht⟩ := hxω
        have hxL : x < stRecL s := by rw [← hLC.1]; exact hxp
        exact hset ω hrω.1 hrω.2.1 hrω.2.2 _ (hneg x hxL).ne t ht
    · rw [hx, GW2aCont.newArc_moveToEnd]
      have hq : ∀ q : ℚ, ∀ᵐ ω ∂ν, (q : ℝ) < stPt s → ∃ t, γ ω t = -((rProf c q : ℂ))⁻¹ := by
        intro q
        by_cases hqI : (q : ℝ) < stPt s
        · filter_upwards [hhighq q hqI fun y hy hyq hyJ =>
            le_add_of_connector hb hLC.2.2 (fun z hz _ hpz => hall z hz hpz) hy hyq hyJ] with ω hω _
            using hω
        · exact Eventually.of_forall fun ω h => absurd h hqI
      filter_upwards [ae_all_iff.2 hq, hreg] with ω hqω hrω
      refine ⟨fun y hy => ?_, fun hT => absurd (isTerminal_moveToEnd' s false) hT⟩
      simp only [Bool.false_eq_true, ↓reduceIte] at hy
      have hyc : y ∈ closure (Iio (stPt s) ∩ range ((↑) : ℚ → ℝ)) :=
        subset_closure_rat_inter isOpen_Iio (closure_Iio (stPt s)).symm.subset hy
      refine map_mem_closure Complex.continuous_ofReal hyc ?_
      rintro _ ⟨hqI, q, rfl⟩
      obtain ⟨t, ht⟩ := hqω q hqI
      have hqL : (q : ℝ) < stRecL s := by rw [← hLC.1]; exact hqI
      exact ⟨t, htip ω hrω.1 hrω.2.1 hrω.2.2 q (Or.inr hqL) (hneg q hqL).ne t ht⟩

end Forcing

/-! ### The named input `GW2aConnectorForcingStatement` -/

/-- **`GW2aStep.GW2aConnectorForcingStatement` from Theorem 1.3** (GW2a, p. 624: "BR6 forces the entire connector and
its reverse first visits"). Theorem 1.3 at universe `0` gives Lemma GW0's forward implication (the conditional
counterflow word with infinite lifetime is admissible, BR6's conditions 1–2); at the universe of the probability space
it gives the continuous transient counterflow trace. -/
theorem gw2aConnectorForcingStatement_of_theorem13 (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) : GW2aStep.GW2aConnectorForcingStatement.{u} := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' _ _ p hp E hE hR hreg k
  set spec : ExplSpec := ⟨0, false, p⟩ with hspec
  obtain ⟨_, _, βt, Yt, -, hWt, hInv⟩ := exists_inv (spec := spec) hκ hb hh rfl rfl hE hreg k
  have h𝒢 : pastSigma κ b jumps spec E k ≤ _ := hE.2.1 k
  filter_upwards [hInv, hWt.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hWt.2.2.1,
    ae_ae_run_eq runMeasStatement hb spec (k := k) (fun j _ => hE.1 j) (fun j _ => hreg j) (P := P),
    hR.ae_pieceRegular] with ω₀ hInv₀ hG₀ hTK hrunK hpr₀
  intro _ hne h' Wk ζk htr hcfk hζk
  obtain ⟨vStop, pref, hstep⟩ := contStep_of_arcs_ne spec (fun j => E j ω₀) k hne
  set s := ExplState.run κ b jumps spec (fun j => E j ω₀) k with hs
  have hne' : (ExplState.contStep κ b jumps s vStop pref).2.1 ≠ s.2.1 := by rw [← hstep]; exact hne
  have hlive : IsLive s := by
    rcases contStep_arc_cases s vStop pref hne' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact isLive_of_rStart h1
    · exact isLive_of_lStart h1
  have hI := hInv₀.2 hlive
  set ν := condExpKernel P (pastSigma κ b jumps spec E k) ω₀ with hν
  have hGν := hG₀ hlive
  -- the chart of the state is conformal with a continuous lift
  have : (ae ν).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero ν)
  obtain ⟨ω₁, hT₁, hr₁⟩ := (hTK.and hrunK).exists
  have hl₁ : IsLive (ExplState.run κ b jumps spec (fun j => E j ω₁) k) := by rw [hr₁]; exact hlive
  obtain ⟨hconf, hlift, -⟩ := hT₁ hl₁
  rw [hr₁] at hconf hlift
  -- the field `h'` is the witness field
  have hgT : ∀ ω, IsChartTransport (stChart s) 1 0 (chiC κ) (h ω)
      (Chart.chartTransport hconf 1 0 (chiC κ) (h ω)) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift) 1 0 _ (h ω)
  have hh'e : h' = fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) :=
    funext fun ω => (htr ω).unique hconf (hgT ω)
  have hh'm : Measurable h' := by
    rw [hh'e]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
  have hYe : Yt =ᵐ[ν] h' := by
    filter_upwards [hTK, hrunK] with ω h1 h2
    have hlω : IsLive (ExplState.run κ b jumps spec (fun j => E j ω) k) := by rw [h2]; exact hlive
    obtain ⟨-, -, hT⟩ := h1 hlω
    rw [h2] at hT
    exact hT.unique hconf (htr ω)
  have hh' : IsGFFWithBoundaryData ν h' (βt ω₀).fn (βt ω₀).jumps := isGFFWithBoundaryData_congr_ae hGν hh'm hYe
  -- the chart's boundary extension
  obtain ⟨f, C, hf, -⟩ := (GW1P.isClosed_pieces_run spec (fun j => E j ω₀) hpr₀ k).1
  have hθ := stAngle_run_mem (κ := κ) (b := b) (jumps := jumps) spec hp (fun j => E j ω₀) k
  have hF := forcing_at hT13 hGW0 hκ hκ4 hb hh' hcfk hζk hI hθ hf vStop pref hne'
  filter_upwards [hF] with ω hω
  rw [GW2aCont.arcAt_eq_newArc, hstep]
  exact hω

/-! ### Wiring -/

/-- **GW2a's connector step without the forcing input**: PROVE-GW2AC's named connector step from BR4a's leaf and
Theorem 1.3 (`GW2aStep.gw2aConnectorStepStatement_of_forcing` with the forcing proved here). -/
theorem gw2aConnectorStepStatement_of_br4a (hBR4a : BR4a.BR4aStatement.{u}) (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) : GW2aCont.GW2aConnectorStepStatement.{u} :=
  GW2aStep.gw2aConnectorStepStatement_of_forcing (gw2aConnectorForcingStatement_of_theorem13 hT13 hT13₀) hBR4a hT13

/-- **Theorem 1.4's leaf `GW2aContainmentRegStatement` without the forcing input**
(`GW2aStep.gw2aContainmentRegStatement_of_bw1` with the forcing proved here). -/
theorem gw2aContainmentRegStatement_of_bw1_conn (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBW1 : BW1.BW1Statement.{u}) (hFix : GW2aStep.FlowFixedTimeInteriorStatement.{u})
    (hBR4a : BR4a.BR4aStatement.{u}) : GW2aCont.GW2aContainmentRegStatement.{u} :=
  GW2aStep.gw2aContainmentRegStatement_of_bw1 hD h12 h13 h12₀ h13₀ hBW1 hFix
    (gw2aConnectorForcingStatement_of_theorem13 h13 h13₀) hBR4a

end GW2aConn

end Theorem14

end InteractingSLE
