/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk
import InteractingSLE.Spec.Supplement.GW1LaterR51

/-!
# Theorem 1.4's walks: an ordinary piece contains no real arc (Lemma 2.5 in chart form)

Packet PROVE-T14-GW9. Theorem GW4, proof (`source/spec/p625-671.md`, p. 637): "An ordinary piece contains no real
interval"; follow-up note A–E, Part D.2 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L804–L806): "the
continuous inverse would put a nontrivial real subarc in the ordinary flow, contrary to Lemma 2.5 (p. 38)".

## The argument (`subsingleton_real_of_subset_range`, deterministic)

Let a regular piece (driver `W` continuous up to its stop `S`, continuous generating trace `α`) be read in a good
conformal chart `c` (boundary-limit map `f`, `GW1P.HasProperBdryExt`), so that its physical tip set is
`T = f(α([0, S]))` (closed, `GW1P.isClosed_tipSet`), and suppose `T` lies in the range of a proper curve `γ`. If a
preconnected set `A ⊆ T` of real points had two points, it would contain an arc `γ([s, t])`, `s < t`. The image
`γ((s, t))` is open in `range γ` (`γ` is an embedding): `γ((s, t)) = V ∩ range γ` with `V` open. The own times
`u ∈ (0, S)` with `f(α u) ∈ V` form an open set of reals (`f ∘ α` is continuous), nonempty by continuity at the time
of a midpoint of the arc. At each such time the physical tip lies in `γ((s, t)) ⊆ ℝ`, so `α u ∉ ℍ` (on `ℍ`,
`f = c.inv` maps into `ℍ`). By Lemma 2.5 (`IsGeneratingTrace.volume_setOf_notMem_H`) these times are Lebesgue-null:
a nonempty open null set of reals, a contradiction.

## Main results

* `pieces_run_regular`: along a run whose launched pieces are regular, every chart is conformal and good, and every
  recorded piece is a regular piece read in such a chart (the conformal strengthening of `GW1P.isClosed_pieces_run`);
* **`pieces_real_subsingleton_of_range`**: if the physical set of the run is the range of a proper curve, no recorded
  piece contains a real arc;
* `WalkPiecePairRegStatement`: clause (1) of `WalkCont.WalkPieceContinuumRegStatement` alone (an ordinary piece of
  `R` and one of `L` share no arc), the genuinely probabilistic clause;
* **`walkPieceContinuumRegStatement_of_pair`**: the piece statement from clause (1) and the two walks' proper
  parametrizations (clauses (2)–(3) proved);
* **`rightWalkNegRealRegStatement_of_proper`**, `rightWalkNegRealRegStatement_of_theorem13`:
  `GW3SidedProof.RightWalkNegRealRegStatement` from the right walk's proper parametrization and the connector sides
  (from Theorem 1.3); the piece statement is no longer needed for it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkPiece

open GW1P CounterflowRange

/-- A conformal chart's boundary-limit map agrees with its inverse on `ℍ`. -/
theorem bdry_eq_inv_of_mem_H {c : Chart} (hcc : c.IsConformal) {f : ℂ → ℂ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {p : ℂ} (hp : p ∈ H) : f p = c.2.1 p := by
  have hpb : p ∈ Hbar := le_of_lt (show (0 : ℝ) < p.im from hp)
  have := neBot_nhdsWithin_H hpb
  have hcont : ContinuousAt c.2.1 p :=
    (hcc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hp)).continuousAt
  exact tendsto_nhds_unique (hf p hpb) (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-- A real number is not in `ℍ`. -/
theorem ofReal_notMem_H (x : ℝ) : (x : ℂ) ∉ H := fun h => by
  have h' : (0 : ℝ) < (x : ℂ).im := h
  simp at h'


/-- **An ordinary piece inside the range of a proper curve contains no real arc** (Lemma 2.5 in chart form). Let `γ`
be a proper curve and the piece run by the regular data `(W, S)` in a good conformal chart `c` have its physical tips
in `range γ`. Then the closure of the piece's tip set contains no nondegenerate preconnected set of real points. -/
theorem subsingleton_real_of_subset_range {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ) {c : Chart}
    (hcc : c.IsConformal) (hc : HasProperBdryExt c) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (hr : PieceRegular W S)
    (hT : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ⊆ range γ) :
    ∀ A ⊆ closure (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S) ∩ range ((↑) : ℝ → ℂ),
      IsPreconnected A → A.Subsingleton := by
  intro A hA hAc x hx y hy
  by_contra hxy
  rw [(isClosed_tipSet hc hr).closure_eq] at hA
  obtain ⟨f, C, hf, -⟩ := hc
  obtain ⟨hW0, hWc, α, hα, -⟩ := hr
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  rw [tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)] at hA hT
  -- a zero stop gives a single point
  rcases eq_or_ne S 0 with hS0 | hS0
  · have hpt : ∀ z ∈ A, z = f (α 0) := fun z hz => by
      obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := (hA hz).1
      have hu' : (u : ℝ≥0∞) ≤ 0 := hS0 ▸ hu
      rw [nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hu'
      rw [hu']
    exact hxy ((hpt x hx).trans (hpt y hy).symm)
  have hSpos : 0 < S := pos_iff_ne_zero.2 hS0
  -- an open subarc of `γ` inside `A`
  have he := (WalkCont.isClosedEmbedding_of_isProperCurve hγ).isEmbedding
  obtain ⟨s, t, hst, hsub⟩ :=
    WalkCont.exists_Icc_image_subset_of_isPreconnected he (fun z hz => hT (hA hz).1) hAc hx hy hxy
  obtain ⟨V, hVo, hVpre⟩ := he.isInducing.isOpen_iff.1 (isOpen_Ioo (a := s) (b := t))
  -- the key property: a tip time landing in `V` has its trace point off `ℍ`
  have hkey : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ S → f (α u) ∈ V → α u ∉ H := by
    intro u hu hV hαu
    obtain ⟨r, hr⟩ := hT ⟨α u, ⟨u, hu, rfl⟩, rfl⟩
    have hrst : r ∈ Ioo s t := by rw [← hVpre]; show γ r ∈ V; rw [hr]; exact hV
    obtain ⟨xr, hxr⟩ := (hA (hsub ⟨r, Ioo_subset_Icc_self hrst, hr⟩)).2
    have h1 : f (α u) ∈ H := by rw [bdry_eq_inv_of_mem_H hcc hf hαu]; exact hcc.2.1 hαu
    rw [← hxr] at h1
    exact ofReal_notMem_H xr h1
  -- a tip time landing in `V`
  obtain ⟨m, hsm, hmt⟩ := exists_between hst
  obtain ⟨_, ⟨u₀, hu₀, rfl⟩, hΓu₀⟩ := (hA (hsub ⟨m, ⟨hsm.le, hmt.le⟩, rfl⟩)).1
  have hV₀ : f (α u₀) ∈ V := by
    rw [hΓu₀]
    show m ∈ γ ⁻¹' V
    rw [hVpre]; exact ⟨hsm, hmt⟩
  -- the open set of real times
  set I : Set ℝ := Ioi 0 ∩ ENNReal.ofReal ⁻¹' Iio S with hIdef
  have hIo : IsOpen I := isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hfc : ContinuousOn f Hbar := continuousOn_of_tendsto hf
  have hΓc : ContinuousOn (fun u : ℝ≥0 => f (α u)) {u : ℝ≥0 | (u : ℝ≥0∞) ≤ S} :=
    hfc.comp hα.2.1 fun u hu => hαH u hu
  have hmapI : MapsTo Real.toNNReal I {u : ℝ≥0 | (u : ℝ≥0∞) ≤ S} := fun r hr =>
    le_of_lt (show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < S from hr.2)
  have hgc : ContinuousOn (fun r : ℝ => f (α r.toNNReal)) I :=
    hΓc.comp continuous_real_toNNReal.continuousOn hmapI
  set O : Set ℝ := I ∩ (fun r : ℝ => f (α r.toNNReal)) ⁻¹' V with hOdef
  have hOo : IsOpen O := hgc.isOpen_inter_preimage hIo hVo
  -- `O` is nonempty
  have hcl : ((u₀ : ℝ)) ∈ closure I := by
    rcases eq_or_ne u₀ 0 with h0 | h0
    · obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ < S := by
        obtain ⟨q, -, hq0, hqS⟩ := ENNReal.lt_iff_exists_real_btwn.1 hSpos
        exact ⟨q, ENNReal.ofReal_pos.1 hq0, hqS⟩
      have hsubI : Ioo 0 δ ⊆ I := fun r hr =>
        ⟨hr.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2.le) hδ⟩
      refine closure_mono hsubI ?_
      rw [closure_Ioo hδ0.ne, h0, NNReal.coe_zero]
      exact left_mem_Icc.2 hδ0.le
    · have hpos : (0 : ℝ) < u₀ := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
      have hsubI : Ioo 0 (u₀ : ℝ) ⊆ I := fun r hr => by
        refine ⟨hr.1, show ENNReal.ofReal r < S from lt_of_lt_of_le ?_ hu₀⟩
        rw [← ENNReal.ofReal_coe_nnreal]
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hr.2
      refine closure_mono hsubI ?_
      rw [closure_Ioo hpos.ne]
      exact right_mem_Icc.2 hpos.le
  have hcw : ContinuousWithinAt (fun r : ℝ => f (α r.toNNReal)) I (u₀ : ℝ) := by
    have h1 : ContinuousWithinAt (fun u : ℝ≥0 => f (α u)) {u : ℝ≥0 | (u : ℝ≥0∞) ≤ S} (u₀ : ℝ).toNNReal := by
      rw [Real.toNNReal_coe]; exact hΓc u₀ hu₀
    exact h1.comp continuous_real_toNNReal.continuousWithinAt hmapI
  have hev : ∀ᶠ r in 𝓝[I] (u₀ : ℝ), f (α r.toNNReal) ∈ V := by
    refine hcw ?_
    simp only [Real.toNNReal_coe]
    exact hVo.mem_nhds hV₀
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  obtain ⟨r, hrV, hrI⟩ := (hev.and self_mem_nhdsWithin).exists
  have hOne : O.Nonempty := ⟨r, hrI, hrV⟩
  -- `O` is null by Lemma 2.5
  have hnull : volume O = 0 := by
    refine measure_mono_null (fun r hr => ?_)
      (hα.volume_setOf_notMem_H (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0)
    exact ⟨hr.1.1.le, hr.1.2, hkey _ (le_of_lt (show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < S from hr.1.2)) hr.2⟩
  exact (hOo.measure_pos volume hOne).ne' hnull


section Run

open Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Along a run whose launched pieces are regular, every chart is conformal and good, and every recorded piece is a
regular piece read in a conformal good chart** (the conformal strengthening of `GW1P.isClosed_pieces_run`). -/
theorem pieces_run_regular (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    ((ExplState.run κ b jumps spec D n).2.2.2.2.1.IsConformal ∧
      HasProperBdryExt (ExplState.run κ b jumps spec D n).2.2.2.2.1) ∧
      ∀ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.IsConformal ∧ HasProperBdryExt p.1 ∧
        ∃ (W : ℝ≥0 → ℝ) (S : ℝ≥0∞), PieceRegular W S ∧
          p.2 = ((fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal), S) := by
  induction n with
  | zero =>
    refine ⟨⟨Chart.isConformal_id.recenter spec.1, hasProperBdryExt_recenter_id spec.1⟩, fun p hp => ?_⟩
    simp [ExplState.run, ExplState.init] at hp
  | succ n ih =>
    obtain ⟨⟨hcc, hc⟩, hp⟩ := ih
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha, pieces_run_succ_of_noLaunch spec D hl]
      exact ⟨⟨hcc.recenter a, hc.recenter a⟩, hp⟩
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      refine ⟨?_, fun p hp' => ?_⟩
      · rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
        · rw [chart_launch_of_top _ _ _ _ _ htop]
          exact ⟨hcc, hc⟩
        · rw [chart_launch _ _ _ _ _ htop]
          exact ⟨hcc.loewner hr.continuous_stoppedReal.1 hr.continuous_stoppedReal.2 (NNReal.coe_nonneg _),
            hc.loewner_stopped hr htop⟩
      · rcases List.mem_append.1 hp' with hq | hq
        · exact hp p hq
        · rw [List.mem_singleton] at hq
          subst hq
          exact ⟨hcc, hc, _, _, hr, rfl⟩

/-- **No real arc in the pieces of a run whose physical set is the range of a proper curve** (every launched piece
regular). -/
theorem pieces_real_subsingleton_of_range (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) {γ : ℝ≥0 → ℂ} (hγ : Supp9B.IsProperCurve γ)
    (hγr : range γ = ExplState.physSet κ b jumps spec D) :
    ∀ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1,
      ∀ A ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ range ((↑) : ℝ → ℂ), IsPreconnected A → A.Subsingleton := by
  intro p hp
  have hT : p.1.tipSet p.2.1 p.2.2 ⊆ range γ := by
    rw [hγr]
    intro z hz
    exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨p, hp, hz⟩))
  obtain ⟨hcc, hc, W, S, hr, hp2⟩ := (pieces_run_regular spec D hreg _).2 p hp
  obtain ⟨c, Wp, Sp⟩ := p
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp2
  exact subsingleton_real_of_subset_range hγ hcc hc hr hT

end Run


/-! ### The statements -/

universe u

/-- **Named input: clause (1) of the piece statement, R51 form** (Theorem GW4, proof, p. 637: "An interior common
open subarc is impossible: on the same incident side the two exact flow germs differ by `πχ`, whereas an inherited
branch change is an integer multiple of `2πχ`"): almost surely the closure of an ordinary piece of the right walk and
the closure of an ordinary piece of the left walk share no nondegenerate preconnected set. With the walks' proper
parametrizations it gives `WalkCont.WalkPieceContinuumRegStatement` (`walkPieceContinuumRegStatement_of_pair`). -/
def WalkPiecePairRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ p ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀)
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length).1,
          ∀ q ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)
              (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2.length).1,
          ∀ S ⊆ closure (p.1.tipSet p.2.1 p.2.2) ∩ closure (q.1.tipSet q.2.1 q.2.2),
            IsPreconnected S → S.Subsingleton

/-- **The piece statement from its clause (1) and the walks' proper parametrizations**: clauses (2)–(3) (no real
arc in an ordinary piece) hold almost surely once each walk is the range of a proper curve, by Lemma 2.5 in chart
form (`pieces_real_subsingleton_of_range`). -/
theorem walkPieceContinuumRegStatement_of_pair (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hpair : WalkPiecePairRegStatement.{u}) :
    WalkCont.WalkPieceContinuumRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hpair κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    (hreg _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)).ae_pieceRegular,
    (hreg _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)).ae_pieceRegular] with ω₀ hPRω hPLω hpω hrR hrL
  obtain ⟨γR, hγR, -, hγRr⟩ := hPRω
  obtain ⟨γL, hγL, -, hγLr⟩ := hPLω
  exact ⟨hpω, pieces_real_subsingleton_of_range _ _ hrR hγR hγRr,
    pieces_real_subsingleton_of_range _ _ hrL hγL hγLr⟩

/-- **The right walk contains no nondegenerate continuum of negative reals**
(`GW3SidedProof.RightWalkNegRealRegStatement`) from its proper parametrization and the sides of the real connectors:
the pieces contain no real arc
(`pieces_real_subsingleton_of_range`, Lemma 2.5) and the connectors lie in `[0, ∞)`. -/
theorem rightWalkNegRealRegStatement_of_proper (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hS : WalkCont.WalkConnectorSideRegStatement.{u}) : GW3SidedProof.RightWalkNegRealRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    (hreg _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)).ae_pieceRegular] with ω₀ hPRω hSω hrR
  obtain ⟨γR, hγR, -, hγRr⟩ := hPRω
  rw [← hγRr]
  exact GW3SidedProof.neg_real_subsingleton hγR hγRr hSω.1 (pieces_real_subsingleton_of_range _ _ hrR hγR hγRr)

/-- `GW3SidedProof.RightWalkNegRealRegStatement` from the right walk's proper parametrization and Theorem 1.3 (which
gives the sides of the real connectors, `GW1X.walkConnectorSideRegStatement_of_theorem13`). -/
theorem rightWalkNegRealRegStatement_of_theorem13 (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) : GW3SidedProof.RightWalkNegRealRegStatement.{u} :=
  rightWalkNegRealRegStatement_of_proper hPR (GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀)

end InteractingSLE.Theorem14.WalkPiece
