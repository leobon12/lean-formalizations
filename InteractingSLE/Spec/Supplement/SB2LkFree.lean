/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwLift
import InteractingSLE.Spec.Supplement.SB4RTop
import InteractingSLE.Spec.Supplement.SB2KEntry

/-!
# The completed lower walk leaves real points free far left (`LowerWalkLeftFreeStatement`)

Packet PROVE-T14-SB2LIFT. PROVE-T14-SB2LOW's named input `Lh.LowerWalkLeftFreeStatement` (for every level `a`, almost
surely some real point left of `a` is off the completed lower walk) is proved here from Theorems 1.2–1.3 (ruling R48
allows them for Theorem 1.4), by a deterministic argument:

* `isClosedEmbedding_of_isProperCurve`: a proper curve (continuous, injective, tending to `∞`) is a closed embedding;
* **`exists_lt_notMem_range`**: a proper curve whose points are adherent to its points in `ℍ`, except for a finite set
  and points of `[0, ∞)`, misses real points arbitrarily far left — otherwise a real segment left of `0` would be the
  image of a nondegenerate time interval, and an interior point of it is not a limit of points of the curve in `ℍ`;
* `tipSet_adherent`, **`physSet_subset_adherent`**: every point of a regular ordinary piece read in a good chart
  (mapping `ℍ` into `ℍ`) is adherent to the piece's points in `ℍ`, unless the piece is a single point (its stop is
  `0`): the generating trace visits `ℍ` in every time interval, and the boundary readout is continuous on `ℍ̄`; so a
  regular run's physical set is adherent to its points in `ℍ` up to its root, finitely many one-point pieces and its
  real connectors;
* **`lowerWalkLeftFreeStatement_of_rightWalkProper`**: the walk is a proper curve (`RightWalkProperRegStatement`,
  Lemma GW1), its connectors lie in `[0, ∞)` (`Lv.ae_arcs_subset_Ici`, under GW1's ambient bound from Theorem 1.3);
  **`lowerWalkLeftFreeStatement_of_thm12_thm13`**;
* `sb2LowerLaunchLift_zero'`, **`sb2LowerLaunchLiftStatement_of_succ'`**: PROVE-T14-SB2LOW's results with this input
  discharged.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw GW1P
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Proper curves -/

/-- A proper curve is a proper map. -/
theorem isProperMap_of_isProperCurve {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) : IsProperMap γ := by
  refine isProperMap_iff_isCompact_preimage.2 ⟨hγ.1, fun K hK => ?_⟩
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hγ.2.2.2.eventually_gt_atTop M)
  refine (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).of_isClosed_subset (hK.isClosed.preimage hγ.1) ?_
  intro t ht
  refine ⟨zero_le, ?_⟩
  by_contra hlt
  exact (hT t (le_of_lt (not_le.1 hlt))).not_ge (hM _ ht)

/-- A proper curve is a closed embedding. -/
theorem isClosedEmbedding_of_isProperCurve {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) : IsClosedEmbedding γ :=
  .of_continuous_injective_isClosedMap hγ.1 hγ.2.1 (isProperMap_of_isProperCurve hγ).isClosedMap

/-- **A proper curve adherent to its points in `ℍ` off a finite set and `[0, ∞)` misses real points arbitrarily
far left.** If it contained every real point left of `a`, the preimage of a real segment left of `min a 0` would be a
nondegenerate time interval (the curve is a closed embedding) on which the curve is real; an interior point of it, off
the finite set, is not a limit of points of the curve in `ℍ`. -/
theorem exists_lt_notMem_range {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) {F : Set ℂ} (hF : F.Finite)
    (hcl : range γ ⊆ closure (range γ ∩ H) ∪ F ∪ ((↑) : ℝ → ℂ) '' Ici 0) (a : ℝ) :
    ∃ y : ℝ, y < a ∧ (y : ℂ) ∉ range γ := by
  by_contra hcon
  push Not at hcon
  have he := isClosedEmbedding_of_isProperCurve hγ
  set q : ℝ := min a 0 - 1 with hq
  set p : ℝ := q - 1 with hp
  have hqa : q < a := by have := min_le_left a 0; linarith
  have hq0 : q < 0 := by have := min_le_right a 0; linarith
  set S : Set ℂ := ((↑) : ℝ → ℂ) '' Icc p q with hS
  have hSγ : S ⊆ range γ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcon y (lt_of_le_of_lt hy.2 hqa)
  set K : Set ℝ≥0 := γ ⁻¹' S with hK
  have hKS : γ '' K = S := image_preimage_eq_of_subset hSγ
  have hSc : IsPreconnected S :=
    (isPreconnected_Icc).image _ Complex.continuous_ofReal.continuousOn
  have hKc : IsPreconnected K := he.isInducing.isPreconnected_image.1 (hKS ▸ hSc)
  obtain ⟨t₁, ht₁⟩ := hcon p (by linarith)
  obtain ⟨t₂, ht₂⟩ := hcon q hqa
  have ht₁K : t₁ ∈ K := by
    show γ t₁ ∈ S
    rw [ht₁]; exact ⟨p, ⟨le_rfl, by linarith⟩, rfl⟩
  have ht₂K : t₂ ∈ K := by
    show γ t₂ ∈ S
    rw [ht₂]; exact ⟨q, ⟨by linarith, le_rfl⟩, rfl⟩
  have ht₁₂ : t₁ ≠ t₂ := by
    intro h
    rw [h, ht₂] at ht₁
    have := Complex.ofReal_injective ht₁
    linarith
  set lo := min t₁ t₂
  set hi := max t₁ t₂
  have hlohi : lo < hi := min_lt_max.2 ht₁₂
  have hIK : Icc lo hi ⊆ K := by
    rcases le_total t₁ t₂ with h | h
    · have e1 : lo = t₁ := min_eq_left h
      have e2 : hi = t₂ := max_eq_right h
      rw [e1, e2]; exact hKc.Icc_subset ht₁K ht₂K
    · have e1 : lo = t₂ := min_eq_right h
      have e2 : hi = t₁ := max_eq_left h
      rw [e1, e2]; exact hKc.Icc_subset ht₂K ht₁K
  -- a time strictly inside, whose point is off `F`
  have hinf : (γ '' Ioo lo hi).Infinite :=
    (Set.Ioo_infinite hlohi).image hγ.2.1.injOn
  obtain ⟨_, ⟨t₀, ht₀, rfl⟩, ht₀F⟩ := (hinf.sdiff hF).nonempty
  have ht₀S : γ t₀ ∈ S := hIK (Ioo_subset_Icc_self ht₀)
  obtain ⟨y₀, hy₀, hy₀e⟩ := ht₀S
  have hnot0 : γ t₀ ∉ ((↑) : ℝ → ℂ) '' Ici 0 := by
    rintro ⟨x, hx, hxe⟩
    rw [← hy₀e] at hxe
    have := Complex.ofReal_injective hxe
    have hx0 : (0 : ℝ) ≤ x := hx
    linarith [hy₀.2]
  have hmem : γ t₀ ∈ closure (range γ ∩ H) := by
    rcases hcl ⟨t₀, rfl⟩ with (h | h) | h
    · exact h
    · exact absurd h ht₀F
    · exact absurd h hnot0
  -- pull back through the closed embedding
  have himg : range γ ∩ H = γ '' {t | γ t ∈ H} := by
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, hz⟩; exact ⟨t, hz, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, rfl⟩, ht⟩
  rw [himg, he.closure_image_eq] at hmem
  obtain ⟨t', ht', htt'⟩ := hmem
  have htt : t' = t₀ := hγ.2.1 htt'
  rw [htt] at ht'
  obtain ⟨t, htI, htH⟩ := mem_closure_iff.1 ht' (Ioo lo hi) isOpen_Ioo ht₀
  have htS : γ t ∈ S := hIK (Ioo_subset_Icc_self htI)
  obtain ⟨y, -, hye⟩ := htS
  have hH : 0 < (γ t).im := htH
  rw [← hye, Complex.ofReal_im] at hH
  exact lt_irrefl _ hH

/-! ### Ordinary pieces are adherent to their points in `ℍ` -/

/-- **A regular piece read in a good chart is adherent to its points in `ℍ`, unless it is a single point.** -/
theorem tipSet_adherent {c : Chart} (hc : HasProperBdryExt c) (hcc : c.IsConformal) (hcH : ∀ z ∈ H, c.2.1 z ∈ H)
    {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (h : PieceRegular W S) :
    c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ⊆
        closure (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ∩ H) ∨
      (c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S).Subsingleton := by
  obtain ⟨f, C, hf, -⟩ := hc
  obtain ⟨hW0, hWc, α, hα, -⟩ := h
  have hWc' : ContinuousOn W {s | (s : ℝ≥0∞) < S} := hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα hWc' hW0 ht
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)]
  have hfc : ContinuousOn f Hbar := continuousOn_of_tendsto hf
  have hfH : MapsTo f H H := fun z hz => by rw [Lf.eqOn_readout hcc hf hz]; exact hcH z hz
  rcases eq_or_ne S 0 with hS0 | hS0
  · right
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} = {0} := by
      ext t
      simp only [hS0, mem_ofPred_eq, nonpos_iff_eq_zero, ENNReal.coe_eq_zero, mem_singleton_iff]
    rw [hset, image_singleton, image_singleton]
    exact subsingleton_singleton
  · left
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    -- a finite positive horizon `S' ≥ t` inside `[0, S]`
    obtain ⟨S', hS'S, hS'0, htS'⟩ : ∃ S' : ℝ≥0, (S' : ℝ≥0∞) ≤ S ∧ 0 < S' ∧ t ≤ S' := by
      rcases eq_or_ne S ⊤ with hSt | hSt
      · exact ⟨t + 1, hSt ▸ le_top, add_pos_of_nonneg_of_pos zero_le one_pos, le_add_of_nonneg_right zero_le⟩
      · refine ⟨S.toNNReal, ENNReal.coe_toNNReal_le_self, ?_, ?_⟩
        · exact ENNReal.toNNReal_pos hS0 hSt
        · rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hSt]; exact ht
    have hfαc : ContinuousOn (fun t => f (α t)) {t : ℝ≥0 | t ≤ S'} := by
      refine hfc.comp (hα.2.1.mono fun s (hs : s ≤ S') => ?_) fun s (hs : s ≤ S') => hαH s ?_
      · show (s : ℝ≥0∞) ≤ S; exact (ENNReal.coe_le_coe.2 hs).trans hS'S
      · exact (ENNReal.coe_le_coe.2 hs).trans hS'S
    have hmem := Lf.mem_closure_image_inter_H hα hWc' hW0 hS'S hS'0 hfαc hfH htS'
    refine closure_mono (inter_subset_inter_left _ ?_) hmem
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨α s, ⟨s, (ENNReal.coe_le_coe.2 hs).trans hS'S, rfl⟩, rfl⟩

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Every recorded piece of a regular run is adherent to its points in `ℍ`, unless it is a single point.** -/
theorem pieces_run_adherent (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    ∀ p ∈ (ExplState.run κ b jumps spec D n).1,
      p.1.tipSet p.2.1 p.2.2 ⊆ closure (p.1.tipSet p.2.1 p.2.2 ∩ H) ∨ (p.1.tipSet p.2.1 p.2.2).Subsingleton := by
  induction n with
  | zero =>
    intro p hp
    simp [ExplState.run, ExplState.init] at hp
  | succ n ih =>
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · rw [pieces_run_succ_of_noLaunch spec D hl]
      exact ih
    · have hr := hreg n c θ hl
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      intro p hp'
      rcases List.mem_append.1 hp' with hq | hq
      · exact ih p hq
      · rw [List.mem_singleton] at hq
        subst hq
        have hgood := (isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hreg n).1
        have hdom := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) spec D hreg n
          (Lx.stStatus_ne_done_of_launches spec D hl)
        have hcH : ∀ z ∈ H, (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 z ∈ H := fun z hz => by
          have hz' : (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 z ∈
              (ExplState.run κ b jumps spec D n).2.2.2.2.1.2.1 '' H := mem_image_of_mem _ hz
          rw [hdom.image_eq] at hz'
          exact hz'.1
        exact tipSet_adherent hgood hdom.isConformal hcH hr

/-- **A regular run's physical set is adherent to its points in `ℍ`** up to a finite set (the root and the one-point
pieces) and the real connectors. -/
theorem physSet_subset_adherent (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) :
    ∃ F : Set ℂ, F.Finite ∧ ExplState.physSet κ b jumps spec D ⊆
      closure (ExplState.physSet κ b jumps spec D ∩ H) ∪ F ∪
        ⋃ a ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1, ((↑) : ℝ → ℂ) '' a := by
  set s := ExplState.run κ b jumps spec D spec.2.2.length with hs
  classical
  refine ⟨{(spec.1 : ℂ)} ∪ ⋃ p ∈ {p | p ∈ s.1 ∧ (p.1.tipSet p.2.1 p.2.2).Subsingleton}, p.1.tipSet p.2.1 p.2.2,
    (finite_singleton _).union ((s.1.finite_toSet.subset fun p hp => hp.1).biUnion fun p hp => hp.2.finite), ?_⟩
  have hphys : ExplState.physSet κ b jumps spec D =
      {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a := rfl
  have hpieces := pieces_run_adherent (κ := κ) (b := b) (jumps := jumps) spec D hreg spec.2.2.length
  intro z hz
  rw [hphys] at hz
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inr (Or.inl hz))
  · obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    rcases hpieces p hp with h | h
    · refine Or.inl (Or.inl (closure_mono (inter_subset_inter_left _ ?_) (h hzp)))
      intro w hw
      rw [hphys]
      exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨p, hp, hw⟩))
    · exact Or.inl (Or.inr (Or.inr (mem_iUnion₂.2 ⟨p, ⟨hp, h⟩, hzp⟩)))
  · exact Or.inr hz

/-! ### The lower walk -/

/-- **Almost surely the completed lower walk is adherent to its points in `ℍ`** up to a finite set and `[0, ∞)` (its
root, one-point pieces and connectors), under GW1's ambient bound. -/
theorem ae_lowerWalkSet_subset_adherent (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, ∃ F : Set ℂ, F.Finite ∧ lowerWalkSet κ b jumps E ω ⊆
      closure (lowerWalkSet κ b jumps E ω ∩ H) ∪ F ∪ ((↑) : ℝ → ℂ) '' Ici 0 := by
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  have hlwp : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  filter_upwards [hER lw hlwp, Lv.ae_arcs_subset_Ici hκ hb hh (hE' lw hlwp) (hreg' lw) hamb, hrun lw hlwp]
    with ω hr harcs hrω
  have hP : ∀ (j : ℕ) (c : Chart) (θ' : ℝ), (ExplState.run κ b jumps lw (fun i => E lw i ω) (j + 1)).2.2.2.1 j =
      some (c, θ') → PieceRegular (E lw j ω).1 (min (instrTime lw j) (E lw j ω).2) :=
    fun j c θ' hl' => hr j θ' _ c (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨F, hF, hsub⟩ := physSet_subset_adherent lw (fun i => E lw i ω) hP
  refine ⟨F, hF, fun z hz => ?_⟩
  rcases hsub hz with h | h
  · exact Or.inl h
  · obtain ⟨a, ha, hza⟩ := mem_iUnion₂.1 h
    rw [← hrω] at ha
    obtain ⟨x, hx, rfl⟩ := hza
    exact Or.inr ⟨x, harcs _ a ha hx, rfl⟩

/-- **`LowerWalkLeftFreeStatement` from the walk's properness** (`RightWalkProperRegStatement`, Lemma GW1) and
Theorem 1.3 at universe `0` (GW1's ambient bound, for the connectors). -/
theorem lowerWalkLeftFreeStatement_of_rightWalkProper (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (h130 : Exist.Theorem13Statement.{0}) : Lh.LowerWalkLeftFreeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER a
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 h130
  have hamb := (GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ').1
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER,
    ae_lowerWalkSet_subset_adherent hκ hb hh hE hER hamb] with ω hγω hFω
  obtain ⟨γ, hγ, -, hγr⟩ := hγω
  obtain ⟨F, hF, hsub⟩ := hFω
  have hcl : range γ ⊆ closure (range γ ∩ H) ∪ F ∪ ((↑) : ℝ → ℂ) '' Ici 0 := by
    rw [hγr]; exact hsub
  obtain ⟨y, hy, hyγ⟩ := exists_lt_notMem_range hγ hF hcl a
  refine ⟨y, hy, fun hyW => hyγ ?_⟩
  rw [hγr]
  exact hyW

/-- **`LowerWalkLeftFreeStatement` from Theorems 1.2–1.3** (both universes; ruling R48). -/
theorem lowerWalkLeftFreeStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : Lh.LowerWalkLeftFreeStatement.{u} :=
  lowerWalkLeftFreeStatement_of_rightWalkProper (Wire.walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀).1
    h13₀

/-- **SB2(2)'s combined target (R104a) from the later launches** and Theorems 1.2–1.3: PROVE-T14-SB2LOW's
`Lh.sb2LowerLaunchLiftStatement_of_succ` with its input `LowerWalkLeftFreeStatement` discharged. -/
theorem sb2LowerLaunchLiftStatement_of_succ' (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hs : Lh.SB2LowerLaunchLiftSuccStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  Lh.sb2LowerLaunchLiftStatement_of_succ h13 h13₀ (lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀) hs

end InteractingSLE.Theorem14.SB.Lk
