/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfLive

/-!
# F2b′'s root objects and their good events

Packet PROVE-AUX61-NOJUMP (round 22, the root variant, D51/D57/D63). **`RootObj`**: the objects of F2b′'s root at a
flow stage `ℓ` of B, as `Nc.StageObj` at the tails:

* the retained hull `K` (`Nc.exists_retHull`), the chart offset `x₀ = entryRead (fill K) R` read at
  `R = max (A ∩ ℝ)` (`exists_realMax_lineC0`), the B-time-0 event `FB` (`exists_rootLive`), a regular version `Ê` of
  B's family;
* a good event `Eg₀` of the completed line σ-algebra at B-time `0`, inside `FB` and containing almost every point of
  it, with the B-time-0 facts `Root0At`;
* a measurable event `Ent` that is, on `Eg₀`, the entrance of B at `R` before B's lifetime (PROVE-SB2-CONDFIN's
  `Cn.exists_measurableSet_rootTime_le`).

The root's good event is `Eg = Eg₀ ∩ Ent`: there `ℓ = relOff`, the root is not a zero root (`root_of_entr`), and the
root's geometry holds for the offset `x₀` (**`RootObj.geo`**, `rootGeo_of_entryRead`); almost surely it is the root
event (**`RootObj.ae_mem_Eg_iff`**). **`exists_rootObj`**: such objects exist (Theorems 1.2–1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets Sec7.PocketTraversal Lk LuM
  Nc GW1Bookkeep

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **F2b′'s root facts at a B-time-0 good sample.** -/
structure Root0At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    Prop where
  walk : WalkGood κ b jumps E u l k ω
  stage : ω ∈ stageEvent κ b jumps E u l k ℓ
  offle : ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
  pos : bLife b jumps E ℓ ω ≠ 0
  fill : fillH (K ω) = fillH (retX κ b jumps E u l k ℓ ω)
  retc : IsCompact (retX κ b jumps E u l k ℓ ω)
  retH : ∀ z ∈ retX κ b jumps E u l k ℓ ω, 0 ≤ z.im
  hull : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω))
  stfill : stageFill κ b jumps E u l k ℓ ω = fillH (retX κ b jumps E u l k ℓ ω)
  runw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
    ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n
  runu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
    ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n
  agree : Nv.AgreeAt κ (-(Real.pi / 2)) b jumps (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
    fun j => Ê j ω
  x0 : x₀ ω = entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω))

variable (P) in
/-- **F2b′'s root objects** and their good events. -/
structure RootObj (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) where
  K : Ω → Set ℂ
  x₀ : Ω → ℝ
  FB : Set Ω
  Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞
  Eg₀ : Set Ω
  Ent : Set Ω
  hK : @Restart.IsDyadicHitMeasurable Ω (lineC0 P κ b jumps E u l k ℓ) K
  hKc : ∀ ω, IsCompact (K ω)
  hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)
  hx₀ : Measurable[lineC0 P κ b jumps E u l k ℓ] x₀
  hFB : MeasurableSet[lineSigma0 κ b jumps E u l k ℓ] FB
  hFBae : ∀ᵐ ω ∂P, (ω ∈ FB ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
    ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∧
    0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
  hÊm : ∀ j, Measurable (Ê j)
  hÊreg : ∀ j ω, IsRegularDriver (Ê j ω)
  hÊP : ∀ ω, RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) fun j => Ê j ω
  hEg₀ : MeasurableSet[lineC0 P κ b jumps E u l k ℓ] Eg₀
  hEg₀FB : Eg₀ ⊆ FB
  hEg₀ae : ∀ᵐ ω ∂P, ω ∈ FB → ω ∈ Eg₀
  good₀ : ∀ ω ∈ Eg₀, Root0At κ b jumps E u l k ℓ K x₀ Ê ω
  hEnt : MeasurableSet Ent
  ent : ∀ ω ∈ Eg₀, (ω ∈ Ent ↔ Nd.entrR κ b jumps E u l k ℓ ω < bLife b jumps E ℓ ω)
  shM : Ω → ℝ≥0∞
  hshM : Measurable shM
  shM_eq : ∀ ω ∈ Eg₀, shM ω = Nd.entrR κ b jumps E u l k ℓ ω

namespace RootObj

variable {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
  (S : RootObj P κ b jumps E u l k ℓ)

/-- **The root's good event.** -/
def Eg : Set Ω := S.Eg₀ ∩ S.Ent

theorem measurableSet_Eg : MeasurableSet S.Eg := S.hEg₀.1.inter S.hEnt

theorem Eg_subset_Eg₀ : S.Eg ⊆ S.Eg₀ := inter_subset_left

theorem entr_lt {ω : Ω} (hω : ω ∈ S.Eg) : Nd.entrR κ b jumps E u l k ℓ ω < bLife b jumps E ℓ ω :=
  (S.ent ω hω.1).1 hω.2

/-- On the root's good event, `ℓ = relOff` and the root is not a zero root. -/
theorem root {ω : Ω} (hω : ω ∈ S.Eg) :
    relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
      ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) :=
  root_of_entr (S.good₀ ω hω.1).walk (S.good₀ ω hω.1).stage.2 (S.good₀ ω hω.1).offle (S.entr_lt hω)

/-- **The root's geometry on its good event**, for the offset `x₀`. -/
theorem geo {ω : Ω} (hω : ω ∈ S.Eg) : RootGeo κ b jumps E u l k ℓ ω (S.x₀ ω) :=
  rootGeo_of_entryRead (S.good₀ ω hω.1).walk (S.good₀ ω hω.1).stage.2 (S.root hω).1 (S.entr_lt hω)
    (S.good₀ ω hω.1).fill (S.good₀ ω hω.1).x0

/-- The root's good event lies in the root event. -/
theorem Eg_subset_rootEv : S.Eg ⊆ Ne.rootEv κ b jumps E u l k ℓ := fun ω hω =>
  ⟨(S.good₀ ω hω.1).stage, (S.root hω).1, (S.root hω).2, S.entr_lt hω⟩

/-- **Almost surely the root's good event is the root event.** -/
theorem ae_mem_Eg_iff : ∀ᵐ ω ∂P, (ω ∈ S.Eg ↔ ω ∈ Ne.rootEv κ b jumps E u l k ℓ) := by
  filter_upwards [S.hFBae, S.hEg₀ae] with ω hF hg
  refine ⟨fun hω => S.Eg_subset_rootEv hω, fun hr => ?_⟩
  have hpos : 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 :=
    lt_of_le_of_lt zero_le hr.2.2.2
  have hFB : ω ∈ S.FB := hF.2 ⟨hr.1, hr.2.1.ge, hpos⟩
  have h0 := hg hFB
  exact ⟨h0, (S.ent ω h0).2 hr.2.2.2⟩

end RootObj

/-- **F2b′'s root objects exist** (Theorems 1.2–1.3). -/
theorem exists_rootObj (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    Nonempty (RootObj P κ b jumps E u l k ℓ) := by
  classical
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  set θ : ℝ := -(Real.pi / 2) with hθ
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps θ true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  set Ew := StagedReg.regFam E w with hEwdef
  -- the σ-algebras
  have hcap := WalkSide.pastSigma_capSpec_le (κ := κ) (b := b) (jumps := jumps) Ew hℓ.le hwℓ (0 : ℚ≥0)
  rw [NNRat.cast_zero] at hcap
  have h𝒢 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' su hsu).2.1 k) (hcap.trans ((hE' w hw).2.1 (ℓ + 1)))
  have h𝒢C : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ := le_inf h𝒢 (le_aeSigma _ P)
  -- the components
  obtain ⟨K, G₁, hKm, hKc, hKp, -, hG₁ae, hG₁⟩ := exists_retHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ
    k ℓ hℓ hwℓ hu₀
  have hgood := ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  obtain ⟨FB, hFBm, hFBae⟩ := exists_rootLive hb hE hER hu hlθ k ℓ hℓ hwℓ hgood
  obtain ⟨Ê, GÊ, hÊm, hÊreg, hÊP, -, hGÊn, hGÊ⟩ := Nv.exists_regular_version (κ := κ) (θ := θ)
    (hE w hw).1 (hER w hw)
  have hGÊae : ∀ᵐ ω ∂P, ω ∈ GÊ := by rw [ae_iff]; exact hGÊn
  obtain ⟨Rt, hRtm, hRt⟩ := exists_realMax_lineC0 hb hE hER hlθ k ℓ hℓ hwℓ
  -- the offset
  set x₀ : Ω → ℝ := fun ω => entryRead (fillH (K ω)) (Rt ω) with hx₀def
  have hx₀m : Measurable[lineC0 P κ b jumps E u l k ℓ] x₀ := measurable_entryRead hKm hKc hKp hRtm
  -- the entrance events
  choose S hSm hS using fun q : ℚ≥0 => Cn.exists_measurableSet_rootTime_le (P := P) (k := k) (ℓ := ℓ) hb
    (hE su hsu) (hER su hsu) (hE w hw) (hER w hw) (q : ℝ≥0)
  have hLm : Measurable fun ω => (E w ℓ ω).2 := measurable_snd.comp ((hE w hw).1 ℓ)
  set Ent : Set Ω := ⋃ q : ℚ≥0, S q ∩ {ω | (((q : ℝ≥0) : ℝ≥0∞)) < (E w ℓ ω).2} with hEntdef
  have hEntm : MeasurableSet Ent :=
    MeasurableSet.iUnion fun q => (hSm q).inter (measurableSet_lt measurable_const hLm)
  -- the good event
  have hall : ∀ᵐ ω ∂P, (ω ∈ FB ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      ℓ ≤ relOff κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) ∧
      0 < (E w ℓ ω).2)) ∧
      (ω ∈ Lu.upperLaunchSet κ b jumps E u l k → WalkGood κ b jumps E u l k ω) ∧
      ((ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G₁) ∧
      (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
      (∀ n, ExplState.run κ b jumps su (fun j => StagedReg.regFam E su j ω) n =
        ExplState.run κ b jumps su (fun j => E su j ω) n) ∧ ω ∈ GÊ ∧
      Rt ω = realMax (upperPrefix κ b jumps E u l k ω) ∧
      ∀ q : ℚ≥0, (Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔ ω ∈ S q) := by
    filter_upwards [hFBae, hgood, hG₁ae, hrun' w hw, hrun' su hsu, hGÊae, hRt, ae_all_iff.2 hS] with ω h1 h2 h3 h4
      h5 h6 h7 h8
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  obtain ⟨G, hGae, hGm, hGsub⟩ := hall.exists_measurable_mem
  have hG0 : MeasurableSet[lineC0 P κ b jumps E u l k ℓ] G :=
    ⟨hGm, ⟨univ, @MeasurableSet.univ Ω (lineSigma0 κ b jumps E u l k ℓ), ae_eq_univ.2 (mem_ae_iff.1 hGae)⟩⟩
  -- the measurable entrance time
  set shM : Ω → ℝ≥0∞ := fun ω => ⨅ q : ℚ≥0, if ω ∈ S q then (((q : ℝ≥0) : ℝ≥0∞)) else ⊤ with hshMdef
  have hshMm : Measurable shM :=
    Measurable.iInf fun q => Measurable.ite (hSm q) measurable_const measurable_const
  have hrt : ∀ ω ∈ FB ∩ G, Cm.rootTime κ b jumps E u l k ℓ ω = Nd.entrR κ b jumps E u l k ℓ ω := by
    rintro ω ⟨hωF, hωG⟩
    obtain ⟨h1, -, -, -, -, -, -, -⟩ := hGsub ω hωG
    obtain ⟨hst, -, -⟩ := h1.1 hωF
    unfold Cm.rootTime Nd.entrR
    rw [if_pos hst.2]
  have hshM_eq : ∀ ω ∈ FB ∩ G, shM ω = Nd.entrR κ b jumps E u l k ℓ ω := by
    intro ω hω
    obtain ⟨-, -, -, -, -, -, -, h8⟩ := hGsub ω hω.2
    rw [← hrt ω hω]
    set τ := Cm.rootTime κ b jumps E u l k ℓ ω with hτ
    have hq : ∀ q : ℚ≥0, (if ω ∈ S q then (((q : ℝ≥0) : ℝ≥0∞)) else ⊤) =
        if τ ≤ ((q : ℝ≥0) : ℝ≥0∞) then (((q : ℝ≥0) : ℝ≥0∞)) else ⊤ := fun q => by
      by_cases hs : ω ∈ S q
      · rw [if_pos hs, if_pos ((h8 q).2 hs)]
      · rw [if_neg hs, if_neg fun h' => hs ((h8 q).1 h')]
    simp only [hshMdef, hq]
    refine le_antisymm ?_ (le_iInf fun q => by split_ifs with h' <;> simp [h'])
    refine le_of_forall_gt fun c hc => ?_
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    have hqq : ((q.toNNRat : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      have h : ((q.toNNRat : ℚ) : ℝ) = (q : ℝ) := by rw [Rat.coe_toNNRat q hq0]
      rw [← h]
      norm_cast
    refine lt_of_le_of_lt (iInf_le _ q.toNNRat) ?_
    rw [if_pos (by rw [hqq]; exact hq1.le), hqq]
    exact hq2
  refine ⟨⟨K, x₀, FB, Ê, FB ∩ G, Ent, hKm, hKc, hKp, hx₀m, hFBm, hFBae, hÊm, hÊreg, hÊP,
    (h𝒢C _ hFBm).inter hG0, inter_subset_left, ?_, ?_, hEntm, ?_, shM, hshMm, hshM_eq⟩⟩
  · filter_upwards [hGae] with ω hω hF
    exact ⟨hF, hω⟩
  · rintro ω ⟨hωF, hωG⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := hGsub ω hωG
    obtain ⟨hst, hoff, hpos⟩ := h1.1 hωF
    have hg := h2 hst.1
    obtain ⟨-, hc, hH, hhull, hfill, hsf⟩ := hG₁ ω (h3 hst.2)
    have hx0 : x₀ ω = entryRead (fillH (K ω)) (realMax (upperPrefix κ b jumps E u l k ω)) := by
      simp only [hx₀def, h7]
    exact ⟨hg, hst, hoff, pos_iff_ne_zero.1 hpos, hfill, hc, hH, hhull, hsf, h4, h5, hGÊ ω h6, hx0⟩
  · rintro ω ⟨hωF, hωG⟩
    obtain ⟨h1, -, -, -, -, -, -, h8⟩ := hGsub ω hωG
    obtain ⟨hst, -, -⟩ := h1.1 hωF
    have hrt : Cm.rootTime κ b jumps E u l k ℓ ω = Nd.entrR κ b jumps E u l k ℓ ω := by
      unfold Cm.rootTime Nd.entrR
      rw [if_pos hst.2]
    simp only [hEntdef, mem_iUnion, mem_inter_iff, mem_setOf_eq, ← h8, hrt]
    constructor
    · rintro ⟨q, hq, hqL⟩
      exact lt_of_le_of_lt hq hqL
    · intro hlt
      obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      have hqq : ((q.toNNRat : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        congr 1
        have h : ((q.toNNRat : ℚ) : ℝ) = (q : ℝ) := by rw [Rat.coe_toNNRat q hq0]
        rw [← h]
        norm_cast
      refine ⟨q.toNNRat, ?_, ?_⟩
      · rw [hqq]; exact hq1.le
      · rw [hqq]; exact hq2

end InteractingSLE.Theorem14.SB.Nf
