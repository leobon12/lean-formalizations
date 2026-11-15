/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineS
import InteractingSLE.Spec.Supplement.SB2DrvLineUnion
import InteractingSLE.Spec.Supplement.SB2FinHull
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# SB2(1)'s (S) line sets: the clopen geometry on the live cell

Packet PROVE-T14-SB2DRV (round 6). For the (S) line set `D.lineS A' T` (the fill of the retained prefix union the fill
of the capped upper flow up to `max(T, T_L)`), almost surely on the live cell `{a T < thr}` of a type cell, the chart
image `c(ℍ \ K_{a T})` of the complement of the relative hull is a clopen part of `ℍ \ B T`:

* **`ae_absPart_subset_image`**, **`ae_image_inter_H_subset_absPart`**: the flow part of the absolute union lies in
  `η([0, max(T, T_L)])`, and contains `η([0, T]) ∩ ℍ` below the flow lifetime;
* `prefixPhysSet_inter_H`, so the fill of the walk version is the fill of the retained prefix;
* **`ae_lineS_clopen`**: the clopen geometry. Up to `T_L` (`a T = 0`) the chart image is the whole chart domain
  `ℍ \ fill(A)`, which misses the fill of the erased flow (`sb2ErasedAvoidStatement`, a preconnected unbounded set
  missing the flow); after `T_L` the hull clauses `hullIn`/`hullFr` of the relative chain of the version's chain
  record at `T` (shifted coordinates), with the flow alive at `T` (the clause `alive` of `SB2LineVersionR`).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The flow part of the absolute union lies in the flow up to `max(T, T_L)`.** -/
theorem ae_absPart_subset_image : ∀ᵐ ω ∂P, ω ∈ D.event → ∀ T : ℝ≥0∞,
    D.absPart T ω ⊆ η ω '' {σ : ℝ≥0 | (σ : ℝ≥0∞) ≤
      max T (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)))} := by
  filter_upwards [D.version, D.Lp_eq, D.ae_mem_event_iff] with ω hv hL hev hω T z hz
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hω
  have hz' : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [EntranceUnion.point, hL hl]
  rw [absPart, limSet_eq] at hz
  rcases hz with hz | hz
  · exact absurd hz (notMem_empty z)
  obtain ⟨n, hzn⟩ := mem_iUnion.1 hz
  obtain ⟨⟨s', hs', rfl⟩, -⟩ := hzn
  refine ⟨capTime (n : ℝ≥0) (ζ ω) s', ?_, (hv n s').symm⟩
  by_cases hσT : ((capTime (n : ℝ≥0) (ζ ω) s' : ℝ≥0) : ℝ≥0∞) ≤
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
  · exact hσT.trans (le_max_right _ _)
  push Not at hσT
  have hσζn := coe_capTime_le (ζ := ζ ω) (n : ℝ≥0) s'
  have hTn : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (n : ℝ≥0∞) :=
    hσT.trans_le (hσζn.trans (min_le_right _ _))
  have hhit := (hitQ_capped_eq (γ := η ω) (ζ := ζ ω) (γc := fun n => D.ηc n ω) (n := n) (D.paths.cont n ω) (hv n)
    (z := D.point ω) (by rw [hz']; exact hT) (by rw [hz']; exact hTn)).1
  rw [hz'] at hhit
  have hs'le : (s' : ℝ≥0∞) ≤ max T (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))) := by
    have := hs'
    simp only [mem_ofPred_eq, maxRule] at this
    rw [hz', hhit] at this
    exact this
  exact (ENNReal.coe_le_coe.2 (capTime_le_self _ _)).trans hs'le

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Below the flow lifetime, the flow part of the absolute union contains the flow up to `T` in `ℍ`.** -/
theorem ae_image_inter_H_subset_absPart : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
    η ω '' Icc 0 T ∩ H ⊆ D.absPart (T : ℝ≥0∞) ω := by
  filter_upwards [D.version] with ω hv T hTζ z hz
  obtain ⟨⟨s, hs, rfl⟩, hzH⟩ := hz
  obtain ⟨n, hn⟩ := exists_nat_gt (T : ℝ)
  have hsn : (s : ℝ) ≤ n := le_trans (NNReal.coe_le_coe.2 hs.2) hn.le
  have hsn' : (s : ℝ≥0∞) ≤ min (ζ ω) ((n : ℝ≥0) : ℝ≥0∞) := by
    refine le_min ((ENNReal.coe_le_coe.2 hs.2).trans hTζ.le) (ENNReal.coe_le_coe.2 ?_)
    rw [← NNReal.coe_le_coe]
    simpa using hsn
  have hcap : capTime (n : ℝ≥0) (ζ ω) s = s := capTime_of_le hsn'
  rw [absPart, limSet_eq]
  refine Or.inr (mem_iUnion.2 ⟨n, ⟨s, ?_, ?_⟩, hzH⟩)
  · show (s : ℝ≥0∞) ≤ maxRule (T : ℝ≥0∞) (D.point ω) (pathCoord (D.ηc n ω))
    exact (ENNReal.coe_le_coe.2 hs.2).trans (le_max_left _ _)
  · rw [hv n s, hcap]

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The retained prefix in `ℍ` is the walk's stage set. -/
theorem prefixPhysSet_inter_H (ω : Ω) :
    SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) ∩ H =
    WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω := by
  refine Subset.antisymm ?_ fun z hz => ⟨stageSet_subset_prefixPhysSet ω hz, hz.2⟩
  rintro z ⟨(hz | hz) | hz, hzH⟩
  · rw [mem_singleton_iff] at hz
    subst hz
    have : (0 : ℝ) < (((boundaryWalkSpec b jumps (-(Real.pi / 2)) true).1 : ℝ) : ℂ).im := hzH
    simp at this
  · exact ⟨hz, hzH⟩
  · obtain ⟨a, -, x, -, rfl⟩ := mem_iUnion₂.1 hz
    have : (0 : ℝ) < ((x : ℝ) : ℂ).im := hzH
    simp at this

end EntranceUnion

/-! ### The clopen geometry -/

section Clopen

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The clopen geometry of the (S) line set**: almost surely on the live cell at `t`, the chart image of the
complement of the relative hull lies in `ℍ \ B t` and is relatively closed there. -/
theorem ae_lineS_clopen (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D) {w : WordType}
    (hw : w ∈ I.types) {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ lineLive Vd w t →
      chartImage (I.chart ω) (relHull Vd t ω) ⊆ H \ D.lineS A' (t : ℝ≥0∞) ω ∧
        IsOpen ((H \ D.lineS A' (t : ℝ≥0∞) ω) \ chartImage (I.chart ω) (relHull Vd t ω)) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hwp := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hwp
  filter_upwards [Vd.chain w hw t, Vd.alive w hw t, I.chart_eq, D.Lp_eq,
    ae_verChart_eq_runChart hR (HP.drivers_regular _) (k + 1), hR.ae_pieceRegular,
    sb2ErasedAvoidStatement κ b jumps P h E k u ψ η ζ HP, D.ae_mem_event_iff, hA'ae,
    EntranceUnion.ae_isBounded_stageSet HP, D.ae_absPart_subset_range t, D.ae_absPart_subset_image,
    D.ae_image_inter_H_subset_absPart]
    with ω hch hal hce hL hver hpr hav hev hA hbA hbP hup hlow hlive
  have hcell : ω ∈ seedCell κ ψ I.word D.event w := hlive.1
  have hevω : ω ∈ D.event := hcell.1.1
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hevω
  have hT : firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω := (hev hl).1 hevω
  have hlt := hlive.2
  have htζ : (t : ℝ≥0∞) < ζ ω := hal hcell hlt
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w', ηw, htS, ⟨-, -, -, -, himgp⟩, -, ⟨-, -, -, -, hTL, -, -, -⟩, hagree,
    ⟨-, hchainAll, -⟩, -, ⟨hWWr, ha0, ha⟩⟩ := hch hcell hlt
  -- the charts and the domains
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hDrun : ((I.chart ω).dom : Set ℂ) =
      (((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)).2.2.2.2.1).dom : Set ℂ) := by
    show ((((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)).dom : Set ℂ)) = _
    rw [Chart.dom_recenter, hver]
    rfl
  have hchart : I.chart ω = (launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω) :=
    hce hl
  have hDl : ((I.chart ω).dom : Set ℂ) = ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) := by
    rw [hchart, Chart.dom_recenter]
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  set FA : Set ℂ := fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) with hFAdef
  have hdomA : ((I.chart ω).dom : Set ℂ) = H \ FA := by
    rw [hDrun]
    exact hD.1.coe_dom.trans hD.2.1
  have hpc := Lx.isCompact_prefixPhysSet_run (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1) hnd
  have hcf := isConformal_chart I ω
  have hdomO : IsOpen ((I.chart ω).dom : Set ℂ) := (I.chart ω).dom.isOpen
  have hzdom : ∀ z, z ∈ H → z ∉ FA → z ∈ ((I.chart ω).dom : Set ℂ) := fun z hz hzF => by
    rw [hdomA]
    exact ⟨hz, hzF⟩
  -- the two fills of the line set
  have hbA' : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA hl
  have hFA : fillH (cptClosure A' ω) = FA := by
    rw [cptClosure, ite_eq_left hbA', Sec7.SideHeight.fillH_closure, hA, ← EntranceUnion.prefixPhysSet_inter_H,
      Sec7.SideHeight.fillH_inter_H]
  obtain ⟨N, hN⟩ := hbP hevω
  have hbP' : Bornology.IsBounded (D.absPart (t : ℝ≥0∞) ω) :=
    ((isCompact_Icc.image (D.paths.cont N ω)).isBounded).subset hN
  have hFP : fillH (cptClosure (D.absPart (t : ℝ≥0∞)) ω) = fillH (D.absPart (t : ℝ≥0∞) ω) := by
    rw [cptClosure, ite_eq_left hbP', Sec7.SideHeight.fillH_closure]
  have hS : D.lineS A' (t : ℝ≥0∞) ω = FA ∪ fillH (D.absPart (t : ℝ≥0∞) ω) := by
    rw [EntranceUnion.lineS, ite_eq_left hevω, hFA, hFP]
  have hO := D.isOpen_H_sdiff_lineS A' (t : ℝ≥0∞) ω
  rw [hS] at hO ⊢
  by_cases htL : (t : ℝ) ≤ tL
  · -- up to `T_L`: the chart image is the whole chart domain
    have hat : Vd.a t ω = 0 := ha0 t htL
    have hrel : relHull Vd t ω = ∅ := by
      unfold relHull
      rw [hat, ENNReal.toNNReal_zero, NNReal.coe_zero]
      exact QuantumZipper.RS.fwdHull_zero_eq_empty ((Vd.W_cont ω).comp continuous_real_toNNReal)
    have hCI : chartImage (I.chart ω) (relHull Vd t ω) = ((I.chart ω).dom : Set ℂ) := by
      ext z
      rw [mem_chartImage_iff hcf, hrel]
      simp
    rw [hCI]
    refine ⟨fun z hz => ⟨hcf.dom_subset hz, ?_⟩, ?_⟩
    · rintro (hzA | hzP)
      · rw [hdomA] at hz
        exact hz.2 hzA
      · have hdisj : Disjoint ((I.chart ω).dom : Set ℂ) (D.absPart (t : ℝ≥0∞) ω) := by
          rw [Set.disjoint_left]
          intro y hy hyP
          obtain ⟨σ, hσ, rfl⟩ := hup hevω (t : ℝ≥0∞) hyP
          have htT : (t : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) := by
            rw [← hTL]
            exact_mod_cast htL
          have hσ' : (σ : ℝ≥0∞) ≤ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) :=
            hσ.trans (max_le htT le_rfl)
          rw [hDl] at hy
          exact Set.disjoint_left.1 (hav hl) hy ⟨σ, le_min (hσ'.trans hT.le) hσ', rfl⟩
        have hdcl : ((I.chart ω).dom : Set ℂ) ⊆ H \ closure (D.absPart (t : ℝ≥0∞) ω) := fun y hy =>
          ⟨hcf.dom_subset hy, fun hyc => by
            obtain ⟨y', hy'⟩ := (_root_.mem_closure_iff.1 hyc) _ hdomO hy
            exact Set.disjoint_left.1 hdisj hy'.1 hy'.2⟩
        refine FinRel.notMem_fillH_of_isPreconnected hz ?_ hdcl ?_ hzP
        · rw [hdomA]
          exact HalfPlaneSep.isPreconnected_H_diff_fillH hpc.isClosed hpc.isBounded
        · rw [hdomA]
          exact HalfPlaneSep.not_isBounded_H_diff_fillH hpc.isClosed hpc.isBounded
    · have e : (H \ (FA ∪ fillH (D.absPart (t : ℝ≥0∞) ω))) \ ((I.chart ω).dom : Set ℂ) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun z hz => hz.2 ?_
        exact hzdom z hz.1.1 fun h' => hz.1.2 (Or.inl h')
      rw [e]
      exact isOpen_empty
  -- after `T_L`: the hull clauses of the relative chain at `t`
  push Not at htL
  set sR : ℝ := (t : ℝ) - tL with hsR
  have hs0 : 0 < sR := by rw [hsR]; linarith
  have hsS : sR < S := by rw [hsR]; linarith
  obtain ⟨-, -, -, -, -, -, hcl⟩ := hchainAll sR hs0.le hsS
  obtain ⟨hcap0, -, -, hIn, hFr⟩ := hcl sR ⟨hs0.le, le_rfl⟩
  have hcapR : ((Vd.a t ω).toNNReal : ℝ) = Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR := by
    have ha' : Vd.a t ω = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) ((t : ℝ) - tL)).toNNReal : ℝ≥0∞) :=
      ha t htL.le htS
    rw [ha', ENNReal.toNNReal_coe, Real.coe_toNNReal _ hcap0]
  have hhull : relHull Vd t ω = fwdHull Wr (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR) := by
    unfold relHull
    rw [hcapR]
    obtain ⟨T₀, hT₀a, hT₀V⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    refine ZhanGT4.A34.fwdHull_congr_of_lt hcap0 (T₀ := T₀) ?_ fun r hr => ?_
    · rw [← hcapR]
      have := ENNReal.toNNReal_lt_toNNReal (ne_top_of_lt hlt) ENNReal.coe_ne_top |>.2 hT₀a
      rw [ENNReal.toNNReal_coe] at this
      exact_mod_cast this
    · have hrV : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W
          (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω := by
        refine lt_of_lt_of_le ?_ hT₀V.le
        rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]
        exact hr.2
      show Vd.W r.toNNReal ω = Wr r
      have hW1 : Vd.W r.toNNReal ω = Wr (r.toNNReal : ℝ) := hWWr r.toNNReal hrV
      rw [hW1, Real.coe_toNNReal _ hr.1]
  have htt : tL + sR.toNNReal = t := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs0.le, hsR]
    ring
  -- the flow fill is the fill of the flow up to `t`
  have hmax : max (t : ℝ≥0∞) (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))) = t := by
    refine max_eq_left ?_
    rw [← hTL]
    exact_mod_cast htL.le
  have hFP2 : fillH (D.absPart (t : ℝ≥0∞) ω) = fillH (η ω '' Icc 0 t) := by
    refine Subset.antisymm (fillH_mono ?_) ?_
    · intro y hy
      obtain ⟨σ, hσ, rfl⟩ := hup hevω (t : ℝ≥0∞) hy
      rw [mem_ofPred_eq, hmax] at hσ
      exact ⟨σ, ⟨zero_le, ENNReal.coe_le_coe.1 hσ⟩, rfl⟩
    · rw [← Sec7.SideHeight.fillH_inter_H (η ω '' Icc 0 t)]
      exact fillH_mono (hlow t htζ)
  -- shifted coordinates
  have himgβ : β' '' Icc 0 (tL + sR.toNNReal) = (fun z : ℂ => z - (u : ℂ)) '' (η ω '' Icc 0 t) := by
    rw [htt, Set.image_image]
    exact Set.image_congr fun r hr => hagree r (lt_of_le_of_lt (NNReal.coe_le_coe.2 hr.2) htS)
  have hshift : ∀ z, z ∈ fillH (η ω '' Icc 0 t) ↔ z - (u : ℂ) ∈ fillH (β' '' Icc 0 (tL + sR.toNNReal)) := by
    intro z
    rw [himgβ, Lw.fillH_image_sub_real]
    exact (sub_left_injective.mem_set_image).symm
  have hpre : ∀ z, z ∉ FA → z - (u : ℂ) ∉ fillH (p '' Icc 0 1) := by
    intro z hzF hm
    rw [himgp, Lw.fillH_image_sub_real, sub_left_injective.mem_set_image,
      show fillH (lowerPrefix κ b jumps E (k + 1) u ω) = FA from Lw.fillH_union_real _ _] at hm
    exact hzF hm
  have hfwd : ∀ z, (Lw.shiftChart (launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).1
      (z - (u : ℂ)) = (I.chart ω).1 z := by
    intro z
    rw [Lw.shiftChart_fwd, sub_add_cancel, hchart]
    rfl
  have hsubH : ∀ z, z ∈ H → z - (u : ℂ) ∈ H := fun z hz => by
    show 0 < (z - (u : ℂ)).im
    have : 0 < z.im := hz
    simpa using this
  rw [hFP2] at hO ⊢
  rw [hhull]
  refine ⟨fun z hz => ?_, ?_⟩
  · obtain ⟨hzd, hzK⟩ := (mem_chartImage_iff hcf).1 hz
    have hzF : z ∉ FA := by
      have hzd' : z ∈ ((I.chart ω).dom : Set ℂ) := hzd
      rw [hdomA] at hzd'
      exact hzd'.2
    refine ⟨hcf.dom_subset hzd, ?_⟩
    rintro (h1 | h1)
    · exact hzF h1
    · have h2 := hIn _ ((hshift z).1 h1) (hpre z hzF)
      rw [hfwd] at h2
      exact hzK h2
  · set C := chartImage (I.chart ω) (fwdHull Wr (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR)) with hC
    have e : (H \ (FA ∪ fillH (η ω '' Icc 0 t))) \ C = (H \ (FA ∪ fillH (η ω '' Icc 0 t))) \ closure C := by
      ext z
      constructor
      · rintro ⟨hzO, hzC⟩
        refine ⟨hzO, fun hzcl => hzC ?_⟩
        have hzF : z ∉ FA := fun h' => hzO.2 (Or.inl h')
        have hzd := hzdom z hzO.1 hzF
        refine (mem_chartImage_iff hcf).2 ⟨hzd, fun hK => ?_⟩
        have hcont : ContinuousAt (I.chart ω).1 z :=
          (hcf.differentiableOn_fwd.differentiableAt (hdomO.mem_nhds hzd)).continuousAt
        have hcl' : (I.chart ω).1 z ∈
            closure (fwdHull Wr (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR))ᶜ := by
          refine closure_mono ?_ (mem_closure_image hcont hzcl)
          rintro _ ⟨y, hy, rfl⟩
          exact ((mem_chartImage_iff hcf).1 hy).2
        have hfr : (I.chart ω).1 z ∈ frontier (fwdHull Wr (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) sR)) := by
          rw [frontier_eq_closure_inter_closure]
          exact ⟨subset_closure hK, hcl'⟩
        have h3 := hFr (z - (u : ℂ)) ⟨hsubH z hzO.1, hpre z hzF⟩ (by rw [hfwd]; exact hfr)
        exact hzO.2 (Or.inr ((hshift z).2 h3))
      · rintro ⟨hzO, hzC⟩
        exact ⟨hzO, fun h' => hzC (subset_closure h')⟩
    rw [e]
    exact hO.sdiff isClosed_closure

/-! ### The line union from the (S) line sets -/

/-- **Named input (the mean of the (S) line set)**: for every walk version `A'` of the retained prefix (in `ℍ`, exact
past-measurable avoidance events, almost surely the stage set), every local-set mean of the (S) line set at the absolute
time `t`, read in the launch chart, is the canonical mean off the relative hull, almost surely on the live cell. -/
def SB2LineSMeanStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D),
    ∀ w ∈ I.types, ∀ A' : Ω → Set ℂ, (∀ ω, A' ω ⊆ H) →
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U}) →
    (∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) →
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (D.lineS A' (t : ℝ≥0∞)) (WholeField.centredField h u₀) P g → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z

/-- **The line union input from the mean of the (S) line sets** (the sets: `D.lineS A'` for a walk version `A'`;
measurability, relative closedness, marked locality for the completed line filtration and the clopen geometry are
proved). -/
theorem sb2LineUnionStatement_of_sMean (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hS : SB2LineSMeanStatement.{u}) : SB2LineUnionStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw
  obtain ⟨hev, hopen, -⟩ := walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)
  obtain ⟨A', hA'H, hA'ae, hA'm⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps _ _ (k + 1) ω) hopen hev
  exact ⟨fun t => D.lineS A' (t : ℝ≥0∞), fun t => D.measurable_lineS HP hA'H hA'm (t : ℝ≥0∞),
    fun t ω => ⟨D.lineS_subset_H A' _ ω, D.isOpen_H_sdiff_lineS A' _ ω⟩,
    fun t => D.isHistoryAvoidanceLocal_lineFiltC HP t
      (D.isHistoryAvoidanceLocal_lineS h12p h13 HP hu₀ hA'H hA'm hA'ae t),
    fun t => ae_lineS_clopen HP I D Vd hw hA'ae t,
    fun t g hg φ => hS κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ⟩

/-- **SB2(1)'s ambient driver link from the repaired version half and the mean of the (S) line sets** (Theorems
1.2–1.3 as hypotheses, R48). -/
theorem sb2DriverLinkAmbStatement_of_versionR_sMean (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hV : SB2LineVersionRStatement.{u}) (hS : SB2LineSMeanStatement.{u}) :
    SB2DriverLinkAmbStatement.{u} :=
  sb2DriverLinkAmbStatement_of_version_union h12p h13 hV (sb2LineUnionStatement_of_sMean h12p h13 hS)

end Clopen

end InteractingSLE.Theorem14.SB.Lv
