/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KbRead
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2FbConfig
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Supplement.GB6SourceCContact

/-!
# Claim(k)'s base (GEOM2 round 12): the stage-start mean of the history `l = []`

Packet PROVE-GW2-GEOM2, round 12. STAGEMEAN's `GW2Psm.pair_root0` takes Claim(k) as its input `hclaim`: every local-set
mean of the stage-start union `B 0` pairs as the explicit stage mean at clock `0`,
`stgMeanR κ rec R a₀ 0 U₀ u₀ σa = couplingMean κ (rpath (stgDrv R a₀)) 0 U₀ (cs.1 ·) − u₀ − σa − χ · cs.lift`
(`cs = stgChart (relChart rec) R a₀`). This file proves it for the history `l = []` at the root `0`, under the
instance's readings at the sample (those of `pair_root0`'s `hread` at `l = []`, `t = 0`: success, an interior
counterflow tip at `s`, no contact before `T`, the version's driver `R` and clock `A` with the stage shape at every
time of the root piece, and the stage-start data `U₀`).

* `firstContactTime_swap` (the two contact forms of GW2 and GB6 agree);
* `chosenTrace_eq_schedTr` (the root piece's trace is the explored trace up to `T`);
* `lt_contact_root` (product-form no contact ⇒ GB6's contact form for the root piece);
* `fwdHull_root_subset` (the root piece's hulls miss the retained hull before contact);
* **`claim_base_root0`**: Claim(k) at `l = []` (root `0`).

The stage-start data `U₀` enter through the word identity `U₀ = G + (σa − specOffset κ − θ_root χ)` for every
bounded harmonic extension `G` of the counterflow's joint word (word `cw`) flowed by the version's driver to `a₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)

universe u

namespace InteractingSLE.Theorem14.GW2Kb

open GW2Omx Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 GW2JointKernel
open Supp8.Q3Rel (invHull)
open Supp8.Q3Chain (flowedData flowedJumps)

/-- **The two contact forms agree** (GW2's: the moving curve against the inverted prefix; GB6's: the inverted moving
curve against the prefix). -/
theorem firstContactTime_swap (α γ : ℝ≥0 → ℂ) (S : Set ℝ≥0) :
    firstContactTime (fun u => (α u : OnePoint ℂ)) ((fun u => sphereInv (γ u : OnePoint ℂ)) '' S) =
      firstContactTime (fun t => sphereInv (α t : OnePoint ℂ)) ((fun u => (γ u : OnePoint ℂ)) '' S) := by
  have h : ∀ t, ((α t : OnePoint ℂ) ∈ (fun u => sphereInv (γ u : OnePoint ℂ)) '' S) ↔
      (sphereInv (α t : OnePoint ℂ) ∈ (fun u => (γ u : OnePoint ℂ)) '' S) := by
    intro t
    constructor
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, ?_⟩
      have h1 := (SourceC.sphereInv_eq_iff (γ u) (α t)).1 he
      exact ((SourceC.sphereInv_eq_iff (α t) (γ u)).2 (by rw [mul_comm]; exact h1)).symm
    · rintro ⟨u, hu, he⟩
      refine ⟨u, hu, ?_⟩
      have h1 := (SourceC.sphereInv_eq_iff (α t) (γ u)).1 he.symm
      exact (SourceC.sphereInv_eq_iff (γ u) (α t)).2 (by rw [mul_comm]; exact h1)
  unfold firstContactTime
  simp only [h]

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)

/-- **The root piece's trace is the explored trace up to `T`** (on success). -/
theorem chosenTrace_eq_schedTr {ω : Ω} (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hc0 : Continuous (stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) 0 = 0)
    (hreg : IsRegularDriver (futFam c r [] a 0 ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (fun t => (futFam c r [] a 0 ω).1 t) (futFam c r [] a 0 ω).2 α) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => schedW c r [] a t ω) ⊤ η) {t : ℝ≥0} (ht : t ≤ historyTime c r []) :
    α t = η t := by
  set e := futFam c r [] a 0 ω with he
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  obtain ⟨T', hT'1, hT'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hTT' : (historyTime c r [] : ℝ) < T' := by exact_mod_cast hT'1
  have htT' : (t : ℝ) < T' := lt_of_le_of_lt (by exact_mod_cast ht) hTT'
  have hte : (t : ℝ≥0∞) < e.2 := lt_of_le_of_lt ((ENNReal.coe_le_coe.2 ht).trans hT'1.le) hT'2
  have hcont : ContinuousOn (fun q : ℝ => e.1 q.toNNReal) (Icc 0 (T' : ℝ)) := by
    refine hreg.1.comp continuous_real_toNNReal.continuousOn ?_
    intro q hq
    show ((q.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hq.2)) hT'2
  have hW : Continuous fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω := by
    rw [show (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) =
      fun q : ℝ => Gm.futureJoined c r [] a ω q.toNNReal from
        funext fun q => congrFun (GW2Rd.schedW_of_oldSuccess c r [] a hold) q.toNNReal]
    exact (Gm.continuous_futureJoined c r [] a ω).1.comp continuous_real_toNNReal
  have hW0 : GW2Rd.schedW c r [] a 0 ω = 0 := by
    rw [congrFun (GW2Rd.schedW_of_oldSuccess c r [] a hold) 0]
    exact (Gm.continuous_futureJoined c r [] a ω).2
  have h1 := hα.trace_eq hreg.1 hreg.2.1 hte
  have hWn : Continuous fun t : ℝ≥0 => GW2Rd.schedW c r [] a t ω := by
    rw [GW2Rd.schedW_of_oldSuccess c r [] a hold]
    exact (Gm.continuous_futureJoined c r [] a ω).1
  have h2 := hη.trace_eq hWn.continuousOn hW0 (ENNReal.coe_lt_top (r := t))
  rw [← h1, ← h2]
  rw [_root_.InteractingSLE.trace_eq_of_eqOn (W := fun q : ℝ => e.1 q.toNNReal)
    (W' := Ito.clampDrv (fun q : ℝ => e.1 q.toNNReal) T') t.coe_nonneg htT'
      fun q hq => (Ito.clampDrv_eqOn (W := fun q : ℝ => e.1 q.toNNReal) hq).symm]
  refine LP.trace_eq_of_eqOn_Icc (Ito.continuous_clampDrv T'.coe_nonneg hcont) hW
    (by rw [Ito.clampDrv_eqOn ⟨le_rfl, T'.coe_nonneg⟩]; simpa using hreg.2.1) (by simpa using hW0)
    t.coe_nonneg fun q hq => ?_
  have hqT : q ∈ Icc 0 (historyTime c r [] : ℝ) := ⟨hq.1, hq.2.trans (by exact_mod_cast ht)⟩
  show Ito.clampDrv (fun q : ℝ => e.1 q.toNNReal) T' q = GW2Rd.schedW c r [] a q.toNNReal ω
  rw [Ito.clampDrv_eqOn ⟨hq.1, hq.2.trans htT'.le⟩, schedW_eq_stopDrv_root c r a hold hgood hc0.2 hqT,
    stopDrv_root_eq c r a hold hqT]

/-- **Product-form no contact up to `T` gives GB6's contact form for the root piece** (on success). -/
theorem lt_contact_root {ω : Ω} (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hc0 : Continuous (stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (futSpec c r [] a) 0) (futFam c r [] a 0 ω) 0 = 0)
    (hreg : IsRegularDriver (futFam c r [] a 0 ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (fun t => (futFam c r [] a 0 ω).1 t) (futFam c r [] a 0 ω).2 α) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun t => schedW c r [] a t ω) ⊤ η) {ac : ℝ≥0 → ℂ}
    (hac : IsGeneratingTrace (fun t => c.W t ω) ⊤ ac)
    (hnc : ∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r [], ac v * η u + 1 ≠ 0) :
    ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun t => sphereInv (α t : OnePoint ℂ))
      ((fun u => (ac u : OnePoint ℂ)) '' Icc 0 c.s) := by
  set e := futFam c r [] a 0 ω with he
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  obtain ⟨T', hT'1, hT'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  have hTT' : historyTime c r [] < T' := by exact_mod_cast hT'1
  set αc : ℝ≥0 → ℂ := fun u => α (min u T') with hαc
  have hαcont : Continuous αc := by
    refine hα.2.1.comp_continuous (continuous_id.min continuous_const) fun u => ?_
    show ((min u T' : ℝ≥0) : ℝ≥0∞) ≤ e.2
    exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hT'2.le
  have hacc : Continuous ac := continuousOn_univ.1 (hac.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hlt2 : ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun t => sphereInv (αc t : OnePoint ℂ))
      ((fun u => (ac u : OnePoint ℂ)) '' Icc 0 c.s) := by
    rw [Gm.lt_firstContactTime_iff_noncontact hαcont hacc]
    intro t ht u hu
    have e1 : αc t = η t := by
      show α (min t T') = η t
      rw [min_eq_left (ht.2.trans hTT'.le)]
      exact chosenTrace_eq_schedTr c r a hold hgood hc0 hreg hα hη ht.2
    rw [e1, mul_comm]
    exact hnc u hu t ht.2
  refine GW2Fb.lt_firstContactTime_of_prefix hTT' (fun u hu => ?_) hlt2
  show sphereInv (α u : OnePoint ℂ) = sphereInv (α (min u T') : OnePoint ℂ)
  rw [min_eq_left hu]

/-- **Before contact the root piece's hulls miss the retained hull.** -/
theorem fwdHull_root_subset {ω : Ω} (hold : oldSuccess c r [] ω) (hreg : IsRegularDriver (futFam c r [] a 0 ω))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (fun t => (futFam c r [] a 0 ω).1 t) (futFam c r [] a 0 ω).2 α)
    {ac : ℝ≥0 → ℂ} (hac : IsGeneratingTrace (fun t => c.W t ω) ⊤ ac) (hWc : Continuous fun t => c.W t ω)
    (hW0 : c.W 0 ω = 0)
    (hTc : ((historyTime c r [] : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun t => sphereInv (α t : OnePoint ℂ))
      ((fun u => (ac u : OnePoint ℂ)) '' Icc 0 c.s)) {u : ℝ≥0} (hu : u ≤ historyTime c r []) :
    fwdHull (fun q : ℝ => (futFam c r [] a 0 ω).1 q.toNNReal) u ⊆
      H \ invHull (fun q : ℝ => c.W q.toNNReal ω) c.s := by
  have hlt := (oldSuccess_nil_iff c r a ω).1 hold
  have hdis := GB6.disjoint_closure_fwdHull_of_lt_firstContactTime hac hWc.continuousOn hW0 hα hreg.1 hreg.2.1
    ENNReal.coe_lt_top hlt hTc
  intro z hz
  refine ⟨Exist.fwdHull_subset_H u.coe_nonneg hz, ?_⟩
  rintro ⟨y, hy, rfl⟩
  have hzT : -y⁻¹ ∈ fwdHull (fun q : ℝ => (futFam c r [] a 0 ω).1 q.toNNReal) (historyTime c r [] : ℝ) :=
    QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hu) hz
  have hy' : y ∈ (fun w : ℂ => -w⁻¹) '' fwdHull (fun q : ℝ => (futFam c r [] a 0 ω).1 q.toNNReal)
      (historyTime c r [] : ℝ) := ⟨-y⁻¹, hzT, by simp⟩
  exact Set.disjoint_left.1 hdis (subset_closure hy) (subset_closure hy')

variable [StandardBorelSpace Ω]

/-- **The root piece is the angle-`θ_root` flow line of `h` under `P`** (root `0`). -/
theorem isFlowLineDriver_root0 (h13 : Exist.Theorem13Statement.{u}) (hr0 : rootPt r.1 = 0) :
    IsFlowLineDriver c.κ c.b c.jumps (rootEntry r.1).1 c.P c.h (fun t ω => (futFam c r [] a 0 ω).1 t)
      (fun ω => (futFam c r [] a 0 ω).2) := by
  set spec := futSpec c r [] a with hspec
  set E := futFam c r [] a with hEdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true (futureProgram c r [] a)) (specDelta_ne_top _)
  have hfl0 := hS.isFlowLineDriver_first_root c.hκ c.hb c.hh (futSpec_nil_prog c r a)
  have hx0 : spec.1 = 0 := hr0
  have e1 : (fun y => c.b (y + spec.1)) = c.b := funext fun y => by rw [hx0, add_zero]
  have e2 : c.jumps.image (· - spec.1) = c.jumps := by
    rw [hx0]
    simp
  have e3 : (fun ω => Exist.flowField spec.1 0 (c.h ω)) = c.h :=
    funext fun ω => by rw [hx0, Sec7.Prop74B.flowField_zero_zero]
  rw [e1, e2, e3] at hfl0
  exact hfl0

/-- **Claim(k) at `l = []` (root `0`)**: every local-set mean of the stage-start union of the history `[]` pairs, on
the good event `G`, as the explicit stage mean at clock `0` (`GW2Psm.stgMeanR … a₀ 0 U₀ u₀ σa`, written out), under
the instance's readings at the sample and the word identity for the stage-start data `U₀`. -/
theorem claim_base_root0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hr0 : rootPt r.1 = 0) {cw : BoundaryWord} (hcw : IsCfWordOf c.κ c.P c.h c.W c.ζ cw)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r [] a 0) (schedUnionS c r [] a 0) (centredField c.h u₀) c.P)
    {G : Set Ω} (hGs : ∀ ω ∈ G, oldSuccess c r [] ω) {R : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0} {σa : ℝ}
    {U₀ : Ω → ℂ → ℝ}
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r [], c.α ω v * schedTr c r [] a ω u + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = 0 ∧
      ContinuousOn (fun u => A u ω) (Icc 0 (historyTime c r [])) ∧
      (∀ u ≤ historyTime c r [], H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
          fwdHull (fun q : ℝ => schedW c r [] a q.toNNReal ω) u) =
        (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω))) ∧
      ∀ G' : ℂ → ℝ, IsBoundedHarmonicExtension
          (flowedData c.κ (flowLineRhoL c.κ (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0
              (rootEntry r.1).1)
            (flowLineRhoR c.κ (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0 (rootEntry r.1).1)
            (flowLineXL (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0)
            (flowLineXR (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0)
            (Ito.rpath fun q => R q ω) (A (historyTime c r []) ω))
          (flowedJumps (flowLineXL (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0)
            (flowLineXR (jw c.κ cw c.s c.W c.ζ ω).fn (jw c.κ cw c.s c.W c.ζ ω).jumps 0)
            (Ito.rpath fun q => R q ω) (A (historyTime c r []) ω)) G' →
        ∀ z ∈ H, U₀ ω z = G' z + (σa - (specOffset c.κ + (rootEntry r.1).1 * chiC c.κ)))
    (g₀ : Ω → DistOn upperHalfPlaneOpens)
    (hg₀ : IsLocalSetMean (schedUnionS c r [] a 0) (centredField c.h u₀) c.P g₀) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r [] a 0 ω →
      g₀ ω φ = ∫ z, (couplingMean c.κ (Ito.rpath (GW2Rd.stgDrv (fun q => R q ω) (A (historyTime c r []) ω))) 0
          (U₀ ω) ((GW2Rd.stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω)
            (A (historyTime c r []) ω)).1 z) - u₀ z - σa -
        chiC c.κ * (GW2Rd.stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω)
          (A (historyTime c r []) ω)).2.2 z) * φ z := by
  classical
  obtain ⟨g, hg, hmh, γ, uθ, huθ, hcomp, hmain⟩ := ae_root_union_form h12 h13 c r a hr0 hcw hu₀ hloc₀
  have hhm := measurable_centredField c.hh.1 u₀
  have hgg := IsLocalSetMean.ae_apply_eq (measurable_schedUnionS c r [] a 0) hhm hg₀ hg φ
  set spec := futSpec c r [] a with hspec
  set E := futFam c r [] a with hEdef
  set T : ℝ≥0 := historyTime c r [] with hT
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true (futureProgram c r [] a)) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle spec) (specDelta spec) (c.h ω) j
  have hR := stagedPiecesRegular_of_regular h13 c.hκ c.hb hS hreg
  have hfl := isFlowLineDriver_root0 c r a h13 hr0
  have hαr := GW2aSingle.ae_chosenTrace h13 c.hκ hfl
  have hcfreg := GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ
  filter_upwards [hread, hmain, hmh, hgg, c.hα, hαr, ae_schedW_trace c r [] a h13, hcfreg,
    Gm.ae_futureJoined_trace h13 c r, hR.ae_pieceRegular, c.hζ, hcomp]
    with ω hrω hmω hmhω hggω hαω hαrω hschω hcfω hfutω hprω hζω hcompω hωG hsupp
  obtain ⟨hαs, hnc, hRc, hR0, hA0, hAc, hshape, hword⟩ := hrω hωG
  have hold := hGs ω hωG
  have hTζ := (oldSuccess_nil_iff c r a ω).1 hold
  obtain ⟨hgood, -⟩ := hfutω [] a hold
  have hc0 := stopDrv_cont_of_oldSuccess c r [] a hold hprω 0 (by simp [curIdx])
  obtain ⟨γ', -, hWc, hW0, -⟩ := hcfω
  have hsζ : (c.s : ℝ≥0∞) < c.ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  have hγα : γ ω = c.α ω :=
    funext fun t => IsGeneratingTrace.eq_of_le hcompω.2 hαω hWc.continuousOn hW0 le_top
  have hBeq := schedUnionS_nil_eq c r a hold hgood hc0 (hreg 0 ω) hW0 hWc.continuousOn hsζ
  have hTc := lt_contact_root c r a hold hgood hc0 (hreg 0 ω) hαrω.1 hschω.1 hαω hnc
  have hTpos : 0 < T := c.hQpos _ r.1.2.2.2
  obtain ⟨w, hw, hwpair⟩ := hmhω
  have hform := hmω hTζ (by rw [hγα]; exact hαs) hTpos (by rw [firstContactTime_swap, hγα]; exact hTc) w hw
    hwpair
  rw [hBeq] at hform
  have hshape' : ∀ u ≤ T, H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
      fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) u) =
        (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω)) := by
    intro u hu
    rw [fwdHull_root_eq c r a hold hgood hc0 (hreg 0 ω) hu]
    exact hshape u hu
  have hdisj := fun u (hu : u ≤ T) => fwdHull_root_subset c r a hold (hreg 0 ω) hαrω.1 hαω hWc hW0 hTc hu
  obtain ⟨G', hG', hrd⟩ := root_stage_read (κ := c.κ) (θ := (rootEntry r.1).1) (b := c.b) (J := c.jumps)
    (c' := cw) (W := c.W) (ζ := c.ζ) (Wα := fun t ω => (E 0 ω).1 t) (ω := ω) (s := c.s) (T := T)
    (R := fun q => R q ω) (A := fun u => A u ω) (w := w) c.hκ c.hb hu₀ huθ hW0 hWc hsζ hRc hR0 hA0 hAc
    hshape' hdisj hform
  -- the stage chart's domain is the complement of the union
  set a₀ := A T ω with ha₀
  set c₀ := RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω) with hc₀def
  set cs := GW2Rd.stgChart c₀ (fun q => R q ω) a₀ with hcsdef
  have hRp : Continuous (Ito.rpath fun q => R q ω) := hRc.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath (fun q => R q ω) 0 = 0 := by simp [Ito.rpath, hR0]
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart (RelSafeS.isConformal_relChart _) hRc hR0 a₀
  have hcsdom : (cs.dom : Set ℂ) = H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
      fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) T) := by
    rw [hcs.coe_dom, hshape' T le_rfl]
    change (fun w => c₀.2.1 (QuantumZipper.fwdMapInv (Ito.rpath fun q => R q ω) (a₀ : ℝ) w)) '' H = _
    rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hRp hRp0 a₀.coe_nonneg]
  have hS0 : Ito.rpath (GW2Rd.stgDrv (fun q => R q ω) a₀) 0 = 0 := by simp [Ito.rpath, GW2Rd.stgDrv_zero]
  rw [hggω, hwpair φ hsupp]
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · have hzB : z ∈ H \ (invHull (fun q : ℝ => c.W q.toNNReal ω) c.s ∪
        fwdHull (fun q : ℝ => (E 0 ω).1 q.toNNReal) T) := by
      rw [← hBeq]
      exact hsupp hz
    have hzdom : z ∈ (cs.dom : Set ℂ) := by rw [hcsdom]; exact hzB
    have hcsH : cs.1 z ∈ H := hcs.fwd_mem hzdom
    have hld : logDerivFwd (Ito.rpath (GW2Rd.stgDrv (fun q => R q ω) a₀)) 0 (cs.1 z) = 0 := by
      simp [QuantumZipper.logDerivFwd]
    rw [hrd z hzB, couplingMean, Exist.StagedLaw.fwdMap_zero_time hS0, hld, hword G' hG' _ hcsH]
    simp only [Complex.zero_im, mul_zero, sub_zero]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end InteractingSLE.Theorem14.GW2Kb
