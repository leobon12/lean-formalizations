/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmKerId
import InteractingSLE.Spec.Supplement.GW2OmxChain2
import InteractingSLE.Spec.Supplement.GW2SpmPhys
import InteractingSLE.Spec.Sobolev.CondMean
import InteractingSLE.Spec.Coupling.MartMeans2Lemma71

/-!
# GW2's open lines: the pairing of the instance's mean at stage time `t > 0` from the stage start (root `0`)

Packet PROVE-GW2-STAGEMEAN, R121 round. The kernel chain (`GW2Omx.ae_of_kernel_curS`) applied to the event
`{ω ∈ G → supp φ ⊆ ℍ ∖ B t → g ω φ = F φ ω}`, with the kernel bundle `GW2Psm.ae_kernel_identity_root0`:

* `stgMeanR`: the explicit stage mean of a relative driver `R` read from the stage start `a₀` at clock `Q`;
* **`pair_root0`**: if, almost surely on a measurable event `G` of successful histories, the instance's readings hold
  (stage shape, no physical contact before `T + t`, interior counterflow tip at `s`, the piece alive at `t`, typed
  data with the far-right height `λ'(16/κ) − πχ + θχ` at the launch angle `θ`) and the stage-start pairing holds for
  every local-set mean of `B 0` (Claim(k)), then every local-set mean `g` of `B t` pairs as the explicit stage mean.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart GW2Omx
  MartChar.RealFlow

/-- **The explicit stage mean** of a relative driver `R` read from the stage start `a₀` at clock `Q`. -/
def stgMeanR (κ : ℝ) (rec : RecData) (R : ℝ≥0 → ℝ) (a₀ : ℝ≥0) (Q : ℝ) (U u₀ : ℂ → ℝ) (σa : ℝ) (y : ℂ) : ℝ :=
  couplingMean κ (Ito.rpath (stgDrv R a₀)) Q U ((stgChart (RelSafeS.relChart rec) R a₀).1 y) - u₀ y - σa -
    chiC κ * (stgChart (RelSafeS.relChart rec) R a₀).2.2 y


/-- `specDelta` of a schedule program is the schedule's delta on its indices. -/
theorem specDelta_eq_schedDelta (x : ℝ) (gw : Bool) (L : List (ℝ × ℝ≥0)) {j : ℕ}
    (hj : j < (scheduleProgram 0 L).length) : specDelta ⟨x, gw, scheduleProgram 0 L⟩ j = schedDelta 0 L j := by
  have h1 := isFlowProg_spec x gw L j hj
  have h2 := isFlowProg_scheduleProgram 0 L j hj
  rw [h1] at h2
  exact (Prod.mk.inj (Sum.inl.inj (Option.some.inj h2))).2

/-- **`AllSucc` with the schedule's deltas is `AllSucc` with the program's.** -/
theorem allSucc_futSpec_iff {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    AllSucc (schedDelta 0 (futureProgram c r l a)) (fun j => futFam c r l a j ω) (curIdx c r l) ↔
      AllSucc (specDelta (futSpec c r l a)) (fun j => futFam c r l a j ω) (curIdx c r l) := by
  have hlenL : (futureProgram c r l a).length = curIdx c r l + 1 := by
    rw [futureProgram, List.length_append, List.length_singleton]
  have hlen : (scheduleProgram 0 (futureProgram c r l a)).length = curIdx c r l + 1 :=
    (GW2Schedule.length_scheduleProgram 0 _).trans hlenL
  have he : ∀ j < curIdx c r l, specDelta (futSpec c r l a) j = schedDelta 0 (futureProgram c r l a) j :=
    fun j hj => specDelta_eq_schedDelta (rootPt r.1) true (futureProgram c r l a) (by omega)
  constructor
  · intro h j hj
    rw [he j hj]
    exact h j hj
  · intro h j hj
    rw [← he j hj]
    exact h j hj

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Off the history's success at `ω₀`, the conditional kernel sees no success.** -/
theorem ae_ae_not_oldSuccess (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ¬ AllSucc (specDelta (futSpec c r l a)) (fun j => futFam c r l a j ω₀) (curIdx c r l) →
      ∀ᵐ ω ∂(condExpKernel c.P (pastG c r l a) ω₀), ¬ oldSuccess c r l ω := by
  set x := rootPt r.1 with hx
  set L := futureProgram c r l a with hL
  set spec := futSpec c r l a with hspec
  set E := futFam c r l a with hEdef
  set k := curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec x true L) (specDelta_ne_top _)
  have hreg : ∀ j ω, IsRegularDriver (E j ω) := fun j ω =>
    isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x (specAngle spec) (specDelta spec) (c.h ω) j
  have h𝒢 : pastG c r l a ≤ mΩ := hS.2.1 k
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hprog := isFlowProg_spec x true L
  have hgw : spec.2.1 = true := rfl
  have hk' : k < spec.2.2.length := by omega
  filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := c.P) (κ := c.κ) (b := c.b) (jumps := c.jumps) spec
      (fun j _ ω => hreg j ω) h𝒢 le_rfl] with ω₀ hrun hn
  filter_upwards [hrun] with ω hrω hold
  have hs : AllSucc (specDelta spec) (fun j => E j ω) k := Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hr := (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _)
    (fun j => E j ω) k hk'.le).1 hs
  have hst := (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog (specDelta_ne_top _)
    (fun j => E j ω₀) k hk'.le).2 hn
  rw [← hrω] at hst
  rcases hr.1 with h | h <;> rcases hst with h' | ⟨o, h'⟩ <;> rw [h] at h' <;> cases h'

/-- **The pairing at `t > 0` from the stage start** (root `0`). -/
theorem pair_root0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hr0 : rootPt r.1 = 0) (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0) (htpos : 0 < t)
    (htcap : t < candidateCap c r a)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionS c r l a t) (centredField c.h u₀) c.P)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r l a 0) (schedUnionS c r l a 0) (centredField c.h u₀) c.P)
    {G : Set Ω} (hGm : MeasurableSet G) (hGs : ∀ ω ∈ G, oldSuccess c r l ω)
    {R : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0} {a₀ : Ω → ℝ≥0} {σa : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {U₀ U : Ω → ℂ → ℝ} {hβ : ℝ}
    (hθ : ∀ (ω₀ : Ω) (cL : Chart) (θ : ℝ), curLaunch c r l a ω₀ = some (cL, θ) →
      sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ = hβ)
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      (t : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 ∧ c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r l + t, c.α ω v * schedTr c r l a ω u + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = a₀ ω ∧ (∀ u, a₀ ω ≤ A u ω) ∧ Continuous (fun u => A u ω) ∧
      (∀ u ≤ t, H \ schedUnionS c r l a u ω =
        (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u ω))) ∧
      (∀ i, xL ω i ≤ 0) ∧ (∀ j, 0 ≤ xR ω j) ∧
      IsBoundedHarmonicExtension (forceBoundaryData c.κ ρL ρR (xL ω) (xR ω)) (forceJumpSet (xL ω) (xR ω)) (U₀ ω) ∧
      (∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (xL ω) (xR ω) →
        forceBoundaryData c.κ ρL ρR (xL ω) (xR ω) y = hβ) ∧
      IsBoundedHarmonicExtension
        (forceBoundaryData c.κ ρL ρR
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω)))
        (forceJumpSet
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))) (U ω) ∧
      InnerProductSpace.HarmonicOnNhd
        (stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa)
        (H \ schedUnionS c r l a 0 ω))
    (hclaim : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionS c r l a 0) (centredField c.h u₀) c.P g₀ → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r l a 0 ω →
        g₀ ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa z * φ z)
    {F : TestOn upperHalfPlaneOpens → Ω → ℝ} (hFm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable (F φ))
    (hFeq : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r l a t ω →
      F φ ω = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω) (U ω) u₀ σa z *
        φ z)
    (g : Ω → DistOn upperHalfPlaneOpens) (hg : IsLocalSetMean (schedUnionS c r l a t) (centredField c.h u₀) c.P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r l a t ω →
      g ω φ = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω) (U ω) u₀ σa z *
        φ z := by
  classical
  obtain ⟨g', g₀', hg', hg₀', hK⟩ := ae_kernel_identity_root0 h12 h13 c r l a hr0 hord hs0 hu₀ hh0 t htpos htcap
    hloc hloc₀
  have hhm : Measurable (centredField c.h u₀) := measurable_centredField c.hh.1 u₀
  have hBm := measurable_schedUnionS c r l a t
  have hBc := schedUnionS_subset_isOpen c r l a
  have hgg' := IsLocalSetMean.ae_apply_eq hBm hhm hg hg' φ
  -- Claim(k) for `g₀'`, at every test function on one event
  have hclaimAll : ∀ᵐ ω ∂c.P, ω ∈ G → ∀ φ' : TestOn upperHalfPlaneOpens,
      tsupport φ' ⊆ H \ schedUnionS c r l a 0 ω →
        g₀' ω φ' = ∫ z, stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa z * φ' z := by
    set A' : Ω → Set ℂ := fun ω => if ω ∈ G then schedUnionS c r l a 0 ω else H with hA'
    set m : Ω → ℂ → ℝ := fun ω => if ω ∈ G then
      stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa else 0 with hm
    have hφ' : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ' ⊆ H \ A' ω →
        g₀' ω φ' = ∫ z, m ω z * φ' z := by
      intro φ'
      filter_upwards [hclaim g₀' hg₀' φ'] with ω h1 hsupp
      by_cases hω : ω ∈ G
      · simp only [hA', hω, ↓reduceIte] at hsupp
        simp only [hm, hω, ↓reduceIte]
        exact h1 hω hsupp
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self] at hsupp
        have h0 : ∀ z, φ' z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hsupp hz)
        have hφ0 : φ' = 0 := by
          ext z
          exact h0 z
        rw [hφ0, map_zero]
        have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
          funext z
          rw [← hφ0, h0 z, mul_zero]
        rw [e, integral_zero]
    have hharm' : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g₀' ω) (H \ A' ω) := by
      filter_upwards [hg₀'.2.1] with ω h
      by_cases hω : ω ∈ G
      · simpa only [hA', hω, ↓reduceIte] using h
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
        exact GW2Scl.isHarmonicDistOn_empty _
    have hopen' : ∀ᵐ ω ∂c.P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ G
      · simpa only [hA', hω, ↓reduceIte] using (hBc 0 ω).2
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self, isOpen_empty]
    have hm' : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := by
      filter_upwards [hread] with ω hrd
      by_cases hω : ω ∈ G
      · simp only [hA', hm, hω, ↓reduceIte]
        exact (hrd hω).2.2.2.2.2.2.2.2.2.2.2.2.2.2
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
        exact fun z hz => absurd hz (notMem_empty z)
    filter_upwards [WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm' hφ'] with ω hω hωG φ' hsupp
    have h := hω φ' (by simpa only [hA', hωG, ↓reduceIte] using hsupp)
    simpa only [hm, hωG, ↓reduceIte] using h
  -- the chain
  set Aφ : Set Ω := {ω | ω ∈ G → tsupport φ ⊆ H \ schedUnionS c r l a t ω → g' ω φ = F φ ω} with hAφ
  have hAm : MeasurableSet Aφ := by
    have h1 : MeasurableSet {ω | tsupport φ ⊆ H \ schedUnionS c r l a t ω} :=
      GW2Spm.measurableSet_tsupport_subset_H_diff hBm (hBc t) φ
    have hg'm : Measurable fun ω => g' ω φ :=
      (Sobolev.measurable_distOn_apply φ).comp (hg'.1.mono (germSigma_le hBm hhm) le_rfl)
    have h2 : MeasurableSet {ω | g' ω φ = F φ ω} := measurableSet_eq_fun hg'm (hFm φ)
    have e : Aφ = Gᶜ ∪ ({ω | tsupport φ ⊆ H \ schedUnionS c r l a t ω}ᶜ ∪ {ω | g' ω φ = F φ ω}) := by
      ext ω
      simp only [hAφ, mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [e]
    exact hGm.compl.union (h1.compl.union h2)
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  set spec := futSpec c r l a with hspec
  set E := futFam c r l a with hEdef
  set k := curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true (futureProgram c r l a)) (specDelta_ne_top _)
  have h𝒢 : pastG c r l a ≤ mΩ := hS.2.1 k
  have hchain := ae_of_kernel_curS h12 h13 h12₀ h13₀ c r l a (Or.inl hr0) hord hAm (by
    filter_upwards [hK, ae_ae_not_oldSuccess h13 c r l a, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hread,
      KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hclaimAll, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hg'.2.1,
      KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (hFeq φ)] with ω₀ hKω hnot hreadν hclaimν hharmν hFν hcase
    by_cases hs : AllSucc (schedDelta 0 (futureProgram c r l a)) (fun j => futFam c r l a j ω₀) (curIdx c r l)
    · have hdat := hcase hs
      have hs' : AllSucc (specDelta spec) (fun j => E j ω₀) k := (allSucc_futSpec_iff c r l a ω₀).1 hs
      set L := futureProgram c r l a with hL
      have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
      have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
      have hl' := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
        (isFlowProg_spec (rootPt r.1) true L) (specDelta_ne_top _) (fun j => E j ω₀)
        (show k < spec.2.2.length by omega)).1 hs'
      have hl : curLaunch c r l a ω₀ = some (succChart spec.1 (specDelta spec) (fun j => E j ω₀) k,
          specAngle spec k) := hl'
      filter_upwards [hKω hdat _ _ hl, hreadν, hclaimν, hharmν, hFν] with ω hω hrd hcl hharm hF hωG hsupp
      obtain ⟨htζ, hαs, hnc, hRc, hR0, hA0, hAa, hAc, hshape, hxL, hxR, hU₀, hfarβ, hU, hM₀⟩ := hrd hωG
      obtain ⟨wP, hwP, hgP⟩ := hharm
      set cs := stgChart (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω) with hcs
      have hcsD := isDomainChart_stgChart_relChart (gb6Rec c.s c.W c.ζ ω) hRc hR0 (a₀ ω)
      have hinst0 : ∀ y ∈ (cs.dom : Set ℂ),
          stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa y + u₀ y + σa +
            chiC c.κ * cs.2.2 y = U₀ ω (cs.1 y) := by
        intro y hy
        have hy0 : cs.1 y ≠ 0 := fun h0 => by
          have := hcsD.fwd_mem hy
          rw [h0] at this
          have h' : (0 : ℝ) < (0 : ℂ).im := this
          simp at h'
        have hS0 : Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
        simp only [stgMeanR]
        rw [Coupling.MartMeans2.couplingMean_zero c.κ hS0 (U₀ ω) hy0]
        ring
      have hid := hω htζ hαs hnc (fun q => R q ω) (fun u => A u ω) (a₀ ω) hRc hR0 hA0 hAa hAc hshape wP
        (stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa) σa hwP hgP hM₀
        (hcl hωG) ρL ρR (xL ω) (xR ω) (U₀ ω) (U ω) hβ hxL hxR hU₀ hinst0 hfarβ (hθ ω₀ _ _ hl) hU
      -- `wP` is the explicit stage mean off `B t`
      have hsh := GW2Rd.stgChart_inv_image (RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) hRc hR0 (a₀ ω)
        (A t ω - a₀ ω)
      have hsum : a₀ ω + (A t ω - a₀ ω) = A t ω := add_tsub_cancel_of_le (hAa t)
      have hcoe : ((A t ω - a₀ ω : ℝ≥0) : ℝ) = (A t ω : ℝ) - a₀ ω := by rw [NNReal.coe_sub (hAa t)]
      rw [hsum, hcoe, ← hshape t le_rfl] at hsh
      have heq : ∀ y ∈ H \ schedUnionS c r l a t ω,
          wP y = stgMeanR c.κ (gb6Rec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω) (U ω) u₀ σa y := by
        intro y hy
        rw [← hsh] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have h1 := hid z hz
        have hcz : cs.1 (cs.2.1 z) = z := hcsD.fwd_inv hz.1
        simp only [stgMeanR]
        rw [hcz]
        linarith
      rw [hgP φ hsupp, hF hωG hsupp]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport φ
      · simp only
        rw [heq z (hsupp hz)]
      · simp only
        rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
    · have hs' : ¬ AllSucc (specDelta spec) (fun j => E j ω₀) k := fun h => hs ((allSucc_futSpec_iff c r l a ω₀).2 h)
      filter_upwards [hnot hs'] with ω hω hωG
      exact absurd (hGs ω hωG) hω)
  filter_upwards [hchain, hgg', hFeq φ] with ω h1 h2 h3 hωG hsupp
  rw [h2, h1 hωG hsupp, h3 hωG hsupp]

end InteractingSLE.Theorem14.GW2Psm
