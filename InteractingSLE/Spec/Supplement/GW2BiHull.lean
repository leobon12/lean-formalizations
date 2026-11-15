/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BfJ32Drv
import InteractingSLE.Spec.Supplement.GW2RootZ21Clock
import InteractingSLE.Spec.Supplement.GW2SyVer
import InteractingSLE.Spec.Supplement.GW2SyGood

/-!
# J32's forward hulls at root `0` are GB6's relative hulls (S1, decision D3)

Packet PROVE-GW2-BUF (S1, round 6). Decision D3 (`planning/reviews/DECISIONS-FABLE-1.md`) indexes the slow stage
instance by the member `n` of RELDET's exhausting version family. Then `VDriverId` must hold for each `n` below the
`n`-th cap. Its analytic core is that J32's reader hulls are GB6's relative hulls. At root `0`:

* **`forwardHull_zero_eq`** (pathwise): before the first contact, the forward hull reader of a live record at root
  `0` is the relative image of the explored Loewner hull, `relMap '' fwdHull e.1 t` (JOINTDET's
  `RootZ21.forwardCapacity_eq_relClock_before_contact` route, with a horizon `v ≥ t`);
* **`ae_exactPair_root0`**: almost surely at every live sample, (i) the buffer time `T + F` is before GB6's first
  contact, (ii) J32's re-centring `relBase` is `0`, and (iii) on `[0, T + F]` J32's forward hulls of the exact-horizon
  pair are GB6's relative hulls of the explored curve and (iv) their capacities are GB6's relative clock;
* **`ae_hull_version_root0`**: every GB6 version `(R, V)` of the schedule instance satisfies J32's re-centred hull
  identity (the hypothesis of `GW2Bf.ae_j32Read_eq_of_hull`) at every `t ≤ T + F` whose relative clock is `≤ V`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.RelDrv GW2TipSystem
  GW2TipSystem.RootC24 GW2Rd

/-- **The forward hull reader at root `0` is the relative image of the explored hull**, before the first contact. -/
theorem forwardHull_zero_eq {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (fun t => W t ω) (ζ ω) α) (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hW0 : W 0 ω = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace e.1 e.2 γ) {t v : ℝ≥0} (htv : t ≤ v)
    (hv : (v : ℝ≥0∞) < min (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    RootH29.forwardHull 0 s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      relMap (Ito.rpath (W · ω)) s '' QuantumZipper.fwdHull (Ito.rpath e.1) t := by
  have hve : (v : ℝ≥0∞) < e.2 := (lt_min_iff.mp hv).2
  have hte : (t : ℝ≥0∞) < e.2 := (ENNReal.coe_le_coe.2 htv).trans_lt hve
  have ht : (t : ℝ≥0∞) < min (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2 := (ENNReal.coe_le_coe.2 htv).trans_lt hv
  -- the record at the horizon `v` decodes to the driver on `[0, t]`
  have hpiece : QuantumZipper.fwdHull (rdrv (recOf (v : ℝ≥0∞) e)) t =
      QuantumZipper.fwdHull (Ito.rpath e.1) t := by
    have hg := isDrvGood_recOf_of_lt he hve
    have heq : EqOn (rdrv (recOf (v : ℝ≥0∞) e)) (Ito.rpath e.1) (Icc 0 (t : ℝ)) := by
      intro q hq
      apply rdrv_recOf_eq he hg (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
      simpa only [rtime_recOf_coe, min_eq_left hve.le, ENNReal.toNNReal_coe] using
        hq.2.trans (NNReal.coe_le_coe.2 htv)
    obtain ⟨B, htB, hBe⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hte
    have hcont : ContinuousOn (Ito.rpath e.1) (Icc 0 (B : ℝ)) :=
      he.1.comp continuous_real_toNNReal.continuousOn fun q hq =>
        (ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr hq.2)).trans_lt hBe
    exact LocalExt.fwdHull_congr_of_continuousOn (continuous_rdrv _).continuousOn
      hcont t.coe_nonneg (by exact_mod_cast htB) heq
  have hH : QuantumZipper.fwdHull (Ito.rpath e.1) t ⊆ H := by
    rw [← RootZ21.fwdHull_record_of_live he hte]
    exact (isHPHull_fwdHull (continuous_rdrv _) t.coe_nonneg).1
  have hUK : QuantumZipper.fwdHull (rdrv (cfRec s W ζ ω)) s =
      QuantumZipper.fwdHull (fun q : ℝ => regW s W ζ q.toNNReal ω) s :=
    (GaugeE.record_hull_eq s hW0 hW hs).trans (RootG15.regW_fwdHull_eq W ζ ω hW hW0 hs).symm
  have hD : QuantumZipper.fwdHull (Ito.rpath e.1) t ⊆ relDomain (rdrv (cfRec s W ζ ω)) s := by
    intro z hz
    apply (mem_relDomain_iff _ _ _).mpr
    refine ⟨hH hz, ?_⟩
    rw [hUK]
    exact RootG15.inv_notMem_regW_fwdHull_before_contact W ζ ω hα hW hW0 hs hγ he.1 he.2.1 t ht z hz
  have hm : relMap (rdrv (cfRec s W ζ ω)) s = relMap (Ito.rpath (W · ω)) s := GaugeE.record_relMap_eq s hW0 hW hs
  unfold RootH29.forwardHull RootH29.translatedHull
  simp only [Complex.ofReal_zero, zero_add, image_id']
  rw [hpiece, inter_eq_left.mpr hD, hm]

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **At root `0`, J32's exact-horizon forward hulls are GB6's relative hulls**, almost surely at every live sample:
the buffer time is before GB6's first contact, the re-centring vanishes, and on `[0, T + F]` the forward hulls and
capacities are the relative hulls and the relative clock of the explored curve. -/
theorem ae_exactPair_root0 (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      (c.s : ℝ≥0∞) < c.ζ ξ ∧ c.α ξ c.s ∈ H ∧
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞) <
        gb6Tc c.s (schedTr c r l a) c.α ξ ∧
      GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) = 0 ∧
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ,
        RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) =
          relMap (Ito.rpath (c.W · ξ)) c.s '' QuantumZipper.fwdHull (Ito.rpath (schedW c r l a · ξ)) t ∧
        RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) =
          gb6Clock c.s (schedW c r l a) c.W ξ t := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, ae_schedW_regular h13 c r l a]
    with ξ hcover hα hreg hζ hsched hlive
  obtain ⟨hcov, hold, -, -⟩ := RootK32.sourceSample_live_geometry c r l a ξ hlive
  obtain ⟨hseed, hsH, -, -, -, harc⟩ := hcover hcov
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hs : 0 < c.s := by
    by_contra hn
    have hs0 : c.s = 0 := le_antisymm (not_lt.mp hn) zero_le
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  have hγ : IsGeneratingTrace (Gm.futureJoined c r l a ξ) ⊤ (schedTr c r l a ξ) := by
    have h := hsched.2.2.1
    rwa [schedW_of_oldSuccess c r l a hold] at h
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  have hvL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ ≤
      Sec5.Prop513Schedule.lastTime 0 (RootJ31.futureProgram c r l a) := by
    rw [Gm.lastTime_futureProgram]
    exact add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ξ)
  have hv := RootK32.sourceSample_live_before_contact c r l a ξ hlive
  rw [← Gm.lastTime_futureProgram] at hv
  have hγc : Continuous (schedTr c r l a ξ) := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ξ) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hnc := (Gm.lt_translatedContact_iff c.W c.ζ ξ hα hW hW0 hζ (rootPt r.1) c.s hJ hJ0 hγ hvL).1 hv
  have hv' : ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv ((((rootPt r.1 : ℝ) : ℂ) + schedTr c r l a ξ t : ℂ) : OnePoint ℂ))
        ((fun u => (c.α ξ u : OnePoint ℂ)) '' Icc 0 c.s)) (Gm.futureJoined c r l a ξ, (⊤ : ℝ≥0∞)).2 := by
    change _ < min _ ⊤
    rw [min_top_right]
    exact (Gm.lt_firstContactTime_iff_noncontact (continuous_const.add hγc) hαc _ c.s).2 hnc
  have he := Gm.isRegularDriver_top hJ hJ0
  have hx := RootH29.rootPt_nonneg_of_seedOK c hseed
  obtain ⟨_, -, -, -, -, hK⟩ := RootI30.exists_reader_chain c.W c.ζ ξ hα hW hW0 hζ hs hx harc he hγ hv'
  have hv0 : ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (schedTr c r l a ξ t : OnePoint ℂ))
        ((fun u => (c.α ξ u : OnePoint ℂ)) '' Icc 0 c.s)) (Gm.futureJoined c r l a ξ, (⊤ : ℝ≥0∞)).2 := by
    rw [hroot] at hv'
    simpa only [Complex.ofReal_zero, zero_add] using hv'
  have hsζ : (c.s : ℝ≥0∞) < c.ζ ξ := by rw [hζ]; exact ENNReal.coe_lt_top
  have hαζ : IsGeneratingTrace (fun t => c.W t ξ) (c.ζ ξ) (c.α ξ) := by rw [hζ]; exact hα
  refine ⟨hsζ, hsH, (lt_min_iff.mp hv0).1, ?_, fun t ht => ⟨?_, ?_⟩⟩
  · -- the re-centring vanishes at root `0`
    unfold GW2Bf.relBase
    rw [hroot, Complex.ofReal_zero, relBdry_zero (continuous_rdrv _) (rdrv_zero _) c.s.coe_nonneg]
    rfl
  · rw [hroot]
    refine (forwardHull_zero_eq c.W c.ζ ξ hαζ hW.continuousOn hW0 hsζ he hγ ht hv0).trans ?_
    change relMap (Ito.rpath (c.W · ξ)) c.s '' QuantumZipper.fwdHull (Ito.rpath (Gm.futureJoined c r l a ξ)) t =
      relMap (Ito.rpath (c.W · ξ)) c.s '' QuantumZipper.fwdHull (Ito.rpath fun t => schedW c r l a t ξ) t
    rw [schedW_of_oldSuccess c r l a hold]
  · refine ((hK t ⟨zero_le, ht⟩).1).trans ?_
    rw [hroot]
    simp only [add_zero]
    change _ = relClock (Ito.rpath (c.W · ξ)) c.s (Ito.rpath fun t => schedW c r l a t ξ) t
    rw [schedW_of_oldSuccess c r l a hold]

/-- **Every GB6 version of the schedule instance has J32's re-centred hulls below its cap** (root `0`). -/
theorem ae_hull_version_root0 (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersion c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ,
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ t) ≤ V ξ →
        QuantumZipper.fwdHull (fun q : ℝ => R q.toNNReal ξ)
            (RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ)) =
          (fun z : ℂ => z + ((-GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) : ℝ) : ℂ)) ''
            RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) := by
  obtain ⟨-, -, -, -, -, -, hae⟩ := hver
  filter_upwards [ae_exactPair_root0 h13 c r l a hroot, hae] with ξ hpair hverω hlive t ht hle
  obtain ⟨hsζ, hsH, hTc, hbase, hK⟩ := hpair hlive
  obtain ⟨-, -, hhull⟩ := hverω hsζ hsH
  obtain ⟨hKt, hcap⟩ := hK t ht
  have htc : (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ := (ENNReal.coe_le_coe.2 ht).trans_lt hTc
  rw [hcap, hKt, hbase, hhull t htc hle]
  simp only [neg_zero, Complex.ofReal_zero, add_zero, image_id']
  rfl

end InteractingSLE.Theorem14.GW2Bh
