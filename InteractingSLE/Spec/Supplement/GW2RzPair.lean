/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzMono
import InteractingSLE.Spec.Supplement.GW2BiHull


/-!
# GW2 at a root `x`: J32's exact pair reads the root-`x` versions (decision D8, BUF's S1 input)

Packet PROVE-GW2-ROOTX, round 3. D8's hint: J32's readers are already re-centred at the root, so a root-`x` version
satisfies the hypothesis of BUF's `GW2Bf.ae_j32Read_eq_of_hull` (and `VDriverId` holds by construction):

* **`ae_exactPair_rootX`** (BUF's `GW2Bh.ae_exactPair_root0` at the root `rootPt r.1`): at live samples the record is
  a good record at the root, `T + F` is before the root-`x` contact, and on `[0, T + F]` the root-`x` clock and the
  re-centred hulls are J32's forward capacities and re-centred forward hulls of the exact pair;
* **`ae_hull_version_rootX`** (BUF's `GW2Bh.ae_hull_version_root0` at the root): every root-`x` version of the
  schedule satisfies J32's re-centred hull identity at every `t ≤ T + F` whose root-`x` clock is `≤ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.RelDrv GW2TipSystem GW2Rd
  GW2TipSystem.RootC24 Supp8.GB6.ReadD

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **At a root `x`, J32's exact-horizon pair reads the root-`x` clock and the re-centred hulls** (BUF's
`GW2Bh.ae_exactPair_root0` at the root `rootPt r.1`), almost surely at every live sample: the counterflow record is
a good record at the root, the buffer time `T + F` is before the root-`x` contact, and on `[0, T + F]` the root-`x`
clock and the re-centred hulls of the schedule are J32's forward capacities and re-centred forward hulls. -/
theorem ae_exactPair_rootX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s ∧
      ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ,
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ =
          RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) ∧
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ =
          (fun z : ℂ => z + ((-GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) : ℝ) : ℂ)) ''
            RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) := by
  obtain ⟨_, _, _, hfl, hαs⟩ := source_counterflow c
  have hgood := ae_gb6RecGood hfl hαs c.s
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ, ae_schedW_regular h13 c r l a, hgood]
    with ξ hcover hα hreg hζ hsched hrg hlive
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
  have hsζ : (c.s : ℝ≥0∞) < c.ζ ξ := by rw [hζ]; exact ENNReal.coe_lt_top
  have hαζ : IsGeneratingTrace (fun t => c.W t ξ) (c.ζ ξ) (c.α ξ) := by rw [hζ]; exact hα
  -- the good record at the root
  have hAe : ∀ v ≤ c.s, recordTrace v (cfRec c.s c.W c.ζ ξ) = c.α ξ v := fun v hv =>
    GaugeE.recordTrace_eq (Wα := c.W) (ζα := c.ζ) c.s hW0 (by rw [hζ]; exact hW.continuousOn) hαζ hsζ hv
  have hA : ContinuousOn (fun v => recordTrace v (cfRec c.s c.W c.ζ ξ)) (Iic c.s) :=
    hαc.continuousOn.congr fun v hv => hAe v hv
  have hgx : cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s := by
    refine ⟨(mem_gb6TS_iff hrg).1 ⟨hsζ, hsH⟩, (mem_arcSet_iff hA).2 fun u hu => ?_⟩
    rw [hAe u hu.2]
    exact harc u hu
  have hfj : (fun t => schedW c r l a t ξ) = Gm.futureJoined c r l a ξ := schedW_of_oldSuccess c r l a hold
  refine ⟨hgx, (lt_min_iff.mp hv').1, fun t ht => ⟨?_, ?_⟩⟩
  · unfold clockX recPair
    rw [hfj]
    exact forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top ht le_rfl
  · unfold hullX recPair
    rw [hfj, forwardHull_prefix_eq he _ ENNReal.coe_lt_top ht le_rfl]
    rfl

/-- **Every root-`x` version of the schedule satisfies J32's re-centred hull identity** (BUF's
`GW2Bh.ae_hull_version_root0` at the root `rootPt r.1`; the hypothesis of `GW2Bf.ae_j32Read_eq_of_hull`) at every
`t ≤ T + F` whose root-`x` clock is `≤ V`. -/
theorem ae_hull_version_rootX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ,
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ V ξ →
        fwdHull (fun q : ℝ => R q.toNNReal ξ)
            (RootH29.forwardCapacity (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ)) =
          (fun z : ℂ => z + ((-GW2Bf.relBase (rootPt r.1) c.s (GW2Bf.exactPair c r l a ξ) : ℝ) : ℂ)) ''
            RootH29.forwardHull (rootPt r.1) c.s t (GW2Bf.exactPair c r l a ξ) := by
  filter_upwards [ae_exactPair_rootX h13 c r l a, hver.2.2.2.2.2.2] with ξ hpair hv hlive t ht hle
  obtain ⟨hgx, hTc, hK⟩ := hpair hlive
  obtain ⟨-, -, hhull⟩ := hv hgx
  have htc : (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 ht).trans_lt hTc
  obtain ⟨hclk, hhx⟩ := hK t ht
  rw [← hclk, ← hhx]
  exact hhull t htc hle

end InteractingSLE.Theorem14.GW2Rz
