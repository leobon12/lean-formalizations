/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2RzSched
import InteractingSLE.Spec.Supplement.GW2BfJ32Start

/-!
# The near words (N1)–(N2) at a root `x`: every good near slot reads the same stage record

Packet PROVE-GW2-SDE (round 14). The near word of the candidate `Nat.pair i k` asks its stage word to be
`upW (angle_i χ) (base l ω)` with ONE base word for all candidates and versions. With GEOM2's root-`x` word map
(`GW2Wm.wmChoiceX`) the stage word of a root-`x` instance is `upW (θ_a χ) (baseWordX … record)`, so it is enough that
the instances' stage records agree. They do, at every sample where they are good:

* **`stgPreRecX_eq`** (pathwise): two root-`x` instances (explored drivers `W`, `W'`, good sets, versions `R`, `R'`
  with caps `V`, `V'`) whose explored drivers agree up to the history time `T > 0`, with `T` before both root-`x`
  contacts and the clock at `T` strictly below both caps, have the same relative prefix record. Both versions are
  J31's capacity reader of the horizon `T` below the clock (ROOTX's `version_eq_reader`), and the reader reads only
  the explored driver up to `T`; the endpoint is by continuity. The stage starts are the clock at `T`
  (`physClockX_eq_clockX`).
* **`ae_stgPreRecX_sched_eq`**: almost surely, the root-`x` schedule instances of ANY two candidates `a`, `a'` (any
  root-`x` versions) have the same relative prefix record at every good record where the history time is before both
  contacts and the clock at the history time is below both caps (also at a history time `0`). The explored drivers
  share the history (`GW2Bf.futureJoined_eq_histJoined`); the good sets are ROOTX's `schedGTX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Sdo

open Restart Exist.StagedLaw GW2Rz GW2Rd

variable {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W W' : ℝ≥0 → Ω → ℝ}
  {γ γ' α : Ω → ℝ≥0 → ℂ} {GT GT' : Set Ω}

/-- The pair record of the horizon `T` reads the explored driver only up to `T`. -/
theorem recPair_congr {T : ℝ≥0} {ω : Ω} (hWW : ∀ t ≤ T, W t ω = W' t ω) :
    recPair s Wα ζα W T ω = recPair s Wα ζα W' T ω := by
  unfold recPair
  rw [GW2Wm.recOf_congr_top hWW]

theorem clockX_congr {T : ℝ≥0} {ω : Ω} (hWW : ∀ t ≤ T, W t ω = W' t ω) :
    clockX x₀ s Wα ζα W T ω = clockX x₀ s Wα ζα W' T ω := by
  unfold clockX
  rw [recPair_congr hWW]

/-- **The root-`x` stage start is the clock at `T`** on the good event, before the contact, below the cap. -/
theorem stgStartX_eq_clockX (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω) (hs : 0 < s) (hx : 0 ≤ x₀)
    {V : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) (hTc : (T : ℝ≥0∞) < contactX x₀ s γ α ω)
    (hV : ENNReal.ofReal (clockX x₀ s Wα ζα W T ω) < V ω) :
    stgStartX x₀ s Wα ζα W GT V T ω = (clockX x₀ s Wα ζα W T ω).toNNReal := by
  unfold stgStartX stgStartMX
  rw [physClockX_eq_clockX hGT hs hx hω hTc, min_eq_left hV.le]
  exact ENNReal.toNNReal_coe _

/-- **Two good root-`x` instances with the same history have the same relative prefix record** (pathwise). -/
theorem stgPreRecX_eq (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω)
    (hGT' : ∀ ω ∈ GT', PhysGoodX x₀ s Wα ζα W' γ' α ω) (hs : 0 < s) (hx : 0 ≤ x₀) {R R' : ℝ≥0 → Ω → ℝ}
    {V V' : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) (hω' : ω ∈ GT')
    (hR : VersionAtX x₀ s Wα ζα W γ α R V ω) (hR' : VersionAtX x₀ s Wα ζα W' γ' α R' V' ω) (hT0 : 0 < T)
    (hTc : (T : ℝ≥0∞) < contactX x₀ s γ α ω) (hTc' : (T : ℝ≥0∞) < contactX x₀ s γ' α ω)
    (hWW : ∀ t ≤ T, W t ω = W' t ω) (hV : ENNReal.ofReal (clockX x₀ s Wα ζα W T ω) < V ω)
    (hV' : ENNReal.ofReal (clockX x₀ s Wα ζα W' T ω) < V' ω) :
    stgPreRecX x₀ s Wα ζα W GT V T R ω = stgPreRecX x₀ s Wα ζα W' GT' V' T R' ω := by
  have hclk := clockX_congr (x₀ := x₀) (Wα := Wα) (ζα := ζα) (s := s) hWW
  have hS := stgStartX_eq_clockX hGT hs hx hω hTc hV
  have hS' := stgStartX_eq_clockX hGT' hs hx hω' hTc' hV'
  rw [← hclk] at hS'
  -- the two versions agree below the clock (both are the reader of the horizon `T`)
  have hlt : ∀ u : ℝ≥0, (u : ℝ) < clockX x₀ s Wα ζα W T ω → R u ω = R' u ω := fun u hu => by
    have huV : (u : ℝ≥0∞) ≤ V ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal hu.le).trans hV.le
    have huV' : (u : ℝ≥0∞) ≤ V' ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal (hu.le.trans hclk.le)).trans hV'.le
    rw [version_eq_reader hGT hs hx hω hR hT0 hTc hu huV,
      version_eq_reader hGT' hs hx hω' hR' hT0 hTc' (hclk ▸ hu) huV', recPair_congr hWW]
  have hle : ∀ u ≤ (clockX x₀ s Wα ζα W T ω).toNNReal, R u ω = R' u ω := by
    intro u hu
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ (clockX x₀ s Wα ζα W T ω).toNNReal) with h0 | hpos
    · have hu0 : u = 0 := le_antisymm (h0 ▸ hu) (by simp)
      rw [hu0, hR.2.1, hR'.2.1]
    · have heq : EqOn (fun t => R t ω) (fun t => R' t ω) (Iio (clockX x₀ s Wα ζα W T ω).toNNReal) :=
        fun t ht => hlt t (by
          have ht' : t < (clockX x₀ s Wα ζα W T ω).toNNReal := ht
          have hcpos : 0 < clockX x₀ s Wα ζα W T ω := by
            by_contra hc
            rw [Real.toNNReal_of_nonpos (not_lt.1 hc)] at hpos
            exact lt_irrefl _ hpos
          rw [← Real.coe_toNNReal _ hcpos.le]
          exact_mod_cast ht')
      have hcl := heq.closure hR.1 hR'.1
      rw [closure_Iio' (show (Iio (clockX x₀ s Wα ζα W T ω).toNNReal).Nonempty from ⟨0, hpos⟩)] at hcl
      exact hcl hu
  unfold stgPreRecX
  rw [hS, hS']
  exact GW2Wm.recOf_congr_top hle

universe u

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 in
/-- **Any two candidates' root-`x` schedule instances have the same relative prefix record** (almost surely, at every
good record whose history time is before both root-`x` contacts with the clock there below both caps). -/
theorem ae_stgPreRecX_sched_eq {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R R' : ℝ≥0 → Ω → ℝ}
    {V V' : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hA' : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a') (schedTr c r l a') c.α R' V') :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      ((historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < V ω) →
      ((historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a') c.α ω ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a') (historyTime c r l) ω) < V' ω) →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (historyTime c r l) R ω =
        stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a') (schedGTX h13 c r l a') V' (historyTime c r l) R'
          ω := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT', -, hGTae'⟩ := schedGTX_spec h13 c r l a'
  filter_upwards [hA.2.2.2.2.2.2, hA'.2.2.2.2.2.2, hGTae, hGTae'] with ω h1 h1' hg hg' hcf hc hc'
  have hω := hg.2 hcf
  have hω' := hg'.2 hcf
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ historyTime c r l) with h0 | hT0
  · unfold stgPreRecX stgStartX stgStartMX
    rw [← h0, physClockX_zero hGT hs hx, physClockX_zero hGT' hs hx, min_eq_left zero_le,
      min_eq_left zero_le]
    refine GW2Wm.recOf_congr_top fun u hu => ?_
    have hu0 : u = 0 := le_antisymm (by simpa using hu) (by simp)
    rw [hu0, hA.2.2.1 ω, hA'.2.2.1 ω]
  · have hWW : ∀ t ≤ historyTime c r l, schedW c r l a t ω = schedW c r l a' t ω := fun t ht => by
      unfold schedW
      split_ifs
      · rw [GW2Bf.futureJoined_eq_histJoined c r l a ω ht, GW2Bf.futureJoined_eq_histJoined c r l a' ω ht]
      · rfl
    exact stgPreRecX_eq hGT hGT' hs hx hω hω' ⟨hA.2.1 ω, hA.2.2.1 ω, (h1 hcf).2.2⟩
      ⟨hA'.2.1 ω, hA'.2.2.1 ω, (h1' hcf).2.2⟩ hT0 hc.1 hc'.1 hWW hc.2 hc'.2

end InteractingSLE.Theorem14.GW2Sdo
