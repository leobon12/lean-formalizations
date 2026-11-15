/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RvSlow
import InteractingSLE.Spec.Supplement.GW2SdoWord

/-!
# J32's readings through root-`x` versions; versions of schedules sharing a driver agree

PROVE-GW2-ROOTX round 6, for the two-sweep of the slow shell.

* **`ae_sourceX_eq_version`**: at a live sample, J32's reading at `q` in the live window is
  `(−1)^{|l|} 2^{r.2} (R(c(q)) − R(c(v₀)))` for any root-`x` version `R` covering the clock `c(q)`;
* **`version_eq_of_drv_eq`**: versions of two schedules whose explored drivers agree up to `T` agree up to the clock
  at `T` (both are J31's capacity reader of the horizon, `GW2Rz.version_eq_reader`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ru

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Rv

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **J32's reading of a live sample through any root-`x` version of its schedule**: at a time `q` of the live window
`[T, T + F)` whose clock is below the version's cap, `X_{l,a}(q) = (−1)^{|l|} 2^{r.2} (R(c(q)) − R(c(v₀)))`, with
`c` the root-`x` clock. -/
theorem ae_sourceX_eq_version (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 → (rootEntry r.1).2 ≤ RootJ31.historyTime c r l →
      ∀ q : ℝ≥0, RootJ31.historyTime c r l ≤ q →
        q < RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) q ξ) < V ξ →
        RootJ32.sourceX c r l a ξ q = (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
          (R (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) q ξ).toNNReal ξ -
            R (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ξ).toNNReal ξ) := by
  filter_upwards [ae_j32Read_eq_versionX h13 c r l a hx hver, Gm.ae_live_clock h13 c r,
    ae_rootCapAt_eq_clockX h13 c r l a] with ξ hread hclock hcap hlive hv₀ q hTq hqF hV
  set T := RootJ31.historyTime c r l with hT
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ with hv
  set F : ℝ≥0 → ℝ := fun t => RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ξ) with hF
  obtain ⟨-, -, -, hsm, -, -, -⟩ := hclock l a hlive
  have hsm' : StrictMonoOn F (Icc 0 v) := hsm
  have hF0 : ∀ t, 0 ≤ F t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  have hqv : q ≤ v := hqF.le
  have hTq' : F T ≤ F q := hsm'.monotoneOn ⟨zero_le, hTq.trans hqv⟩ ⟨zero_le, hqv⟩ hTq
  have hv₀q : (rootEntry r.1).2 ≤ q := hv₀.trans hTq
  have hFv : F q < F v := hsm' ⟨zero_le, hqv⟩ ⟨zero_le, le_rfl⟩ hqF
  have hFv₀ : F (rootEntry r.1).2 ≤ F q :=
    hsm'.monotoneOn ⟨zero_le, hv₀q.trans hqv⟩ ⟨zero_le, hqv⟩ hv₀q
  have hcq : F q = clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) q ξ := hcap hlive q hqv
  have hc₀ : F (rootEntry r.1).2 = clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ξ :=
    hcap hlive _ (hv₀q.trans hqv)
  have hexact : F v = RootH29.forwardCapacity (rootPt r.1) c.s v (GW2Bf.exactPair c r l a ξ) :=
    GW2Bf.forwardCapacity_future_eq_exact c r l a ξ le_rfl
  -- the capacity read at `q`
  have hsum : (F T).toNNReal + ((2 : ℝ≥0) ^ r.2) ^ 2 * (F (T + (q - T)) - F T).toNNReal / ((2 : ℝ≥0) ^ r.2) ^ 2 =
      (F q).toNNReal := by
    have h2 : ((2 : ℝ≥0) ^ r.2) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    rw [add_tsub_cancel_of_le hTq, mul_div_cancel_left₀ _ h2, ← Real.toNNReal_add (hF0 T) (sub_nonneg.2 hTq'),
      add_sub_cancel]
  -- J32's reader is the version
  have hR1 : GW2Bf.j32Read c r l a (F q).toNNReal ξ = R (F q).toNNReal ξ := by
    refine hread hlive _ ?_ ?_
    · rw [Real.coe_toNNReal _ (hF0 q), ← hexact]
      exact hFv
    · rw [hcq]
      exact hV
  have hR0 : GW2Bf.j32Read c r l a (F (rootEntry r.1).2).toNNReal ξ = R (F (rootEntry r.1).2).toNNReal ξ := by
    refine hread hlive _ ?_ ?_
    · rw [Real.coe_toNNReal _ (hF0 _), ← hexact]
      exact hFv₀.trans_lt hFv
    · refine lt_of_le_of_lt ?_ (show ((F q).toNNReal : ℝ≥0∞) < V ξ from by rw [hcq]; exact hV)
      exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hFv₀)
  unfold RootJ32.sourceX RootJ32.sourceDriver RootJ32.stageDriverRead RootJ31.sourceClock
    RootJ31.capacityIncrement
  rw [Real.toNNReal_coe]
  change (-1) ^ l.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
    (GW2Bf.j32Read c r l a ((F T).toNNReal + ((2 : ℝ≥0) ^ r.2) ^ 2 * (F (T + (q - T)) - F T).toNNReal /
      ((2 : ℝ≥0) ^ r.2) ^ 2) ξ - GW2Bf.j32Read c r l a (F (rootEntry r.1).2).toNNReal ξ) = _
  rw [hsum, hR1, hR0, hcq, hc₀]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
/-- **Versions of two schedules with the same explored driver up to `T` agree up to the clock at `T`** (pathwise;
both are J31's capacity reader of the horizon `T`, `GW2Rz.version_eq_reader`, and SDE's `GW2Sdo.stgPreRecX_eq`
argument at the endpoint). -/
theorem version_eq_of_drv_eq {x₀ : ℝ} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W W' : ℝ≥0 → Ω → ℝ}
    {γ γ' α : Ω → ℝ≥0 → ℂ} {GT GT' : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω)
    (hGT' : ∀ ω ∈ GT', PhysGoodX x₀ s Wα ζα W' γ' α ω) (hs : 0 < s) (hx : 0 ≤ x₀) {R R' : ℝ≥0 → Ω → ℝ}
    {V V' : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) (hω' : ω ∈ GT')
    (hR : VersionAtX x₀ s Wα ζα W γ α R V ω) (hR' : VersionAtX x₀ s Wα ζα W' γ' α R' V' ω) (hT0 : 0 < T)
    (hTc : (T : ℝ≥0∞) < contactX x₀ s γ α ω) (hTc' : (T : ℝ≥0∞) < contactX x₀ s γ' α ω)
    (hWW : ∀ t ≤ T, W t ω = W' t ω) (hV : ENNReal.ofReal (clockX x₀ s Wα ζα W T ω) < V ω)
    (hV' : ENNReal.ofReal (clockX x₀ s Wα ζα W' T ω) < V' ω) :
    ∀ u ≤ (clockX x₀ s Wα ζα W T ω).toNNReal, R u ω = R' u ω := by
  have hclk := GW2Sdo.clockX_congr (x₀ := x₀) (Wα := Wα) (ζα := ζα) (s := s) hWW
  have hlt : ∀ u : ℝ≥0, (u : ℝ) < clockX x₀ s Wα ζα W T ω → R u ω = R' u ω := fun u hu => by
    have huV : (u : ℝ≥0∞) ≤ V ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal hu.le).trans hV.le
    have huV' : (u : ℝ≥0∞) ≤ V' ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal (hu.le.trans hclk.le)).trans hV'.le
    rw [version_eq_reader hGT hs hx hω hR hT0 hTc hu huV,
      version_eq_reader hGT' hs hx hω' hR' hT0 hTc' (hclk ▸ hu) huV', GW2Sdo.recPair_congr hWW]
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

end InteractingSLE.Theorem14.GW2Ru
