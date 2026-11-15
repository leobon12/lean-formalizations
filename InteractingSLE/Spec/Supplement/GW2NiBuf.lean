/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuVer
import InteractingSLE.Spec.Supplement.GW2TrCap
import InteractingSLE.Spec.Supplement.GW2RootK32Candidates
import InteractingSLE.Spec.Supplement.GW2RvSlow
import InteractingSLE.Spec.Supplement.GW2GmClock

/-!
# The source buffer of a fixed cap: the gain eventually passes any exit before the end

Packet PROVE-GW2-NEARIMG2 (layer 2, the buffer half of `kSel`). Fix a candidate `a` (angle and cap). Its buffer
variants `RootK32.candidateWithBuffer a b` explore the same curve; only the J31 sample's source buffer
`sourceBuffer = min (life ∧ cap, separation stop at level b)` changes, and it exhausts every own time `t₀` before the
cap, the life and the root-`x` contact (`RootK32.eventually_lt_sourceBuffer_withBuffer`). J32's gain `rootGain` is the
root-`x` clock gained up to that buffer. So any exit `e` with `e + clock(T) < clock(T + t₀)` is eventually below
the gain.

* `schedW_withBuffer`: the buffer variants explore the same curve;
* **`rootCapAt_eq_clockX`** (every sample of the history's success): J32's capacity reader is the root-`x` clock
  before the buffer (no liveness needed);
* **`eventually_lt_rootGain`** (one sample on the good set): the gain eventually passes `e`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The buffer variants explore the same curve.** -/
theorem schedW_withBuffer (b : ℕ) : schedW c r l (RootK32.candidateWithBuffer a b) = schedW c r l a := by
  funext t ω
  simp only [schedW, Gm.futureJoined]
  rw [RootK32.futureProgram_withBuffer]

/-- **J32's capacity reader is the root-`x` clock before the buffer** (history's success; no liveness needed). -/
theorem rootCapAt_eq_clockX {ξ : Ω} (hold : oldSuccess c r l ξ) {t : ℝ≥0}
    (ht : t ≤ historyTime c r l + sourceBuffer c r l a ξ) :
    GW2Sdg.rootCapAt c r l a t ξ = clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := by
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  unfold GW2Sdg.rootCapAt clockX recPair
  rw [GW2Bf.forwardCapacity_future_eq_exact c r l a ξ ht, schedW_of_oldSuccess c r l a hold]
  exact (forwardCapacity_prefix_eq' (Gm.isRegularDriver_top hJ hJ0) _ ENNReal.coe_lt_top ht le_rfl).symm

variable [StandardBorelSpace Ω]

/-- **Before the cap, the root-`x` contact is J31's translated contact** (one sample on the good set, history's
success). -/
theorem lt_contactX_iff_translated (h13 : Exist.Theorem13Statement.{u}) {ξ : Ω} (hξ : ξ ∈ schedGTX h13 c r l a)
    (hold : oldSuccess c r l ξ) {v : ℝ≥0} (hv : v ≤ historyTime c r l + candidateCap c r a) :
    (v : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ↔
      (v : ℝ≥0∞) < RootK32.translatedContact (rootPt r.1) c.s (historyTime c r l + candidateCap c r a)
        (futurePair c r l a ξ) := by
  obtain ⟨⟨-, -, hγ⟩, ⟨hα, hW, hW0, hζ⟩, -, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ξ
  have hγ' : IsGeneratingTrace (Gm.futureJoined c r l a ξ) ⊤ (schedTr c r l a ξ) := by
    rwa [schedW_of_oldSuccess c r l a hold] at hγ
  have hγc : Continuous (schedTr c r l a ξ) := continuousOn_univ.1 (hγ'.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ξ) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hvL : v ≤ Sec5.Prop513Schedule.lastTime 0 (futureProgram c r l a) := by
    rw [Gm.lastTime_futureProgram]; exact hv
  have h1 := Gm.lt_translatedContact_iff c.W c.ζ ξ hα hW hW0 hζ (rootPt r.1) c.s hJ hJ0 hγ' hvL
  have h2 := Gm.lt_firstContactTime_iff_noncontact (γ := fun t => ((rootPt r.1 : ℝ) : ℂ) + schedTr c r l a ξ t)
    (continuous_const.add hγc) hαc v c.s
  rw [← Gm.lastTime_futureProgram]
  exact h2.trans h1.symm

/-- **The gain eventually passes any exit before the end** (one sample on the good set). Let `t₀` be an own time
before the life and the cap, with `T + t₀` before the root-`x` contact, and `e + clock(T) < clock(T + t₀)`. Then
J32's gain of the buffer variants `b` eventually exceeds `e`. -/
theorem eventually_lt_rootGain (h13 : Exist.Theorem13Statement.{u}) (hx : 0 ≤ rootPt r.1) {ξ : Ω}
    (hξ : ξ ∈ schedGTX h13 c r l a) (hcov : ξ ∈ RootCv.coverEvent c r) (hold : oldSuccess c r l ξ) {t₀ : ℝ≥0}
    (ht₀n : t₀ < (nextRecord c r l a ξ).2.1.toNNReal) (ht₀c : t₀ < candidateCap c r a)
    (ht₀T : ((historyTime c r l + t₀ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    {e : ℝ≥0∞} (he : e + ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ξ) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l + t₀) ξ)) :
    ∀ᶠ b in atTop, e < (GW2Sdg.rootGain c r l (RootK32.candidateWithBuffer a b) ξ : ℝ≥0∞) := by
  have hGT := (schedGTX_spec h13 c r l a).1
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  have hs : 0 < c.s := GW2Rv.pos_of_physGoodX (hGT ξ hξ)
  obtain ⟨ha0, hsm, -⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ
  set T := historyTime c r l with hTdef
  set clk : ℝ≥0 → ℝ := fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ with hclk
  have hT0c : ((T + t₀ : ℝ≥0) : ℝ≥0∞) ≤ ((T + candidateCap c r a : ℝ≥0) : ℝ≥0∞) :=
    ENNReal.coe_le_coe.2 (add_le_add le_rfl ht₀c.le)
  have htc := (lt_contactX_iff_translated c r l a h13 hξ hold (add_le_add le_rfl ht₀c.le)).1 ht₀T
  filter_upwards [RootK32.eventually_lt_sourceBuffer_withBuffer c r l a ξ t₀ hcov hold ht₀n ht₀c htc] with b hb
  set a' := RootK32.candidateWithBuffer a b with ha'
  set F := sourceBuffer c r l a' ξ with hF
  have hF0 : 0 < F := lt_of_le_of_lt zero_le hb
  -- `T + F` is before the contact
  obtain ⟨-, -, -, hsep⟩ := (RootK32.sourceBuffer_pos_iff c r l a' ξ).1 hF0
  rw [RootK32.candidateCap_withBuffer, RootK32.futurePair_withBuffer] at hsep
  have hFsw : F ≤ RootJ31.switchedBuffer (rootPt r.1) c.s (T + candidateCap c r a) T (candidateCap c r a) b
      (futurePair c r l a ξ) := by
    rw [hF, ha', RootK32.sourceBuffer_withBuffer, ite_eq_left ⟨hcov, hold⟩]
    exact min_le_right _ _
  have hsw := RootK32.switchedBuffer_lt_contact (rootPt r.1) c.s (T + candidateCap c r a) T
    (candidateCap c r a) b (futurePair c r l a ξ) hsep
  have hFcap : F ≤ candidateCap c r a := by
    have := sourceBuffer_le c r l a' ξ
    rwa [ha', RootK32.candidateCap_withBuffer] at this
  have hTF : ((T + F : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    (lt_contactX_iff_translated c r l a h13 hξ hold (add_le_add le_rfl hFcap)).2
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add le_rfl hFsw)) hsw)
  -- the gain is the clock gained up to `T + F`
  have hold' : oldSuccess c r l ξ := hold
  have hcap : ∀ t ≤ T + F, GW2Sdg.rootCapAt c r l a' t ξ = clk t := fun t ht => by
    rw [rootCapAt_eq_clockX c r l a' hold' ht, ha', schedW_withBuffer]
  have hgain : (GW2Sdg.rootGain c r l a' ξ : ℝ≥0∞) = ENNReal.ofReal (clk (T + F) - clk T) := by
    unfold GW2Sdg.rootGain
    rw [hcap _ le_rfl, hcap _ le_self_add]
    rfl
  -- monotonicity of the clock before the contact
  have hTc : ((T : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 le_self_add) hTF
  have h0c : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 zero_le) hTc
  have hcT0 : 0 ≤ clk T := by
    have h := hsm.monotoneOn h0c hTc (zero_le : (0 : ℝ≥0) ≤ T)
    have h0 : clk 0 = 0 := ha0
    change clk 0 ≤ clk T at h
    rwa [h0] at h
  have hmono : clk (T + t₀) ≤ clk (T + F) := hsm.monotoneOn ht₀T hTF (add_le_add le_rfl hb.le)
  rw [hgain, ENNReal.ofReal_sub _ hcT0]
  exact lt_tsub_iff_right.2 (he.trans_le (ENNReal.ofReal_le_ofReal hmono))

end InteractingSLE.Theorem14.GW2Ni
