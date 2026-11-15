/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiDrv

/-!
# The slow stop of decision D3 covers the gain eventually in `n` (S3 in its indexed form)

Packet PROVE-GW2-BUF (S3, round 6). Decision D3: the slow stage instance on the member `n` of an exhausting version
family `(R n, V n)` has the stop `V n − start`. `VStopCovers` becomes "almost surely on the gate, eventually in `n`,
`gain ≤ stop n`". At root `0`:

* **`ae_histCap_add_gain`**: at every live sample, `rootHistCap + rootGain` is GB6's relative clock at the buffer time
  `T + F`;
* **`ae_gain_le_sub_of_lt`**: for any version `(R, V)`, if `V` exceeds the relative clock at `T + F`, then
  `gain ≤ V − rootHistCap`;
* **`ae_stopCovers_eventually`**: for any family of versions that covers every pre-contact relative clock EVENTUALLY
  in `n` (decision D3's RELDET export; it is a property of the family, taken as a binder of this generic theorem),
  almost surely, eventually in `n`, `gain ≤ V n − rootHistCap`. No gate is needed: at dead samples the gain is `0`;
* **`ae_j32DriverId_version_sub`**: `VDriverId` in the indexed form `u < min(gain, V − rootHistCap)`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2TipSystem GW2TipSystem.RootC24 GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The history's capacity plus the gain is the relative clock at the buffer time** (root `0`, live samples). -/
theorem ae_histCap_add_gain (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ξ ∂c.P, 0 < GW2Sdg.rootGain c r l a ξ →
      ((GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ
          (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ)) := by
  filter_upwards [ae_exactPair_root0 h13 c r l a hroot] with ξ hpair hgain
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [GW2Sdg.sourceSample_fst]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')
  obtain ⟨-, -, -, -, hK⟩ := hpair hlive
  set T := RootJ31.historyTime c r l
  set v := RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ
  have hT0 : 0 ≤ RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) :=
    RootJ32.forwardCapacity_nonneg _ _ _ _
  have hgain' : (0 : ℝ) < RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ) -
      RootH29.forwardCapacity (rootPt r.1) c.s T (RootJ31.futurePair c r l a ξ) := by
    have h := hgain
    unfold GW2Sdg.rootGain GW2Sdg.rootCapAt at h
    exact Real.toNNReal_pos.1 h
  have hsum : GW2Sdg.rootHistCap c r l a ξ + GW2Sdg.rootGain c r l a ξ =
      (RootH29.forwardCapacity (rootPt r.1) c.s v (RootJ31.futurePair c r l a ξ)).toNNReal := by
    unfold GW2Sdg.rootHistCap GW2Sdg.rootGain GW2Sdg.rootCapAt
    rw [← Real.toNNReal_add hT0 hgain'.le, add_sub_cancel]
  rw [hsum, GW2Bf.forwardCapacity_future_eq_exact c r l a ξ le_rfl, (hK v le_rfl).2]
  rfl

/-- **A version beyond the buffer's clock covers the gain.** -/
theorem ae_gain_le_sub_of_lt (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ξ ∂c.P, ∀ V : ℝ≥0∞, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ
        (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ξ)) ≤ V →
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  filter_upwards [ae_histCap_add_gain h13 c r l a hroot] with ξ hsum V hV
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · refine ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top ?_
    rw [← ENNReal.coe_add, hsum hpos]
    exact hV

/-- **Decision D3's `VStopCovers`**: for a family of versions covering every pre-contact clock eventually in `n`,
almost surely, eventually in `n`, the gain is below the `n`-th stop `V n − rootHistCap`. -/
theorem ae_stopCovers_eventually (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) {Vn : ℕ → Ω → ℝ≥0∞}
    (hev : ∀ᵐ ξ ∂c.P, (c.s : ℝ≥0∞) < c.ζ ξ → c.α ξ c.s ∈ H → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ t) < Vn n ξ) :
    ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ Vn n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  filter_upwards [hev, ae_exactPair_root0 h13 c r l a hroot, ae_gain_le_sub_of_lt h13 c r l a hroot]
    with ξ hevξ hpair hcov
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · refine Eventually.of_forall fun n => ?_
    rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
      rw [GW2Sdg.sourceSample_fst]
      exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hpos.ne')
    obtain ⟨hsζ, hsH, hTc, -, -⟩ := hpair hlive
    filter_upwards [hevξ hsζ hsH _ hTc] with n hn
    exact hcov (Vn n ξ) hn.le

/-- **`VDriverId` in decision D3's indexed form** (root `0`): below `min(gain, V − rootHistCap)`. -/
theorem ae_j32DriverId_version_sub (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersion c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α R V) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      (u : ℝ≥0∞) < V ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ + u) ξ -
          GW2Bf.j32Read c r l a (GW2Sdg.rootHistCap c r l a ξ) ξ =
        R (GW2Sdg.rootHistCap c r l a ξ + u) ξ - R (GW2Sdg.rootHistCap c r l a ξ) ξ := by
  filter_upwards [ae_j32DriverId_version h13 c r l a hroot hver] with ξ hid u hu hV
  refine hid u hu ?_
  rw [ENNReal.coe_add]
  exact lt_tsub_iff_left.1 hV

end InteractingSLE.Theorem14.GW2Bh
