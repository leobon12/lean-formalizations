/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2TcRead

/-!
# SB2(1)'s version half: the flow's lifetime is read from the line marks

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The relative clock is constant after
the flow's lifetime `ζ`, so its reading at time `t` needs the event `{ζ ≤ t}`. It is a line mark at `t`: the killed
history of the capped flow `η_n` (`n > t`) through `max(t, T_n) ≥ t` records the killing time `ζ` iff `ζ ≤ t`.

* `comap_ruleHist_le_iterMarks` (generic): the killed history of the `n`-th path is a mark of the iterated union;
* **`EntranceUnion.measurableSet_lifetime_le`**: `{ζ ≤ t} ∈ D.absMarks t` for every `t : ℝ≥0` (exactly, at every
  sample); `measurableSet_lt_lifetime` for the complement.

Deterministic; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vg

open Lv Restart Sec6 Exist.Staged Exist.StagedLaw

/-- **The killed history of the `n`-th path is a mark of the iterated union.** -/
theorem comap_ruleHist_le_iterMarks {Ω 𝒴 : Type*} {𝒢 : MeasurableSpace Ω} {η : ℕ → Ω → ℝ≥0 → ℂ}
    {ζ : ℕ → Ω → ℝ≥0∞} {Y : Ω → 𝒴} {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞} (n : ℕ) :
    MeasurableSpace.comap (ruleHist (η n) (ζ n) Y S) inferInstance ≤ iterMarks 𝒢 η ζ Y S n := by
  cases n with
  | zero => exact le_sup_right
  | succ n => exact le_sup_right

/-- **The killing record of the cut lifetime decides `{ζ ≤ t}`** when the cut `m` exceeds `t` and the recording time
is at least `t`. -/
theorem lifeRec_cutLife_le_iff {z : ℝ≥0∞} {t m : ℝ≥0} {S : ℝ≥0∞} (htm : (t : ℝ≥0∞) < m) (htS : (t : ℝ≥0∞) ≤ S) :
    lifeRec (cutLife z m) S ≤ t ↔ z ≤ t := by
  constructor
  · intro hle
    by_contra hz
    rw [not_le] at hz
    unfold lifeRec cutLife at hle
    split_ifs at hle with h1 h2 h2
    · exact absurd hle (not_le.2 hz)
    · exact absurd hle (not_le.2 ENNReal.coe_lt_top)
    · exact absurd hle (not_le.2 ENNReal.coe_lt_top)
    · exact absurd hle (not_le.2 ENNReal.coe_lt_top)
  · intro hz
    have h1 : z ≤ m := hz.trans htm.le
    have h2 : z ≤ S := hz.trans htS
    unfold lifeRec cutLife
    simp only [h1, h2, ↓reduceIte]
    exact hz

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The lifetime event `{ζ ≤ t}` is a line mark at `t`.** -/
theorem measurableSet_lifetime_le (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (t : ℝ≥0) :
    MeasurableSet[D.absMarks (t : ℝ≥0∞)] {ω | ζ ω ≤ t} := by
  set n : ℕ := ⌈(t : ℝ)⌉₊ + 1 with hn
  have htn : (t : ℝ≥0∞) < ((n : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_natCast, hn]
    push_cast
    linarith [Nat.le_ceil (t : ℝ)]
  set R := ruleHist (D.ηc n) (capLife ζ n) D.point (maxRule (t : ℝ≥0∞)) with hR
  have e : {ω | ζ ω ≤ t} = R ⁻¹' {k : KHist | k.2 ≤ t} := by
    ext ω
    show ζ ω ≤ t ↔ lifeRec (cutLife (ζ ω) (n : ℝ≥0)) (max (t : ℝ≥0∞) (hitQ (D.point ω) (pathCoord (D.ηc n ω)))) ≤ t
    exact (lifeRec_cutLife_le_iff htn (le_max_left _ _)).symm
  rw [e]
  have hm : MeasurableSet[MeasurableSpace.comap R inferInstance] (R ⁻¹' {k : KHist | k.2 ≤ t}) :=
    ⟨_, measurableSet_le measurable_snd measurable_const, rfl⟩
  exact (le_iSup (fun m => iterMarks _ D.ηc (capLife ζ) D.point (maxRule (t : ℝ≥0∞)) m) n)
    _ ((comap_ruleHist_le_iterMarks (𝒢 := pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) n) _ hm)

/-- **The event `{t < ζ}` is a line mark at `t`.** -/
theorem measurableSet_lt_lifetime (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (t : ℝ≥0) :
    MeasurableSet[D.absMarks (t : ℝ≥0∞)] {ω | (t : ℝ≥0∞) < ζ ω} := by
  have e : {ω | (t : ℝ≥0∞) < ζ ω} = {ω | ζ ω ≤ t}ᶜ := by ext ω; simp
  rw [e]
  exact (measurableSet_lifetime_le D t).compl

end EntranceUnion

end InteractingSLE.Theorem14.SB.Vg
