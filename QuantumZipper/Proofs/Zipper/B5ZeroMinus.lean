import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.WeldingConsistency
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.Thm14.FromThm13
import QuantumZipper.Proofs.Zipper.B2Defs

/-!
# B5: the left end `0₋(s) = zeroMinus V s` of the zipped segment and the hitting times

Node **B5** (Theorem 1.3, E-branch), the `zeroMinus` facts required by `handoff/ESM.md` (items 2
and 3) for the LR-ID step of E-SM. Deterministic part, for a continuous driver `V` with `V 0 = 0`
whose reverse hull at time `T > 0` is a simple arc:

* `zeroMinus_zero_time`: `zeroMinus V 0 = 0` (the reverse map at time `0` is the identity);
* `swallowedSet_eq_Icc_zeroMinus`: the real points swallowed by time `s` form `[0₋(s), b]`;
* `strictAntiOn_zeroMinus`, `continuousOn_zeroMinus_Icc`: `s ↦ 0₋(s)` is strictly decreasing and
  continuous on `[0,T]`;
* `hitTime_spec`: for `x ∈ (0₋(T), 0]`, `τ_x = realHitTime V x` is `ofReal τ` with
  `τ ∈ [0,T]` and `0₋(τ) = x`;
* `realHitTime_lt_iff`: for `x ≤ 0`, `τ_x < T ↔ 0₋(T) < x`.

Random part: `ae_isSimpleCurveHull_revHull_Vr` (from `Blueprint.RohdeSchrammSimple`, taken as a
hypothesis) and `ae_zeroMinus_Vr_facts`, all of the above a.s. for `V = Vr κ T B ω`.

Sources: Lawler, *Conformally Invariant Processes in the Plane* (AMS 2005), §4.1, p. 80 (the
swallowed set `K_t ∩ ℝ = [x⁻_t, x⁺_t]` and `g_t(x)` solves the Loewner equation up to `T_x`);
the Carathéodory boundary correspondence is the proved `CaraR.revMapCaratheodory`, the arc
structure the proved `CoreArc.loewnerSubhullsOfArc`; monotonicity/continuity of `0₋` are
`WeldingConsistency.zeroMinus_lt_of_lt` / `continuousOn_zeroMinus`. The assembly (identification
of the left end of the swallowed interval with `zeroMinus`, and of the hitting time) is our own
elementary argument.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace B5

open CaraR WeldingConsistency

variable {W : ℝ → ℝ}

/-- `0₋(0) = 0`: at time `0` the reverse map is the identity, so no negative point is sent to `0`
and `zeroMinus` is `sSup ∅ = 0`. -/
theorem zeroMinus_zero_time (hW : Continuous W) (hW0 : W 0 = 0) : zeroMinus W 0 = 0 := by
  have hb : ∀ x : ℝ, revMapBdry W 0 x = (x : ℂ) := fun x =>
    revMapBdry_eq_of_extension_R8 (F := id)
      (fun z hz => (CharFun.revMap_zero_eq hW hW0 hz).symm) continuousOn_id x
  have hE : {x : ℝ | x < 0 ∧ revMapBdry W 0 x = 0} = ∅ := by
    ext x
    simp only [hb, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, Complex.ofReal_eq_zero]
    exact fun hx h => hx.ne h
  unfold zeroMinus
  rw [hE, Real.sSup_empty]

/-- For a simple reverse hull at time `T > 0`, `0₋(T) < 0` and the swallowed set is
`[0₋(T), b]` for some `b ≥ 0`. -/
theorem swallowedSet_eq_Icc_zeroMinus (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hK : IsSimpleCurveHull (revHull W T)) :
    zeroMinus W T < 0 ∧ ∃ b, 0 ≤ b ∧ swallowedSet W T = Icc (zeroMinus W T) b := by
  obtain ⟨γ, hγc, hγi, hγ0, hγH, hKγ⟩ := hK
  obtain ⟨F, hF⟩ := extExists W hW hW0 T hT γ hγc hγi hγ0 hγH hKγ
  have hγ00 := arc_base_eq_zero hW hW0 hT hγc hγH hKγ
  have htip := revExt_zero_eq_tip extExists hW hW0 hT hγc hγi hγ0 hγH hKγ hF
  obtain ⟨a, b, -, hb0', hS⟩ := swallowedSet_eq_Icc hW hW0 hT.le
  obtain ⟨ha0, hb0, ha, hb⟩ :=
    revExt_ends extExists hW hW0 hT hγc hγi hγ0 hγH hKγ hF htip hS
  obtain ⟨hleft, hright, htop, hbot⟩ := revExt_real_outside hW hW0 hT hF hS
  obtain ⟨hmid, hinjL, hinjR, hpair⟩ :=
    revExt_structure_S hγc hγi hγH hF hγ00 htip ha0 hb0 ha hb hleft hright htop hbot
  have hcar := isCaratheodoryRevExt_of_structure hW hT hγc hγi hγH hKγ hF hγ00 ha0 hb0 ha hb
    hleft hright hmid hinjL hinjR hpair
  have hne : (revHull W T).Nonempty :=
    simpleCurveHull_nonempty ⟨γ, hγc, hγi, hγ0, hγH, hKγ⟩
  obtain ⟨hm, hp, -⟩ := car_basic hW hT hcar hne
  have hae := car_eq_zeroMinus hcar hm hp ha0.le ha
  exact ⟨hm, b, hb0', hae ▸ hS⟩

section Simple

variable (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
  (hK : IsSimpleCurveHull (revHull W T))
include hW hW0 hT hK

theorem isSimpleCurveHull_of_le {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    IsSimpleCurveHull (revHull W s) :=
  isSimpleCurveHull_revHull_of_le CoreArc.loewnerSubhullsOfArc hW hW0 hT hK hs hsT

theorem zeroMinus_neg_of_le {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) : zeroMinus W s < 0 :=
  (swallowedSet_eq_Icc_zeroMinus hW hW0 hs (isSimpleCurveHull_of_le hW hW0 hT hK hs hsT)).1

/-- `s ↦ 0₋(s)` is strictly decreasing on `[0,T]`. -/
theorem strictAntiOn_zeroMinus : StrictAntiOn (zeroMinus W) (Icc 0 T) := by
  intro s₁ hs₁ s₂ hs₂ hlt
  have hs₂0 : 0 < s₂ := lt_of_le_of_lt hs₁.1 hlt
  rcases eq_or_lt_of_le hs₁.1 with h | h
  · rw [← h, zeroMinus_zero_time hW hW0]
    exact zeroMinus_neg_of_le hW hW0 hT hK hs₂0 hs₂.2
  · exact zeroMinus_lt_of_lt revMapCaratheodory CoreArc.loewnerSubhullsOfArc hW hW0 hs₂0
      (isSimpleCurveHull_of_le hW hW0 hT hK hs₂0 hs₂.2) h hlt

/-- `s ↦ 0₋(s)` is continuous on `[0,T]`. -/
theorem continuousOn_zeroMinus_Icc : ContinuousOn (zeroMinus W) (Icc 0 T) := by
  have hIoc := continuousOn_zeroMinus revMapCaratheodory CoreArc.loewnerSubhullsOfArc hW hW0 hT hK
  have h0 : ContinuousWithinAt (zeroMinus W) (Ioc 0 T) 0 := by
    have := tendsto_zeroMinus_zero revMapCaratheodory CoreArc.loewnerSubhullsOfArc hW hW0 hT hK
    rw [ContinuousWithinAt, zeroMinus_zero_time hW hW0]
    exact this.mono_left (nhdsWithin_mono _ fun x hx => hx.1)
  have hI : Icc 0 T = insert 0 (Ioc 0 T) := (Ioc_insert_left hT.le).symm
  intro s hs
  rw [hI]
  rcases eq_or_lt_of_le hs.1 with h | h
  · rw [← h]
    exact (continuousWithinAt_insert_self).2 h0
  · exact (continuousWithinAt_insert (y := (0 : ℝ))).2 (hIoc s ⟨h, hs.2⟩)

/-- A point strictly left of `0₋(s)` is not swallowed by time `s`: `s < τ_x`. -/
theorem ofReal_lt_realHitTime {s x : ℝ} (hs : 0 < s) (hsT : s ≤ T) (hx : x < zeroMinus W s) :
    ENNReal.ofReal s < realHitTime W x := by
  obtain ⟨-, b, -, hS⟩ := swallowedSet_eq_Icc_zeroMinus hW hW0 hs
    (isSimpleCurveHull_of_le hW hW0 hT hK hs hsT)
  rw [ofReal_lt_realHitTime_iff hW hs.le, hS]
  exact fun h => absurd h.1 (not_le.2 hx)

/-- If `x < 0₋(s)` for all `s ∈ (0, τ)`, then `τ ≤ τ_x`. -/
theorem ofReal_le_realHitTime {τ x : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T)
    (hx : ∀ s ∈ Ioo 0 τ, x < zeroMinus W s) : ENNReal.ofReal τ ≤ realHitTime W x := by
  by_contra hlt
  push Not at hlt
  have hne : realHitTime W x ≠ ⊤ := ne_top_of_lt hlt
  set r := (realHitTime W x).toReal
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hrτ : r < τ := by
    have := (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).2 hlt
    rwa [ENNReal.toReal_ofReal hτ.le] at this
  set s := (r + τ) / 2
  have hs0 : 0 < s := by simp only [s]; linarith
  have hsτ : s < τ := by simp only [s]; linarith
  have h1 := ofReal_lt_realHitTime hW hW0 hT hK hs0 (hsτ.le.trans hτT) (hx s ⟨hs0, hsτ⟩)
  have h2 : realHitTime W x ≤ ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_toReal hne]
    exact ENNReal.ofReal_le_ofReal (by simp only [s, r] at *; linarith)
  exact absurd (h1.trans_le h2) (lt_irrefl _)

/-- The hitting time of a swallowed point of the left side: for `x ∈ (0₋(T), 0]`,
`τ_x = ofReal τ` with `τ ∈ [0,T]` and `0₋(τ) = x`. -/
theorem hitTime_spec {x : ℝ} (hx : x ∈ Ioc (zeroMinus W T) 0) :
    realHitTime W x = ENNReal.ofReal (realHitTime W x).toReal ∧
      (realHitTime W x).toReal ∈ Icc 0 T ∧ zeroMinus W (realHitTime W x).toReal = x := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · subst h
    have h0 : realHitTime W 0 = 0 := by
      have := (ofReal_lt_realHitTime_iff hW le_rfl (x := 0)).not.2
        (not_not.2 (zero_mem_swallowedSet hW0 le_rfl))
      rw [ENNReal.ofReal_zero, not_lt] at this
      exact le_antisymm this bot_le
    rw [h0]
    simp [zeroMinus_zero_time hW hW0, hT.le]
  obtain ⟨τ, hτ, hzτ⟩ := exists_zeroMinus_eq revMapCaratheodory CoreArc.loewnerSubhullsOfArc
    hW hW0 hT hK hx.1.le h
  have hanti := strictAntiOn_zeroMinus hW hW0 hT hK
  have hle : realHitTime W x ≤ ENNReal.ofReal τ := by
    obtain ⟨-, b, hb0, hS⟩ := swallowedSet_eq_Icc_zeroMinus hW hW0 hτ.1
      (isSimpleCurveHull_of_le hW hW0 hT hK hτ.1 hτ.2)
    have hmem : x ∈ swallowedSet W τ := by
      rw [hS, hzτ]; exact ⟨le_rfl, h.le.trans hb0⟩
    have := (ofReal_lt_realHitTime_iff hW hτ.1.le (x := x)).not.2 (not_not.2 hmem)
    exact not_lt.1 this
  have hge : ENNReal.ofReal τ ≤ realHitTime W x :=
    ofReal_le_realHitTime hW hW0 hT hK hτ.1 hτ.2 fun s hs =>
      hzτ ▸ hanti ⟨hs.1.le, hs.2.le.trans hτ.2⟩ ⟨hτ.1.le, hτ.2⟩ hs.2
  have heq := le_antisymm hle hge
  rw [heq, ENNReal.toReal_ofReal hτ.1.le]
  exact ⟨rfl, ⟨hτ.1.le, hτ.2⟩, hzτ⟩

/-- For `x ≤ 0`: `x` collides with `0` strictly before time `T` iff `0₋(T) < x`. -/
theorem realHitTime_lt_iff {x : ℝ} (hx : x ≤ 0) :
    realHitTime W x < ENNReal.ofReal T ↔ zeroMinus W T < x := by
  have hanti := strictAntiOn_zeroMinus hW hW0 hT hK
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    have : ENNReal.ofReal T ≤ realHitTime W x :=
      ofReal_le_realHitTime hW hW0 hT hK hT le_rfl fun s hs =>
        lt_of_le_of_lt hle (hanti ⟨hs.1.le, hs.2.le⟩ ⟨hT.le, le_rfl⟩ hs.2)
    exact absurd (hlt.trans_le this) (lt_irrefl _)
  · intro hlt
    obtain ⟨he, hτ, hzτ⟩ := hitTime_spec hW hW0 hT hK ⟨hlt, hx⟩
    rw [he, ENNReal.ofReal_lt_ofReal_iff hT]
    refine lt_of_le_of_ne hτ.2 fun h => ?_
    rw [h] at hzτ
    exact absurd hzτ (ne_of_lt hlt)

end Simple

/-! ## The random driver `V = Vr κ T B ω` -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- Under `RohdeSchrammSimple`, a.s. the reverse hull of `V = Vr κ T B ω` at time `T` is a simple
arc: it is the forward SLE hull `η(0,T]` (time reversal, `LoewnerAlgebra.revHull_eq_fwdHull_timeRev`). -/
theorem ae_isSimpleCurveHull_revHull_Vr (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ ≤ 4) {T : ℝ} (hT : 0 < T) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, IsSimpleCurveHull (revHull (B2.Vr κ T B ω) T) := by
  filter_upwards [hRSS κ hκ0 hκ4 P B hB, hB.cont, hB.eval_zero_ae_eq_zero] with ω hrs hc h0
  obtain ⟨hchord, hhull⟩ := hrs
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hVc : Continuous (B2.Vr κ T B ω) := B2.continuous_vrev hWc T
  have hV0 : B2.Vr κ T B ω 0 = 0 := B2.vrev_zero hT.le
  rw [LoewnerAlgebra.revHull_eq_fwdHull_timeRev _ hVc hV0 hT,
    Thm14FromThm13.fwdHull_eq_of_eqOn (by fun_prop) hWc hT.le, hhull T hT.le]
  · exact Thm14FromThm13.isSimpleCurveHull_image_Ioc hchord hT
  · intro s hs
    simp only [B2.Vr]
    rw [B2.vrev_of_mem ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B2.vrev_of_mem ⟨hT.le, le_rfl⟩, sub_sub_cancel, sub_self, hW0]
    ring

/-- **`zeroMinus` facts of `handoff/ESM.md` (items 2, 3), a.s.** For `V = Vr κ T B ω`,
`a = zeroMinus V T`: `0₋(0) = 0`, `a < 0`, `0₋` strictly decreasing and continuous on `[0,T]`,
`τ_x ∈ [0,T]` with `0₋(τ_x) = x` for `x ∈ (a, 0]`, and `τ_x < T ↔ a < x` for `x ≤ 0`. -/
theorem ae_zeroMinus_Vr_facts (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ ≤ 4) {T : ℝ} (hT : 0 < T) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, zeroMinus (B2.Vr κ T B ω) 0 = 0 ∧ zeroMinus (B2.Vr κ T B ω) T < 0 ∧
      StrictAntiOn (zeroMinus (B2.Vr κ T B ω)) (Icc 0 T) ∧
      ContinuousOn (zeroMinus (B2.Vr κ T B ω)) (Icc 0 T) ∧
      (∀ x ∈ Ioc (zeroMinus (B2.Vr κ T B ω) T) 0,
        realHitTime (B2.Vr κ T B ω) x =
            ENNReal.ofReal (realHitTime (B2.Vr κ T B ω) x).toReal ∧
          (realHitTime (B2.Vr κ T B ω) x).toReal ∈ Icc 0 T ∧
          zeroMinus (B2.Vr κ T B ω) (realHitTime (B2.Vr κ T B ω) x).toReal = x) ∧
      (∀ x ≤ 0, realHitTime (B2.Vr κ T B ω) x < ENNReal.ofReal T ↔
        zeroMinus (B2.Vr κ T B ω) T < x) := by
  filter_upwards [ae_isSimpleCurveHull_revHull_Vr hRSS hκ0 hκ4 hT P B hB, hB.cont] with ω hK hc
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hVc : Continuous (B2.Vr κ T B ω) := B2.continuous_vrev hWc T
  have hV0 : B2.Vr κ T B ω 0 = 0 := B2.vrev_zero hT.le
  exact ⟨zeroMinus_zero_time hVc hV0, zeroMinus_neg_of_le hVc hV0 hT hK hT le_rfl,
    strictAntiOn_zeroMinus hVc hV0 hT hK, continuousOn_zeroMinus_Icc hVc hV0 hT hK,
    fun x hx => hitTime_spec hVc hV0 hT hK hx, fun x hx => realHitTime_lt_iff hVc hV0 hT hK hx⟩

end B5
end QuantumZipper
