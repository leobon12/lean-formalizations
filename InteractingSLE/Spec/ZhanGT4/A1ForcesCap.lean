/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ForcesFam

/-!
# Zhan's A.1 (R80): the family's caps (`measurable_S`, `hSm`, `hgS`, `hgζ`, `hcov`)

Packet PROVE-A1-FORCES. A1-FAMILY's step 1 asks for caps `S σ k = a(T_k)`: the image capacity of the image curve at
its own rectangle-`k` exit `T_k`, `0` off the live event or when the frozen hull is not protected. A1-FAMILY's
`isSeedSampleLaw_of_seed` needs `S k = a(T_k)` when `T_k` is before the seeded horizon and `S k ≥ S m` when `T_k`
is after it; `FamilyRect(Fst).ofRect` needs the cap measurable for the two stopped records (`hSm`), the cap comparisons
`{S k ≤ r} ∩ {r < S m}` measurable for them (`hgS`), the cap below the image lifetime (`hgζ`) and the clock exhaustion
(`hcov`); `FrozenFamily(Fst)` needs joint measurability in the frozen time (`measurable_S`). An own time `T_k` that is
not a pre-contact time (the image curve dies inside its enclosure) has no clock value, so the cap is read through the
**clock up to `T`**:

* `clkSup … T = ⨆ {ofReal (clock q) : q ∈ ℚ, 0 ≤ q < T, q before contact}`: monotone in `T` (`clkSup_mono`), `0` for
  `T ≤ 0`, below the image lifetime (`clkSup_le_imgLife`), above the clock at every pre-contact `s < T`
  (`imgClk_le_clkSup`), and **the clock itself at a good time** (`clkSup_eq_of_isGoodTime`, by left continuity of the
  clock); **`clkSup_congr`**: it reads the image curve's driver on `[0, T)` only (and the conditioning curve's on
  `[0, τ]`), given both lifetimes are at least `T`; **`CanonHyp.measurable_clkSup`**: at a measurable random own time it
  is measurable (a countable supremum of A1-MARG's `clkAt` on the pre-contact events);
* `capFst live … τ T`: the cap on `X × Y` (conditioning curve on `X`), `(clkSup … (T z)).toNNReal` on the live event;
  **`measurable_capFst`** (`measurable_S`), **`measurable_capFst_of_stopped`** (`hSm`, from replacement drivers
  measurable for the records), **`capFst_le_inter_eq`** / **`measurableSet_capFst_le_inter`** (`hgS`: on
  `{r < S m}` the comparison with `S k` is the comparison with the cap at `min T_k T_m`), **`capFst_le_rLifeFst`**
  (`hgζ`), **`imgClk_le_capFst`** (`hcov`), `capFst_eq_of_isGoodTime`, `capFst_mono`, `capFst_of_nonpos`
  (A1-FAMILY's `hSm`, `hcap₁`, `hcap₂`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Forces

open A2X A1Ref A1Core A1Marg A1SeedGeom

/-! ### The clock up to an own time -/

/-- **The canonical clock up to the own time `T`**: the supremum of `ofReal (imgClk q)` over the rational pre-contact
own times `0 ≤ q < T`. -/
def clkSup (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ T : ℝ) : ℝ≥0∞ :=
  ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T ∧ ENNReal.ofReal q < contactTime xj wj ζj xk wk τ),
    ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q)

section Det

variable {xj xk τ : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞}

theorem clkSup_mono {T T' : ℝ} (h : T ≤ T') : clkSup xj wj ζj xk wk τ T ≤ clkSup xj wj ζj xk wk τ T' :=
  iSup_mono fun _ => iSup_mono' fun hq => ⟨⟨hq.1, hq.2.1.trans_le h, hq.2.2⟩, le_rfl⟩

theorem clkSup_of_nonpos {T : ℝ} (hT : T ≤ 0) : clkSup xj wj ζj xk wk τ T = 0 :=
  le_antisymm (iSup₂_le fun _ hq => absurd (hq.1.trans_lt hq.2.1) (not_lt.2 hT)) bot_le

/-- The clock up to any own time is below the canonical image lifetime. -/
theorem clkSup_le_imgLife (T : ℝ) : clkSup xj wj ζj xk wk τ T ≤ imgLife xj wj ζj xk wk τ :=
  iSup₂_le fun q hq => le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ) =>
    ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ s)) (Real.toNNReal q) (by rw [← ENNReal.ofReal]; exact hq.2.2)
    (by rw [Real.coe_toNNReal _ hq.1])

variable (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
  (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
include hj hj0 hk hk0 hτ

/-- The clock at a pre-contact own time `s < T` is below the clock up to `T`. -/
theorem imgClk_le_clkSup {s T : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    (hs : ENNReal.ofReal s < contactTime xj wj ζj xk wk τ) :
    ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ s) ≤ clkSup xj wj ζj xk wk τ T := by
  have hmono := (isImageChainUpTo_canonical (xj := xj) (xk := xk) hj hj0 hk hk0 hτ 0).2.2.1
  obtain ⟨r, -, hsr, hrc⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs
  have hsr' : s < r := ((ENNReal.ofReal_lt_ofReal_iff').1 hsr).1
  obtain ⟨q, hsq, hqm⟩ := exists_rat_btwn (lt_min hsr' hsT)
  have hq0 : (0 : ℝ) ≤ q := hs0.trans hsq.le
  have hqc : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ :=
    (ENNReal.ofReal_le_ofReal (hqm.le.trans (min_le_left _ _))).trans_lt hrc
  refine le_iSup₂_of_le (f := fun (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T ∧
    ENNReal.ofReal q < contactTime xj wj ζj xk wk τ) => ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q)) q
    ⟨hq0, hqm.trans_le (min_le_right _ _), hqc⟩ ?_
  exact ENNReal.ofReal_le_ofReal (hmono.monotoneOn ⟨hs0, hs⟩ ⟨hq0, hqc⟩ hsq.le)

/-- **At a good own time the clock up to `T` is the clock at `T`** (left continuity of the clock). -/
theorem clkSup_eq_of_isGoodTime {T : ℝ} (hT : IsGoodTime xj wj ζj xk wk τ T) :
    clkSup xj wj ζj xk wk τ T = ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ T) := by
  have hch := isImageChainUpTo_canonical (xj := xj) (xk := xk) hj hj0 hk hk0 hτ 0
  have hmono := hch.2.2.1
  have hTI : T ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} := ⟨hT.1.le, hT.2⟩
  refine le_antisymm (iSup₂_le fun q hq => ENNReal.ofReal_le_ofReal
    (hmono.monotoneOn ⟨hq.1, hq.2.2⟩ hTI hq.2.1.le)) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hch.2.1 T hTI) ε (NNReal.coe_pos.2 hε)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self T hδ) hT.1)
  have hq0 : (0 : ℝ) ≤ q := (le_max_right _ _).trans hq1.le
  have hqc : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ := (ENNReal.ofReal_le_ofReal hq2.le).trans_lt hT.2
  have hd : dist (q : ℝ) T < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 hq2)]
    linarith [le_max_left (T - δ) 0]
  have h1 := hδc ⟨hq0, hqc⟩ hd
  rw [Real.dist_eq] at h1
  have h2 : A1Ref.imgClk xj wj xk wk τ T ≤ A1Ref.imgClk xj wj xk wk τ q + ε := by
    linarith [(abs_sub_lt_iff.1 h1).2]
  have hqle : ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q) ≤ clkSup xj wj ζj xk wk τ T :=
    le_iSup₂_of_le (f := fun (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T ∧
      ENNReal.ofReal q < contactTime xj wj ζj xk wk τ) => ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q)) q
      ⟨hq0, hq2, hqc⟩ le_rfl
  calc ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ T)
      ≤ ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q + ε) := ENNReal.ofReal_le_ofReal h2
    _ ≤ ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (A1Ref.imgClk xj wj xk wk τ q) + ε := by rw [ENNReal.ofReal_coe_nnreal]
    _ ≤ clkSup xj wj ζj xk wk τ T + ε := add_le_add_left hqle _

end Det

/-! ### Locality of the clock up to `T` -/

section Congr

variable {xj xk τ : ℝ} {wj wk wj' wk' : ℝ → ℝ} {ζj ζj' : ℝ≥0∞}

/-- Pre-contact transfers to drivers agreeing on `[0, T₀]`, `T₀ > q`, when the second lifetime is at least `T₀`. -/
theorem ofReal_lt_contactTime_of_eqOn {T₀ q : ℝ} (hq0 : 0 ≤ q) (hqT : q < T₀)
    (hwj : ContinuousOn wj (Icc 0 T₀)) (hwj' : ContinuousOn wj' (Icc 0 T₀)) (hjeq : EqOn wj wj' (Icc 0 T₀))
    (hζ' : ENNReal.ofReal T₀ ≤ ζj') (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ'))
    (hk' : ∃ τ', τ < τ' ∧ ContinuousOn wk' (Icc 0 τ')) (hτ : 0 ≤ τ) (hkeq : EqOn wk wk' (Icc 0 τ))
    (hq : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ) : ENNReal.ofReal q < contactTime xj wj' ζj' xk wk' τ := by
  obtain ⟨q', hqq', -, hdisj⟩ := (ofReal_lt_contactTime_iff hq0).1 hq
  obtain ⟨q'', h1, h2⟩ := exists_rat_btwn (lt_min hqq' hqT)
  have hq''0 : (0 : ℝ) ≤ q'' := hq0.trans h1.le
  have hq''T : (q'' : ℝ) < T₀ := h2.trans_le (min_le_right _ _)
  refine (ofReal_lt_contactTime_iff hq0).2 ⟨q'', h1, ?_, fun hne => hdisj ?_⟩
  · exact ((ENNReal.ofReal_lt_ofReal_iff (hq0.trans_lt hqT)).2 hq''T).trans_le hζ'
  · have hjh : physHull xj wj q'' = physHull xj wj' q'' :=
      physHull_congr_of_continuousOn hwj hwj' hq''0 hq''T (hjeq.mono (Icc_subset_Icc_right hq''T.le))
    have hkh : physHull xk wk τ = physHull xk wk' τ := by
      obtain ⟨τ₁, hτ₁, hc₁⟩ := hk
      obtain ⟨τ₂, hτ₂, hc₂⟩ := hk'
      exact physHull_congr_of_continuousOn (hc₁.mono (Icc_subset_Icc_right (min_le_left _ _)))
        (hc₂.mono (Icc_subset_Icc_right (min_le_right _ _))) hτ (lt_min hτ₁ hτ₂) hkeq
    rw [← hjh, ← hkh] at hne
    obtain ⟨z, hz1, hz2⟩ := hne
    exact ⟨z, closure_mono (physHull_mono xj wj (h2.le.trans (min_le_left _ _))) hz1, hz2⟩

/-- **The clock up to `T` is local**: it reads the image curve's driver on `[0, T)` only and the conditioning curve's
driver on `[0, τ]` only, when both image lifetimes are at least `T`. -/
theorem clkSup_congr {T : ℝ} (hj : ∀ T' : ℝ, ENNReal.ofReal T' < ζj → ContinuousOn wj (Icc 0 T'))
    (hj' : ∀ T' : ℝ, ENNReal.ofReal T' < ζj' → ContinuousOn wj' (Icc 0 T'))
    (hζ : ENNReal.ofReal T ≤ ζj) (hζ' : ENNReal.ofReal T ≤ ζj') (hjeq : ∀ s, 0 ≤ s → s < T → wj s = wj' s)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk' : ∃ τ', τ < τ' ∧ ContinuousOn wk' (Icc 0 τ'))
    (hτ : 0 ≤ τ) (hkeq : EqOn wk wk' (Icc 0 τ)) :
    clkSup xj wj ζj xk wk τ T = clkSup xj wj' ζj' xk wk' τ T := by
  unfold clkSup
  refine iSup_congr fun q => ?_
  by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T
  · set T₀ : ℝ := ((q : ℝ) + T) / 2 with hT₀
    have hqT₀ : (q : ℝ) < T₀ := by rw [hT₀]; linarith [hq.2]
    have hT₀T : T₀ < T := by rw [hT₀]; linarith [hq.2]
    have hlt : ENNReal.ofReal T₀ < ENNReal.ofReal T :=
      (ENNReal.ofReal_lt_ofReal_iff (hq.1.trans_lt hq.2)).2 hT₀T
    have hc : ContinuousOn wj (Icc 0 T₀) := hj T₀ (hlt.trans_le hζ)
    have hc' : ContinuousOn wj' (Icc 0 T₀) := hj' T₀ (hlt.trans_le hζ')
    have he : EqOn wj wj' (Icc 0 T₀) := fun s hs => hjeq s hs.1 (hs.2.trans_lt hT₀T)
    have hiff : ENNReal.ofReal q < contactTime xj wj ζj xk wk τ ↔
        ENNReal.ofReal q < contactTime xj wj' ζj' xk wk' τ :=
      ⟨ofReal_lt_contactTime_of_eqOn hq.1 hqT₀ hc hc' he (hlt.le.trans hζ') hk hk' hτ hkeq,
        ofReal_lt_contactTime_of_eqOn hq.1 hqT₀ hc' hc he.symm (hlt.le.trans hζ) hk' hk hτ hkeq.symm⟩
    have hclk : A1Ref.imgClk xj wj xk wk τ q = A1Ref.imgClk xj wj' xk wk' τ q :=
      imgClk_congr hτ hkeq hc hc' hqT₀ (he.mono (Icc_subset_Icc_right hqT₀.le))
    exact iSup_congr_Prop (and_congr_right' (and_congr_right' hiff)) fun _ => by rw [hclk]
  · rw [iSup_neg (fun h => hq ⟨h.1, h.2.1⟩), iSup_neg (fun h => hq ⟨h.1, h.2.1⟩)]

end Congr

/-! ### Measurability at a random own time -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ}
  {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}

/-- **The clock up to a measurable random own time is measurable** (masked by the live event), under A1-MARG's
standing hypotheses: a countable supremum of A1-MARG's clocks on the pre-contact events. -/
theorem _root_.InteractingSLE.ZhanGT4.A1Marg.CanonHyp.measurable_clkSup (hC : CanonHyp L wj ζj wk ζk τ)
    (xj xk : ℝ) {T : Ω → ℝ} (hT : Measurable T) :
    Measurable (L.indicator fun ω => clkSup xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)
      (T ω)) := by
  classical
  set g : ℚ → Ω → ℝ≥0∞ := fun q ω => if 0 ≤ (q : ℝ) then {ω | (q : ℝ) < T ω}.indicator (fun ω =>
    ENNReal.ofReal ((preC L xj xk wj ζj wk τ q).indicator (clkAt xj xk wj wk τ q) ω)) ω else 0 with hg
  have hgm : ∀ q, Measurable (g q) := fun q => by
    by_cases hq : 0 ≤ (q : ℝ)
    · simp only [hg, hq, ↓reduceIte]
      exact (ENNReal.measurable_ofReal.comp (hC.measurable_clkAt_drvAt xj xk hq).1).indicator
        (measurableSet_lt measurable_const hT)
    · simp only [hg, hq, ↓reduceIte]
      exact measurable_const
  have hzero : ∀ (q : ℚ) ω, ¬(0 ≤ (q : ℝ) ∧ (q : ℝ) < T ω ∧ ω ∈ preC L xj xk wj ζj wk τ q) → g q ω = 0 := by
    intro q ω h
    simp only [hg]
    split_ifs with h0
    · by_cases hlt : (q : ℝ) < T ω
      · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) < T ω} from hlt),
          indicator_of_notMem (fun hp => h ⟨h0, hlt, hp⟩), ENNReal.ofReal_zero]
      · rw [indicator_of_notMem (show ω ∉ {ω | (q : ℝ) < T ω} from hlt)]
    · rfl
  have e : (L.indicator fun ω => clkSup xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) (T ω)) =
      fun ω => ⨆ q, g q ω := by
    funext ω
    by_cases hL : ω ∈ L
    · rw [indicator_of_mem hL, clkSup]
      refine iSup_congr fun q => ?_
      by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T ω ∧
          ENNReal.ofReal q < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)
      · rw [iSup_pos hq]
        have hp : ω ∈ preC L xj xk wj ζj wk τ q := ⟨hL, hq.2.2⟩
        simp only [hg, hq.1, ↓reduceIte, indicator_of_mem (show ω ∈ {ω | (q : ℝ) < T ω} from hq.2.1),
          indicator_of_mem hp, clkAt]
      · rw [iSup_neg hq, hzero q ω fun h => hq ⟨h.1, h.2.1, h.2.2.2⟩]
        rfl
    · rw [indicator_of_notMem hL]
      exact (ENNReal.iSup_eq_zero.2 fun q => hzero q ω fun h => hL h.2.2.1).symm
  rw [e]
  exact Measurable.iSup hgm

end Meas

/-! ### The cap on `X × Y` (conditioning curve on `X`, image curve on `Y`) -/

section Fst

variable {X Y : Type*}

/-- **The cap** of the image curve (on `Y`) at its own time `T z`, for the conditioning curve (on `X`) at the stop
`τ`: the clock up to `T z` on the live event (`0` off it, and for `T z ≤ 0`). -/
def capFst (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (τ : X → ℝ≥0) (T : X × Y → ℝ) (z : X × Y) : ℝ≥0 :=
  ({z : X × Y | live (τ z.1) z.1}.indicator (fun z => clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
    (Strip.extPath (Wk · z.1)) (τ z.1) (T z)) z).toNNReal

variable {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
  {τ : X → ℝ≥0} {T T' : X × Y → ℝ} {z : X × Y}

/-- On the fibre over `x` only the frozen time `τ x` is read (`FrozenFamilyFst.Sat`). -/
theorem capFst_at (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (τ : X → ℝ≥0) (T : ℝ≥0 → X × Y → ℝ) (z : X × Y) :
    capFst live xj Wj ζj xk Wk (fun _ => τ z.1) (T (τ z.1)) z =
      capFst live xj Wj ζj xk Wk τ (fun z => T (τ z.1) z) z := rfl

theorem capFst_of_live (h : live (τ z.1) z.1) :
    capFst live xj Wj ζj xk Wk τ T z = (clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
      (Strip.extPath (Wk · z.1)) (τ z.1) (T z)).toNNReal := by
  rw [capFst, indicator_of_mem (show z ∈ {z : X × Y | live (τ z.1) z.1} from h)]

theorem capFst_of_not_live (h : ¬ live (τ z.1) z.1) : capFst live xj Wj ζj xk Wk τ T z = 0 := by
  rw [capFst, indicator_of_notMem (show z ∉ {z : X × Y | live (τ z.1) z.1} from h), ENNReal.toNNReal_zero]

/-- The cap reads the own time only at the sample. -/
theorem capFst_congr_pt (h : T z = T' z) : capFst live xj Wj ζj xk Wk τ T z = capFst live xj Wj ζj xk Wk τ T' z := by
  by_cases hl : live (τ z.1) z.1
  · rw [capFst_of_live hl, capFst_of_live hl, h]
  · rw [capFst_of_not_live hl, capFst_of_not_live hl]

/-- No cap before a positive own time (A1-FAMILY's `isSeedSampleLaw_of_cap_zero`; an unprotected rectangle). -/
theorem capFst_of_nonpos (hT : T z ≤ 0) : capFst live xj Wj ζj xk Wk τ T z = 0 := by
  by_cases hl : live (τ z.1) z.1
  · rw [capFst_of_live hl, clkSup_of_nonpos hT, ENNReal.toNNReal_zero]
  · exact capFst_of_not_live hl

/-- **At a good own time the cap is the clock** (A1-FAMILY's `hSm`, `hcap₁`: the seeded horizon `a(S)`). -/
theorem capFst_eq_of_isGoodTime (hlive : live (τ z.1) z.1)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T))
    (hj0 : Wj 0 z.2 = 0) (hk : ∃ τ' : ℝ, (τ z.1 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ'))
    (hk0 : Wk 0 z.1 = 0)
    (hT : IsGoodTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z)) :
    capFst live xj Wj ζj xk Wk τ T z =
      (A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z)).toNNReal := by
  rw [capFst_of_live hlive, clkSup_eq_of_isGoodTime hj (by simp only [Strip.extPath, Real.toNNReal_zero, hj0]) hk
    (by simp only [Strip.extPath, Real.toNNReal_zero, hk0]) (τ z.1).coe_nonneg hT, ENNReal.ofReal,
    ENNReal.toNNReal_coe]

/-- **The cap is monotone in the own time** (A1-FAMILY's `hcap₂`), when the later clock is finite. -/
theorem capFst_mono (hTT : T z ≤ T' z)
    (hfin : live (τ z.1) z.1 → clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1)
      (T' z) ≠ ∞) :
    capFst live xj Wj ζj xk Wk τ T z ≤ capFst live xj Wj ζj xk Wk τ T' z := by
  by_cases hl : live (τ z.1) z.1
  · rw [capFst_of_live hl, capFst_of_live hl]
    exact ENNReal.toNNReal_mono (hfin hl) (clkSup_mono hTT)
  · rw [capFst_of_not_live hl, capFst_of_not_live hl]

/-- **`hgζ`: the cap is below the masked canonical image lifetime.** -/
theorem capFst_le_rLifeFst (T : X × Y → ℝ) (z : X × Y) :
    (capFst live xj Wj ζj xk Wk τ T z : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk τ z := by
  by_cases hl : live (τ z.1) z.1
  · rw [capFst_of_live hl]
    simp only [rLifeFst, A1Ref.cImgLifeM, A1Ref.cImgLife, hl, ↓reduceIte]
    exact ENNReal.coe_toNNReal_le_self.trans (clkSup_le_imgLife _)
  · rw [capFst_of_not_live hl, ENNReal.coe_zero]
    exact bot_le

/-- **`hcov`: the clock at a pre-contact own time `s < T z` is below the cap** (finite clock up to `T z`). -/
theorem imgClk_le_capFst (hlive : live (τ z.1) z.1)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T))
    (hj0 : Wj 0 z.2 = 0) (hk : ∃ τ' : ℝ, (τ z.1 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ'))
    (hk0 : Wk 0 z.1 = 0) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T z)
    (hs : ENNReal.ofReal s < contactTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1))
      (τ z.1))
    (hfin : clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (T z) ≠ ∞) :
    A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤
      capFst live xj Wj ζj xk Wk τ T z := by
  rw [capFst_of_live hlive]
  have h := imgClk_le_clkSup hj (by simp only [Strip.extPath, Real.toNNReal_zero, hj0]) hk
    (by simp only [Strip.extPath, Real.toNNReal_zero, hk0]) (τ z.1).coe_nonneg hs0 hsT hs
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h

/-- **The clock exhaustion of `FamilyRectFst.ofRect` (`hcov`)** for caps at own times `T m` exhausting the contact
time with finite clocks. -/
theorem cover_capFst {Tm : ℕ → X × Y → ℝ} (hlive : live (τ z.1) z.1)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T))
    (hj0 : Wj 0 z.2 = 0) (hk : ∃ τ' : ℝ, (τ z.1 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ'))
    (hk0 : Wk 0 z.1 = 0)
    (hex : ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
      (Strip.extPath (Wk · z.1)) (τ z.1) → ∃ m, (s : ℝ) < Tm m z)
    (hfin : ∀ m, clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) (Tm m z) ≠ ∞) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk (Strip.extPath (Wk · z.1))
      (τ z.1) → ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤
        capFst live xj Wj ζj xk Wk τ (Tm m) z := by
  intro s hs
  obtain ⟨m, hm⟩ := hex s hs
  exact ⟨m, imgClk_le_capFst hlive hj hj0 hk hk0 s.coe_nonneg hm (by rwa [ENNReal.ofReal_coe_nnreal]) (hfin m)⟩

/-- **`hgS`, set form**: on `{r < S m}` the comparison `S k ≤ r` is the comparison of the cap at `min T_k T_m` (a time
before the `m`-th record's stop), when the clock up to `T_k` is finite. -/
theorem capFst_le_inter_eq {Tk Tm : X × Y → ℝ}
    (hfin : ∀ z : X × Y, live (τ z.1) z.1 → clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
      (Strip.extPath (Wk · z.1)) (τ z.1) (Tk z) ≠ ∞) (r : ℝ≥0) :
    {z | capFst live xj Wj ζj xk Wk τ Tk z ≤ r} ∩ {z | r < capFst live xj Wj ζj xk Wk τ Tm z} =
      {z | capFst live xj Wj ζj xk Wk τ (fun z => min (Tk z) (Tm z)) z ≤ r} ∩
        {z | r < capFst live xj Wj ζj xk Wk τ Tm z} := by
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases le_total (Tk z) (Tm z) with h | h
    · rwa [capFst_congr_pt (T' := Tk) (min_eq_left h)]
    · rw [capFst_congr_pt (T' := Tm) (min_eq_right h)]
      exact (capFst_mono h (hfin z)).trans h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases le_total (Tk z) (Tm z) with h | h
    · rwa [capFst_congr_pt (T' := Tk) (min_eq_left h)] at h1
    · rw [capFst_congr_pt (T' := Tm) (min_eq_right h)] at h1
      exact absurd (h1.trans_lt h2) (lt_irrefl _)

/-- **`hgS` of `FamilyRectFst.ofRect`**: the cap comparisons are events of any σ-algebra `𝓜` for which the caps at
`min T_k T_m` and at `T_m` are measurable. -/
theorem measurableSet_capFst_le_inter [𝓜 : MeasurableSpace (X × Y)] {Tk Tm : X × Y → ℝ}
    (hmin : Measurable (capFst live xj Wj ζj xk Wk τ fun z => min (Tk z) (Tm z)))
    (hm : Measurable (capFst live xj Wj ζj xk Wk τ Tm))
    (hfin : ∀ z : X × Y, live (τ z.1) z.1 → clkSup xj (Strip.extPath (Wj · z.2)) (ζj z.2) xk
      (Strip.extPath (Wk · z.1)) (τ z.1) (Tk z) ≠ ∞) (r : ℝ≥0) :
    MeasurableSet ({z | capFst live xj Wj ζj xk Wk τ Tk z ≤ r} ∩ {z | r < capFst live xj Wj ζj xk Wk τ Tm z}) := by
  rw [capFst_le_inter_eq hfin r]
  exact (measurableSet_le hmin measurable_const).inter (measurableSet_lt measurable_const hm)

/-- **`FrozenFamilyFst.measurable_S`**: the caps at the deterministic frozen time `σ`, with own times `T σ` jointly
measurable, are jointly measurable in `(σ, z)` (A1-MARG's standing hypotheses on the two drivers). -/
theorem measurable_capFst [MeasurableSpace X] [MeasurableSpace Y]
    (hlive : MeasurableSet {q : ℝ≥0 × X | live q.1 q.2}) {ζk : X → ℝ≥0∞}
    (hlk : ∀ s x, live s x → (s : ℝ≥0∞) < ζk x)
    (hjc : ∀ y, ContinuousOn (Wj · y) {t | (t : ℝ≥0∞) < ζj y}) (hj0 : ∀ y, Wj 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk · x) {t | (t : ℝ≥0∞) < ζk x}) (hk0 : ∀ x, Wk 0 x = 0)
    (hjm : ∀ t, Measurable (Wj t)) (hkm : ∀ t, Measurable (Wk t)) (hζj : Measurable ζj) (hζk : Measurable ζk)
    {T : ℝ≥0 → X × Y → ℝ} (hT : Measurable fun q : ℝ≥0 × (X × Y) => T q.1 q.2) :
    Measurable fun q : ℝ≥0 × (X × Y) => capFst live xj Wj ζj xk Wk (fun _ => q.1) (T q.1) q.2 := by
  have hC := canonHyp_of_paths (Ω := ℝ≥0 × (X × Y)) (πj := fun q => q.2.2) (πk := fun q => q.2.1)
    (τ := Prod.fst) measurable_snd.snd measurable_snd.fst measurable_fst hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
  exact (hC.measurable_clkSup xj xk hT).ennreal_toNNReal

/-- **`hSm` of `FamilyRectFst.ofRect`: the cap is measurable for the two stopped records**, from replacement data
measurable for the records (as measurable structures `𝓐`, `𝓑`) satisfying A1-MARG's (m3) hypotheses, which agree with
the original data where the own time is positive: the same live event, and on it the image curve's drivers agree
before `T z` (both lifetimes at least `T z`) and the conditioning curve's drivers agree up to the stop. -/
theorem measurable_capFst_of_stopped [𝓐 : MeasurableSpace X] [𝓑 : MeasurableSpace Y] {live' : ℝ≥0 → X → Prop}
    {Wj' : ℝ≥0 → Y → ℝ} {ζj' : Y → ℝ≥0∞} {Wk' : ℝ≥0 → X → ℝ} {ζk' : X → ℝ≥0∞} (hτ : Measurable τ)
    (hlm : MeasurableSet {q : ℝ≥0 × X | live' q.1 q.2}) (hlk : ∀ s x, live' s x → (s : ℝ≥0∞) < ζk' x)
    (hjc : ∀ y, ContinuousOn (Wj' · y) {t | (t : ℝ≥0∞) < ζj' y}) (hj0' : ∀ y, Wj' 0 y = 0)
    (hkc : ∀ x, ContinuousOn (Wk' · x) {t | (t : ℝ≥0∞) < ζk' x}) (hk0' : ∀ x, Wk' 0 x = 0)
    (hjm : ∀ t, Measurable (Wj' t)) (hkm : ∀ t, Measurable (Wk' t)) (hζj : Measurable ζj') (hζk : Measurable ζk')
    (hT : Measurable T)
    (hloc : ∀ z : X × Y, 0 < T z → (live (τ z.1) z.1 ↔ live' (τ z.1) z.1) ∧ (live (τ z.1) z.1 →
      (∀ T : ℝ, ENNReal.ofReal T < ζj z.2 → ContinuousOn (Strip.extPath (Wj · z.2)) (Icc 0 T)) ∧
      (∃ τ' : ℝ, (τ z.1 : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (Wk · z.1)) (Icc 0 τ')) ∧
      ENNReal.ofReal (T z) ≤ ζj z.2 ∧ ENNReal.ofReal (T z) ≤ ζj' z.2 ∧
      (∀ t : ℝ≥0, (t : ℝ) < T z → Wj' t z.2 = Wj t z.2) ∧ (∀ t ≤ τ z.1, Wk' t z.1 = Wk t z.1))) :
    Measurable (capFst live xj Wj ζj xk Wk τ T) := by
  have hC := canonHyp_of_paths (Ω := X × Y) (πj := Prod.snd) (πk := Prod.fst) (τ := fun z => τ z.1)
    measurable_snd measurable_fst (hτ.comp measurable_fst) hlm hlk hjc hj0' hkc hk0' hjm hkm hζj hζk
  have hm : Measurable (capFst live' xj Wj' ζj' xk Wk' τ T) := (hC.measurable_clkSup xj xk hT).ennreal_toNNReal
  convert hm using 1
  funext z
  rcases le_or_gt (T z) 0 with h0 | h0
  · rw [capFst_of_nonpos h0, capFst_of_nonpos h0]
  obtain ⟨hiff, hdat⟩ := hloc z h0
  by_cases hl : live (τ z.1) z.1
  · obtain ⟨hj, hk, hζ, hζ', hjeq, hkeq⟩ := hdat hl
    rw [capFst_of_live hl, capFst_of_live (hiff.1 hl)]
    congr 1
    refine clkSup_congr hj (fun T hT => A1Ref.continuousOn_extPath_Icc (hjc z.2) hT) hζ hζ' (fun s hs0 hsT => ?_)
      hk (A1Ref.exists_continuousOn_extPath_beyond (hkc z.1) (hlk _ _ (hiff.1 hl))) (τ z.1).coe_nonneg
      (fun s hs => ?_)
    · simp only [Strip.extPath]
      rw [hjeq _ (by rw [Real.coe_toNNReal _ hs0]; exact hsT)]
    · simp only [Strip.extPath]
      rw [hkeq _ (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  · rw [capFst_of_not_live hl, capFst_of_not_live (fun h => hl (hiff.2 h))]

end Fst

end InteractingSLE.ZhanGT4.A1Forces
