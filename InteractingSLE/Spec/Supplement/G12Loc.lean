/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Obs
import InteractingSLE.Spec.Supplement.G12Det
import InteractingSLE.Spec.Supplement.GB5Loc
import InteractingSLE.Spec.Zhan.StripTimeMart

/-!
# Lemma G12: localization of the mark observable of an arbitrary word

Packet PROVE-G12. For an integrated `SLE_κ(ρ)` evolution of any force word and a right mark `j₀` with `x_{j₀} > 0`,
the coordinates `Λ = (V^L, V^R, T)` (`T = ∫ (V^{j₀} − W)⁻²` the clock of the mark) are localized at

  `σ_n = T_n ∧ (exit of the level-`n` box) ∧ (exit of `|B|` from `(−n, n)`)`

(`locG`), where `T_n ≤ n` is an announcing sequence of the lifetime (`Coupling.exists_isAnnouncingSeq_le`) and the
level-`n` box of the state is: `V^{j₀} − W ≥ δ`, `|V^{j₀} − V^m| ≥ δ` for every mark `m` off the group of `j₀`,
`‖(W, V)‖ ≤ n` (`δ = 1/(n+1)`). The good paths are PROVE-T14-GB's `GB5.IsGBGood` (the frozen pathwise conditions, a
continuous Brownian path from `0`, the announcing property), whose stopping-time and Brownian lemmas are reused.

* `martingale_locG`: the localized Itô formula (`Ito.martingale_itoLocalized`) for every `C³` function on the region
  of the mark observable (`G12Obs.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

open Supp8.GB5 (IsGBGood isFilteredBrownianReal_brownG_gb continuous_brownG_gb isStoppingTime_hit_gb
  measurableSet_good_usual' nonneg_of_le_hitBelow abs_le_norm_state)

variable {nL nR : ℕ}

/-! ### The level function and the box -/

/-- `δ_n = 1/(n+1)`. -/
def dlt (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem dlt_pos (n : ℕ) : 0 < dlt n := by unfold dlt; positivity

/-- The level-`n` function of the state `(w, v^L, v^R)`: nonnegative exactly in the box. -/
def levG (xR : Fin nR → ℝ) (j₀ : Fin nR) (n : ℕ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min (min (st.2.2 j₀ - st.1 - dlt n) ((n : ℝ) - ‖st‖))
    (-((∑ i, max 0 (dlt n - |st.2.2 j₀ - st.2.1 i|)) + ∑ j ∈ offY xR j₀, max 0 (dlt n - |st.2.2 j₀ - st.2.2 j|)))

theorem continuous_levG (xR : Fin nR → ℝ) (j₀ : Fin nR) (n : ℕ) : Continuous (levG (nL := nL) xR j₀ n) := by
  unfold levG
  fun_prop

theorem levG_nonneg_iff {xR : Fin nR → ℝ} {j₀ : Fin nR} {n : ℕ} {st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} :
    0 ≤ levG xR j₀ n st ↔ dlt n ≤ st.2.2 j₀ - st.1 ∧ ‖st‖ ≤ n ∧ (∀ i, dlt n ≤ |st.2.2 j₀ - st.2.1 i|) ∧
      ∀ j ∈ offY xR j₀, dlt n ≤ |st.2.2 j₀ - st.2.2 j| := by
  simp only [levG, le_min_iff, Left.nonneg_neg_iff]
  have hL : (∑ i, max 0 (dlt n - |st.2.2 j₀ - st.2.1 i|)) ≤ 0 ↔ ∀ i, dlt n ≤ |st.2.2 j₀ - st.2.1 i| := by
    constructor
    · intro h i
      have h1 := (Finset.single_le_sum (fun k _ => le_max_left 0 (dlt n - |st.2.2 j₀ - st.2.1 k|))
        (mem_univ i)).trans h
      have h2 := le_max_right 0 (dlt n - |st.2.2 j₀ - st.2.1 i|)
      linarith
    · intro h
      exact (Finset.sum_eq_zero fun i _ => max_eq_left (by linarith [h i])).le
  have hR : (∑ j ∈ offY xR j₀, max 0 (dlt n - |st.2.2 j₀ - st.2.2 j|)) ≤ 0 ↔
      ∀ j ∈ offY xR j₀, dlt n ≤ |st.2.2 j₀ - st.2.2 j| := by
    constructor
    · intro h j hj
      have h1 := (Finset.single_le_sum (fun k _ => le_max_left 0 (dlt n - |st.2.2 j₀ - st.2.2 k|)) hj).trans h
      have h2 := le_max_right 0 (dlt n - |st.2.2 j₀ - st.2.2 j|)
      linarith
    · intro h
      exact (Finset.sum_eq_zero fun j hj => max_eq_left (by linarith [h j hj])).le
  have hsum : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b ≤ 0 ↔ a ≤ 0 ∧ b ≤ 0) := fun a b ha hb =>
    ⟨fun h => ⟨by linarith, by linarith⟩, fun h => by linarith [h.1, h.2]⟩
  rw [hsum _ _ (sum_nonneg fun i _ => le_max_left _ _) (sum_nonneg fun i _ => le_max_left _ _), hL, hR]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by linarith, by linarith, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩

section Box

variable (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j₀ : Fin nR)

/-- The level-`n` box of the Itô coordinates. -/
def boxG (n : ℕ) : Set (GCoord nL nR × ℝ) :=
  {p | ‖p.1.1‖ ≤ n ∧ ‖p.1.2.1‖ ≤ n ∧ 0 ≤ p.1.2.2 ∧ p.1.2.2 ≤ n * ((n : ℝ) + 1) ^ 2 ∧ |p.2| ≤ n ∧
    dlt n ≤ gGap κ xL xR ρL ρR j₀ p ∧ (∀ i, dlt n ≤ |p.1.2.1 j₀ - p.1.1 i|) ∧
    ∀ j ∈ offY xR j₀, dlt n ≤ |p.1.2.1 j₀ - p.1.2.1 j|}

/-- The initial point of the coordinates and of the Brownian motion. -/
def initG : GCoord nL nR × ℝ := ((xL, xR, 0), 0)

/-- The box together with the initial point. -/
def kcG (n : ℕ) : Set (GCoord nL nR × ℝ) := insert (initG xL xR) (boxG κ xL xR ρL ρR j₀ n)

theorem isClosed_boxG (n : ℕ) : IsClosed (boxG κ xL xR ρL ρR j₀ n) := by
  have hg : Continuous (gGap κ xL xR ρL ρR j₀) := (contDiff_gGap κ xL xR ρL ρR j₀ (n := 0)).continuous
  have e : boxG κ xL xR ρL ρR j₀ n =
      {p : GCoord nL nR × ℝ | ‖p.1.1‖ ≤ n} ∩ {p | ‖p.1.2.1‖ ≤ n} ∩ {p | 0 ≤ p.1.2.2} ∩
        {p | p.1.2.2 ≤ n * ((n : ℝ) + 1) ^ 2} ∩ {p | |p.2| ≤ n} ∩ {p | dlt n ≤ gGap κ xL xR ρL ρR j₀ p} ∩
        (⋂ i, {p | dlt n ≤ |p.1.2.1 j₀ - p.1.1 i|}) ∩
        (⋂ j ∈ offY xR j₀, {p | dlt n ≤ |p.1.2.1 j₀ - p.1.2.1 j|}) := by
    ext p
    simp only [boxG, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [e]
  refine (((((((isClosed_le (by fun_prop) continuous_const).inter (isClosed_le (by fun_prop)
    continuous_const)).inter (isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_le (by fun_prop) continuous_const)).inter (isClosed_le (by fun_prop) continuous_const)).inter
    (isClosed_le continuous_const hg)).inter (isClosed_iInter fun i => isClosed_le continuous_const
    (by fun_prop))).inter (isClosed_biInter fun j _ => isClosed_le continuous_const (by fun_prop))

theorem isBounded_boxG (n : ℕ) : Bornology.IsBounded (boxG κ xL xR ρL ρR j₀ n) := by
  refine (Metric.isBounded_closedBall (x := (0 : GCoord nL nR × ℝ))
    (r := (n : ℝ) + n * ((n : ℝ) + 1) ^ 2)).subset fun p hp => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hT : (0 : ℝ) ≤ n * ((n : ℝ) + 1) ^ 2 := by positivity
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hp
  simp only [Prod.norm_def, Real.norm_eq_abs]
  refine max_le (max_le (by linarith) (max_le (by linarith) ?_)) (by linarith)
  rw [abs_of_nonneg h3]; linarith

theorem isCompact_kcG (n : ℕ) : IsCompact (kcG κ xL xR ρL ρR j₀ n) :=
  (Metric.isCompact_of_isClosed_isBounded (isClosed_boxG κ xL xR ρL ρR j₀ n)
    (isBounded_boxG κ xL xR ρL ρR j₀ n)).insert _

theorem initG_mem_region (hxL : ∀ i, xL i ≤ 0) (hy : 0 < xR j₀) :
    initG xL xR ∈ g12Region κ xL xR ρL ρR j₀ := by
  refine ⟨?_, fun i => ?_, fun j hj => ?_⟩
  · simp only [initG, gGap, gDriftLin, sub_self, mul_zero, sum_const_zero, zero_add, sub_zero]
    simpa using hy
  · simp only [initG]
    linarith [hxL i]
  · simp only [initG]
    exact sub_ne_zero.2 (Ne.symm (by simpa [offY] using hj))

theorem kcG_subset_region (hxL : ∀ i, xL i ≤ 0) (hy : 0 < xR j₀) (n : ℕ) :
    kcG κ xL xR ρL ρR j₀ n ⊆ g12Region κ xL xR ρL ρR j₀ := by
  refine insert_subset (initG_mem_region κ xL xR ρL ρR j₀ hxL hy) fun p hp => ?_
  have hd := dlt_pos n
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := hp
  refine ⟨hd.trans_le h6, fun i => ?_, fun j hj => ?_⟩
  · exact abs_pos.1 (hd.trans_le (h7 i))
  · exact abs_pos.1 (hd.trans_le (h8 j hj))

end Box

/-! ### Integrals of `GCoord`-valued functions -/

theorem intervalIntegrable_gcoord {g : ℝ → GCoord nL nR} {a b : ℝ}
    (h1 : ∀ i, IntervalIntegrable (fun s => (g s).1 i) volume a b)
    (h2 : ∀ j, IntervalIntegrable (fun s => (g s).2.1 j) volume a b)
    (h3 : IntervalIntegrable (fun s => (g s).2.2) volume a b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff] at h3 ⊢
  have h1' : IntegrableOn (fun s => (g s).1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h1 i)
  have h2' : IntegrableOn (fun s => (g s).2.1) (uIoc a b) :=
    integrable_pi_iff.2 fun j => intervalIntegrable_iff.1 (h2 j)
  exact h1'.prodMk (h2'.prodMk h3)

theorem integral_gcoord_L {g : ℝ → GCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (i : Fin nL) : (∫ s in a..b, g s).1 i = ∫ s in a..b, (g s).1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nL => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ))).intervalIntegral_comp_comm hg).symm

theorem integral_gcoord_R {g : ℝ → GCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (j : Fin nR) : (∫ s in a..b, g s).2.1 j = ∫ s in a..b, (g s).2.1 j :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nR => ℝ) j).comp
    ((ContinuousLinearMap.fst ℝ (Fin nR → ℝ) ℝ).comp
      (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ)))).intervalIntegral_comp_comm hg).symm

theorem integral_gcoord_T {g : ℝ → GCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s).2.2 = ∫ s in a..b, (g s).2.2 :=
  (((ContinuousLinearMap.snd ℝ (Fin nR → ℝ) ℝ).comp
    (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ))).intervalIntegral_comp_comm hg).symm

theorem norm_gcoord_le (p : GCoord nL nR) : ‖p‖ ≤ ∑ i, |p.1 i| + ∑ j, |p.2.1 j| + |p.2.2| := by
  have h1 := Zhan.norm_pi_le_sum' p.1
  have h2 := Zhan.norm_pi_le_sum' p.2.1
  have h0 : 0 ≤ ∑ i, |p.1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h0' : 0 ≤ ∑ j, |p.2.1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs]
  refine max_le (h1.trans (by linarith [abs_nonneg p.2.2])) (max_le (h2.trans ?_) ?_) <;>
    linarith [abs_nonneg p.2.2]

/-! ### The mark life, the clock and the coordinates along one path -/

theorem isMarkLife_mono {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {s r : ℝ≥0} (h : G11.IsMarkLife w v ζ s) (hrs : r ≤ s) :
    G11.IsMarkLife w v ζ r :=
  ⟨lt_of_le_of_lt (by exact_mod_cast hrs) h.1, fun u hu => h.2 u (hu.trans hrs)⟩

section PathCoord

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {j₀ : Fin nR}

/-- The clock `T(t) = ∫₀ᵗ (V^{j₀} − W)⁻²` of the mark. -/
def clockAt (w : ℝ≥0 → ℝ) (v : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := ∫ s in (0 : ℝ)..t, ((v s.toNNReal - w s.toNNReal) ^ 2)⁻¹

/-- The Itô coordinates along one path. -/
def coordAtG (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (j₀ : Fin nR) (t : ℝ≥0) :
    GCoord nL nR :=
  (fun i => vL i t, fun j => vR j t, clockAt w (vR j₀) t)

/-- Their density along one path. -/
def densAtG (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (j₀ : Fin nR) (s : ℝ) :
    GCoord nL nR :=
  g12Dens j₀ (w s.toNNReal) (fun i => vL i s.toNNReal) (fun j => vR j s.toNNReal)

theorem continuousOn_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : G11.IsMarkLife w (vR j₀) ζ t) :
    ContinuousOn (fun s : ℝ => ((vR j₀ s.toNNReal - w s.toNNReal) ^ 2)⁻¹) (Icc 0 (t : ℝ)) := by
  have hsub : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun r hr =>
    Sec2.toNNReal_lt_of_mem_Icc hs.1 hr
  refine ((((h.continuousOn_vR j₀).comp continuous_real_toNNReal.continuousOn hsub).sub
    (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub)).pow 2).inv₀ fun r hr => ?_
  exact pow_ne_zero 2 (sub_pos.2 (hs.2 _ (Sec2.toNNReal_le_of_mem_Icc hr))).ne'

theorem intervalIntegrable_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : G11.IsMarkLife w (vR j₀) ζ t) :
    IntervalIntegrable (fun s : ℝ => ((vR j₀ s.toNNReal - w s.toNNReal) ^ 2)⁻¹) volume 0 t :=
  (continuousOn_clockRate h hs).intervalIntegrable_of_Icc t.coe_nonneg

theorem intervalIntegrable_densAtG (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : G11.IsMarkLife w (vR j₀) ζ t) : IntervalIntegrable (densAtG w vL vR j₀) volume 0 t :=
  intervalIntegrable_gcoord (fun i => h.intervalIntegrable_forceL hs.1 i)
    (fun j => h.intervalIntegrable_forceR hs.1 j) (intervalIntegrable_clockRate h hs)

/-- **The coordinates are absolutely continuous** on the mark life. -/
theorem coordAtG_eq_add_integral (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : G11.IsMarkLife w (vR j₀) ζ t) :
    coordAtG w vL vR j₀ t = coordAtG w vL vR j₀ 0 + ∫ s in (0 : ℝ)..t, densAtG w vL vR j₀ s := by
  have hint := intervalIntegrable_densAtG h hs
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
  · simp only [Prod.fst_add, Pi.add_apply, integral_gcoord_L hint]
    simp only [coordAtG, densAtG, g12Dens, h.vL_zero]
    exact h.vL_eq hs.1 i
  · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_gcoord_R hint]
    simp only [coordAtG, densAtG, g12Dens, h.vR_zero]
    exact h.vR_eq hs.1 j
  · simp only [Prod.snd_add, integral_gcoord_T hint]
    simp only [coordAtG, densAtG, g12Dens, clockAt, NNReal.coe_zero, intervalIntegral.integral_same, zero_add]

theorem integral_abs_forceL (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| = xL i - vL i t := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := h.vL_le_w (Sec2.toNNReal_lt_of_mem_Icc ht hs) i
    exact abs_of_nonpos (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 hle))
  rw [heq, intervalIntegral.integral_neg, h.vL_eq ht i]
  ring

theorem integral_abs_forceR (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (j : Fin nR) :
    ∫ s in (0 : ℝ)..t, |2 / (vR j s.toNNReal - w s.toNNReal)| = vR j t - xR j := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vR j s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := h.w_le_vR (Sec2.toNNReal_lt_of_mem_Icc ht hs) j
    exact abs_of_nonneg (div_nonneg zero_le_two (sub_nonneg.2 hle))
  rw [heq, h.vR_eq ht j]
  ring

/-- **The total variation of the coordinates** is bounded by the displacements and the clock. -/
theorem integral_norm_densAtG_le (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : G11.IsMarkLife w (vR j₀) ζ t) :
    ∫ s in (0 : ℝ)..t, ‖densAtG w vL vR j₀ s‖ ≤
      ∑ i, (xL i - vL i t) + ∑ j, (vR j t - xR j) + clockAt w (vR j₀) t := by
  have hint := intervalIntegrable_densAtG h hs
  have hL := fun i => (h.intervalIntegrable_forceL hs.1 i).abs
  have hR := fun j => (h.intervalIntegrable_forceR hs.1 j).abs
  have hT := intervalIntegrable_clockRate h hs
  have hsum : IntervalIntegrable (fun s => ∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)| +
      ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)| +
      ((vR j₀ s.toNNReal - w s.toNNReal) ^ 2)⁻¹) volume 0 t := by
    have a1 : IntervalIntegrable (fun s => ∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)|) volume 0 t := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum (univ : Finset (Fin nL)) fun i _ => hL i
    have a2 : IntervalIntegrable (fun s => ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)|) volume 0 t := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum (univ : Finset (Fin nR)) fun j _ => hR j
    exact (a1.add a2).add hT
  have hle : ∫ s in (0 : ℝ)..t, ‖densAtG w vL vR j₀ s‖ ≤ ∫ s in (0 : ℝ)..t, (∑ i,
      |2 / (vL i s.toNNReal - w s.toNNReal)| + ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)| +
      ((vR j₀ s.toNNReal - w s.toNNReal) ^ 2)⁻¹) := by
    refine intervalIntegral.integral_mono_on t.coe_nonneg hint.norm hsum fun s _ => ?_
    refine (norm_gcoord_le _).trans (le_of_eq ?_)
    simp only [densAtG, g12Dens]
    rw [abs_of_nonneg (inv_nonneg.2 (sq_nonneg _))]
  refine hle.trans (le_of_eq ?_)
  have a1 : IntervalIntegrable (fun s => ∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)|) volume 0 t := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum (univ : Finset (Fin nL)) fun i _ => hL i
  have a2 : IntervalIntegrable (fun s => ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)|) volume 0 t := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum (univ : Finset (Fin nR)) fun j _ => hR j
  rw [intervalIntegral.integral_add (a1.add a2) hT, intervalIntegral.integral_add a1 a2,
    intervalIntegral.integral_finsetSum fun i _ => hL i, intervalIntegral.integral_finsetSum fun j _ => hR j]
  simp only [integral_abs_forceL h hs.1, integral_abs_forceR h hs.1, clockAt]


theorem w_eq_gDriftLin {a : ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt a * b t + gDriftLin xL xR ρL ρR (coordAtG w vL vR j₀ t) := by
  rw [hp.isForcePath.w_eq_N1 hp.driverEq ht]
  simp only [gDriftLin, coordAtG]
  ring

end PathCoord

/-! ### The localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The first exit of the state from the level-`n` box before `ζ`, on the good event (`0` off it). -/
def hitG (xR : Fin nR → ℝ) (j₀ : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => levG xR j₀ n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing time** `σ_n = T_n ∧ hitG ∧ (exit of |B| from (−n, n))`. -/
def locG (xR : Fin nR → ℝ) (j₀ : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    ℝ≥0 :=
  Sec2.TwoSeed.capTime (T n) (fun ω => min (hitG xR j₀ G W VL VR ζ n ω)
    (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {j₀ : Fin nR}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {n : ℕ}

theorem locG_le_T (ω : Ω) : locG xR j₀ G W VL VR B ζ T n ω ≤ T n ω :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem locG_le_hitG (ω : Ω) :
    (locG xR j₀ G W VL VR B ζ T n ω : WithTop ℝ≥0) ≤ hitG xR j₀ G W VL VR ζ n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_left _ _)

theorem locG_le_exitTime (ω : Ω) :
    (locG xR j₀ G W VL VR B ζ T n ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem locG_of_not_mem {ω : Ω} (hω : ω ∉ G) : locG xR j₀ G W VL VR B ζ T n ω = 0 := by
  have h := locG_le_hitG (xR := xR) (j₀ := j₀) (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
    (T := T) (n := n) ω
  simp only [hitG, hω, ↓reduceIte] at h
  exact le_antisymm (by exact_mod_cast h) bot_le

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_locG (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0)) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (locG xR j₀ G W VL VR B ζ T n ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (hT n)
    ((isStoppingTime_hit_gb hE hGm hGc hgood (continuous_levG xR j₀ n)).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_gb hE hGm hGc hgood).2.1 (continuous_brownG_gb hgood) n))

/-! ### Pathwise facts on good paths -/

section GoodFacts

variable {ω : Ω} (hω : IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
include hω

theorem locG_lt_lifetime : (locG xR j₀ G W VL VR B ζ T n ω : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast locG_le_T ω) (hω.2.2.2.1 n)

include hωG in
theorem levG_nonneg_of_le_locG (hσ0 : 0 < locG xR j₀ G W VL VR B ζ T n ω) {r : ℝ≥0}
    (hr : r ≤ locG xR j₀ G W VL VR B ζ T n ω) :
    0 ≤ levG xR j₀ n (Coupling.stateAt W VL VR r ω) := by
  have h := locG_le_hitG (xR := xR) (j₀ := j₀) (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ)
    (T := T) (n := n) ω
  simp only [hitG, hωG, ↓reduceIte] at h
  have hF := hω.1.isForcePath
  exact nonneg_of_le_hitBelow ((continuous_levG xR j₀ n).comp_continuousOn
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR)))) (locG_lt_lifetime hω) h hσ0 hr

include hωG in
theorem abs_B_le_of_le_locG (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω) {r : ℝ≥0}
    (hr : r ≤ locG xR j₀ G W VL VR B ζ T n ω) : |B r ω| ≤ n := by
  rcases (zero_le (a := r)).eq_or_lt with h0 | h0
  · rw [← h0, hω.2.2.1, abs_zero]; exact Nat.cast_nonneg n
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_gb hgood) h0
    ((WithTop.coe_le_coe.2 hr).trans (locG_le_exitTime ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

include hωG in
/-- **`σ_n` lies in the life of the mark** (when `x_{j₀} > 0`). -/
theorem isMarkLife_locG (hy : 0 < xR j₀) :
    G11.IsMarkLife (W · ω) (VR j₀ · ω) (ζ ω) (locG xR j₀ G W VL VR B ζ T n ω) := by
  refine ⟨locG_lt_lifetime hω, fun r hr => ?_⟩
  rcases (zero_le (a := locG xR j₀ G W VL VR B ζ T n ω)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    have hF := hω.1.isForcePath
    show W 0 ω < VR j₀ 0 ω
    rw [hF.w_zero, hF.vR_zero j₀]; exact hy
  have h := (levG_nonneg_iff.1 (levG_nonneg_of_le_locG hω hωG h0 hr)).1
  simp only [Coupling.stateAt] at h
  linarith [dlt_pos n]

end GoodFacts

/-! ### The coordinates on the probability space -/

open scoped Classical in
/-- The Itô coordinates on the good event (their initial value off it). -/
def coordG (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (j₀ : Fin nR) (t : ℝ≥0) (ω : Ω) : GCoord nL nR :=
  if ω ∈ G then coordAtG (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) j₀ t else (xL, xR, 0)

open scoped Classical in
/-- Their density on the good event (`0` off it). -/
def densG (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (j₀ : Fin nR) (s : ℝ) (ω : Ω) : GCoord nL nR :=
  if ω ∈ G then densAtG (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) j₀ s else 0

open scoped Classical in
/-- The gap `V^{j₀} − W` stopped at `σ`, on the good event (`1` off it). -/
def gapStopG (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (j₀ : Fin nR) (σ : Ω → ℝ≥0)
    (r : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then VR j₀ (min r (σ ω)) ω - W (min r (σ ω)) ω else 1

/-- The bound on the total variation of the coordinates up to `σ_n`. -/
def kbG (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (n : ℕ) : ℝ :=
  nL * (‖xL‖ + n) + nR * (‖xR‖ + n) + n * ((n : ℝ) + 1) ^ 2

theorem kbG_nonneg (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (n : ℕ) : 0 ≤ kbG xL xR n := by
  unfold kbG; positivity

section Facts

variable (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω) (hTn : ∀ n ω, T n ω ≤ n)
  (hy : 0 < xR j₀)

include hgood hTn hy in
/-- The clock stays below `n (n + 1)²` up to `σ_n`. -/
theorem clockAt_le_of_le_locG {ω : Ω} (hωG : ω ∈ G) {r : ℝ≥0} (hr : r ≤ locG xR j₀ G W VL VR B ζ T n ω) :
    0 ≤ clockAt (W · ω) (VR j₀ · ω) r ∧ clockAt (W · ω) (VR j₀ · ω) r ≤ n * ((n : ℝ) + 1) ^ 2 := by
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  set σ := locG xR j₀ G W VL VR B ζ T n ω with hσ
  have hlife := isMarkLife_mono (isMarkLife_locG hω hωG hy (n := n)) hr
  have hrn : (r : ℝ) ≤ n := by
    have := (hr.trans (locG_le_T ω)).trans (hTn n ω); exact_mod_cast this
  rcases (zero_le (a := σ)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    simp only [clockAt, NNReal.coe_zero, intervalIntegral.integral_same, le_refl, true_and]
    positivity
  have hbound : ∀ s ∈ Icc (0 : ℝ) r, ((VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 2)⁻¹ ≤ ((n : ℝ) + 1) ^ 2 := by
    intro s hs
    have hsr : s.toNNReal ≤ r := Sec2.toNNReal_le_of_mem_Icc hs
    have h := (levG_nonneg_iff.1 (levG_nonneg_of_le_locG hω hωG h0 (hsr.trans hr))).1
    simp only [Coupling.stateAt] at h
    have hd : dlt n = ((n : ℝ) + 1)⁻¹ := by simp [dlt]
    have hpos : 0 < dlt n := dlt_pos n
    rw [inv_le_comm₀ (by nlinarith) (by positivity), ← inv_pow, ← hd]
    exact pow_le_pow_left₀ hpos.le h 2
  have hint := intervalIntegrable_clockRate hF hlife
  constructor
  · exact intervalIntegral.integral_nonneg r.coe_nonneg fun s _ => inv_nonneg.2 (sq_nonneg _)
  · calc clockAt (W · ω) (VR j₀ · ω) r ≤ ∫ s in (0 : ℝ)..r, ((n : ℝ) + 1) ^ 2 :=
          intervalIntegral.integral_mono_on r.coe_nonneg hint intervalIntegrable_const hbound
      _ = r * ((n : ℝ) + 1) ^ 2 := by simp
      _ ≤ n * ((n : ℝ) + 1) ^ 2 := by gcongr

include hgood hTn hy in
/-- **Up to `σ_n` the coordinates and the Brownian motion stay in the compact set.** -/
theorem mem_kcG_of_le_locG {ω : Ω} {r : ℝ≥0} (hr : r ≤ locG xR j₀ G W VL VR B ζ T n ω) :
    (coordG xL xR G W VL VR j₀ r ω, Sec2.TwoSeed.brownG G B r ω) ∈ kcG κ xL xR ρL ρR j₀ n := by
  by_cases hωG : ω ∈ G
  swap
  · simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
    exact mem_insert _ _
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
  rcases (zero_le (a := locG xR j₀ G W VL VR B ζ T n ω)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    refine Set.mem_insert_iff.2 (Or.inl ?_)
    have hL : (fun i => VL i 0 ω) = xL := funext hF.vL_zero
    have hR : (fun j => VR j 0 ω) = xR := funext hF.vR_zero
    simp only [initG, coordAtG, clockAt, hL, hR, hω.2.2.1, NNReal.coe_zero, intervalIntegral.integral_same]
  have hlev := levG_nonneg_iff.1 (levG_nonneg_of_le_locG hω hωG h0 hr)
  obtain ⟨hu, hn, hLg, hRg⟩ := hlev
  simp only [Coupling.stateAt] at hu hn hLg hRg
  obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR r ω)
  simp only [Coupling.stateAt] at hvL hvR
  have hclock := clockAt_le_of_le_locG hgood hTn hy hωG hr
  have hB := abs_B_le_of_le_locG hω hωG hgood hr
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr) (locG_lt_lifetime hω)
  have hN := w_eq_gDriftLin (j₀ := j₀) hω.1 hrζ
  refine mem_insert_of_mem _ ⟨?_, ?_, hclock.1, hclock.2, hB, ?_, ?_, ?_⟩
  · exact (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg n)).2 fun i => by
      rw [Real.norm_eq_abs]; exact (hvL i).trans hn
  · exact (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg n)).2 fun j => by
      rw [Real.norm_eq_abs]; exact (hvR j).trans hn
  · simp only [gGap, coordAtG] at hN ⊢
    rw [← hN]; exact hu
  · exact hLg
  · exact hRg

end Facts

/-! ### Adaptedness and the localized Itô formula -/

section Adapted

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hy : 0 < xR j₀)

include hE hGm hGc hgood hT in
/-- The stopped gap is adapted. -/
theorem measurable_gapStopG (r : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P r] (gapStopG G W VR j₀ (locG xR j₀ G W VL VR B ζ T n) r) := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hσ := isStoppingTime_locG (j₀ := j₀) (n := n) hE hGm hGc hgood hT
  have hK : ∀ s, Measurable[usualAugmentation 𝓕 P s] fun ω =>
      Zhan.killedAt ζ (VR j₀) s ω - Zhan.killedAt ζ W s ω := fun s =>
    (Sec2.TwoSeed.measurable_killed (hVRa j₀) s).sub (Sec2.TwoSeed.measurable_killed hWa s)
  have h := Ito.measurable_stopped_of_agree (X := fun s ω => VR j₀ s ω - W s ω) hσ hK hG0
    (1 : ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) r
  · exact h
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (locG_lt_lifetime (hgood ω hω))
    simp only [Zhan.killedAt, hsζ, ↓reduceIte]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (locG xR j₀ G W VL VR B ζ T n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (locG_lt_lifetime (hgood ω hω))
    exact ((hF.continuousOn_vR j₀).sub hF.continuousOn_w).mono hsub

include hgood in
theorem continuous_gapStopG (ω : Ω) :
    Continuous fun r => gapStopG G W VR j₀ (locG xR j₀ G W VL VR B ζ T n) r ω := by
  by_cases hω : ω ∈ G
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (locG xR j₀ G W VL VR B ζ T n ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast hs) (locG_lt_lifetime (hgood ω hω))
    have hc := ((hF.continuousOn_vR j₀).sub hF.continuousOn_w).mono hsub
    simp only [gapStopG, hω, ↓reduceIte]
    exact hc.comp_continuous (continuous_id.min continuous_const) fun r => mem_Iic.2 (min_le_right _ _)
  · simp only [gapStopG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood hT hy in
/-- **The stopped coordinates are adapted.** -/
theorem measurable_coordG_locG (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordG xL xR G W VL VR j₀ (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  set σ := locG xR j₀ G W VL VR B ζ T n
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hσ := isStoppingTime_locG (j₀ := j₀) (n := n) hE hGm hGc hgood hT
  have hprog : IsStronglyProgressive 𝓖 (gapStopG G W VR j₀ σ) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun r => (measurable_gapStopG hE hGm hGc hgood hT r).stronglyMeasurable)
      (continuous_gapStopG hgood)
  set K : ℝ≥0 → Ω → GCoord nL nR := fun s ω => ((fun i => Zhan.killedAt ζ (VL i) s ω),
    (fun j => Zhan.killedAt ζ (VR j) s ω), ∫ u in (0 : ℝ)..s, ((gapStopG G W VR j₀ σ u.toNNReal ω) ^ 2)⁻¹)
    with hKdef
  have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s => by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact @Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) (𝓖 s) _ _ fun i =>
        Sec2.TwoSeed.measurable_killed (hVLa i) s
    · exact @Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) (𝓖 s) _ _ fun j =>
        Sec2.TwoSeed.measurable_killed (hVRa j) s
    · exact (Girsanov.stronglyMeasurable_integral_comp hprog
        (g := fun x : ℝ => (x ^ 2)⁻¹) (by fun_prop) s).measurable
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => coordAtG (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) j₀ s) hσ hK hG0
    ((xL, xR, 0) : GCoord nL nR) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · exact h
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (locG_lt_lifetime (hgood ω hω))
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
    · simp only [hKdef, Zhan.killedAt, hsζ, ↓reduceIte, coordAtG]
    · simp only [hKdef, Zhan.killedAt, hsζ, ↓reduceIte, coordAtG]
    · simp only [hKdef, coordAtG, clockAt]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le s.coe_nonneg] at hu
      have hus : u.toNNReal ≤ σ ω := (Sec2.toNNReal_le_of_mem_Icc hu).trans hs
      simp only [gapStopG, hω, ↓reduceIte, min_eq_left hus]
  · have hF := (hgood ω hω).1.isForcePath
    have hlife := isMarkLife_locG (hgood ω hω) hω hy (n := n)
    have hsub : Iic (σ ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := fun s hs => (isMarkLife_mono hlife hs).1
    have hTc : ContinuousOn (fun s : ℝ≥0 => clockAt (W · ω) (VR j₀ · ω) s) (Iic (σ ω)) := by
      have hc := intervalIntegral.continuousOn_primitive_interval'
        (intervalIntegrable_clockRate hF hlife) (left_mem_uIcc (a := (0 : ℝ)) (b := σ ω))
      refine hc.comp NNReal.continuous_coe.continuousOn fun s hs => ?_
      rw [uIcc_of_le (σ ω).coe_nonneg]
      exact ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
      ((continuousOn_pi.2 fun j => (hF.continuousOn_vR j).mono hsub).prodMk hTc)

include hE hGm hGc hgood hT hTn hy in
/-- **The localized Itô formula** for a `C³` function `F` on the region of the mark observable:
`F(Λ_{t∧σ_n}, B_{t∧σ_n}) − ∫₀^{t∧σ_n} itoGen F` is a martingale of the usual augmentation. -/
theorem martingale_locG (hxL : ∀ i, xL i ≤ 0) {F : GCoord nL nR × ℝ → ℝ}
    (hF : ContDiffOn ℝ 3 F (g12Region κ xL xR ρL ρR j₀)) (n : ℕ) :
    Martingale (fun t ω => F (coordG xL xR G W VL VR j₀ (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (locG xR j₀ G W VL VR B ζ T n ω) : ℝ≥0),
        Ito.itoGen F (coordG xL xR G W VL VR j₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
          (densG G W VL VR j₀ s ω)) (usualAugmentation 𝓕 P) P := by
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densG G W VL VR j₀ · ω) volume 0 (locG xR j₀ G W VL VR B ζ T n ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densG, hω, ↓reduceIte] using
        intervalIntegrable_densAtG (hgood ω hω).1.isForcePath (isMarkLife_locG (hgood ω hω) hω hy (n := n))
    · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ locG xR j₀ G W VL VR B ζ T n ω → coordG xL xR G W VL VR j₀ t ω =
      coordG xL xR G W VL VR j₀ 0 ω + ∫ s in (0 : ℝ)..t, densG G W VL VR j₀ s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordG, densG, hω, ↓reduceIte]
      exact coordAtG_eq_add_integral (hgood ω hω).1.isForcePath
        (isMarkLife_mono (isMarkLife_locG (hgood ω hω) hω hy (n := n)) ht)
    · simp only [coordG, densG, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(locG xR j₀ G W VL VR B ζ T n ω), ‖densG G W VL VR j₀ s ω‖ ≤ kbG xL xR n := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [densG, hω, ↓reduceIte]
      have hF := (hgood ω hω).1.isForcePath
      have hlife := isMarkLife_locG (hgood ω hω) hω hy (n := n)
      refine (integral_norm_densAtG_le hF hlife).trans ?_
      rcases (zero_le (a := locG xR j₀ G W VL VR B ζ T n ω)).eq_or_lt with h0 | h0
      · rw [← h0]
        simp only [hF.vL_zero, hF.vR_zero, sub_self, sum_const_zero, clockAt, NNReal.coe_zero,
          intervalIntegral.integral_same, add_zero]
        exact kbG_nonneg xL xR n
      have hlev := levG_nonneg_iff.1 (levG_nonneg_of_le_locG (hgood ω hω) hω h0 le_rfl)
      have hn : ‖Coupling.stateAt W VL VR (locG xR j₀ G W VL VR B ζ T n ω) ω‖ ≤ n := hlev.2.1
      obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (locG xR j₀ G W VL VR B ζ T n ω) ω)
      simp only [Coupling.stateAt] at hvL hvR
      have hcl := (clockAt_le_of_le_locG hgood hTn hy hω (n := n) le_rfl).2
      have hLi : ∀ i, xL i - VL i (locG xR j₀ G W VL VR B ζ T n ω) ω ≤ ‖xL‖ + n := fun i => by
        have h1 : |xL i| ≤ ‖xL‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xL i
        linarith [le_abs_self (xL i), neg_abs_le (VL i (locG xR j₀ G W VL VR B ζ T n ω) ω), (hvL i).trans hn]
      have hRj : ∀ j, VR j (locG xR j₀ G W VL VR B ζ T n ω) ω - xR j ≤ ‖xR‖ + n := fun j => by
        have h1 : |xR j| ≤ ‖xR‖ := by
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm xR j
        linarith [le_abs_self (VR j (locG xR j₀ G W VL VR B ζ T n ω) ω), neg_abs_le (xR j), (hvR j).trans hn]
      have hsL : ∑ i, (xL i - VL i (locG xR j₀ G W VL VR B ζ T n ω) ω) ≤ (nL : ℝ) * (‖xL‖ + n) := by
        calc ∑ i, (xL i - VL i (locG xR j₀ G W VL VR B ζ T n ω) ω) ≤ ∑ _i : Fin nL, (‖xL‖ + n) :=
            Finset.sum_le_sum fun i _ => hLi i
          _ = _ := by simp; ring
      have hsR : ∑ j, (VR j (locG xR j₀ G W VL VR B ζ T n ω) ω - xR j) ≤ (nR : ℝ) * (‖xR‖ + n) := by
        calc ∑ j, (VR j (locG xR j₀ G W VL VR B ζ T n ω) ω - xR j) ≤ ∑ _j : Fin nR, (‖xR‖ + n) :=
            Finset.sum_le_sum fun j _ => hRj j
          _ = _ := by simp; ring
      unfold kbG
      linarith
    · simp only [densG, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact kbG_nonneg xL xR n
  have hK : ∀ ω (t : ℝ≥0), t ≤ locG xR j₀ G W VL VR B ζ T n ω →
      (coordG xL xR G W VL VR j₀ t ω, Sec2.TwoSeed.brownG G B t ω) ∈ kcG κ xL xR ρL ρR j₀ n :=
    fun ω t ht => mem_kcG_of_le_locG hgood hTn hy ht
  have hBm : ∀ t, Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (locG xR j₀ G W VL VR B ζ T n ω)) ω := fun t => by
    have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
    have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B)
      (isStoppingTime_locG (j₀ := j₀) (n := n) hE hGm hGc hgood hT) hB'.2.1 hG0 (0 : ℝ)
      (fun ω _ s _ => rfl) (fun ω _ => (continuous_brownG_gb hgood ω).continuousOn) t
    convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_gb hgood)
    (isOpen_g12Region κ xL xR ρL ρR j₀) hF (isCompact_kcG κ xL xR ρL ρR j₀ n)
    (kcG_subset_region κ xL xR ρL ρR j₀ hxL hy n) (isStoppingTime_locG hE hGm hGc hgood hT)
    (measurable_coordG_locG hE hGm hGc hgood hT hy) hlam hΛ hKb hK

end Adapted

end Loc

end G12

end Supp7

end InteractingSLE
