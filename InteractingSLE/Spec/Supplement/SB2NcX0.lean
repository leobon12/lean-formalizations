/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcSeed

/-!
# F2b′'s chart offset `x₀`: the right entry value of B's seed, read measurably

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A).

* `qApprox`, `apprPt`: the points `q_n + i/(m+1)` with `q_n ↓ R` on the grid `ℤ/(n+1)`;
* **`entryRead A R`**: `limsup_n limsup_m Re (hull chart of A)(q_n + i/(m+1))`, the forward map read only on its
  domain;
* **`entryRead_eq`** (deterministic): if the recentred chart of `fill X` is a right entry chart of `X` at `R = max X`
  (`IsRightEntryChart`, from PROVE-R6-CORNER's `Dv.exists_canon_package_pinv`), the read is the entry value;
* **`measurable_entryRead`**: for a dyadic-hit measurable compact random hull and a measurable `R`, the read is
  measurable (`Mt.hullChart_k2Inputs` at fixed points, countably many grid points).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

/-! ### The approach points -/

/-- The grid point of `ℤ/(n+1)` just right of `R`. -/
def qApprox (R : ℝ) (n : ℕ) : ℝ := ((⌊R * ((n : ℝ) + 1)⌋ : ℝ) + 1) / ((n : ℝ) + 1)

theorem lt_qApprox (R : ℝ) (n : ℕ) : R < qApprox R n := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold qApprox
  rw [lt_div_iff₀ hn]
  exact Int.lt_floor_add_one _

theorem qApprox_le (R : ℝ) (n : ℕ) : qApprox R n ≤ R + 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold qApprox
  rw [div_le_iff₀ hn, add_mul, one_div_mul_cancel hn.ne']
  linarith [Int.floor_le (R * ((n : ℝ) + 1))]

theorem tendsto_qApprox (R : ℝ) : Tendsto (qApprox R) atTop (𝓝[>] R) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => lt_qApprox R n⟩
  have h1 : Tendsto (fun n : ℕ => R + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have := (tendsto_const_nhds (x := R)).add h
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun n => (lt_qApprox R n).le)
    (fun n => qApprox_le R n)

/-- The approach point `q_n + i/(m+1)`. -/
def apprPt (R : ℝ) (n m : ℕ) : ℂ := (qApprox R n : ℂ) + Complex.I / ((m : ℂ) + 1)

theorem apprPt_im (R : ℝ) (n m : ℕ) : (apprPt R n m).im = 1 / ((m : ℝ) + 1) := by
  unfold apprPt
  have h : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.add_im, Complex.ofReal_im, zero_add, Complex.div_ofReal_im, Complex.I_im]

theorem apprPt_mem_H (R : ℝ) (n m : ℕ) : apprPt R n m ∈ H := by
  show 0 < (apprPt R n m).im
  rw [apprPt_im]; positivity

theorem tendsto_apprPt (R : ℝ) (n : ℕ) :
    Tendsto (fun m : ℕ => apprPt R n m) atTop (𝓝[H] ((qApprox R n : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => apprPt_mem_H R n m⟩
  have h : Tendsto (fun m : ℕ => Complex.I / ((m : ℂ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := h1.const_mul Complex.I
    rw [Complex.ofReal_zero, mul_zero] at h2
    refine h2.congr fun m => ?_
    push_cast; ring
  have := tendsto_const_nhds (x := ((qApprox R n : ℝ) : ℂ)).add h
  rw [add_zero] at this
  exact this

/-! ### The entry read -/

open Classical in
/-- **The entry read** of a hull `A` at `R`: the forward map of `Mo.hullChart A 0` at the approach points (on its
domain), first `m → ∞`, then `n → ∞`. -/
def entryRead (A : Set ℂ) (R : ℝ) : ℝ :=
  limsup (fun n : ℕ => limsup (fun m : ℕ =>
    (if apprPt R n m ∈ ((Mo.hullChart A 0).dom : Set ℂ) then (Mo.hullChart A 0).1 (apprPt R n m) else 0).re)
      atTop) atTop

/-- **The entry read of a right entry chart is its entry value.** -/
theorem entryRead_eq {X : Set ℂ} (hX : IsCompact X) (hA : IsHPHull (fillH X)) {e : ℝ}
    (hc : IsRightEntryChart X (realMax X) ((Mo.hullChart (fillH X) 0).recenter e)) :
    entryRead (fillH X) (realMax X) = e := by
  classical
  obtain ⟨-, ⟨f, hf, hflim⟩, -, -⟩ := hc
  set R := realMax X with hR
  have hdom : ((Mo.hullChart (fillH X) 0).dom : Set ℂ) = H \ fillH X := Mo.coe_dom_hullChart hA 0
  -- the inner limits
  have hinner : ∀ n : ℕ, Tendsto (fun m : ℕ =>
      (if apprPt R n m ∈ ((Mo.hullChart (fillH X) 0).dom : Set ℂ) then
        (Mo.hullChart (fillH X) 0).1 (apprPt R n m) else 0).re) atTop (𝓝 (f (qApprox R n) + e)) := by
    intro n
    set x := qApprox R n with hx
    have hxR : R < x := lt_qApprox R n
    obtain ⟨ρ, hρ, hd⟩ := Lx.exists_ball_disjoint_fillH_right hX fun y hy =>
      lt_of_le_of_lt (Lx.le_realMax_of_mem hX hy) hxR
    have hlim := (hf x hxR).comp (tendsto_apprPt R n)
    have hlim' : Tendsto (fun m : ℕ => ((Mo.hullChart (fillH X) 0).1 (apprPt R n m)).re) atTop
        (𝓝 (f x + e)) := by
      have h2 := ((Complex.continuous_re.tendsto _).comp hlim).add_const e
      rw [Complex.ofReal_re] at h2
      refine h2.congr fun m => ?_
      simp only [Function.comp, Chart.recenter, Complex.sub_re, Complex.ofReal_re, sub_add_cancel]
    have hev : ∀ᶠ m : ℕ in atTop, apprPt R n m ∈ ((Mo.hullChart (fillH X) 0).dom : Set ℂ) := by
      have hb : ∀ᶠ m : ℕ in atTop, apprPt R n m ∈ ball ((x : ℝ) : ℂ) ρ :=
        (tendsto_nhdsWithin_iff.1 (tendsto_apprPt R n)).1 (ball_mem_nhds _ hρ)
      filter_upwards [hb] with m hm
      rw [hdom]
      exact ⟨apprPt_mem_H R n m, fun hfill => hd.le_bot ⟨hm, hfill⟩⟩
    refine hlim'.congr' ?_
    filter_upwards [hev] with m hm
    simp only [hm, ↓reduceIte]
  -- the outer limit
  have houter : Tendsto (fun n : ℕ => f (qApprox R n) + e) atTop (𝓝 e) := by
    have := (hflim.comp (tendsto_qApprox R)).add_const e
    rwa [zero_add] at this
  unfold entryRead
  have e1 : (fun n : ℕ => limsup (fun m : ℕ =>
      (if apprPt R n m ∈ ((Mo.hullChart (fillH X) 0).dom : Set ℂ) then
        (Mo.hullChart (fillH X) 0).1 (apprPt R n m) else 0).re) atTop) =
      fun n : ℕ => f (qApprox R n) + e := funext fun n => (hinner n).limsup_eq
  rw [e1]
  exact houter.limsup_eq

/-- **The entry read is measurable** for a dyadic-hit measurable compact random hull and a measurable `R`. -/
theorem measurable_entryRead {Ω : Type*} {m : MeasurableSpace Ω} {K : Ω → Set ℂ}
    (hK : @Restart.IsDyadicHitMeasurable Ω m K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {R : Ω → ℝ} (hR : Measurable[m] R) :
    Measurable[m] fun ω => entryRead (fillH (K ω)) (R ω) := by
  classical
  obtain ⟨-, -, -, -, hfwdm, -⟩ := @Mt.hullChart_k2Inputs Ω m K (fun _ => 0) hK hKc hKp measurable_const
  let _ : MeasurableSpace Ω := m
  refine Measurable.limsup fun n => Measurable.limsup fun m' => ?_
  -- the grid point and its index
  set z : ℤ → ℂ := fun i => ((((i : ℝ) + 1) / ((n : ℝ) + 1) : ℝ) : ℂ) + Complex.I / ((m' : ℂ) + 1) with hzdef
  set G : ℤ × Ω → ℝ := fun p => (({ω | z p.1 ∈ (Mo.hullChart (fillH (K ω)) 0).dom}.indicator
    fun ω => (Mo.hullChart (fillH (K ω)) 0).1 (z p.1)) p.2).re with hGdef
  have hG : Measurable G :=
    measurable_from_prod_countable_right fun i => Complex.measurable_re.comp (hfwdm (z i))
  have hj : Measurable fun ω => ⌊R ω * ((n : ℝ) + 1)⌋ := (hR.mul_const _).floor
  have e : (fun ω => (if apprPt (R ω) n m' ∈ ((Mo.hullChart (fillH (K ω)) 0).dom : Set ℂ) then
      (Mo.hullChart (fillH (K ω)) 0).1 (apprPt (R ω) n m') else 0).re) =
      fun ω => G (⌊R ω * ((n : ℝ) + 1)⌋, ω) := by
    funext ω
    have hz : apprPt (R ω) n m' = z ⌊R ω * ((n : ℝ) + 1)⌋ := by simp only [apprPt, qApprox, hzdef]
    simp only [hGdef, hz, Set.indicator_apply, Set.mem_ofPred_eq, SetLike.mem_coe]
  rw [e]
  exact hG.comp (hj.prodMk measurable_id)

end InteractingSLE.Theorem14.SB.Nc
