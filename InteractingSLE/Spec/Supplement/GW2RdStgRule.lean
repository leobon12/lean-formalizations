/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgChain

/-!
# GW2's stage identity: stage path rules from a GB6 path rule

Packet PROVE-GW2-RELDET, ruling R106. GB6's engine needs the stop of a version to be a measurable PATH RULE of
(record, relative path) (`Supp8.GB6.HullId.IsPathRule`: its value only depends on the path up to that value). At stage
`n` the record is the encoded stage-start history and the path is the stage driver `stgDrv R a` (`a` the relative
start). The stage stop is `V − a`, where `V = ρ (rec, R)` for a path rule `ρ` of the whole relative path.

The whole path is rebuilt CAUSALLY and MEASURABLY from (stage record, stage path):

* `dyadLo n x = ⌊x 2ⁿ⌋ / 2ⁿ`, below `x`, tending to `x`;
* `evalDn p τ = limsup_n p (dyadLo n τ)`: a causal (only `p` on `[0, τ]` matters), jointly measurable evaluation,
  equal to `p τ` for continuous `p` (`evalDn_eq`);
* `catAt pre a p`: `pre` up to `a`, then `pre a + p (· − a)` — causal in `p` with delay `a` (`catAt_congr`), and
  equal to the relative path `R` itself when `pre` agrees with `R` up to `a` and `p = stgDrv R a` (`catAt_stgDrv`);
* **`stageRule ρ σ A pre (x, p) = ρ (σ x, catAt (pre x) (A x) p) − A x`**: a path rule whenever `ρ` is
  (`isPathRule_stageRule`), measurable whenever `ρ`, `σ`, `A`, `pre` are (`measurable_stageRule`), and equal to
  `V − a` at (stage record, stage path) (`stageRule_stgDrv`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6.HullId

/-! ### Causal evaluation at a time -/

/-- The dyadic lower approximation `⌊x 2ⁿ⌋ / 2ⁿ`. -/
def dyadLo (n : ℕ) (x : ℝ≥0) : ℝ≥0 := ((⌊(x : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n).toNNReal

theorem coe_dyadLo (n : ℕ) (x : ℝ≥0) : (dyadLo n x : ℝ) = (⌊(x : ℝ) * 2 ^ n⌋₊ : ℝ) / 2 ^ n :=
  Real.coe_toNNReal _ (by positivity)

theorem dyadLo_le (n : ℕ) (x : ℝ≥0) : dyadLo n x ≤ x := by
  rw [← NNReal.coe_le_coe, coe_dyadLo, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem le_dyadLo (n : ℕ) (x : ℝ≥0) : (x : ℝ) - 1 / 2 ^ n ≤ dyadLo n x := by
  rw [coe_dyadLo, le_div_iff₀ (by positivity), sub_mul, one_div, inv_mul_cancel₀ (by positivity)]
  have := Nat.lt_floor_add_one ((x : ℝ) * 2 ^ n)
  linarith

theorem tendsto_dyadLo (x : ℝ≥0) : Tendsto (fun n => dyadLo n x) atTop (𝓝 x) := by
  rw [← NNReal.tendsto_coe]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds (fun n => le_dyadLo n x)
    (fun n => NNReal.coe_le_coe.2 (dyadLo_le n x))
  have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    refine h.congr fun n => ?_
    rw [one_div_pow]
  simpa only [sub_zero] using tendsto_const_nhds.sub this

/-- **Causal evaluation**: the limsup of the values at the dyadic lower approximations of `τ`. -/
def evalDn (p : ℝ≥0 → ℝ) (τ : ℝ≥0) : ℝ := limsup (fun n => p (dyadLo n τ)) atTop

theorem evalDn_eq {p : ℝ≥0 → ℝ} (hp : Continuous p) (τ : ℝ≥0) : evalDn p τ = p τ :=
  ((hp.tendsto τ).comp (tendsto_dyadLo τ)).limsup_eq

theorem evalDn_congr {p p' : ℝ≥0 → ℝ} {τ : ℝ≥0} (h : ∀ u ≤ τ, p u = p' u) : evalDn p τ = evalDn p' τ := by
  unfold evalDn
  congr 1
  funext n
  exact h _ (dyadLo_le n τ)

/-- **Causal evaluation at a measurable time is jointly measurable.** -/
theorem measurable_evalDn {α : Type*} [MeasurableSpace α] {p : α → ℝ≥0 → ℝ} (hp : ∀ t, Measurable fun a => p a t)
    {τ : α → ℝ≥0} (hτ : Measurable τ) : Measurable fun a => evalDn (p a) (τ a) := by
  refine Measurable.limsup fun n => ?_
  set g : α × ℕ → ℝ := fun q => p q.1 (((q.2 : ℝ) / 2 ^ n).toNNReal) with hg
  have hgm : Measurable g := measurable_from_prod_countable_left fun m =>
    show Measurable fun a => p a (((m : ℝ) / 2 ^ n).toNNReal) from hp _
  have hfl : Measurable fun a => ⌊(τ a : ℝ) * 2 ^ n⌋₊ :=
    ((measurable_coe_nnreal_real.comp hτ).mul_const _).nat_floor
  exact hgm.comp (measurable_id.prodMk hfl)

/-! ### The causal concatenation -/

/-- **The prefix `pre` up to `a`, then the path `p` delayed by `a`.** -/
def catAt (pre : ℝ≥0 → ℝ) (a : ℝ≥0) (p : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t ≤ a then pre t else evalDn pre a + evalDn p (t - a)

/-- **Causality with delay `a`**: paths agreeing up to `u` give concatenations agreeing up to `a + u`. -/
theorem catAt_congr (pre : ℝ≥0 → ℝ) (a : ℝ≥0) {p p' : ℝ≥0 → ℝ} {u : ℝ≥0∞}
    (h : ∀ v : ℝ≥0, (v : ℝ≥0∞) ≤ u → p v = p' v) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ a + u) :
    catAt pre a p t = catAt pre a p' t := by
  unfold catAt
  split_ifs with hta
  · rfl
  · congr 1
    refine evalDn_congr fun v hv => h v ?_
    have hv' : (v : ℝ≥0∞) ≤ ((t - a : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hv
    refine hv'.trans ?_
    rw [ENNReal.coe_sub]
    exact tsub_le_iff_left.2 ht

/-- **The concatenation rebuilds the relative path**: `pre` continuous and equal to `R` up to `a`, the delayed path
the stage driver `stgDrv R a`. -/
theorem catAt_stgDrv {R pre : ℝ≥0 → ℝ} (hR : Continuous R) (hpre : Continuous pre) {a : ℝ≥0}
    (hag : ∀ t ≤ a, pre t = R t) : catAt pre a (stgDrv R a) = R := by
  funext t
  unfold catAt
  split_ifs with hta
  · exact hag t hta
  · rw [evalDn_eq hpre, evalDn_eq (continuous_stgDrv hR a), hag a le_rfl, stgDrv,
      add_tsub_cancel_of_le (le_of_not_ge hta)]
    ring

/-! ### The stage rule -/

/-- **The stage rule** of a path rule `ρ` of (record, whole path), for decoders `σ` (the record), `A` (the relative
start) and `pre` (the relative prefix) of the stage record: `ρ (σ x, catAt (pre x) (A x) p) − A x`. -/
def stageRule (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (σ : RecData → RecData) (A : RecData → ℝ≥0)
    (pre : RecData → ℝ≥0 → ℝ) (y : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ρ (σ y.1, catAt (pre y.1) (A y.1) y.2) - A y.1

/-- **A stage rule of a path rule is a path rule.** -/
theorem isPathRule_stageRule {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (σ : RecData → RecData)
    (A : RecData → ℝ≥0) (pre : RecData → ℝ≥0 → ℝ) : IsPathRule (stageRule ρ σ A pre) := by
  intro r w w' hww'
  have hcat : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ρ (σ r, catAt (pre r) (A r) w) →
      catAt (pre r) (A r) w t = catAt (pre r) (A r) w' t := fun t ht =>
    catAt_congr (pre r) (A r) (u := stageRule ρ σ A pre (r, w)) hww' (ht.trans le_add_tsub)
  have h1 := hρ (σ r) (catAt (pre r) (A r) w) (catAt (pre r) (A r) w') hcat
  simp only [stageRule]
  rw [h1]

/-- **A stage rule of a measurable rule with measurable decoders is measurable.** -/
theorem measurable_stageRule {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : Measurable ρ) {σ : RecData → RecData}
    (hσ : Measurable σ) {A : RecData → ℝ≥0} (hA : Measurable A) {pre : RecData → ℝ≥0 → ℝ}
    (hpre : ∀ t, Measurable fun r => pre r t) : Measurable (stageRule ρ σ A pre) := by
  have hcat : ∀ t : ℝ≥0, Measurable fun y : RecData × (ℝ≥0 → ℝ) => catAt (pre y.1) (A y.1) y.2 t := by
    intro t
    have hle : MeasurableSet {y : RecData × (ℝ≥0 → ℝ) | t ≤ A y.1} :=
      measurableSet_le measurable_const (hA.comp measurable_fst)
    have h1 : Measurable fun y : RecData × (ℝ≥0 → ℝ) => pre y.1 t := (hpre t).comp measurable_fst
    have h2 : Measurable fun y : RecData × (ℝ≥0 → ℝ) => evalDn (pre y.1) (A y.1) :=
      measurable_evalDn (p := fun y : RecData × (ℝ≥0 → ℝ) => pre y.1) (fun s => (hpre s).comp measurable_fst)
        (hA.comp measurable_fst)
    have h3 : Measurable fun y : RecData × (ℝ≥0 → ℝ) => evalDn y.2 (t - A y.1) :=
      measurable_evalDn (p := fun y : RecData × (ℝ≥0 → ℝ) => y.2) (fun s => measurable_pi_apply s |>.comp
        measurable_snd) (measurable_const.sub (hA.comp measurable_fst))
    exact Measurable.ite hle h1 (h2.add h3)
  have hcm : Measurable fun y : RecData × (ℝ≥0 → ℝ) => catAt (pre y.1) (A y.1) y.2 := measurable_pi_iff.2 hcat
  exact (hρ.comp ((hσ.comp measurable_fst).prodMk hcm)).sub
    (measurable_coe_nnreal_ennreal.comp (hA.comp measurable_fst))

/-- **The stage rule at (stage record, stage driver) is the whole rule minus the start.** -/
theorem stageRule_stgDrv {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} {σ : RecData → RecData} {A : RecData → ℝ≥0}
    {pre : RecData → ℝ≥0 → ℝ} {x rec : RecData} {R : ℝ≥0 → ℝ} (hR : Continuous R) (hpre : Continuous (pre x))
    (hσ : σ x = rec) (hag : ∀ t ≤ A x, pre x t = R t) :
    stageRule ρ σ A pre (x, stgDrv R (A x)) = ρ (rec, R) - A x := by
  simp only [stageRule, hσ, catAt_stgDrv hR hpre hag]

end InteractingSLE.Theorem14.GW2Rd
