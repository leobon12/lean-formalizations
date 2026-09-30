import QuantumZipper.Proofs.LQG.ZoomRadialMain
import QuantumZipper.Proofs.LQG.ZoomRadial

/-!
# Measurability of the truncated zoom radial path (TASKS.md R6, D3-RAD step (i))

This file supplies the measurability input of the D3 radial comparison
(`ZoomRadial.abs_prob_zoomRadial_sub_le`, TASKS.md row R6): for a Brownian motion `b`, the map

`ω ↦ trunc S (Vpath α Q c b ω) : Ω → (ℝ → ℝ)`

is a.e. strongly measurable for the product σ-algebra on `ℝ → ℝ` (step (i) of the task list). The
proof avoids filtrations and stopping-time measurability entirely, using two ingredients:

* `exists_nice_version`: a version `b₀` of a Brownian motion which is measurable as a function of
  `(s, ω)`, is continuous with `b₀ 0 = 0` for *every* `ω`, and whose drifted path
  `s ↦ √2 b₀ s − (Q − α) s` reaches level `−c` for *every* `ω` (the last two properties come from
  the a.e. statements by freezing the process on the null set where they fail, as in
  `WedgeTrans.wedge_translation`);
* `Thit`: a *measurable surrogate* for the first hitting time of `0` by the drifted radial path
  `Xc`, namely the volume of the set of times where the rational predicate
  `∀ n, ∃ q ∈ ℚ ∩ [0,t], √2 p q − (Q − α) q ≤ −c + 1/(n+1)` fails. The predicate tests only values
  of the path at rational times, hence is jointly measurable, and `Thit_eq` shows that for
  continuous paths that do hit `0` the surrogate is exactly the hitting time.

Sources: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6 (the radial process at a zoom
is `BM + drift` re-centred at its first hit of `0`); the reduction of the hitting time to rational
times is an own elementary argument (the same device as in
`ZoomRadialMain.tendsto_prob_wedge_high`).
-/

noncomputable section

open Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## 2. The hitting time of `−c` by the drifted path, via a measurable surrogate -/

/-- The drifted path of a path `p`, in the parametrization of the wedge path on `t ≥ 0`. -/
def Xdrift (α Q : ℝ) (p : ℝ≥0 → ℝ) (t : ℝ) : ℝ := √2 * p t.toNNReal - (Q - α) * t

/-- The rational predicate: the drifted path of `p` comes within `1/(n+1)` of `−c` at a rational
time before `t`. Only rational times are tested, so this is jointly measurable. -/
def HitPred (α Q c : ℝ) (p : ℝ≥0 → ℝ) (t : ℝ) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Set.Icc 0 t ∧ Xdrift α Q p (q : ℝ) ≤ -c + 1 / (n + 1)

/-- The measurable surrogate for the hitting time of `−c`: the volume of the set of times (after
`0`) where the rational predicate `HitPred` fails. For continuous paths that hit `−c` this is
exactly the hitting time (`Thit_eq`). -/
def Thit (α Q c : ℝ) (p : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ∫⁻ t, if t ∈ Set.Ici (0 : ℝ) ∧ ¬ HitPred α Q c p t then 1 else 0

theorem measurableSet_hitPred (α Q c : ℝ) :
    MeasurableSet {x : (ℝ≥0 → ℝ) × ℝ | HitPred α Q c x.1 x.2} := by
  classical
  have key : {x : (ℝ≥0 → ℝ) × ℝ | HitPred α Q c x.1 x.2} =
      ⋂ n : ℕ, ⋃ q : {q : ℚ // (0 : ℝ) ≤ (q : ℝ)},
        ({x : (ℝ≥0 → ℝ) × ℝ | x.2 ∈ Set.Ici (q : ℝ)} ∩
          {x : (ℝ≥0 → ℝ) × ℝ | Xdrift α Q x.1 (q : ℝ) ≤ -c + 1 / (n + 1)}) := by
    ext x
    simp only [HitPred, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_Icc, Set.mem_Ici, Subtype.exists, exists_prop, and_assoc]
  rw [key]
  refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => MeasurableSet.inter ?_ ?_
  · exact measurableSet_Ici.preimage measurable_snd
  · have h : Measurable fun x : (ℝ≥0 → ℝ) × ℝ => Xdrift α Q x.1 (q : ℝ) := by
      have h1 : Measurable fun x : (ℝ≥0 → ℝ) × ℝ => x.1 ((q : ℝ).toNNReal) :=
        (measurable_pi_apply ((q : ℝ).toNNReal)).comp measurable_fst
      simpa only [Xdrift] using (h1.const_mul (√2)).sub_const ((Q - α) * (q : ℝ))
    exact measurableSet_le h measurable_const

theorem measurable_Thit (α Q c : ℝ) : Measurable (Thit α Q c) := by
  have hs : MeasurableSet {x : (ℝ≥0 → ℝ) × ℝ |
      x.2 ∈ Set.Ici (0 : ℝ) ∧ ¬ HitPred α Q c x.1 x.2} :=
    (measurableSet_Ici.preimage measurable_snd).inter (measurableSet_hitPred α Q c).compl
  have h : Measurable (Function.uncurry fun (p : ℝ≥0 → ℝ) (t : ℝ) =>
      if t ∈ Set.Ici (0 : ℝ) ∧ ¬ HitPred α Q c p t then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite hs measurable_const measurable_const
  exact h.lintegral_prod_right

/-- The drifted path of a continuous path is continuous. -/
theorem continuous_Xdrift {p : ℝ≥0 → ℝ} (hpc : Continuous p) :
    Continuous fun t : ℝ => Xdrift α Q p t :=
  (continuous_const.mul (hpc.comp continuous_real_toNNReal)).sub
    (continuous_const.mul continuous_id)

/-- **The rational predicate characterizes the times after the hitting time**, for continuous
paths that hit `−c`. -/
theorem hitPred_iff {α Q c : ℝ} {p : ℝ≥0 → ℝ} (hpc : Continuous p) (hp0 : p 0 = 0) (hc : 0 < c)
    (hhit : ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q p s ≤ -c) {t : ℝ} (ht : 0 ≤ t) :
    HitPred α Q c p t ↔ sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c} ≤ t := by
  have hx : Continuous fun t : ℝ => Xdrift α Q p t := continuous_Xdrift hpc
  have hx0 : Xdrift α Q p 0 = 0 := by simp [Xdrift, hp0]
  have hspec := WedgeTrans.hitTime_spec hx hx0 hc hhit
  set T : ℝ := sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c} with hT
  have hmem : Xdrift α Q p T ≤ -c := by
    rw [hT]; simpa only [WedgeTrans.hitTime] using hspec.2.1.le
  constructor
  · intro hpred
    -- the minimum of the drifted path on `[0, t]` is `≤ -c`, and it is attained
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, ⟨le_rfl, ht⟩⟩ hx.continuousOn
    have hle : ∀ n : ℕ, Xdrift α Q p s₀ ≤ -c + 1 / (n + 1) := by
      intro n
      obtain ⟨q, hq, hq'⟩ := hpred n
      exact (hmin ⟨hq.1, hq.2⟩).trans hq'
    have hlim : Xdrift α Q p s₀ ≤ -c := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / (n + 1 : ℝ) < ε := by
        obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
        refine ⟨n, ?_⟩
        have h2 : ε * ε⁻¹ < ε * (n : ℝ) := mul_lt_mul_of_pos_left hn hε
        have h3 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
        nlinarith [h2, h3]
      linarith [hle n]
    rw [hT]
    exact (csInf_le (show BddBelow {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c} from
      ⟨0, fun y hy => hy.1⟩) ⟨hs₀.1, hlim⟩).trans hs₀.2
  · intro hTt
    -- just before the hitting time there are rational times with the drifted path `≤ -c + 1/(n+1)`
    intro n
    have hTpos : 0 < T := by
      refine lt_of_le_of_ne hspec.1 (Ne.symm ?_)
      intro hT0
      have hc0 : (0 : ℝ) ≤ -c := by rw [← hx0, ← hT0]; exact hmem
      linarith
    obtain ⟨δ, hδpos, hδ⟩ :=
      (Metric.tendsto_nhds_nhds.1 hx.continuousAt) (1 / (n + 1)) (by positivity)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (show T - δ < T by linarith) hTpos)
    refine ⟨q, ⟨le_of_lt (lt_of_le_of_lt (le_max_right (T - δ) 0) hq1), ?_⟩, ?_⟩
    · exact le_of_lt (hq2.trans_le hTt)
    · have hqT : |(q : ℝ) - T| < δ := by
        have h1 : T - δ < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
        rw [abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hball : dist (Xdrift α Q p (q : ℝ)) (Xdrift α Q p T) < 1 / (n + 1) :=
        hδ (by rw [Real.dist_eq]; exact hqT)
      rw [Real.dist_eq, abs_lt] at hball
      linarith [hball.1, hmem]

/-! ## 3. Step (i): measurability of the truncated zoom radial path -/

/-- The hitting-time functional of the drifted path is the zoom time of `ZoomRadialBasic`. -/
theorem sInf_drift_eq_Tc (α Q c : ℝ) (b : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q (pathOf b ω) s ≤ -c} = Tc α Q c b ω := by
  rw [Tc, Tc_set_eq]
  refine congrArg sInf (Set.ext fun t => ?_)
  simp only [Set.mem_setOf_eq, Xdrift, pathOf]

/-! ## 4. The surrogate is the hitting time -/

/-- **The surrogate is the hitting time** for continuous paths that hit `−c`. -/
theorem Thit_eq {α Q c : ℝ} {p : ℝ≥0 → ℝ} (hpc : Continuous p) (hp0 : p 0 = 0) (hc : 0 < c)
    (hhit : ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q p s ≤ -c) :
    Thit α Q c p = ENNReal.ofReal (sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c}) := by
  set T : ℝ := sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c} with hT
  have hspec := WedgeTrans.hitTime_spec (continuous_Xdrift hpc) (by simp [Xdrift, hp0]) hc hhit
  have hset : ∀ t : ℝ, (¬ HitPred α Q c p t) ↔ t ∈ Set.Iio T := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [Set.mem_Iio, ← not_le, hitPred_iff hpc hp0 hc hhit ht]
    · have hne : ¬ HitPred α Q c p t := by
        simp only [HitPred, Set.Icc_eq_empty ht, Set.mem_empty_iff_false, false_and, exists_false,
          forall_const, not_false_eq_true]
      exact ⟨fun _ => lt_of_lt_of_le (not_le.1 ht) hspec.1, fun _ => hne⟩
  have h1 : Thit α Q c p = ∫⁻ t, if t ∈ Set.Ico (0 : ℝ) T then (1 : ℝ≥0∞) else 0 := by
    rw [Thit]
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Set.Ico (0 : ℝ) T
    · have h2 : t ∈ Set.Ici (0 : ℝ) ∧ ¬ HitPred α Q c p t :=
        ⟨(Set.mem_Ico.1 ht).1, (hset t).2 (Set.mem_Iio.2 (Set.mem_Ico.1 ht).2)⟩
      rw [if_pos h2, if_pos ht]
    · have h2 : ¬ (t ∈ Set.Ici (0 : ℝ) ∧ ¬ HitPred α Q c p t) := by
        rintro ⟨h3, h4⟩
        exact ht (Set.mem_Ico.2 ⟨h3, (hset t).1 h4⟩)
      rw [if_neg h2, if_neg ht]
  have h2 : (∫⁻ t, if t ∈ Set.Ico (0 : ℝ) T then (1 : ℝ≥0∞) else 0) =
      ∫⁻ t, (Set.Ico (0 : ℝ) T).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    refine lintegral_congr fun t => ?_
    by_cases ht : t ∈ Set.Ico (0 : ℝ) T
    · rw [Set.indicator_of_mem ht, if_pos ht]
    · rw [Set.indicator_of_notMem ht, if_neg ht]
  rw [h1, h2, lintegral_indicator measurableSet_Ico, setLIntegral_one, Real.volume_Ico, sub_zero]

/-- The surrogate is a real number equal to the hitting time. -/
theorem Thit_toReal {α Q c : ℝ} {p : ℝ≥0 → ℝ} (hpc : Continuous p) (hp0 : p 0 = 0) (hc : 0 < c)
    (hhit : ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q p s ≤ -c) :
    (Thit α Q c p).toReal = sInf {s : ℝ | 0 ≤ s ∧ Xdrift α Q p s ≤ -c} := by
  rw [Thit_eq hpc hp0 hc hhit, ENNReal.toReal_ofReal]
  exact (WedgeTrans.hitTime_spec (continuous_Xdrift hpc) (by simp [Xdrift, hp0]) hc hhit).1

/-! ## 5. A nice version of a Brownian motion, and step (i) -/

/-- **A nice version of a Brownian motion.** For a Brownian motion `B` (and `α < Q`, `c > 0`)
there is a process `b` which is measurable as a function of `(s, ω)`, is continuous with `b 0 = 0`
for every `ω`, whose drifted path reaches `−c` for every `ω`, and which agrees with `B` a.e.

Own elementary proof (the same construction as in `WedgeTrans.wedge_translation`). -/
theorem exists_nice_version {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {α Q c : ℝ}
    (hαQ : α < Q) (hc : 0 < c) :
    ∃ b : ℝ≥0 → Ω → ℝ, Measurable (Function.uncurry b) ∧ (∀ ω, Continuous fun s => b s ω) ∧
      (∀ ω, b 0 ω = 0) ∧ (∀ ω, ∃ s : ℝ≥0, √2 * b s ω - (Q - α) * s ≤ -c) ∧
      (∀ᵐ ω ∂P, ∀ s, b s ω = B s ω) := by
  classical
  obtain ⟨B₀, hB₀m, hB₀c, hB₀B⟩ := WedgeRes.exists_good_version hB
  have hB₀mt : ∀ t : ℝ≥0, Measurable (B₀ t) := fun t => hB₀m.of_uncurry_left
  have hB₀pre : IsPreBrownianReal B₀ P :=
    hB.toIsPreBrownianReal.congr fun s => hB₀B.mono fun ω h => (h s).symm
  have hμ : 0 < Q - α := sub_pos.2 hαQ
  have hG₁ : MeasurableSet {ω : Ω | B₀ 0 ω = 0} :=
    measurableSet_eq_fun (hB₀mt 0) measurable_const
  have hG₂ : MeasurableSet {ω : Ω | ∃ n : ℕ, √2 * B₀ n ω - (Q - α) * (n : ℝ) < -c} := by
    have h : {ω : Ω | ∃ n : ℕ, √2 * B₀ n ω - (Q - α) * (n : ℝ) < -c} =
        ⋃ n : ℕ, {ω : Ω | √2 * B₀ n ω - (Q - α) * (n : ℝ) < -c} := by ext ω; simp
    rw [h]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_lt (((hB₀mt n).const_mul (√2)).sub_const _) measurable_const
  set G : Set Ω := {ω | B₀ 0 ω = 0 ∧ ∃ n : ℕ, √2 * B₀ n ω - (Q - α) * (n : ℝ) < -c} with hG
  have hGm : MeasurableSet G := hG₁.inter hG₂
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hB₀pre.eval_zero_ae_eq_zero,
      WedgeTrans.ae_exists_below hB₀pre hB₀mt hμ hc] with ω h1 h2 using ⟨h1, h2⟩
  have hbm : Measurable (Function.uncurry fun s ω => if ω ∈ G then B₀ s ω else -(√2 * c) * s) := by
    refine Measurable.ite (hGm.preimage measurable_snd) hB₀m ?_
    exact (measurable_fst.coe_nnreal_real).const_mul (-(√2 * c))
  have hbc : ∀ ω, Continuous fun s : ℝ≥0 => if ω ∈ G then B₀ s ω else -(√2 * c) * s := by
    intro ω
    by_cases hω : ω ∈ G
    · have h : (fun s : ℝ≥0 => if ω ∈ G then B₀ s ω else -(√2 * c) * s) = fun s => B₀ s ω := by
        funext s; rw [if_pos hω]
      rw [h]; exact hB₀c ω
    · have h : (fun s : ℝ≥0 => if ω ∈ G then B₀ s ω else -(√2 * c) * s)
          = fun s : ℝ≥0 => -(√2 * c) * s := by
        funext s; rw [if_neg hω]
      rw [h]; exact continuous_const.mul NNReal.continuous_coe
  have hbz : ∀ ω, (if ω ∈ G then B₀ 0 ω else -(√2 * c) * (0 : ℝ≥0)) = 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [if_pos hω]; exact hω.1
    · rw [if_neg hω]; simp
  have hbh : ∀ ω, ∃ s : ℝ≥0,
      √2 * (if ω ∈ G then B₀ s ω else -(√2 * c) * s) - (Q - α) * s ≤ -c := by
    intro ω
    by_cases hω : ω ∈ G
    · obtain ⟨n, hn⟩ := hω.2
      refine ⟨(n : ℝ≥0), ?_⟩
      rw [if_pos hω]
      have hcoe : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by simp
      rw [hcoe]
      linarith
    · refine ⟨1, ?_⟩
      rw [if_neg hω, NNReal.coe_one, mul_one]
      have h2 : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)
      nlinarith [h2, hc, hμ]
  have hbae : ∀ᵐ ω ∂P, ∀ s, (if ω ∈ G then B₀ s ω else -(√2 * c) * s) = B s ω := by
    filter_upwards [hGae, hB₀B] with ω hω h s
    rw [if_pos hω]
    exact h s
  exact ⟨fun s ω => if ω ∈ G then B₀ s ω else -(√2 * c) * s, hbm, hbc, hbz, hbh, hbae⟩

/-- The wedge-path process of a wedge process is a.e. strongly measurable as a path. -/
theorem aemeasurable_wedgePath {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (fun ω => fun t => A t ω) P := by
  classical
  obtain ⟨B, B', hB, hB', hBB', hAB⟩ := hA
  obtain ⟨B₀, hB₀m, hB₀c, hB₀B⟩ := WedgeRes.exists_good_version hB
  obtain ⟨B₀', hB₀'m, hB₀'c, hB₀'B⟩ := WedgeRes.exists_good_version hB'
  have hYtc : ∀ ω, Continuous fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s := fun ω =>
    (continuous_const.mul ((hB₀'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hYtm : ∀ s : ℝ, Measurable fun ω => √2 * B₀' s.toNNReal ω - (α - Q) * s := fun s =>
    (((hB₀'m.of_uncurry_left (x := s.toNNReal)).const_mul (√2)).sub_const ((α - Q) * s))
  have hYtJ : Measurable fun p : Ω × ℝ => √2 * B₀' p.2.toNNReal p.1 - (α - Q) * p.2 :=
    (measurable_uncurry_of_continuous_of_measurable hYtc hYtm).comp measurable_swap
  have hLm : Measurable fun ω => lastZero (fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s) :=
    WedgeMeas.measurable_lastZero hYtc hYtm
  have hmeas : Measurable fun ω => fun t : ℝ => WedgeTrans.wA α Q B₀ B₀' t ω := by
    refine measurable_pi_iff.2 fun t => ?_
    by_cases ht : 0 ≤ t
    · have heq : (fun ω => WedgeTrans.wA α Q B₀ B₀' t ω)
          = fun ω => √2 * B₀ t.toNNReal ω + (α - Q) * t := by
        funext ω
        simp only [WedgeTrans.wA, wedgePath, if_pos ht]
      rw [heq]
      exact (((hB₀m.of_uncurry_left (x := t.toNNReal)).const_mul (√2)).add_const _)
    · have heq : (fun ω => WedgeTrans.wA α Q B₀ B₀' t ω)
          = fun ω => √2 * B₀' (-t + lastZero (fun s : ℝ => √2 * B₀' s.toNNReal ω
              - (α - Q) * s)).toNNReal ω - (α - Q) * (-t + lastZero (fun s : ℝ =>
                √2 * B₀' s.toNNReal ω - (α - Q) * s)) := by
        funext ω
        simp only [WedgeTrans.wA, wedgePath, if_neg ht]
      rw [heq]
      refine hYtJ.comp (measurable_id.prodMk ?_)
      exact (measurable_const.add hLm)
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hB₀B, hB₀'B] with ω h1 h2
  have h2' : ∀ s : ℝ≥0, B' s ω = B₀' s ω := fun s => (h2 s).symm
  have hYeq : (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s)
      = fun s : ℝ => √2 * B₀' s.toNNReal ω - (α - Q) * s := by
    funext s
    rw [h2' s.toNNReal]
  funext t
  rw [hAB ω t]
  by_cases ht : 0 ≤ t
  · simp only [WedgeTrans.wA, wedgePath, if_pos ht]
    rw [← h1 t.toNNReal]
  · simp only [WedgeTrans.wA, wedgePath, if_neg ht, hYeq, h2']

/-- The truncated re-centred wedge path of two Brownian motions is a.e. strongly measurable; this
is the measurability input for applying `WedgeTrans.wedge_translation` to path sets. -/
theorem aemeasurable_Rw {α Q c S : ℝ} {b b' : ℝ≥0 → Ω → ℝ}
    (hb : IsBrownianReal b P) (hb' : IsBrownianReal b' P) (hαQ : α < Q) (hc : 0 < c) :
    AEMeasurable (fun ω => Rw α Q b b' c ω) P := by
  classical
  obtain ⟨β, hβm, hβc, hβz, hβh, hβb⟩ := exists_nice_version hb hαQ hc
  obtain ⟨β', hβ'm, hβ'c, hβ'b⟩ := WedgeRes.exists_good_version hb'
  have hβmt : ∀ s : ℝ≥0, Measurable fun ω => β s ω := fun s => hβm.of_uncurry_left
  have hdrift : ∀ ω : Ω, ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q (pathOf β ω) s ≤ -c := by
    intro ω
    obtain ⟨s, hs⟩ := hβh ω
    exact ⟨s, s.2, by simpa only [Xdrift, pathOf, Real.toNNReal_coe] using hs⟩
  set τ : Ω → ℝ := fun ω => (Thit α Q c (pathOf β ω)).toReal with hτ
  have hτm : Measurable τ :=
    ((measurable_Thit α Q c).comp (measurable_pi_iff.2 hβmt)).ennreal_toReal
  have hτeq : ∀ ω, Tc α Q c β ω = τ ω := fun ω =>
    ((Thit_toReal (hβc ω) (hβz ω) hc (hdrift ω)).trans
      (sInf_drift_eq_Tc α Q c β ω)).symm
  have hYtc : ∀ ω, Continuous fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s := fun ω =>
    (continuous_const.mul ((hβ'c ω).comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hYtm : ∀ s : ℝ, Measurable fun ω => √2 * β' s.toNNReal ω - (α - Q) * s := fun s =>
    (((hβ'm.of_uncurry_left (x := s.toNNReal)).const_mul (√2)).sub_const ((α - Q) * s))
  have hYtJ : Measurable fun p : Ω × ℝ => √2 * β' p.2.toNNReal p.1 - (α - Q) * p.2 :=
    (measurable_uncurry_of_continuous_of_measurable hYtc hYtm).comp measurable_swap
  have hLm : Measurable fun ω => lastZero (fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s) :=
    WedgeMeas.measurable_lastZero hYtc hYtm
  have hcoord : ∀ t : ℝ, Measurable fun ω => Rw α Q β β' c ω t := by
    intro t
    have hRw : (fun ω => Rw α Q β β' c ω t)
        = fun ω => WedgeTrans.wA α Q β β' (τ ω + t) ω + c := by
      funext ω
      have hs : sInf {s : ℝ | 0 ≤ s ∧ WedgeTrans.wA α Q β β' s ω ≤ -c} = τ ω :=
        (hitTime_eq_Tc α Q c β β' ω).trans (hτeq ω)
      simp only [Rw, hs]
    rw [hRw]
    have hsplit : (fun ω => WedgeTrans.wA α Q β β' (τ ω + t) ω + c)
        = fun ω => (if 0 ≤ τ ω + t then
            √2 * β ((τ ω + t).toNNReal) ω + (α - Q) * (τ ω + t)
          else √2 * β' (-(τ ω + t)
              + lastZero (fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s)).toNNReal ω
            - (α - Q) * (-(τ ω + t)
              + lastZero (fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s))) + c := by
      funext ω
      simp only [WedgeTrans.wA, wedgePath]
    rw [hsplit]
    have hs : MeasurableSet {ω : Ω | 0 ≤ τ ω + t} :=
      measurableSet_le measurable_const (hτm.add_const t)
    have hite : Measurable fun ω : Ω => if 0 ≤ τ ω + t then
        √2 * β ((τ ω + t).toNNReal) ω + (α - Q) * (τ ω + t)
      else √2 * β' (-(τ ω + t) + lastZero (fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s)).toNNReal ω
        - (α - Q) * (-(τ ω + t)
          + lastZero (fun s : ℝ => √2 * β' s.toNNReal ω - (α - Q) * s)) := by
      refine Measurable.ite hs ?_ ?_
      · have hg : Measurable fun ω : Ω => (τ ω + t).toNNReal := (hτm.add_const t).real_toNNReal
        exact ((hβm.comp (hg.prodMk measurable_id)).const_mul (√2)).add
          ((hτm.add_const t).const_mul (α - Q))
      · exact hYtJ.comp (measurable_id.prodMk (((hτm.add_const t).neg).add hLm))
    exact hite.add_const c
  have hmeas : Measurable fun ω => Rw α Q β β' c ω := measurable_pi_iff.2 hcoord
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hβb, hβ'b] with ω h1 h2
  have hp : ∀ s : ℝ≥0, β s ω = b s ω := fun s => h1 s
  have hp' : ∀ s : ℝ≥0, β' s ω = b' s ω := fun s => h2 s
  refine funext fun t => ?_
  have hA : ∀ s : ℝ, WedgeTrans.wA α Q β β' s ω = WedgeTrans.wA α Q b b' s ω := by
    intro s
    by_cases hs : 0 ≤ s
    · have hgoal : √2 * β s.toNNReal ω + (α - Q) * s = √2 * b s.toNNReal ω + (α - Q) * s := by
        rw [hp s.toNNReal]
      simpa only [WedgeTrans.wA, wedgePath, if_pos hs] using hgoal
    · have hYeq : (fun u : ℝ => √2 * β' u.toNNReal ω - (α - Q) * u)
          = fun u : ℝ => √2 * b' u.toNNReal ω - (α - Q) * u := by
        funext u
        rw [hp' u.toNNReal]
      have hgoal : (fun u : ℝ => √2 * β' u.toNNReal ω - (α - Q) * u)
            (-s + lastZero (fun u : ℝ => √2 * β' u.toNNReal ω - (α - Q) * u))
          = (fun u : ℝ => √2 * b' u.toNNReal ω - (α - Q) * u)
            (-s + lastZero (fun u : ℝ => √2 * b' u.toNNReal ω - (α - Q) * u)) := by
        rw [hYeq]
      simpa only [WedgeTrans.wA, wedgePath, if_neg hs] using hgoal
  have hset : sInf {s : ℝ | 0 ≤ s ∧ WedgeTrans.wA α Q β β' s ω ≤ -c}
      = sInf {s : ℝ | 0 ≤ s ∧ WedgeTrans.wA α Q b b' s ω ≤ -c} := by
    congr 1
    ext s
    exact and_congr_right fun _ => by rw [hA s]
  simp only [Rw, hset, hA]

/-! ## 6. Evaluating a path at a measurable time with countable range -/

/-- A measurable map into a countable set, used as a (random) time index, can be used to evaluate
a path measurably. -/
theorem measurable_apply_of_countable_range {idx : (ℝ≥0 → ℝ) → ℝ≥0} {C : Set ℝ≥0}
    (hidx : Measurable idx) (hC : C.Countable) (hrange : ∀ p, idx p ∈ C) :
    Measurable fun p : (ℝ≥0 → ℝ) => p (idx p) := by
  refine measurable_of_Iio fun a => ?_
  have h : (fun p : ℝ≥0 → ℝ => p (idx p)) ⁻¹' Set.Iio a =
      ⋃ r ∈ C, ((fun p : ℝ≥0 → ℝ => idx p) ⁻¹' {r}) ∩ ((fun p : ℝ≥0 → ℝ => p r) ⁻¹' Set.Iio a) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨idx p, hrange p, rfl, hp⟩
    · rintro ⟨r, hr, hidxr, hpr⟩
      rw [hidxr]
      exact hpr
  rw [h]
  exact MeasurableSet.biUnion hC fun r _ =>
    (measurableSet_singleton r).preimage hidx |>.inter
      (measurableSet_Iio.preimage (measurable_pi_apply r))

/-- The dyadic rounding (from above) of a real number: the smallest number of the form
`k / 2^n` (`k : ℤ`) that exceeds `x`. -/
def dyadicRound (n : ℕ) (x : ℝ) : ℝ := ((Int.floor (2 ^ n * x) + 1 : ℤ) : ℝ) / 2 ^ n

theorem measurable_dyadicRound (n : ℕ) : Measurable (dyadicRound n) := by
  have h1 : Measurable fun x : ℝ => ((Int.floor (2 ^ n * x) + 1 : ℤ) : ℝ) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      ((Measurable.floor (measurable_const.mul measurable_id)).add_const 1)
  exact h1.div_const (2 ^ n)

theorem dyadicRound_gt (n : ℕ) (x : ℝ) : x < dyadicRound n x := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicRound, lt_div_iff₀ h2]
  have := Int.lt_floor_add_one (2 ^ n * x)
  push_cast
  linarith [this]

theorem dyadicRound_le (n : ℕ) (x : ℝ) : dyadicRound n x ≤ x + 1 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicRound, div_le_iff₀ h2]
  have := Int.floor_le (2 ^ n * x)
  have h3 : 1 / 2 ^ n * 2 ^ n = (1 : ℝ) := by
    rw [div_mul_cancel₀]; positivity
  push_cast
  nlinarith [this, h3]

theorem tendsto_dyadicRound (x : ℝ) :
    Tendsto (fun n : ℕ => dyadicRound n x) atTop (𝓝 x) := by
  have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := ((1 : ℝ) / 2))
      (by norm_num : ‖((1 : ℝ) / 2)‖ < 1)
    simpa only [one_div, inv_pow] using hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
    (Eventually.of_forall fun n => (dyadicRound_gt n x).le)
    (Eventually.of_forall fun n => dyadicRound_le n x)
  simpa only [add_zero] using tendsto_const_nhds.add h0

theorem dyadicRound_toNNReal_mem (n : ℕ) (x : ℝ) :
    (dyadicRound n x).toNNReal ∈ Set.range (fun k : ℤ => (((k : ℝ) / 2 ^ n).toNNReal)) :=
  ⟨Int.floor (2 ^ n * x) + 1, rfl⟩

theorem countable_range_dyadicRound_toNNReal (n : ℕ) :
    (Set.range (fun k : ℤ => (((k : ℝ) / 2 ^ n).toNNReal))).Countable := by
  simpa only [Set.image_univ] using
    (Set.countable_univ.image fun k : ℤ => (((k : ℝ) / 2 ^ n).toNNReal))

/-! ## 7. The measurable path-space surrogate of the truncated zoom path -/

/-- `Xc` read as a functional of the path: `t ↦ c + √2 * p t.toNNReal + (α − Q) * t`. -/
def Xpath (α Q c : ℝ) (p : ℝ≥0 → ℝ) (t : ℝ) : ℝ := c + √2 * p t.toNNReal + (α - Q) * t

theorem continuous_Xpath {p : ℝ≥0 → ℝ} (hp : Continuous p) :
    Continuous fun t : ℝ => Xpath α Q c p t :=
  (continuous_const.add (continuous_const.mul (hp.comp continuous_real_toNNReal))).add
    (continuous_const.mul continuous_id)

/-- The truncated zoom radial path as a functional of a path (it matches `trunc S (Vpath …)`). -/
def VpathPath (α Q c S : ℝ) (p : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun s => Xpath α Q c p (sInf {t : ℝ | 0 ≤ t ∧ Xdrift α Q p t ≤ -c} + max s (-S))

/-- The `n`-th dyadic approximation of the truncated zoom path. -/
def Zappr (α Q c S : ℝ) (n : ℕ) (p : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun s => Xpath α Q c p (dyadicRound n ((Thit α Q c p).toReal + max s (-S)))

/-- The measurable surrogate of the truncated zoom path on path space. -/
def Zsur (α Q c S : ℝ) (p : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun s => liminf (fun n : ℕ => Zappr α Q c S n p s) atTop

theorem measurable_Zappr (α Q c S : ℝ) (n : ℕ) (s : ℝ) :
    Measurable fun p : ℝ≥0 → ℝ => Zappr α Q c S n p s := by
  have hτ : Measurable fun p : ℝ≥0 → ℝ => (Thit α Q c p).toReal + max s (-S) :=
    ((measurable_Thit α Q c).ennreal_toReal).add_const _
  have hd : Measurable fun p : ℝ≥0 → ℝ =>
      dyadicRound n ((Thit α Q c p).toReal + max s (-S)) :=
    (measurable_dyadicRound n).comp hτ
  have hidx : Measurable fun p : ℝ≥0 → ℝ =>
      (dyadicRound n ((Thit α Q c p).toReal + max s (-S))).toNNReal := hd.real_toNNReal
  have hev : Measurable fun p : ℝ≥0 → ℝ =>
      p ((dyadicRound n ((Thit α Q c p).toReal + max s (-S))).toNNReal) :=
    measurable_apply_of_countable_range hidx (countable_range_dyadicRound_toNNReal n)
      fun p => dyadicRound_toNNReal_mem n _
  have hdrift : Measurable fun p : ℝ≥0 → ℝ =>
      (α - Q) * dyadicRound n ((Thit α Q c p).toReal + max s (-S)) := hd.const_mul (α - Q)
  have h : Measurable fun p : ℝ≥0 → ℝ =>
      c + √2 * p ((dyadicRound n ((Thit α Q c p).toReal + max s (-S))).toNNReal)
        + (α - Q) * dyadicRound n ((Thit α Q c p).toReal + max s (-S)) :=
    ((hev.const_mul (√2)).const_add c).add hdrift
  simpa only [Zappr, Xpath] using h

theorem measurable_Zsur (α Q c S : ℝ) : Measurable (Zsur α Q c S) := by
  refine measurable_pi_iff.2 fun s => ?_
  have h : Measurable fun p : ℝ≥0 → ℝ =>
      liminf (fun n : ℕ => Zappr α Q c S n p s) atTop :=
    Measurable.liminf fun n => measurable_Zappr α Q c S n s
  simpa only [Zsur] using h

/-- The nice-version hitting condition, in the form used by `Xdrift`. -/
theorem exists_drift_le {α Q c : ℝ} {β : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : ∃ s : ℝ≥0, √2 * β s ω - (Q - α) * s ≤ -c) :
    ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q (pathOf β ω) s ≤ -c := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, s.2, by simpa only [Xdrift, pathOf, Real.toNNReal_coe] using hs⟩

/-- **The surrogate is exact** on continuous paths that hit `−c`. -/
theorem Zsur_eq_VpathPath {α Q c S : ℝ} {p : ℝ≥0 → ℝ} (hpc : Continuous p) (hp0 : p 0 = 0)
    (hc : 0 < c) (hhit : ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q p s ≤ -c) (s : ℝ) :
    Zsur α Q c S p s = VpathPath α Q c S p s := by
  have hlim : Tendsto (fun n : ℕ =>
      Xpath α Q c p (dyadicRound n ((Thit α Q c p).toReal + max s (-S)))) atTop
      (𝓝 (Xpath α Q c p ((Thit α Q c p).toReal + max s (-S)))) :=
    ((continuous_Xpath (α := α) (Q := Q) (c := c) hpc).tendsto
      ((Thit α Q c p).toReal + max s (-S))).comp (tendsto_dyadicRound _)
  rw [Zsur, show (fun n : ℕ => Zappr α Q c S n p s) = fun n : ℕ =>
      Xpath α Q c p (dyadicRound n ((Thit α Q c p).toReal + max s (-S))) from rfl,
    hlim.liminf_eq, VpathPath, Thit_toReal hpc hp0 hc hhit]

/-- The truncated zoom radial path is the path functional `VpathPath`. -/
theorem trunc_Vpath_eq_VpathPath (b : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    trunc S (Vpath α Q c b ω) = VpathPath α Q c S (pathOf b ω) := by
  have hsInf : sInf {t : ℝ | 0 ≤ t ∧ Xdrift α Q (pathOf b ω) t ≤ -c} = Tc α Q c b ω :=
    sInf_drift_eq_Tc α Q c b ω
  funext s
  simp only [trunc_apply, Vpath, VpathPath, Xpath, Xc, pathOf, hsInf]

/-- Two processes that agree at all times give the same truncated zoom path. -/
theorem trunc_Vpath_congr {b b' : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ∀ s, b s ω = b' s ω) :
    trunc S (Vpath α Q c b ω) = trunc S (Vpath α Q c b' ω) := by
  have hXc : ∀ t : ℝ, Xc α Q c b ω t = Xc α Q c b' ω t := by
    intro t; simp only [Xc, h t.toNNReal]
  have hTc : Tc α Q c b ω = Tc α Q c b' ω := by
    rw [Tc, Tc]
    congr 1
    ext t
    exact and_congr_right fun _ => by rw [hXc t]
  congr 1
  funext s
  simp only [Vpath]
  rw [← hTc, hXc]

/-- **Step (iii) of D3-RAD: the law of the truncated zoom radial path of a Brownian motion
depends only on the law of the Brownian motion.** -/
theorem prob_trunc_Vpath_cross {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P')
    {α Q c S : ℝ} (hαQ : α < Q) (hc : 0 < c) {E : Set (ℝ → ℝ)} (hE : MeasurableSet E)
    (hb : IsBrownianReal b P) :
    P {ω | trunc S (Vpath α Q c b ω) ∈ E} = P' {ω' | trunc S (Vpath α Q c B ω') ∈ E} := by
  obtain ⟨β, hβm, hβc, hβz, hβh, hβb⟩ := exists_nice_version hb hαQ hc
  obtain ⟨β', hβ'm, hβ'c, hβ'z, hβ'h, hβ'b⟩ := exists_nice_version hB hαQ hc
  have hβpre : IsPreBrownianReal β P :=
    hb.toIsPreBrownianReal.congr fun s => hβb.mono fun ω h => (h s).symm
  have hβ'pre : IsPreBrownianReal β' P' :=
    hB.toIsPreBrownianReal.congr fun s => hβ'b.mono fun ω h => (h s).symm
  have hβpath : Measurable fun ω (s : ℝ≥0) => β s ω :=
    measurable_pi_iff.2 fun s => hβm.of_uncurry_left
  have hβ'path : Measurable fun ω (s : ℝ≥0) => β' s ω :=
    measurable_pi_iff.2 fun s => hβ'm.of_uncurry_left
  have hZm : Measurable (Zsur α Q c S) := measurable_Zsur α Q c S
  have h1 : Measurable (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β s ω) := hZm.comp hβpath
  have h2 : Measurable (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β' s ω) := hZm.comp hβ'path
  have hZβ : ∀ ω, trunc S (Vpath α Q c β ω) = Zsur α Q c S (pathOf β ω) := fun ω => by
    rw [trunc_Vpath_eq_VpathPath]
    funext s
    change VpathPath α Q c S (fun s => β s ω) s = Zsur α Q c S (fun s => β s ω) s
    rw [Zsur_eq_VpathPath (hβc ω) (hβz ω) hc
      (exists_drift_le (α := α) (Q := Q) (c := c) (β := β) (ω := ω) (hβh ω)) s]
  have hZβ' : ∀ ω, trunc S (Vpath α Q c β' ω) = Zsur α Q c S (pathOf β' ω) := fun ω => by
    rw [trunc_Vpath_eq_VpathPath]
    funext s
    change VpathPath α Q c S (fun s => β' s ω) s = Zsur α Q c S (fun s => β' s ω) s
    rw [Zsur_eq_VpathPath (hβ'c ω) (hβ'z ω) hc
      (exists_drift_le (α := α) (Q := Q) (c := c) (β := β') (ω := ω) (hβ'h ω)) s]
  have e1 : P {ω | trunc S (Vpath α Q c b ω) ∈ E} = P {ω | trunc S (Vpath α Q c β ω) ∈ E} := by
    refine measure_congr ?_
    filter_upwards [hβb] with ω hω
    simp only [Set.mem_setOf_eq, trunc_Vpath_congr (α := α) (Q := Q) (c := c) (S := S)
      (b := β) (b' := b) hω]
  have e2 : P {ω | trunc S (Vpath α Q c β ω) ∈ E} = P {ω | Zsur α Q c S (pathOf β ω) ∈ E} := by
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, hZβ ω]
  have hmap : P.map (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β s ω)
      = P'.map (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β' s ω) := by
    rw [← Measure.map_map hZm hβpath, ← Measure.map_map hZm hβ'path,
      WedgeRes.map_path_eq hβpre hβ'pre hβpath hβ'path]
  have e3 : P {ω | Zsur α Q c S (pathOf β ω) ∈ E}
      = P' {ω' | Zsur α Q c S (pathOf β' ω') ∈ E} := by
    rw [show P {ω | Zsur α Q c S (pathOf β ω) ∈ E}
        = (P.map (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β s ω)) E from
      (Measure.map_apply h1 hE).symm,
      show P' {ω' | Zsur α Q c S (pathOf β' ω') ∈ E}
        = (P'.map (Zsur α Q c S ∘ fun ω (s : ℝ≥0) => β' s ω)) E from
      (Measure.map_apply h2 hE).symm,
      hmap]
  have e4 : P' {ω' | Zsur α Q c S (pathOf β' ω') ∈ E}
      = P' {ω' | trunc S (Vpath α Q c B ω') ∈ E} := by
    symm
    refine measure_congr ?_
    filter_upwards [hβ'b] with ω hω
    simp only [Set.mem_setOf_eq, ← hZβ' ω,
      trunc_Vpath_congr (α := α) (Q := Q) (c := c) (S := S) (b := β') (b' := B) hω]
  rw [e1, e2, e3, e4]

/-- The re-centred wedge path `Rw` is the re-centred `A`-path (from the wedge-process
decomposition of `A`). -/
theorem Rw_eq_recentre {α Q c : ℝ} {A : ℝ → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ}
    (hAB : ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t) (ω : Ω) :
    Rw α Q B B' c ω = fun t => A (sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} + t) ω + c := by
  have hset : sInf {s : ℝ | 0 ≤ s ∧ WedgeTrans.wA α Q B B' s ω ≤ -c}
      = sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} := by
    congr 1
    ext s
    exact and_congr_right fun _ =>
      (by rw [show WedgeTrans.wA α Q B B' s ω = A s ω from (hAB ω s).symm])
  funext t
  have h2 : WedgeTrans.wA α Q B B' (sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} + t) ω
      = A (sInf {s : ℝ | 0 ≤ s ∧ A s ω ≤ -c} + t) ω := (hAB ω _).symm
  simp only [Rw, hset, h2]

end ZoomRadial
end QuantumZipper
