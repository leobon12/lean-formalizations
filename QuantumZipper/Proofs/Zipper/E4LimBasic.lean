import QuantumZipper.Proofs.Zipper.E4GridDet
import QuantumZipper.Proofs.Loewner.CaraR1
import QuantumZipper.Proofs.Zipper.RegContRandom

/-!
# E4-LIM, basic inputs L1 (deterministic limits) and L2 (left-side field continuity)

`handoff/E4.md`, items L1 and L2.

* **L1** (deterministic, for a continuous driver `V` with `V 0 = 0` and a point `x < 0`):
  `le_dyUp`, `dyUp_lt`, `tendsto_dyUp` (the dyadic upper approximation `dyUp n s ↓ s`);
  `eventually_dyUp_lt_live` (if `σ < T₀` is a live time, so are the `dyUp n σ` for large `n`);
  `tendsto_realRevMap_hit_neg` (the flow from `x < 0` tends to `0` at the hitting time; the
  negative-side form of `CaraR.tendsto_realRevMap_hitTime`, via `CaraR.realHitTime_neg`);
  `sigEps_lt_hit`, `isLive_sigEps` (for `ε > 0` the entrance time is strictly before the hitting
  time, hence live); `tendsto_sigEps_hit` (`σ_ε → τ_x` as `ε ↓ 0` when `τ_x ≤ T₀`) and
  `eventually_sigEps_eq_cap` (`σ_ε = T₀` for small `ε` when `T₀ < τ_x`).
* **L2**: `ae_continuousOn_coordsFull_Yf`: almost surely every `coordsFull` coordinate of the
  zipped field `Y_s` is continuous in `s ∈ [0, T]` (from REG-CONT,
  `RegCont.ae_continuousOn_unzippedField`, since `Y_s = unzippedField √κ 𝒵 (T − s)`).

The arguments are own elementary ones (compactness of `[0, s₀]` and the R1 hitting limit);
Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68) uses such limits implicitly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open E1 RealLine

/-! ## L1 (a): the dyadic upper approximation -/

theorem le_dyUp (n : ℕ) (s : ℝ) : s ≤ dyUp n s := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyUp
  rw [le_div_iff₀ h2, mul_comm]
  exact Int.le_ceil _

theorem dyUp_lt (n : ℕ) (s : ℝ) : dyUp n s < s + 1 / (2 : ℝ) ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  unfold dyUp
  rw [div_lt_iff₀ h2, add_mul, one_div, inv_mul_cancel₀ h2.ne', mul_comm]
  exact Int.ceil_lt_add_one _

theorem tendsto_dyUp (s : ℝ) : Tendsto (fun n => dyUp n s) atTop (𝓝 s) := by
  have h : Tendsto (fun n : ℕ => s + 1 / (2 : ℝ) ^ n) atTop (𝓝 (s + 0)) := by
    refine tendsto_const_nhds.add ?_
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (le_dyUp · s)
    fun n => (dyUp_lt n s).le

/-! ## L1 (b): liveness of the grid times -/

theorem eventually_dyUp_lt_live {V : ℝ → ℝ} {s T₀ x : ℝ} (hl : IsLive V s x) (hs : s < T₀) :
    ∀ᶠ n in atTop, dyUp n s < T₀ ∧ IsLive V (dyUp n s) x :=
  ((tendsto_dyUp s).eventually_lt_const hs).and
    (((ENNReal.continuous_ofReal.tendsto s).comp (tendsto_dyUp s)).eventually_lt_const hl)

/-! ## L1 (c): the entrance time as `ε ↓ 0` -/

variable {V : ℝ → ℝ} {x : ℝ}

/-- Negative side of R1: the flow from `x < V 0` tends to `0` at the hitting time. -/
theorem tendsto_realRevMap_hit_neg (hV : Continuous V) (hx : x < V 0) {τ : ℝ}
    (hτ : realHitTime V x = ENNReal.ofReal τ) :
    Tendsto (fun s => realRevMap V s x) (𝓝[<] τ) (𝓝 0) := by
  have hτ' : realHitTime (-V) (-x) = ENNReal.ofReal τ := by
    rw [CaraR.realHitTime_neg (W := V)]; exact hτ
  have h := (CaraR.tendsto_realRevMap_hitTime hV.neg (x := -x)
    (by simp only [Pi.neg_apply]; linarith) hτ').neg
  rw [neg_zero] at h
  have hτpos : 0 < τ := by
    have := realHitTime_pos hV hx.ne
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  refine h.congr' (eventually_of_mem (Ioo_mem_nhdsLT hτpos) fun s hs => ?_)
  have hsol : ∃ u, IsRealRevSol V (-(-x)) s u := by
    rw [neg_neg]
    exact exists_isRealRevSol_of_lt_realHitTime
      (by rw [hτ]; exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs.2)
  rw [CaraR.realRevMap_neg hV hs.1.le hsol, neg_neg, neg_neg]

theorem sigEps_le_cap {T ε : ℝ} (hT : 0 ≤ T) : sigEps V T ε x ≤ T := by
  refine csInf_le ⟨0, fun y hy => ?_⟩ (Or.inr rfl)
  rcases hy with h | h
  · exact h.1
  · rw [mem_singleton_iff.1 h]; exact hT

/-- For `ε > 0` the entrance time is strictly before the hitting time. -/
theorem sigEps_lt_hit (hV : Continuous V) (hx : x < V 0) {τ T₀ ε : ℝ}
    (hτ : realHitTime V x = ENNReal.ofReal τ) (hT₀ : 0 ≤ T₀) (hε : 0 < ε) :
    sigEps V T₀ ε x < τ := by
  have hτpos : 0 < τ := by
    have := realHitTime_pos hV hx.ne
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  have h1 := (tendsto_realRevMap_hit_neg hV hx hτ).eventually (Metric.closedBall_mem_nhds 0 hε)
  obtain ⟨s, hs, hsI⟩ := (h1.and (Ioo_mem_nhdsLT hτpos)).exists
  rw [Real.dist_eq, sub_zero] at hs
  exact (sigEps_le_of_mem hT₀ hsI.1.le hs).trans_lt hsI.2

/-- Lower bound: before a live time `s₀ ≤ T₀`, the flow stays away from `0`. -/
theorem exists_le_sigEps (hV : Continuous V) {s₀ T₀ : ℝ} (hs₀ : 0 ≤ s₀) (hl : IsLive V s₀ x)
    (hs₀T : s₀ ≤ T₀) : ∃ c > 0, ∀ ε < c, s₀ ≤ sigEps V T₀ ε x := by
  obtain ⟨u, hu⟩ := exists_isRealRevSol_of_lt_realHitTime hl
  obtain ⟨c, hc, hcu⟩ := exists_pos_le_abs_isRealRevSol hu hs₀
  refine ⟨c, hc, fun ε hε => le_csInf ⟨T₀, Or.inr rfl⟩ fun y hy => ?_⟩
  rcases hy with ⟨hy0, hy⟩ | hy
  · by_contra hys
    push Not at hys
    have hly : IsLive V y x :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hys.le) hl
    have := hy.resolve_right fun h => h hly
    rw [realRevMap_eq hV hu hy0 hys.le] at this
    linarith [hcu y ⟨hy0, hys.le⟩]
  · rw [mem_singleton_iff.1 hy]; exact hs₀T

/-- For `ε > 0` and `x < V 0`, the entrance time `σ_ε` (cap `T₀ ≥ 0`) is a live time. -/
theorem isLive_sigEps (hV : Continuous V) (hx : x < V 0) {T₀ ε : ℝ} (hT₀ : 0 ≤ T₀)
    (hε : 0 < ε) : IsLive V (sigEps V T₀ ε x) x := by
  unfold IsLive
  rcases le_or_gt (realHitTime V x) (ENNReal.ofReal T₀) with h | h
  · obtain ⟨τ, hτ⟩ : ∃ τ, realHitTime V x = ENNReal.ofReal τ :=
      ⟨(realHitTime V x).toReal, (ENNReal.ofReal_toReal (ne_top_of_le_ne_top
        ENNReal.ofReal_ne_top h)).symm⟩
    have hτpos : 0 < τ := by
      have := realHitTime_pos hV hx.ne
      rw [hτ] at this
      exact ENNReal.ofReal_pos.1 this
    rw [hτ]
    exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 (sigEps_lt_hit hV hx hτ hT₀ hε)
  · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (sigEps_le_cap hT₀)) h

/-- **L1 (c), hit before the cap.** If `τ_x ≤ T₀` then `σ_ε → τ_x` as `ε ↓ 0`. -/
theorem tendsto_sigEps_hit (hV : Continuous V) (hx : x < V 0) {τ T₀ : ℝ}
    (hτ : realHitTime V x = ENNReal.ofReal τ) (hτT : τ ≤ T₀) :
    Tendsto (fun ε => sigEps V T₀ ε x) (𝓝[>] 0) (𝓝 τ) := by
  have hτpos : 0 < τ := by
    have := realHitTime_pos hV hx.ne
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  have hT₀ : 0 ≤ T₀ := hτpos.le.trans hτT
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set s₀ := max ((a + τ) / 2) 0
    have hs₀τ : s₀ < τ := max_lt (by linarith) hτpos
    have hl : IsLive V s₀ x := by
      unfold IsLive; rw [hτ]; exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs₀τ
    obtain ⟨c, hc, hcs⟩ := exists_le_sigEps hV (le_max_right _ _) hl (hs₀τ.le.trans hτT)
    filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
    exact lt_of_lt_of_le (lt_of_lt_of_le (by linarith) (le_max_left _ _)) (hcs ε hε.2)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (sigEps_lt_hit hV hx hτ hT₀ hε).trans ha

/-- **L1 (c), no hit before the cap.** If `T₀ < τ_x` then `σ_ε = T₀` for small `ε`. -/
theorem eventually_sigEps_eq_cap (hV : Continuous V) {T₀ : ℝ} (hT₀ : 0 ≤ T₀)
    (h : ENNReal.ofReal T₀ < realHitTime V x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sigEps V T₀ ε x = T₀ := by
  obtain ⟨c, hc, hcs⟩ := exists_le_sigEps hV hT₀ h le_rfl
  filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
  exact le_antisymm (sigEps_le_cap hT₀) (hcs ε hε.2)

/-! ## L2: continuity of the left-side field coordinates -/

section L2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

open B2 CoordsFull in
/-- **L2.** Almost surely all `coordsFull` coordinates of `Y_s` are continuous on `[0, T]`. -/
theorem ae_continuousOn_coordsFull_Yf (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∀ i, ContinuousOn (fun s => coordsFull (Yf κ T s B X ω) i) (Icc 0 T) := by
  rw [ae_all_iff]
  intro i
  have hr : 0 < (fullIndex i).2 := by
    unfold fullIndex; dsimp only; positivity
  filter_upwards [RegCont.ae_continuousOn_unzippedField κ (Real.sqrt κ) hB hX hind hT
    (fullIndex i).1 hr] with ω h
  have hm : MapsTo (fun s : ℝ => T - s) (Icc 0 T) (Icc 0 T) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact h.comp (continuousOn_const.sub continuousOn_id) hm

end L2

end E4Grid
end QuantumZipper
