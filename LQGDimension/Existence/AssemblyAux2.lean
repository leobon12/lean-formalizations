import LQGDimension.Blueprint.Existence
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Assembly of `GFFCircleAverageExists`, part 2: the index set `T₀` and continuous extension

* `T₀`: pairs `(q, a + b i)` with `q, a, b ∈ ℚ`, `q > 0`.  It is countable (`T₀_countable`)
  and every `x` with `x.1 > 0` lies in its closure (`mem_closure_T₀`).
* `box_mem_nhds`: every `x` with `x.1 > 0` has some `box m` as a neighbourhood.
* If `f` is uniformly continuous on every `T₀ ∩ box m`, then `f` has a limit along `𝓝[T₀] x`
  at every `x` with `x.1 > 0` (`exists_tendsto_of_unifOn`), so `extendFrom T₀ f` is continuous
  on `{x | 0 < x.1}` and is the limit of `f` along any sequence of `T₀` converging to `x`.
-/

noncomputable section

open Filter Topology Set

namespace LQGDimension.ExistAsm

open Blueprint.Existence

/-- Rational radii and rational centres. -/
def T₀ : Set (ℝ × ℂ) :=
  {t | 0 < t.1 ∧ t.1 ∈ range ((↑) : ℚ → ℝ) ∧ t.2.re ∈ range ((↑) : ℚ → ℝ) ∧
    t.2.im ∈ range ((↑) : ℚ → ℝ)}

theorem pos_of_mem_T₀ {t : ℝ × ℂ} (ht : t ∈ T₀) : 0 < t.1 := ht.1

theorem T₀_countable : T₀.Countable := by
  have : T₀ ⊆ range (fun q : ℚ × ℚ × ℚ => ((q.1 : ℝ), (⟨q.2.1, q.2.2⟩ : ℂ))) := by
    rintro ⟨r, z⟩ ⟨-, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    refine ⟨(a, b, c), ?_⟩
    simp only at ha hb hc ⊢
    refine Prod.ext ha ?_
    exact Complex.ext hb hc
  exact (countable_range _).mono this

theorem mem_closure_T₀ {x : ℝ × ℂ} (hx : 0 < x.1) : x ∈ closure T₀ := by
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show max (x.1 - δ / 2) (x.1 / 2) < x.1 from max_lt (by linarith) (by linarith))
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.2.re - δ / 4 < x.2.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.2.im - δ / 4 < x.2.im by linarith)
  have hq0 : x.1 / 2 < q := lt_of_le_of_lt (le_max_right _ _) hq1
  have hqδ : x.1 - δ / 2 < q := lt_of_le_of_lt (le_max_left _ _) hq1
  refine ⟨((q : ℝ), ⟨a, b⟩), ⟨by linarith, ⟨q, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · rw [Complex.dist_eq]
    calc ‖x.2 - ⟨(a : ℝ), (b : ℝ)⟩‖
        ≤ |(x.2 - ⟨(a : ℝ), (b : ℝ)⟩).re| + |(x.2 - ⟨(a : ℝ), (b : ℝ)⟩).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ < δ / 4 + δ / 4 := by
          simp only [Complex.sub_re, Complex.sub_im]
          refine add_lt_add ?_ ?_
          · rw [abs_lt]; constructor <;> linarith
          · rw [abs_lt]; constructor <;> linarith
      _ < δ := by linarith

theorem exists_seq_T₀ {x : ℝ × ℂ} (hx : 0 < x.1) :
    ∃ s : ℕ → ℝ × ℂ, (∀ n, s n ∈ T₀) ∧ Tendsto s atTop (𝓝 x) :=
  mem_closure_iff_seq_limit.1 (mem_closure_T₀ hx)

theorem box_mem_nhds {x : ℝ × ℂ} (hx : 0 < x.1) : ∃ m : ℕ, box m ∈ 𝓝 x := by
  obtain ⟨ε, z⟩ := x
  simp only at hx
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / ε) (max ε ‖z‖))
  refine ⟨m, ?_⟩
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hA : 1 / ε < (m : ℝ) + 1 := by
    have := le_max_left (1 / ε) (max ε ‖z‖); linarith
  have hB : ε < (m : ℝ) + 1 := by
    have := le_max_left ε ‖z‖
    have := le_max_right (1 / ε) (max ε ‖z‖); linarith
  have hC : ‖z‖ < (m : ℝ) + 1 := by
    have := le_max_right ε ‖z‖
    have := le_max_right (1 / ε) (max ε ‖z‖); linarith
  have h1 : 1 / ((m : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hm0]
    rw [div_lt_iff₀ hx] at hA
    linarith
  have hN : Ioo (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) ×ˢ Metric.ball (0 : ℂ) ((m : ℝ) + 1) ∈
      𝓝 (ε, z) :=
    prod_mem_nhds (Ioo_mem_nhds h1 hB) (Metric.isOpen_ball.mem_nhds (by simpa using hC))
  exact Filter.mem_of_superset hN (prod_mono Ioo_subset_Icc_self Metric.ball_subset_closedBall)

section Extension

variable {f : ℝ × ℂ → ℝ}

theorem exists_tendsto_of_unifOn (hf : ∀ m : ℕ, UniformContinuousOn f (T₀ ∩ box m))
    {x : ℝ × ℂ} (hx : 0 < x.1) : ∃ y, Tendsto f (𝓝[T₀] x) (𝓝 y) := by
  obtain ⟨m, hm⟩ := box_mem_nhds hx
  have : (𝓝[T₀] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_T₀ hx)
  have e : 𝓝[T₀ ∩ box m] x = 𝓝[T₀] x :=
    nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hm)
  have hc : Cauchy (𝓝[T₀] x) := cauchy_nhds.mono' inferInstance nhdsWithin_le_nhds
  have hle : 𝓝[T₀] x ≤ 𝓟 (T₀ ∩ box m) := by
    rw [← e]
    exact inf_le_right
  exact cauchy_map_iff_exists_tendsto.1 (hc.map_of_le (hf m) hle)

theorem continuousOn_extendFrom_T₀ (hf : ∀ m : ℕ, UniformContinuousOn f (T₀ ∩ box m)) :
    ContinuousOn (extendFrom T₀ f) {x | 0 < x.1} :=
  continuousOn_extendFrom (fun _ hx => mem_closure_T₀ hx)
    (fun _ hx => exists_tendsto_of_unifOn hf hx)

theorem continuous_extendFrom_T₀_slice (hf : ∀ m : ℕ, UniformContinuousOn f (T₀ ∩ box m))
    {ε : ℝ} (hε : 0 < ε) : Continuous fun z : ℂ => extendFrom T₀ f (ε, z) :=
  (continuousOn_extendFrom_T₀ hf).comp_continuous (continuous_const.prodMk continuous_id)
    fun _ => hε

theorem tendsto_extendFrom_T₀_seq (hf : ∀ m : ℕ, UniformContinuousOn f (T₀ ∩ box m))
    {x : ℝ × ℂ} (hx : 0 < x.1) {s : ℕ → ℝ × ℂ} (hsT : ∀ n, s n ∈ T₀)
    (hs : Tendsto s atTop (𝓝 x)) :
    Tendsto (fun n => f (s n)) atTop (𝓝 (extendFrom T₀ f x)) :=
  (tendsto_extendFrom (exists_tendsto_of_unifOn hf hx)).comp
    (tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall hsT⟩)

end Extension

end LQGDimension.ExistAsm
