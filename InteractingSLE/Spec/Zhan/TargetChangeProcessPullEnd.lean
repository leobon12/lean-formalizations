/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullTrace
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# The pulled-back trace at the separation time

Packet PROVE-SEC7-C10 (step R6 of `planning/handoffs/PROVE-SEC7-C8.md`, endpoint cases; Specification §7.3,
p. 379; supplement Lemma LP9, p. 486). The trace `η = ψ⁻¹ ∘ η̃ ∘ C` generates the original driver before the
separation time `T` (`TargetChangeProcessPullTrace`). This file closes it at `T`:

* `T < ∞`, `T̃ = ∞`: the transformed trace is transient, so `η(t) → ψ⁻¹(∞) = x_k` ("its inverse is a bounded
  continuous completed trace ending at `x_j`", p. 486) — `PullData.isGeneratingTrace_of_top`;
* `T < ∞`, `T̃ < ∞`: with a bound on the original hulls before `T` (a bounded driver), `η̃(T̃) ≠ −1` and
  `η(t) → ψ⁻¹(η̃(T̃))` ("The transformed prefix, including its terminal point, is compact in the sphere and does not
  contain the pole `−1`", p. 379) — `PullData.isGeneratingTrace_of_lt_top`;
* `T = ∞`: a bounded original trace would give bounded hulls of capacity `2t → ∞`; hence `T̃ < ∞`, `η̃(T̃) = −1` and
  `η(t) → ∞` ("If `q = −1`, the inverse image tends to the original target infinity", p. 379) —
  `PullData.isGeneratingTrace_top`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### A generating trace from its pieces -/

/-- **Assembling a generating trace on `[0, T]`** from a function `f` that is continuous and generates the hulls
before `T`, and the value `e` at `T` (its left limit when `T < ∞`). -/
theorem isGeneratingTrace_piecewise {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {f : ℝ≥0 → ℂ} {e : ℂ}
    (h0 : 0 < T → f 0 = 0) (he0 : T = 0 → e = 0) (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ContinuousAt f t)
    (hfill : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) t) (f '' Icc 0 t))
    (hlim : ∀ S : ℝ≥0, (S : ℝ≥0∞) = T → Tendsto f (𝓝[<] S) (𝓝 e)) :
    IsGeneratingTrace w T (fun t => if (t : ℝ≥0∞) < T then f t else e) := by
  set g : ℝ≥0 → ℂ := fun t => if (t : ℝ≥0∞) < T then f t else e with hg
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hgf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → g t = f t := fun t ht => by simp only [hg, ht, ↓reduceIte]
  refine ⟨?_, fun t ht => ?_, fun t ht => ?_⟩
  · rcases eq_or_ne T 0 with hT | hT
    · simp only [hg, hT, lt_self_iff_false, ↓reduceIte, ENNReal.coe_zero]
      exact he0 hT
    · rw [hgf 0 (by simpa using pos_iff_ne_zero.2 hT)]
      exact h0 (pos_iff_ne_zero.2 hT)
  · rcases (show (t : ℝ≥0∞) ≤ T from ht).lt_or_eq with hlt | heq
    · have hca : ContinuousAt g t :=
        ((hc t hlt).congr (Filter.eventuallyEq_of_mem (hopen.mem_nhds hlt) fun s hs => (hgf s hs).symm))
      exact hca.continuousWithinAt
    · have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} = Iic t := by
        ext s; simp only [mem_ofPred_eq, mem_Iic, ← heq, ENNReal.coe_le_coe]
      rw [hset, ← continuousWithinAt_Iio_iff_Iic]
      have hgt : g t = e := by simp only [hg, heq, lt_self_iff_false, ↓reduceIte]
      rw [ContinuousWithinAt, hgt]
      refine (hlim t heq).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
      exact (hgf s (by rw [← heq]; exact_mod_cast hs)).symm
  · have him : g '' Icc 0 t = f '' Icc 0 t :=
      image_congr fun s hs => hgf s ((ENNReal.coe_le_coe.2 hs.2).trans_lt ht)
    rw [him]
    exact hfill t ht

/-! ### The clock near the separation time -/

section Clock

variable {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {xk : ℝ}

/-- The clock is monotone before `T`. -/
theorem PullData.clk_mono (hd : PullData w vk xk T) {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < T) :
    clk (rate xk w vk) s ≤ clk (rate xk w vk) t :=
  ((hd.isRate ht).clk_le_clk ⟨s.coe_nonneg, by exact_mod_cast hst⟩ ⟨t.coe_nonneg, le_rfl⟩).2
    (by exact_mod_cast hst)

/-- A filter on original times that eventually lies before `T` and eventually passes every time before `T`. -/
def IsLeftOf (F : Filter ℝ≥0) (T : ℝ≥0∞) : Prop :=
  (∀ᶠ t : ℝ≥0 in F, (t : ℝ≥0∞) < T) ∧ ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < T → ∀ᶠ t : ℝ≥0 in F, t₀ ≤ t

theorem isLeftOf_nhdsLT (S : ℝ≥0) : IsLeftOf (𝓝[<] S) S := by
  refine ⟨?_, fun t₀ ht₀ => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t < S)
    exact ENNReal.coe_lt_coe.2 ht
  · filter_upwards [Ioo_mem_nhdsLT (ENNReal.coe_lt_coe.1 ht₀)] with t ht using ht.1.le

theorem isLeftOf_atTop : IsLeftOf (atTop : Filter ℝ≥0) ⊤ :=
  ⟨Eventually.of_forall fun _ : ℝ≥0 => ENNReal.coe_lt_top, fun t₀ _ => eventually_ge_atTop t₀⟩

/-- At a finite new horizon `T̃`, the new time `C(t)` tends to `T̃` from below as `t → T`. -/
theorem PullData.tendsto_clk_of_ne_top (hd : PullData w vk xk T) {F : Filter ℝ≥0} (hF : IsLeftOf F T)
    (hT : newHorizon xk w vk T ≠ ⊤) :
    Tendsto (fun t : ℝ≥0 => (clk (rate xk w vk) t).toNNReal) F
      (𝓝[≤] (newHorizon xk w vk T).toNNReal) := by
  set ρs := (newHorizon xk w vk T).toNNReal with hρs
  have hρs' : (ρs : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hT
  have hle : ∀ᶠ t : ℝ≥0 in F, (clk (rate xk w vk) t).toNNReal ≤ ρs := by
    filter_upwards [hF.1] with t ht
    have := (hd.clk_lt ht).le
    rw [← hρs'] at this
    exact_mod_cast this
  refine tendsto_nhdsWithin_iff.2 ⟨?_, hle⟩
  refine tendsto_order.2 ⟨fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨t₀, ht₀T, hρt₀⟩ := exists_lt_clk_of_lt_newHorizon (xk := xk) (w := w) (vk := vk) (T := T)
      (u := ρ) (by rw [← hρs']; exact_mod_cast hρ)
    filter_upwards [hF.1, hF.2 t₀ ht₀T] with t ht ht₀t
    have hm := hd.clk_mono ht₀t ht
    have hc0 : 0 ≤ clk (rate xk w vk) t :=
      (hd.isRate ht).clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]
    linarith
  · filter_upwards [hle] with t ht using ht.trans_lt hρ

/-- At an infinite new horizon, `C(t) → ∞` as `t → T`. -/
theorem PullData.tendsto_clk_of_eq_top (hd : PullData w vk xk T) {F : Filter ℝ≥0} (hF : IsLeftOf F T)
    (hT : newHorizon xk w vk T = ⊤) :
    Tendsto (fun t : ℝ≥0 => (clk (rate xk w vk) t).toNNReal) F atTop := by
  refine tendsto_atTop.2 fun ρ => ?_
  obtain ⟨t₀, ht₀T, hρt₀⟩ := exists_lt_clk_of_lt_newHorizon (xk := xk) (w := w) (vk := vk) (T := T)
    (u := ρ) (by rw [hT]; exact ENNReal.coe_lt_top)
  filter_upwards [hF.1, hF.2 t₀ ht₀T] with t ht ht₀t
  have hm := hd.clk_mono ht₀t ht
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith [ρ.coe_nonneg])]
  linarith

end Clock

/-! ### The endpoint cases -/

section Endpoint

variable {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {xk : ℝ} {η' : ℝ≥0 → ℂ}

theorem newHorizon_zero (xk : ℝ) (w vk : ℝ≥0 → ℝ) : newHorizon xk w vk 0 = 0 := by
  simp [newHorizon]

/-- A hull bound with a nonnegative radius. -/
theorem PullData.exists_closedBall (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ∃ R : ℝ, 0 ≤ R ∧ fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ closedBall 0 R := by
  obtain ⟨R₁, hR₁⟩ := (hd.isHPHull_fwdHull ht).2.1.subset_closedBall 0
  exact ⟨max R₁ 0, le_max_right _ _, hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- `η̃` avoids `−1` before the new horizon. -/
theorem PullData.ne_neg_one_of_lt (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) < newHorizon xk w vk T) : η' ρ ≠ -1 := by
  obtain ⟨t₀, ht₀, hρt₀⟩ := exists_lt_clk_of_lt_newHorizon hρ
  obtain ⟨R, hR0, hR⟩ := hd.exists_closedBall ht₀
  have h := hd.norm_add_one_ge hη ht₀ hR (ρ := ρ) hρt₀.le
  intro he
  rw [he, neg_add_cancel, norm_zero] at h
  have : 0 < min (xk / (xk + R)) 1 := lt_min (div_pos hd.pos (by linarith [hd.pos])) one_pos
  linarith

/-- A continuous path avoiding `−1` on a compact interval stays at a positive distance from it. -/
theorem exists_pos_le_norm_add_one {f : ℝ≥0 → ℂ} {a : ℝ≥0} (hf : ContinuousOn f (Icc 0 a))
    (hne : ∀ ρ ∈ Icc 0 a, f ρ ≠ -1) : ∃ c > 0, ∀ ρ ∈ Icc 0 a, c ≤ ‖f ρ + 1‖ := by
  have hc : ContinuousOn (fun ρ => ‖f ρ + 1‖) (Icc 0 a) := (hf.add continuousOn_const).norm
  obtain ⟨ρ₀, hρ₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hc
  refine ⟨‖f ρ₀ + 1‖, norm_pos_iff.2 fun h => hne ρ₀ hρ₀ (by linear_combination h), fun ρ hρ => hmin hρ⟩

/-- **`T < ∞`, `T̃ = ∞`**: the transient transformed trace pulls back to a trace ending at `x_k`. -/
theorem PullData.isGeneratingTrace_of_top (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') (hTn : newHorizon xk w vk T = ⊤)
    (htr : Tendsto (fun ρ => ‖η' ρ‖) atTop atTop) :
    IsGeneratingTrace w T (fun t => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t else (xk : ℂ)) := by
  have hT0 : T ≠ 0 := by rintro rfl; rw [newHorizon_zero] at hTn; exact ENNReal.zero_ne_top hTn
  refine isGeneratingTrace_piecewise (fun _ => pullTrace_zero hη) (fun h => absurd h hT0)
    (fun t ht => hd.continuousAt_pullTrace hη ht) (fun t ht => hd.isFilling_pullTrace hη ht) fun S hS => ?_
  have hc := hd.tendsto_clk_of_eq_top (hS ▸ isLeftOf_nhdsLT S) hTn
  have hη' : Tendsto η' atTop (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.1 htr
  exact tendsto_targetChangeInv_cobounded.comp (hη'.comp hc)

/-- **`T < ∞`, `T̃ < ∞`**: with bounded original hulls before `T`, the transformed trace stays away from `−1`
on `[0, T̃]`, and the pull-back ends at `ψ⁻¹(η̃(T̃))`. -/
theorem PullData.isGeneratingTrace_of_lt_top (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') (hTn : newHorizon xk w vk T ≠ ⊤)
    {R : ℝ} (hK : ∀ S : ℝ≥0, (S : ℝ≥0∞) < T → fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ closedBall 0 R) :
    IsGeneratingTrace w T (fun t => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t
      else Sec7.targetChangeInv xk (η' (newHorizon xk w vk T).toNNReal)) := by
  set ρs := (newHorizon xk w vk T).toNNReal with hρs
  have hρs' : (ρs : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hTn
  refine isGeneratingTrace_piecewise (fun _ => pullTrace_zero hη) (fun h => ?_)
    (fun t ht => hd.continuousAt_pullTrace hη ht) (fun t ht => hd.isFilling_pullTrace hη ht) fun S hS => ?_
  · have : ρs = 0 := by simp [hρs, h, newHorizon_zero]
    rw [this, hη.1, Sec7.targetChangeInv_zero]
  rcases eq_or_ne S 0 with rfl | hS0
  · have he : Iio (0 : ℝ≥0) = ∅ := by ext ρ; simp
    rw [he, nhdsWithin_empty]
    exact tendsto_bot
  have hT0 : 0 < T := by rw [← hS]; exact_mod_cast pos_iff_ne_zero.2 hS0
  -- `η̃(T̃) ≠ −1`
  set R' := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hK' : ∀ S : ℝ≥0, (S : ℝ≥0∞) < T → fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ closedBall 0 R' :=
    fun S hS => (hK S hS).trans (closedBall_subset_closedBall (le_max_left _ _))
  have hge := ge_of_forall_lt_mem_H hη hd.continuousOn_newDrv (hd.newDrv_zero hT0) hρs'.le
    (c := xk / (xk + R')) fun ρ' hρ' hH => by
      obtain ⟨t₀, ht₀, hρt₀⟩ := exists_lt_clk_of_lt_newHorizon (xk := xk) (w := w) (vk := vk)
        (u := ρ') (by rw [← hρs']; exact_mod_cast hρ')
      obtain ⟨z, hz, he⟩ := hd.mem_image_of_mem_H hη ht₀ hρt₀.le hH
      rw [← he]
      exact norm_targetChange_add_one_ge hd.pos ((QuantumZipper.fwdHull_mono).2 _ hz) (hK' t₀ ht₀ hz)
  have hne : η' ρs ≠ -1 := by
    intro he
    rw [he, neg_add_cancel, norm_zero] at hge
    have : 0 < min (xk / (xk + R')) 1 := lt_min (div_pos hd.pos (by linarith [hd.pos])) one_pos
    linarith
  -- the limit
  have hc := hd.tendsto_clk_of_ne_top (hS ▸ isLeftOf_nhdsLT S) hTn
  have hset : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ newHorizon xk w vk T} = Iic ρs := by
    ext u; simp only [mem_ofPred_eq, mem_Iic, ← hρs', ENNReal.coe_le_coe]
  have hηc : Tendsto η' (𝓝[≤] ρs) (𝓝 (η' ρs)) := by
    have := hη.2.1 ρs hρs'.le
    rw [hset] at this
    exact this
  exact (continuousAt_targetChangeInv hne).tendsto.comp (hηc.comp hc)

/-- **A bounded trace on `[0, ∞)` is impossible**: it would give hulls of capacity `2t` inside a fixed disc. -/
theorem PullData.not_bounded_top (hd : PullData w vk xk ⊤)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η') {B : ℝ}
    (hB : ∀ t, ‖pullTrace xk w vk η' t‖ ≤ B) : False := by
  set t : ℝ≥0 := (B ^ 2 / 2 + 1).toNNReal with htdef
  have ht : ((t : ℝ≥0) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have ht' : (t : ℝ) = B ^ 2 / 2 + 1 := Real.coe_toNNReal _ (by positivity)
  set A := pullTrace xk w vk η' '' Icc 0 t with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn fun s _ =>
    (hd.continuousAt_pullTrace hη ENNReal.coe_lt_top).continuousWithinAt
  have hfill := hd.isFilling_pullTrace hη ht
  have hKeq := (fillH_eq_iff_isFilling_of_isClosed hAc.isBounded hAc.isClosed
    ((QuantumZipper.fwdHull_mono).2 _)).1 hfill
  have hAB : closure A ⊆ closedBall 0 B := by
    rw [hAc.isClosed.closure_eq]
    rintro _ ⟨s, -, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact hB s
  have hKB : fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ closedBall 0 B := hKeq ▸ fillH_subset_closedBall_zero hAB
  -- the capacity
  obtain ⟨W', -, hW'c, -, hW'0, -, hW'eq, -⟩ := hd.local_hull (S := t + 1) ENNReal.coe_lt_top
  have hK' : fwdHull (fun s : ℝ => w s.toNNReal) t = fwdHull W' t :=
    fwdHull_eq_of_eqOn t.coe_nonneg (by push_cast; linarith) fun r hr => (hW'eq r hr).symm
  have hcap := hcap_fwdHull hW'c hW'0 t.coe_nonneg
  have hKB' : fwdHull W' t ⊆ closedBall ((0 : ℝ) : ℂ) B := by rw [← hK']; simpa using hKB
  have hle := HPHull.hcap_le_rad_sq ⟨fwdHull W' t, InteractingSLE.isHPHull_fwdHull hW'c t.coe_nonneg⟩
    (x := 0) (r := B) hKB'
  rw [hcap, ht'] at hle
  nlinarith

/-- **`T = ∞`**: the transformed trace reaches `−1` at a finite new horizon, and the pulled-back trace is a
transient generating trace on `[0, ∞)` ("If `q = −1`, the inverse image tends to the original target infinity").
An infinite new horizon with a transient transformed trace is impossible (a bounded original trace). -/
theorem PullData.isGeneratingTrace_top (hd : PullData w vk xk ⊤)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η')
    (htr : newHorizon xk w vk ⊤ = ⊤ → Tendsto (fun ρ => ‖η' ρ‖) atTop atTop) :
    IsGeneratingTrace w ⊤ (pullTrace xk w vk η') ∧
      Tendsto (fun t => ‖pullTrace xk w vk η' t‖) atTop atTop := by
  have hxk := hd.pos
  have hgen : IsGeneratingTrace w ⊤ (pullTrace xk w vk η') :=
    ⟨pullTrace_zero hη, fun t _ => (hd.continuousAt_pullTrace hη ENNReal.coe_lt_top).continuousWithinAt,
      fun t _ => hd.isFilling_pullTrace hη ENNReal.coe_lt_top⟩
  refine ⟨hgen, ?_⟩
  -- a uniform distance from `−1` along the whole new time range gives a bounded trace
  have hbdd : ∀ c > 0, (∀ t : ℝ≥0, c ≤ ‖η' (clk (rate xk w vk) t).toNNReal + 1‖) → False := fun c hc h =>
    hd.not_bounded_top hη (B := xk * (1 + 1 / c)) fun t => norm_targetChangeInv_le hxk hc (h t)
  by_cases hTn : newHorizon xk w vk ⊤ = ⊤
  · -- impossible
    exfalso
    have htr' := htr hTn
    obtain ⟨ρ₀, hρ₀⟩ := (tendsto_atTop.1 htr') 2 |>.exists_forall_of_atTop
    have hcont : ContinuousOn η' (Icc 0 ρ₀) := hη.2.1.mono fun ρ _ =>
      show (ρ : ℝ≥0∞) ≤ newHorizon xk w vk ⊤ by rw [hTn]; exact le_top
    obtain ⟨c, hc, hcle⟩ := exists_pos_le_norm_add_one hcont fun ρ _ =>
      hd.ne_neg_one_of_lt hη (by rw [hTn]; exact ENNReal.coe_lt_top)
    refine hbdd (min c 1) (lt_min hc one_pos) fun t => ?_
    set ρ := (clk (rate xk w vk) t).toNNReal
    rcases le_total ρ ρ₀ with hρ | hρ
    · exact (min_le_left _ _).trans (hcle ρ ⟨zero_le, hρ⟩)
    · have h2 := hρ₀ ρ hρ
      have : (1 : ℝ) ≤ ‖η' ρ + 1‖ := by
        have := norm_sub_norm_le (η' ρ) (-1)
        rw [norm_neg, norm_one, sub_neg_eq_add] at this
        linarith
      exact (min_le_right _ _).trans this
  -- a finite new horizon
  set ρs := (newHorizon xk w vk ⊤).toNNReal with hρs
  have hρs' : (ρs : ℝ≥0∞) = newHorizon xk w vk ⊤ := ENNReal.coe_toNNReal hTn
  have hcont : ContinuousOn η' (Icc 0 ρs) := hη.2.1.mono fun ρ hρ => by rw [← hρs']; exact_mod_cast hρ.2
  have hle : ∀ t : ℝ≥0, (clk (rate xk w vk) t).toNNReal ≤ ρs := fun t => by
    have := (hd.clk_lt (t := t) ENNReal.coe_lt_top).le
    rw [← hρs'] at this
    exact_mod_cast this
  have hend : η' ρs = -1 := by
    by_contra hne
    obtain ⟨c, hc, hcle⟩ := exists_pos_le_norm_add_one hcont fun ρ hρ => by
      rcases hρ.2.lt_or_eq with hlt | heq
      · exact hd.ne_neg_one_of_lt hη (by rw [← hρs']; exact_mod_cast hlt)
      · rw [heq]; exact hne
    exact hbdd c hc fun t => hcle _ ⟨zero_le, hle t⟩
  -- `η̃(C(t)) → −1` with `η̃(C(t)) ≠ −1`
  have hc := hd.tendsto_clk_of_ne_top isLeftOf_atTop hTn
  have hset : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ newHorizon xk w vk ⊤} = Iic ρs := by
    ext u; simp only [mem_ofPred_eq, mem_Iic, ← hρs', ENNReal.coe_le_coe]
  have hηc : Tendsto η' (𝓝[≤] ρs) (𝓝 (η' ρs)) := by
    have := hη.2.1 ρs hρs'.le
    rw [hset] at this
    exact this
  rw [hend] at hηc
  have h1 : Tendsto (fun t : ℝ≥0 => η' (clk (rate xk w vk) t).toNNReal) atTop (𝓝[≠] (-1 : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hηc.comp hc, Eventually.of_forall fun t =>
      hd.ne_neg_one hη (t := t) ENNReal.coe_lt_top⟩
  exact tendsto_norm_cobounded_atTop.comp ((Sec7.tendsto_targetChangeInv_nhdsNE_neg_one hxk.ne').comp h1)

/-- **Bounded driver, bounded hulls** (Aux. lemma 3's use, p. 379: "a bounded driver on a finite interval generates
a bounded Loewner hull"; [Law05] Lemma 4.12): if `|w| ≤ M` before a finite `T`, the hulls before `T` lie in one
disc. -/
theorem PullData.exists_hull_bound (hd : PullData w vk xk T) (hT : T ≠ ⊤) {M : ℝ}
    (hM : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → |w s| ≤ M) :
    ∃ R : ℝ, ∀ S : ℝ≥0, (S : ℝ≥0∞) < T → fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ closedBall 0 R := by
  refine ⟨M + 3 * Real.sqrt (T.toNNReal : ℝ), fun S hS => ?_⟩
  obtain ⟨S', hSS', hS'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS
  have hSS'' : S < S' := ENNReal.coe_lt_coe.1 hSS'
  obtain ⟨S'', hS'S'', hS''T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS'T
  obtain ⟨W', -, hW'c, -, -, -, hW'eq, -⟩ := hd.local_hull hS''T
  have hS'pos : (0 : ℝ) < S' := by exact_mod_cast lt_of_le_of_lt bot_le hSS''
  have hS'S''r : (S' : ℝ) < S'' := by exact_mod_cast ENNReal.coe_lt_coe.1 hS'S''
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) S' = fwdHull W' S' :=
    fwdHull_eq_of_eqOn S'.coe_nonneg hS'S''r fun r hr => (hW'eq r hr).symm
  have hsub := QuantumZipper.CaraR.fwdHull_subset_closedBall hW'c hS'pos (M := M) fun r hr => by
    rw [hW'eq r ⟨hr.1, hr.2.trans hS'S''r.le⟩]
    exact hM _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hS'T)
  have hS'T' : (S' : ℝ) ≤ (T.toNNReal : ℝ) := by
    have := ENNReal.toNNReal_mono hT hS'T.le
    simpa using NNReal.coe_le_coe.2 this
  refine ((QuantumZipper.fwdHull_mono).1 (show (S : ℝ) ≤ S' by exact_mod_cast hSS''.le)).trans ?_
  rw [hK]
  refine hsub.trans (closedBall_subset_closedBall ?_)
  gcongr

/-- **The pullback** (R6): from a generating trace `η̃` of the new driver on `[0, T̃]`, transient when `T̃ = ∞`,
and a bounded driver before a finite `T`, the original driver has a generating trace on `[0, T]`, transient when
`T = ∞`. -/
theorem PullData.exists_trace (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η')
    (htr : newHorizon xk w vk T = ⊤ → Tendsto (fun ρ => ‖η' ρ‖) atTop atTop)
    (hbdd : T ≠ ⊤ → ∃ M : ℝ, ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → |w s| ≤ M) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w T η ∧ (T = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  rcases eq_or_ne T ⊤ with rfl | hT
  · have h := hd.isGeneratingTrace_top hη htr
    exact ⟨_, h.1, fun _ => h.2⟩
  by_cases hTn : newHorizon xk w vk T = ⊤
  · exact ⟨_, hd.isGeneratingTrace_of_top hη hTn (htr hTn), fun h => absurd h hT⟩
  · obtain ⟨M, hM⟩ := hbdd hT
    obtain ⟨R, hR⟩ := hd.exists_hull_bound hT hM
    exact ⟨_, hd.isGeneratingTrace_of_lt_top hη hTn hR, fun h => absurd h hT⟩

end Endpoint

end Retarget

end Zhan

end InteractingSLE
