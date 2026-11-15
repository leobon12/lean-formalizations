/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullHull
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Restart.ClockTrace
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# Pulling the transformed trace back through `ψ⁻¹`

Packet PROVE-SEC7-C10 (step R6 of `planning/handoffs/PROVE-SEC7-C8.md`; Specification §7.3, p. 379: "The
transformed prefix, including its terminal point, is compact in the sphere and does not contain the pole `−1` of the
inverse map. Its inverse image is a bounded continuous original prefix, with finite capacity"; supplement Lemma LP9,
p. 486). Let `η̃` generate the new driver `W̃` (`newDrv`) up to the new horizon `T̃ = sup_{t<T} C(t)`. Then

  `η(t) = ψ⁻¹(η̃(C(t)))`, `ψ⁻¹(w) = x_k w/(1 + w)`,

generates the original driver before `T` (`pullTrace`):

* `PullData.isFilling_pullTrace`: `K_t = fill(η[0, t])` for `t < T` (hull identity `fwdHull_newDrv_eq` and fillings
  under real Möbius maps, `Sec5.CrossRestart.isFilling_image_realMobius`);
* `PullData.norm_add_one_ge`: `η̃` stays away from the pole `−1` on `[0, C(S)]` when `K_S` is bounded (points of
  `η̃` in `ℍ` lie in `K̃ = ψ(K_S)`, and the interior times are dense, `Restart.IsGeneratingTrace.exists_mem_H`);
* `PullData.continuousOn_pullTrace`: `η` is continuous before `T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H IsForwardSol fwdHull fwdMap)

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The inverse target change -/

section Inv

variable {xk : ℝ}

theorem targetChangeInv_eq_realMobius (xk : ℝ) (w : ℂ) :
    Sec7.targetChangeInv xk w = QuantumZipper.CA.realMobius xk 0 1 1 w := by
  simp [Sec7.targetChangeInv, QuantumZipper.CA.realMobius, add_comm]

theorem targetChangeInv_mem_H_iff (hxk : 0 < xk) (w : ℂ) : Sec7.targetChangeInv xk w ∈ H ↔ w ∈ H := by
  show 0 < (Sec7.targetChangeInv xk w).im ↔ 0 < w.im
  rw [Sec7.im_targetChangeInv]
  by_cases h : 1 + w = 0
  · have : w = -1 := by linear_combination h
    subst this
    simp
  · have hn : 0 < Complex.normSq (1 + w) := Complex.normSq_pos.2 h
    constructor
    · intro hp
      by_contra hw
      have : xk * w.im / Complex.normSq (1 + w) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hxk.le (not_lt.1 hw)) hn.le
      linarith
    · intro hw
      positivity

/-- `ψ(z) + 1 = x_k/(x_k − z)`. -/
theorem targetChange_add_one {z : ℂ} (hz : (xk : ℂ) - z ≠ 0) :
    Sec7.targetChange xk z + 1 = xk / ((xk : ℂ) - z) := by
  simp only [Sec7.targetChange]
  field_simp
  ring

/-- Points of a hull in `closedBall 0 R` are mapped by `ψ` at distance `≥ x_k/(x_k + R)` from `−1`. -/
theorem norm_targetChange_add_one_ge (hxk : 0 < xk) {R : ℝ} {z : ℂ} (hzH : z ∈ H)
    (hzR : z ∈ closedBall (0 : ℂ) R) : xk / (xk + R) ≤ ‖Sec7.targetChange xk z + 1‖ := by
  have hne : (xk : ℂ) - z ≠ 0 := fun he => by
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    have hz' : 0 < z.im := hzH
    linarith
  rw [targetChange_add_one hne, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxk]
  have hzn : ‖z‖ ≤ R := by simpa using hzR
  have h1 : ‖(xk : ℂ) - z‖ ≤ xk + R := by
    calc ‖(xk : ℂ) - z‖ ≤ ‖(xk : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ xk + R := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxk]; linarith
  have h2 : 0 < ‖(xk : ℂ) - z‖ := norm_pos_iff.2 hne
  exact div_le_div_of_nonneg_left hxk.le h2 h1

/-- `ψ⁻¹` is continuous off its pole `−1`. -/
theorem continuousAt_targetChangeInv {w : ℂ} (hw : w ≠ -1) : ContinuousAt (Sec7.targetChangeInv xk) w := by
  have h1 : 1 + w ≠ 0 := fun h => hw (by linear_combination h)
  unfold Sec7.targetChangeInv
  exact (continuousAt_const.mul continuousAt_id).div (continuousAt_const.add continuousAt_id) h1

/-- `‖ψ⁻¹(w)‖ ≤ x_k (1 + 1/c)` when `‖w + 1‖ ≥ c > 0`. -/
theorem norm_targetChangeInv_le (hxk : 0 < xk) {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : c ≤ ‖w + 1‖) :
    ‖Sec7.targetChangeInv xk w‖ ≤ xk * (1 + 1 / c) := by
  have h1 : 1 + w ≠ 0 := by
    intro h; rw [add_comm, h, norm_zero] at hw; linarith
  have e : Sec7.targetChangeInv xk w = xk - xk / (1 + w) := by
    simp only [Sec7.targetChangeInv]; field_simp; ring
  rw [e]
  have hn : 0 < ‖1 + w‖ := norm_pos_iff.2 h1
  have h2 : ‖(xk : ℂ) / (1 + w)‖ ≤ xk / c := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxk, add_comm]
    exact div_le_div_of_nonneg_left hxk.le hc hw
  calc ‖(xk : ℂ) - xk / (1 + w)‖ ≤ ‖(xk : ℂ)‖ + ‖(xk : ℂ) / (1 + w)‖ := norm_sub_le _ _
    _ ≤ xk + xk / c := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxk]; linarith
    _ = xk * (1 + 1 / c) := by ring

/-- `ψ⁻¹(w) → x_k` as `w → ∞`. -/
theorem tendsto_targetChangeInv_cobounded :
    Tendsto (Sec7.targetChangeInv xk) (Bornology.cobounded ℂ) (𝓝 (xk : ℂ)) := by
  have hinv : Tendsto (fun w : ℂ => (1 + w)⁻¹) (Bornology.cobounded ℂ) (𝓝 0) := by
    have h1 : Tendsto (fun w : ℂ => 1 + w) (Bornology.cobounded ℂ) (Bornology.cobounded ℂ) :=
      tendsto_const_add_cobounded 1
    exact tendsto_inv₀_cobounded.comp h1
  have h2 : Tendsto (fun w : ℂ => (xk : ℂ) - xk * (1 + w)⁻¹) (Bornology.cobounded ℂ) (𝓝 (xk - xk * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  rw [mul_zero, sub_zero] at h2
  refine h2.congr' ?_
  have hfar : ∀ᶠ w : ℂ in Bornology.cobounded ℂ, 1 + w ≠ 0 := by
    have : ({(-1 : ℂ)} : Set ℂ)ᶜ ∈ Bornology.cobounded ℂ :=
      Bornology.isCobounded_def.1 (Bornology.isBounded_singleton (x := (-1 : ℂ))).compl
    filter_upwards [this] with w hw
    intro h
    exact hw (by simp only [mem_singleton_iff]; linear_combination h)
  filter_upwards [hfar] with w hw
  simp only [Sec7.targetChangeInv]
  field_simp
  ring

end Inv

/-! ### Staying away from the pole -/

/-- **A trace stays away from `−1` where its points in `ℍ` do** (dense interior times): if every point `η(ρ')`,
`ρ' < ρ`, of the trace in `ℍ` is at distance `≥ c` from `−1`, then so is `η(ρ)`, up to `min c 1`. -/
theorem ge_of_forall_lt_mem_H {wn : ℝ≥0 → ℝ} {T' : ℝ≥0∞} {η' : ℝ≥0 → ℂ} (hη : IsGeneratingTrace wn T' η')
    (hwn : ContinuousOn wn {u | (u : ℝ≥0∞) < T'}) (hwn0 : wn 0 = 0) {c : ℝ} {ρ : ℝ≥0}
    (hρ : (ρ : ℝ≥0∞) ≤ T') (h : ∀ ρ' < ρ, η' ρ' ∈ H → c ≤ ‖η' ρ' + 1‖) : min c 1 ≤ ‖η' ρ + 1‖ := by
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · rw [hη.1, zero_add, norm_one]; exact min_le_right _ _
  have hρpos : 0 < ρ := pos_iff_ne_zero.2 hρ0
  by_contra hlt
  push Not at hlt
  have hlt' : ‖η' ρ + 1‖ < c := hlt.trans_le (min_le_left _ _)
  have hcont : Tendsto η' (𝓝[<] ρ) (𝓝 (η' ρ)) :=
    ((hη.2.1 ρ hρ).mono fun u (hu : u < ρ) => (ENNReal.coe_le_coe.2 hu.le).trans hρ).tendsto
  have hopen : ∀ᶠ ρ' in 𝓝[<] ρ, ‖η' ρ' + 1‖ < c := by
    have h1 : Tendsto (fun ρ' => ‖η' ρ' + 1‖) (𝓝[<] ρ) (𝓝 ‖η' ρ + 1‖) :=
      (hcont.add tendsto_const_nhds).norm
    exact h1.eventually (gt_mem_nhds hlt')
  obtain ⟨a, ha, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hρpos).1 hopen
  obtain ⟨ρ', hρ', hH⟩ := Restart.IsGeneratingTrace.exists_mem_H hη hwn hwn0 ha hρ
  exact absurd (h ρ' hρ'.2 hH) (not_le.2 (hsub hρ'))

/-! ### The pulled-back trace -/

/-- The pulled-back trace `η(t) = ψ⁻¹(η̃(C(t)))`. -/
def pullTrace (xk : ℝ) (w vk : ℝ≥0 → ℝ) (η' : ℝ≥0 → ℂ) (t : ℝ≥0) : ℂ :=
  Sec7.targetChangeInv xk (η' (clk (rate xk w vk) t).toNNReal)

section Pull

variable {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} {xk : ℝ} {η' : ℝ≥0 → ℂ}

theorem PullData.continuousOn_newDrv (hd : PullData w vk xk T) :
    ContinuousOn (newDrv xk w vk) {u | (u : ℝ≥0∞) < newHorizon xk w vk T} :=
  continuousOn_newPath hd.sep hd.pos fun _ hS => (hd.sep.isSep_of_lt hS).continuousOn_mobPath_w

theorem PullData.newDrv_zero (hd : PullData w vk xk T) (hT : 0 < T) : newDrv xk w vk 0 = 0 := by
  simp only [newDrv, newPath_zero]
  exact hd.mobPath_zero hT

theorem PullData.isRate (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    IsRate (rate xk w vk) t :=
  (hd.sep.isSep_of_lt ht).isRate hd.pos

/-- The new time of an original time before `T` is before the new horizon. -/
theorem PullData.clk_lt (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    (((clk (rate xk w vk) t).toNNReal : ℝ≥0) : ℝ≥0∞) < newHorizon xk w vk T :=
  clk_lt_newHorizon hd.sep hd.pos ht

/-- The original hull before `T` is a bounded hull. -/
theorem PullData.isHPHull_fwdHull (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    IsHPHull (fwdHull (fun s : ℝ => w s.toNNReal) t) := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨W', -, hW'c, -, -, -, hW'eq, -⟩ := hd.local_hull hST
  rw [fwdHull_eq_of_eqOn t.coe_nonneg (by exact_mod_cast ENNReal.coe_lt_coe.1 htS)
    fun r hr => (hW'eq r hr).symm]
  exact InteractingSLE.isHPHull_fwdHull hW'c t.coe_nonneg

/-- The new hull at `C(t)`, `t < T`, is a bounded hull. -/
theorem PullData.isHPHull_newHull (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    IsHPHull (fwdHull (fun r : ℝ => newDrv xk w vk r.toNNReal) (clk (rate xk w vk) t)) := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨-, Wn', -, hWn'c, -, -, -, hWn'eq, -⟩ := hd.local_hull hST
  have hR := hd.isRate hST
  have htI : (t : ℝ) ∈ Icc 0 (S : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast (ENNReal.coe_lt_coe.1 htS).le⟩
  rw [fwdHull_eq_of_eqOn (hR.clk_nonneg htI)
    (hR.clk_lt htI ⟨S.coe_nonneg, le_rfl⟩ (by exact_mod_cast ENNReal.coe_lt_coe.1 htS))
    fun r hr => (hWn'eq r hr).symm]
  exact InteractingSLE.isHPHull_fwdHull hWn'c (hR.clk_nonneg htI)

/-- **The trace points of `η̃` in `ℍ` up to `C(S)` lie in `ψ(K_S)`.** -/
theorem PullData.mem_image_of_mem_H (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {S : ℝ≥0} (hS : (S : ℝ≥0∞) < T)
    {ρ : ℝ≥0} (hρ : (ρ : ℝ) ≤ clk (rate xk w vk) S) (hH : η' ρ ∈ H) :
    η' ρ ∈ Sec7.targetChange xk '' fwdHull (fun s : ℝ => w s.toNNReal) S := by
  have hfill := hη.2.2 _ (hd.clk_lt hS)
  have hc0 : 0 ≤ clk (rate xk w vk) S := (hd.isRate hS).clk_nonneg ⟨S.coe_nonneg, le_rfl⟩
  rw [Real.coe_toNNReal _ hc0, hd.fwdHull_newDrv_eq hS] at hfill
  refine Sec5.CrossRestart.inter_H_subset_of_isFilling hfill ⟨⟨ρ, ⟨zero_le, ?_⟩, rfl⟩, hH⟩
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hc0]
  exact hρ

/-- **`η̃` stays away from the pole `−1` up to `C(S)`** when `K_S ⊆ closedBall 0 R`. -/
theorem PullData.norm_add_one_ge (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {S : ℝ≥0} (hS : (S : ℝ≥0∞) < T)
    {R : ℝ} (hK : fwdHull (fun s : ℝ => w s.toNNReal) S ⊆ closedBall 0 R) {ρ : ℝ≥0}
    (hρ : (ρ : ℝ) ≤ clk (rate xk w vk) S) : min (xk / (xk + R)) 1 ≤ ‖η' ρ + 1‖ := by
  have hT0 : 0 < T := lt_of_le_of_lt bot_le hS
  have hρT : (ρ : ℝ≥0∞) ≤ newHorizon xk w vk T := by
    refine le_trans ?_ (hd.clk_lt hS).le
    exact ENNReal.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le (le_trans ρ.coe_nonneg hρ) |>.2 hρ)
  refine ge_of_forall_lt_mem_H hη hd.continuousOn_newDrv (hd.newDrv_zero hT0) hρT fun ρ' hρ' hH => ?_
  obtain ⟨z, hz, he⟩ := hd.mem_image_of_mem_H hη hS ((NNReal.coe_le_coe.2 hρ'.le).trans hρ) hH
  rw [← he]
  exact norm_targetChange_add_one_ge hd.pos ((QuantumZipper.fwdHull_mono).2 _ hz) (hK hz)

/-- `η̃(C(t)) ≠ −1` before `T`. -/
theorem PullData.ne_neg_one (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    η' (clk (rate xk w vk) t).toNNReal ≠ -1 := by
  obtain ⟨R₁, hR₁⟩ := (hd.isHPHull_fwdHull ht).2.1.subset_closedBall 0
  set R := max R₁ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ closedBall 0 R :=
    hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hc0 : 0 ≤ clk (rate xk w vk) t := (hd.isRate ht).clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
  have h := hd.norm_add_one_ge hη ht hR (ρ := (clk (rate xk w vk) t).toNNReal)
    (by rw [Real.coe_toNNReal _ hc0])
  intro he
  rw [he, neg_add_cancel, norm_zero] at h
  have : 0 < min (xk / (xk + R)) 1 := lt_min (div_pos hd.pos (by linarith [hd.pos])) one_pos
  linarith

/-- The clock maps `[0, t]` onto `[0, C(t)]` (in `ℝ≥0`). -/
theorem PullData.image_clk_Icc (hd : PullData w vk xk T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    (fun s : ℝ≥0 => (clk (rate xk w vk) s).toNNReal) '' Icc 0 t = Icc 0 (clk (rate xk w vk) t).toNNReal := by
  have hR := hd.isRate ht
  ext ρ
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsI : (s : ℝ) ∈ Icc 0 (t : ℝ) := ⟨s.coe_nonneg, by exact_mod_cast hs.2⟩
    exact ⟨zero_le, Real.toNNReal_le_toNNReal ((hR.clk_le_clk hsI ⟨t.coe_nonneg, le_rfl⟩).2 hsI.2)⟩
  · rintro ⟨-, hρ⟩
    have hc0 : 0 ≤ clk (rate xk w vk) t := hR.clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
    have hρI : (ρ : ℝ) ∈ Icc 0 (clk (rate xk w vk) t) :=
      ⟨ρ.coe_nonneg, by rw [← Real.coe_toNNReal _ hc0]; exact_mod_cast hρ⟩
    have hm := hR.invClk_mem hρI
    refine ⟨(invClk (rate xk w vk) ρ).toNNReal, ⟨zero_le, ?_⟩, ?_⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hm.1]; exact hm.2
    · simp only
      rw [Real.coe_toNNReal _ hm.1, hR.clk_invClk hρI, Real.toNNReal_coe]

/-- **The pulled-back trace generates the original hulls before `T`** (R6): `K_t = fill(η[0, t])`. -/
theorem PullData.isFilling_pullTrace (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    IsFilling (fwdHull (fun s : ℝ => w s.toNNReal) t) (pullTrace xk w vk η' '' Icc 0 t) := by
  have hxk := hd.pos
  have hc0 : 0 ≤ clk (rate xk w vk) t := (hd.isRate ht).clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
  have hfill := hη.2.2 _ (hd.clk_lt ht)
  rw [Real.coe_toNNReal _ hc0] at hfill
  have hKn := hd.isHPHull_newHull ht
  rw [hd.fwdHull_newDrv_eq ht] at hfill hKn
  -- the pole `−1` of `ψ⁻¹` keeps a positive distance from `ψ(K_t)`
  obtain ⟨R₁, hR₁⟩ := (hd.isHPHull_fwdHull ht).2.1.subset_closedBall 0
  set R := max R₁ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ closedBall 0 R :=
    hR₁.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hpole : Sec5.CrossRestart.mobPole 1 1 = -1 := by simp [Sec5.CrossRestart.mobPole]
  have hdisj : Disjoint (ball ((Sec5.CrossRestart.mobPole 1 1 : ℝ) : ℂ) (xk / (xk + R)))
      (Sec7.targetChange xk '' fwdHull (fun s : ℝ => w s.toNNReal) t) := by
    rw [Set.disjoint_left]
    rintro _ hb ⟨z, hz, rfl⟩
    have hge := norm_targetChange_add_one_ge hxk ((QuantumZipper.fwdHull_mono).2 _ hz) (hR hz)
    rw [hpole, mem_ball, dist_eq_norm] at hb
    push_cast at hb
    rw [sub_neg_eq_add] at hb
    linarith
  have himg := Sec5.CrossRestart.isFilling_image_realMobius (a := xk) (b := 0) (c := 1) (d := 1)
    (by linarith) one_ne_zero hKn (div_pos hxk (by linarith)) hdisj hfill
  have e1 : QuantumZipper.CA.realMobius xk 0 1 1 ''
      (Sec7.targetChange xk '' fwdHull (fun s : ℝ => w s.toNNReal) t) =
      fwdHull (fun s : ℝ => w s.toNNReal) t := by
    rw [image_image]
    refine Eq.trans (image_congr fun z hz => ?_) (image_id _)
    rw [← targetChangeInv_eq_realMobius, id,
      Sec7.targetChangeInv_targetChange hxk.ne' (Sec7.ne_ofReal_of_mem_H ((QuantumZipper.fwdHull_mono).2 _ hz) xk)]
  have e2 : QuantumZipper.CA.realMobius xk 0 1 1 '' (η' '' Icc 0 (clk (rate xk w vk) t).toNNReal ∩ H) =
      pullTrace xk w vk η' '' Icc 0 t ∩ H := by
    rw [← hd.image_clk_Icc ht, image_image]
    ext v
    constructor
    · rintro ⟨_, ⟨⟨s, hs, rfl⟩, hH⟩, rfl⟩
      refine ⟨⟨s, hs, by simp only [pullTrace, targetChangeInv_eq_realMobius]⟩, ?_⟩
      rw [← targetChangeInv_eq_realMobius, targetChangeInv_mem_H_iff hxk]
      exact hH
    · rintro ⟨⟨s, hs, rfl⟩, hH⟩
      refine ⟨_, ⟨⟨s, hs, rfl⟩, (targetChangeInv_mem_H_iff hxk _).1 hH⟩, ?_⟩
      rw [← targetChangeInv_eq_realMobius]
      rfl
  rw [e1, e2] at himg
  exact Sec5.CrossRestart.isFilling_inter_H_iff.1 himg

/-- **The pulled-back trace is continuous before `T`.** -/
theorem PullData.continuousAt_pullTrace (hd : PullData w vk xk T)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ContinuousAt (pullTrace xk w vk η') t := by
  obtain ⟨S, htS, hST⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  have hR := hd.isRate hST
  -- the clock is continuous at `t`
  have hc : ContinuousAt (fun s : ℝ≥0 => (clk (rate xk w vk) s).toNNReal) t := by
    have h1 : ContinuousOn (fun s : ℝ≥0 => clk (rate xk w vk) s) (Iic S) :=
      hR.continuousOn_clk.comp NNReal.continuous_coe.continuousOn fun s hs =>
        ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    exact continuous_real_toNNReal.continuousAt.comp (h1.continuousAt (Iic_mem_nhds htS'))
  -- `η̃` is continuous at `C(t) < T̃`
  have hη' : ContinuousAt η' (clk (rate xk w vk) t).toNNReal := by
    have hlt := hd.clk_lt ht
    have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < newHorizon xk w vk T} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact (hη.2.1 _ hlt.le).continuousAt (Filter.mem_of_superset (hopen.mem_nhds hlt)
      fun u (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) => show (u : ℝ≥0∞) ≤ newHorizon xk w vk T from hu.le)
  exact ContinuousAt.comp (f := fun s : ℝ≥0 => η' (clk (rate xk w vk) s).toNNReal)
    (continuousAt_targetChangeInv (hd.ne_neg_one hη ht))
    (ContinuousAt.comp (f := fun s : ℝ≥0 => (clk (rate xk w vk) s).toNNReal) hη' hc)

theorem pullTrace_zero (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η') :
    pullTrace xk w vk η' 0 = 0 := by
  simp [pullTrace, hη.1]

end Pull

end Retarget

end Zhan

end InteractingSLE
