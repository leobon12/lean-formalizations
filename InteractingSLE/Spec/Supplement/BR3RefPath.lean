/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefCode
import InteractingSLE.Spec.Zhan.TargetChangeProcessPullEnd
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownian
import InteractingSLE.Spec.Supplement.LPProbRetarget
import InteractingSLE.Spec.Sec7.ContinuityProb9Prefix

/-!
# BR3's bounded reference: the retargeting along one path

Packet PROVE-T14-BR3. Pathwise facts of LP9's retargeting (`Zhan.Retarget`, PROVE-SEC7-C8/C9/C10) at a right mark
`x_k > 0` of weight sum `≤ −2` that is the last right mark (supplement p. 608, proof of BR3: "use `φ(w) = w/(w − a)`.
It maps `a` to infinity and the old target to `1`"; here in the reflected form `ψ(z) = z/(x_k − z)` of the landed API,
which sends `x_k` to `∞` and the old target to `−1`).

* `sepTime_eq_of_sum_le`: the driver meets the last right mark only at a continuation threshold, so the separation
  time is the lifetime;
* `newW_sub_beta_clk`: in the new clock, the gap of the transformed driver to the old target `−1` is
  `X̃(C(s)) = α_s/q_s`, `q = V_k − W` (`α_s = x_k e^{−2∫₀ˢ q⁻²}`, PROVE-SEC7-C8's `alpha`);
* `alpha_le`: `α ≤ x_k`;
* **`newHorizon_eq_top_of_gap`**: if the original separation time is infinite and `X̃` stays above a positive constant
  along the original time, the new horizon is infinite (the clock rate `α²/q⁴ = X̃²·q⁻²` is bounded below);
* **`PullData.false_of_newHorizon_top`**: an infinite separation time and an infinite new horizon with a transient
  transformed trace are incompatible (the pulled-back trace would be bounded; the argument of
  `PullData.isGeneratingTrace_top`, PROVE-SEC7-C10);
* `retarget_sep`, `sum_filter_le_castAdd`, `sum_filter_le_natAdd_zero`: the transformed start is separated, and its
  partial sums.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

open Zhan Zhan.Retarget Sec7 Sec7.RandRestart

/-! ### The separation time at a last bad right mark -/

/-- **The separation time is the lifetime** when the target is the last right mark and the right weights sum to at most
`−2`: at a first meeting before the lifetime every right mark collides with the driver, a continuation threshold. -/
theorem sepTime_eq_of_sum_le {κ : ℝ} {nL j : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 0) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + 0) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + 0) → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hR : ∑ i, ρR i ≤ -2) :
    sepTime w (vR (LP.retargetIdx j 0)) ζ = ζ := by
  refine le_antisymm (sepTime_le w _ ζ) (not_lt.1 fun hlt => ?_)
  have hc : ContinuousOn (fun t => vR (LP.retargetIdx j 0) t - w t) {t | (t : ℝ≥0∞) < ζ} :=
    (hp.isForcePath.continuousOn_vR _).sub hp.isForcePath.continuousOn_w
  rw [sepTime_eq_firstMeet] at hlt
  obtain ⟨t₀, -, ht₀ζ, hle⟩ := exists_eq_firstMeet (W := fun t (_ : Unit) => w t)
    (V := fun t _ => vR (LP.retargetIdx j 0) t) (ζ := fun _ => ζ) (ω := ()) hc hlt
  have hk : vR (LP.retargetIdx j 0) t₀ = w t₀ := le_antisymm hle (hp.isForcePath.w_le_vR ht₀ζ _)
  have hall : ∀ i, vR i t₀ = w t₀ := by
    intro i
    have hik : i ≤ LP.retargetIdx j 0 := by
      rw [Fin.le_def]; simp only [LP.retargetIdx, Fin.val_castAdd, Fin.val_last]; have := i.isLt; omega
    exact le_antisymm ((hp.isForcePath.monotone_vR ht₀ζ hik).trans hk.le) (hp.isForcePath.w_le_vR ht₀ζ i)
  have hthr : ForceWord.ThresholdCondition ρL ρR (w t₀) (fun i => vL i t₀) (fun i => vR i t₀) := by
    right
    rw [Finset.filter_true_of_mem fun i _ => hall i]
    exact hR
  exact (hp.isSLEPathUpTo le_rfl).not_threshold ht₀ζ hthr

/-! ### The gap to the old target in the new clock -/

section Clock

variable {xk : ℝ} {w vk : ℝ≥0 → ℝ}

/-- `α_s ≤ x_k`. -/
theorem alpha_le (hxk : 0 < xk) {s : ℝ} (hs : 0 ≤ s) : alpha xk w vk s ≤ xk := by
  unfold alpha
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ :=
    intervalIntegral.integral_nonneg hs fun u _ => inv_nonneg.2 (sq_nonneg _)
  have : Real.exp (-2 * ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc xk * Real.exp (-2 * ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹) ≤ xk * 1 :=
        mul_le_mul_of_nonneg_left this hxk.le
    _ = xk := mul_one _

/-- **The gap of the transformed driver to the old target in the new clock**: at the new time `C(s)`,
`M_s(w_s) − β_s = α_s/q_s`. -/
theorem newW_sub_beta_clk {T : ℝ≥0∞} (h : SepUpTo w vk T) (hxk : 0 < xk) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    newPath xk w vk (mobPath xk w vk w) (clk (rate xk w vk) s).toNNReal -
        newPath xk w vk (beta xk w vk) (clk (rate xk w vk) s).toNNReal = alpha xk w vk s / gap w vk s := by
  have hR := (h.isSep_of_lt hs).isRate hxk
  have hC0 : 0 ≤ clk (rate xk w vk) s := hR.clk_nonneg ⟨s.coe_nonneg, le_rfl⟩
  have hinv : invClk (rate xk w vk) ((clk (rate xk w vk) s).toNNReal : ℝ) = s := by
    rw [Real.coe_toNNReal _ hC0]
    exact hR.invClk_clk ⟨s.coe_nonneg, le_rfl⟩
  simp only [newPath, hinv, mobPath, mob, Real.toNNReal_coe, gap]
  ring

/-- **An infinite separation time with the gap to the old target bounded below has an infinite new horizon**: the
clock rate `α²/q⁴` is at least `c⁴/x_k²` when `α/q ≥ c` (`q ≤ α/c ≤ x_k/c`). -/
theorem newHorizon_eq_top_of_gap (h : SepUpTo w vk ⊤) (hxk : 0 < xk) {c : ℝ} (hc : 0 < c)
    (hX : ∀ s : ℝ≥0, c ≤ alpha xk w vk s / gap w vk s) : newHorizon xk w vk ⊤ = ⊤ := by
  set r : ℝ := c ^ 4 / xk ^ 2 with hr
  have hr0 : 0 < r := by positivity
  have hrate : ∀ s : ℝ≥0, r ≤ rate xk w vk s := by
    intro s
    have hq : 0 < gap w vk s := (h.isSep_of_lt (ENNReal.coe_lt_top (r := s))).pos s ⟨s.coe_nonneg, le_rfl⟩
    have ha : 0 < alpha xk w vk s := alpha_pos hxk w vk s
    have hale := alpha_le (w := w) (vk := vk) hxk s.coe_nonneg
    have h1 : c * gap w vk s ≤ alpha xk w vk s := by
      have := hX s; rwa [le_div_iff₀ hq] at this
    have h2 : gap w vk s ≤ xk / c := by rw [le_div_iff₀ hc]; nlinarith
    have hq' : c / xk ≤ 1 / gap w vk s := by
      rw [div_le_div_iff₀ (by linarith) hq]; linarith [mul_comm c (gap w vk s)]
    have hX' : c ≤ alpha xk w vk s / gap w vk s := hX s
    have e : rate xk w vk s = (alpha xk w vk s / gap w vk s) ^ 2 * (1 / gap w vk s) ^ 2 := by
      unfold rate; field_simp
    rw [e, hr]
    have hcx : 0 ≤ c / xk := by positivity
    calc c ^ 4 / xk ^ 2 = c ^ 2 * (c / xk) ^ 2 := by field_simp
      _ ≤ (alpha xk w vk s / gap w vk s) ^ 2 * (1 / gap w vk s) ^ 2 := by
        gcongr
  refine eq_top_iff.2 (ENNReal.le_of_forall_pos_nnreal_lt fun M _ _ => ?_)
  set S : ℝ≥0 := (M / r + 1 : ℝ).toNNReal with hS
  have hS' : (S : ℝ) = M / r + 1 := Real.coe_toNNReal _ (by positivity)
  have hRS := (h.isSep_of_lt (ENNReal.coe_lt_top (r := S))).isRate hxk
  have hint : r * S ≤ clk (rate xk w vk) S := by
    unfold clk
    have hi := hRS.intervalIntegrable (a := 0) (b := S) ⟨le_rfl, S.coe_nonneg⟩ ⟨S.coe_nonneg, le_rfl⟩
    calc r * (S : ℝ) = ∫ _ in (0 : ℝ)..S, r := by simp [mul_comm]
      _ ≤ ∫ u in (0 : ℝ)..S, rate xk w vk u := by
        refine intervalIntegral.integral_mono_on S.coe_nonneg intervalIntegrable_const hi fun u hu => ?_
        have := hrate u.toNNReal
        rwa [Real.coe_toNNReal _ hu.1] at this
  have hM : (M : ℝ) < clk (rate xk w vk) S := by
    have : (M : ℝ) < r * S := by
      rw [hS']; field_simp; nlinarith [M.coe_nonneg]
    linarith
  refine le_trans ?_ (le_iSup₂_of_le S ENNReal.coe_lt_top le_rfl)
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal hM.le

end Clock

/-! ### Infinite separation time and infinite new horizon -/

/-- **An infinite separation time and an infinite new horizon are incompatible** with a transient transformed trace:
the pulled-back trace `ψ⁻¹ ∘ η̃ ∘ C` would be bounded, while its hulls have capacity `2t → ∞` (the first case of
`PullData.isGeneratingTrace_top`, PROVE-SEC7-C10). -/
theorem PullData.false_of_newHorizon_top {xk : ℝ} {w vk : ℝ≥0 → ℝ} {η' : ℝ≥0 → ℂ} (hd : PullData w vk xk ⊤)
    (hη : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η')
    (htr : Tendsto (fun ρ => ‖η' ρ‖) atTop atTop) (hTn : newHorizon xk w vk ⊤ = ⊤) : False := by
  have hxk := hd.pos
  have hbdd : ∀ c > 0, (∀ t : ℝ≥0, c ≤ ‖η' (clk (rate xk w vk) t).toNNReal + 1‖) → False := fun c hc h =>
    hd.not_bounded_top hη (B := xk * (1 + 1 / c)) fun t => norm_targetChangeInv_le hxk hc (h t)
  obtain ⟨ρ₀, hρ₀⟩ := (tendsto_atTop.1 htr) 2 |>.exists_forall_of_atTop
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

/-! ### The transformed word -/

section Word

variable {nL j m : ℕ}

/-- **The transformed start is separated** when the original one is. -/
theorem retarget_sep {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hsep : ∀ i i', xL i < xR i') : ∀ i i', LP.retargetXL xL xR i < LP.retargetXR xR i' := by
  obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
  have hp := LP.retargetPos_pos hmono hR0 hj
  intro i i'
  have hx' : xR (Fin.castAdd m i'.castSucc) < LP.retargetPos xR := LP.xR_castAdd_castSucc_lt hmono i'
  have hnn : 0 ≤ Sec7.targetChangeReal (LP.retargetPos xR) (xR (Fin.castAdd m i'.castSucc)) :=
    Sec7.targetChangeReal_nonneg (hR0 _) hx'
  induction i using Fin.addCases with
  | left i =>
    simp only [LP.retargetXL, LP.retargetXR, Fin.append_left]
    exact Sec7.strictMonoOn_targetChangeReal_Iio hp (lt_of_le_of_lt (hL0 i) hp) hx' (hsep _ _)
  | right k =>
    simp only [LP.retargetXL, LP.retargetXR, Fin.append_right]
    have hle : (Fin.cons (-1) fun l : Fin m => Sec7.targetChangeReal (LP.retargetPos xR)
        (xR (Fin.natAdd (j + 1) l.rev)) : Fin (m + 1) → ℝ) k ≤ -1 := by
      induction k using Fin.cases with
      | zero => simp
      | succ l =>
        simp only [Fin.cons_succ]
        exact (Sec7.targetChangeReal_lt_neg_one hp (LP.retargetPos_lt_xR_natAdd hmono _)).le
    linarith

/-- Partial sums of an appended tuple at a left index. -/
theorem sum_filter_le_castAdd {a b : ℕ} (f : Fin (a + b) → ℝ) (i : Fin a) :
    ∑ l ∈ univ.filter (· ≤ Fin.castAdd b i), f l = ∑ l ∈ univ.filter (· ≤ i), f (Fin.castAdd b l) := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add]
  have h2 : ∑ l : Fin b, (if Fin.natAdd a l ≤ Fin.castAdd b i then f (Fin.natAdd a l) else 0) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [ite_eq_right_iff]
    intro hle
    exfalso
    rw [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hle; have := i.isLt; omega
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (Fin.castAdd b l ≤ Fin.castAdd b i) ↔ l ≤ i := by
    rw [Fin.le_def, Fin.le_def, Fin.val_castAdd, Fin.val_castAdd]
  simp only [e]

/-- Partial sums of an appended tuple at the first right index with a single right entry: the total. -/
theorem sum_filter_le_natAdd_zero {a : ℕ} (f : Fin (a + 1) → ℝ) :
    ∑ l ∈ univ.filter (· ≤ Fin.natAdd a (0 : Fin 1)), f l =
      (∑ l : Fin a, f (Fin.castAdd 1 l)) + f (Fin.natAdd a 0) := by
  rw [Finset.filter_true_of_mem fun l _ => ?_, Fin.sum_univ_add, Fin.sum_univ_one]
  rw [Fin.le_def, Fin.val_natAdd]; have := l.isLt; simp; omega

end Word

/-! ### The two pathwise conclusions -/

section Conclusions

variable {κ : ℝ} {nL j : ℕ}

theorem newVL_natAdd_zero {m : ℕ} (xR : Fin (j + 1 + m) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin (j + 1 + m) → ℝ≥0 → ℝ) (u : ℝ≥0) :
    newVL xR w vL vR (Fin.natAdd nL 0) u =
      newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)))
        u := by
  simp [newVL]

/-- The data of a retargeting path at the original time `s < T`: the new time `u = C(s)` lies before the new horizon,
and the gap of the transformed driver to the old target there is `α_s/q_s`. -/
theorem newTime_gap {m : ℕ} {xR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hd : PullData w (vR (LP.retargetIdx j m)) (LP.retargetPos xR) T) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) :
    (((clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) s).toNNReal : ℝ≥0) : ℝ≥0∞) <
        newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T ∧
      newW xR w vR (clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) s).toNNReal -
          newVL xR w vL vR (Fin.natAdd nL 0)
            (clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) s).toNNReal =
        alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s / gap w (vR (LP.retargetIdx j m)) s := by
  refine ⟨clk_lt_newHorizon hd.sep hd.pos hs, ?_⟩
  rw [newVL_natAdd_zero]
  exact newW_sub_beta_clk hd.sep hd.pos hs

/-- **(A) along one path: the lifetime is finite.** For a distinct word whose last right mark (Lean index `j ≥ 1`) has
right weight sum `≤ −2`, let a continuous path `(w_c, v_c)` agree with the transformed driver and old target before
the new horizon of the separation time, with the trace event on `[0, ∞)` and the gap `w_c − v_c` uniformly positive on
compacts. Then the original lifetime is finite. -/
theorem lifetime_lt_top_of_code {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 0) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + 0) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + 0) → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hR : ∑ i, ρR i ≤ -2) {wc : ℝ≥0 → ℝ}
    {vLc : Fin (nL + (0 + 1)) → ℝ≥0 → ℝ} (hwc : Continuous wc) (hvLc : Continuous (vLc (Fin.natAdd nL 0)))
    (htrc : TraceEvent wc ⊤) (hgap : BR3Ref.GapPos (Fin.natAdd nL 0) wc vLc ⊤)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0))
        (sepTime w (vR (LP.retargetIdx j 0)) ζ) →
      newW xR w vR t = wc t ∧ newVL xR w vL vR (Fin.natAdd nL 0) t = vLc (Fin.natAdd nL 0) t) :
    ζ < ⊤ := by
  by_contra hζ
  rw [not_lt, top_le_iff] at hζ
  subst hζ
  have hsepT := sepTime_eq_of_sum_le hp hR
  rw [hsepT] at hag
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo le_rfl) hD hj fun t ht =>
    lt_of_lt_sepTime (by rw [hsepT]; exact ht)
  have hd : PullData w (vR (LP.retargetIdx j 0)) (LP.retargetPos xR) ⊤ := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  by_cases hTn : newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)) ⊤ = ⊤
  · obtain ⟨η, hη, htr⟩ := htrc
    have hη' : IsGeneratingTrace (newDrv (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)))
        (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)) ⊤) η := by
      rw [hTn]
      exact IsGeneratingTrace.congr_lt hη fun t ht => (hag t (by rw [hTn]; exact ht)).1
    exact PullData.false_of_newHorizon_top hd hη' (htr rfl) hTn
  · set Tn := (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)) ⊤).toNNReal with hTndef
    have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)) ⊤ :=
      ENNReal.coe_toNNReal hTn
    obtain ⟨n, hn⟩ := hgap ⌈(Tn : ℝ)⌉₊
    have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine hTn (newHorizon_eq_top_of_gap hd.sep hd.pos hc fun s => ?_)
    obtain ⟨hu, he⟩ := newTime_gap (vL := vL) hd (s := s) ENNReal.coe_lt_top
    set u := (clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j 0))) s).toNNReal
    rw [← he, (hag u hu).1, (hag u hu).2]
    have huN : u ≤ ((⌈(Tn : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
      have h1 : u < Tn := by rw [← hTn'] at hu; exact_mod_cast hu
      have h2 : (Tn : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := Nat.le_ceil _
      have h3 : (u : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := (le_of_lt (by exact_mod_cast h1)).trans h2
      exact_mod_cast h3
    exact le_of_forall_rat_le (f := fun t => wc t - vLc (Fin.natAdd nL 0) t)
      ((hwc.sub hvLc).continuousOn) (fun q hq => hn q ENNReal.coe_lt_top hq) huN

/-- **(B) along one path: the gap of the last right mark stays positive.** For a distinct word whose last right mark
(Lean index `j ≥ 1`) closes a right list of total weight `≤ −2`, let a path `(w_c, v_c)` with finite lifetime `ζ_c`,
continuous before it, agree with the transformed driver and old target before the new horizon of the separation time,
which is at most `ζ_c`, with the gap `w_c − v_c` between `1/(n+1)` and `n+1` at the rational times before `ζ_c`. Then
`V_k − W` is bounded below by a positive constant before the original lifetime: the clock `∫ q⁻² ≤ (n+1)² C ≤
(n+1)² T̃` is bounded, so `α ≥ x_k e^{−2(n+1)² T̃}` and `q = α/X̃ ≥ α/(n+1)`. -/
theorem far_gap_of_code {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 0) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + 0) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + 0) → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hR : ∑ i, ρR i ≤ -2) {wc : ℝ≥0 → ℝ}
    {vLc : Fin (nL + (0 + 1)) → ℝ≥0 → ℝ} {ζc : ℝ≥0∞} (hwc : ContinuousOn wc {t | (t : ℝ≥0∞) < ζc})
    (hvLc : ContinuousOn (vLc (Fin.natAdd nL 0)) {t | (t : ℝ≥0∞) < ζc})
    (hgap : BR3Ref.GapBdd (Fin.natAdd nL 0) wc vLc ζc)
    (hle : newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0)) (sepTime w (vR (LP.retargetIdx j 0)) ζ) ≤ ζc)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j 0))
        (sepTime w (vR (LP.retargetIdx j 0)) ζ) →
      newW xR w vR t = wc t ∧ newVL xR w vL vR (Fin.natAdd nL 0) t = vLc (Fin.natAdd nL 0) t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → δ ≤ vR (LP.retargetIdx j 0) t - w t := by
  have hsepT := sepTime_eq_of_sum_le hp hR
  rw [hsepT] at hle hag
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo le_rfl) hD hj fun t ht =>
    lt_of_lt_sepTime (by rw [hsepT]; exact ht)
  have hd : PullData w (vR (LP.retargetIdx j 0)) (LP.retargetPos xR) ζ := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  set xk := LP.retargetPos xR with hxk
  set vk := vR (LP.retargetIdx j 0) with hvk
  obtain ⟨hζc, n, hn⟩ := hgap
  have hTn : newHorizon xk w vk ζ ≠ ⊤ := ne_top_of_le_ne_top hζc.ne hle
  set Tn := (newHorizon xk w vk ζ).toNNReal with hTndef
  have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk ζ := ENNReal.coe_toNNReal hTn
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the two bounds at real new times before the horizon
  have hX : ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon xk w vk ζ →
      c ≤ newW xR w vR u - newVL xR w vL vR (Fin.natAdd nL 0) u ∧
        newW xR w vR u - newVL xR w vL vR (Fin.natAdd nL 0) u ≤ (n : ℝ) + 1 := by
    intro u hu
    rw [(hag u hu).1, (hag u hu).2]
    have huc : ∀ t ∈ Icc (0 : ℝ≥0) u, (t : ℝ≥0∞) < ζc := fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) (hu.trans_le hle)
    have hcont : ContinuousOn (fun t => wc t - vLc (Fin.natAdd nL 0) t) (Icc 0 u) :=
      (hwc.sub hvLc).mono huc
    refine ⟨le_of_forall_rat_le (f := fun t => wc t - vLc (Fin.natAdd nL 0) t) hcont
      (fun q hq => (hn q (huc q ⟨zero_le, hq⟩)).1) le_rfl, ?_⟩
    have h2 := le_of_forall_rat_le (f := fun t => ((n : ℝ) + 1) - (wc t - vLc (Fin.natAdd nL 0) t))
      (continuousOn_const.sub hcont) (fun q hq => by
        have := (hn q (huc q ⟨zero_le, hq⟩)).2; linarith) (le_refl u) (c := 0)
    linarith
  -- the bounds along the original time
  have hXs : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → c ≤ alpha xk w vk s / gap w vk s ∧
      alpha xk w vk s / gap w vk s ≤ (n : ℝ) + 1 := by
    intro s hs
    obtain ⟨hu, he⟩ := newTime_gap (vL := vL) hd hs
    rw [← he]
    exact hX _ hu
  have hpos := hd.pos
  set δ : ℝ := xk * Real.exp (-2 * (((n : ℝ) + 1) ^ 2 * Tn)) / ((n : ℝ) + 1) with hδ
  refine ⟨δ, by positivity, fun s hs => ?_⟩
  have hS := hd.sep.isSep_of_lt hs
  have hRt := hS.isRate hpos
  have hq : 0 < gap w vk s := hS.pos s ⟨s.coe_nonneg, le_rfl⟩
  -- the clock bound
  have hclk : clk (rate xk w vk) s ≤ Tn := by
    obtain ⟨hu, -⟩ := newTime_gap (vL := vL) hd hs
    rw [← hTn'] at hu
    have h1 : (clk (rate xk w vk) s).toNNReal ≤ Tn := (ENNReal.coe_lt_coe.1 hu).le
    have h0 : 0 ≤ clk (rate xk w vk) s := hRt.clk_nonneg ⟨s.coe_nonneg, le_rfl⟩
    have := NNReal.coe_le_coe.2 h1
    rwa [Real.coe_toNNReal _ h0] at this
  have hint : ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ ≤ ((n : ℝ) + 1) ^ 2 * Tn := by
    have hi1 : IntervalIntegrable (fun u => (gap w vk u ^ 2)⁻¹) volume 0 s :=
      (hS.continuousOn_inv_sq.mono (by rw [uIcc_of_le s.coe_nonneg])).intervalIntegrable
    have hi2 := hRt.intervalIntegrable (a := 0) (b := s) ⟨le_rfl, s.coe_nonneg⟩ ⟨s.coe_nonneg, le_rfl⟩
    calc ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ ≤ ∫ u in (0 : ℝ)..s, ((n : ℝ) + 1) ^ 2 * rate xk w vk u := by
          refine intervalIntegral.integral_mono_on s.coe_nonneg hi1 (hi2.const_mul _) fun u hu => ?_
          have hu' : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ :=
            lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)) hs
          have hb := (hXs u.toNNReal hu').1
          rw [Real.coe_toNNReal _ hu.1] at hb
          have hqu : 0 < gap w vk u := hS.pos u hu
          have hau : 0 < alpha xk w vk u := alpha_pos hpos w vk u
          have e : rate xk w vk u = (alpha xk w vk u / gap w vk u) ^ 2 * (gap w vk u ^ 2)⁻¹ := by
            unfold rate; field_simp
          rw [e]
          have hc2 : c ^ 2 ≤ (alpha xk w vk u / gap w vk u) ^ 2 := by gcongr
          have hcn : ((n : ℝ) + 1) ^ 2 * c ^ 2 = 1 := by rw [hcdef]; field_simp
          have hinv : 0 ≤ (gap w vk u ^ 2)⁻¹ := by positivity
          calc (gap w vk u ^ 2)⁻¹ = ((n : ℝ) + 1) ^ 2 * c ^ 2 * (gap w vk u ^ 2)⁻¹ := by rw [hcn, one_mul]
            _ ≤ ((n : ℝ) + 1) ^ 2 * (alpha xk w vk u / gap w vk u) ^ 2 * (gap w vk u ^ 2)⁻¹ := by gcongr
            _ = ((n : ℝ) + 1) ^ 2 * ((alpha xk w vk u / gap w vk u) ^ 2 * (gap w vk u ^ 2)⁻¹) := by ring
      _ = ((n : ℝ) + 1) ^ 2 * clk (rate xk w vk) s := by rw [intervalIntegral.integral_const_mul]; rfl
      _ ≤ ((n : ℝ) + 1) ^ 2 * Tn := by gcongr
  have halpha : xk * Real.exp (-2 * (((n : ℝ) + 1) ^ 2 * Tn)) ≤ alpha xk w vk s := by
    unfold alpha
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hpos.le
    linarith
  have hb2 := (hXs s hs).2
  have hXpos : 0 < alpha xk w vk s / gap w vk s := hc.trans_le (hXs s hs).1
  have hgap_eq : gap w vk s = alpha xk w vk s / (alpha xk w vk s / gap w vk s) := by
    have ha : alpha xk w vk s ≠ 0 := (alpha_pos hpos w vk s).ne'
    field_simp
  have : δ ≤ gap w vk s := by
    rw [hgap_eq, hδ]
    calc xk * Real.exp (-2 * (((n : ℝ) + 1) ^ 2 * Tn)) / ((n : ℝ) + 1)
        ≤ alpha xk w vk s / ((n : ℝ) + 1) := by gcongr
      _ ≤ alpha xk w vk s / (alpha xk w vk s / gap w vk s) := by
          gcongr
          exact (alpha_pos hpos w vk s).le
  simpa [gap, hvk] using this

end Conclusions

end BR3Ref

end Theorem14

end InteractingSLE
