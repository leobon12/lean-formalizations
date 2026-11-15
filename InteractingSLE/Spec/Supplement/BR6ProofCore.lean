/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR3RefDist
import InteractingSLE.Spec.Supplement.BR3RefCore
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Theorem BR6, sufficiency: the core for a distinct separated word

Packet PROVE-T14-BR3. Supplement p. 610, proof of Theorem BR6 ("For sufficiency form the retargeted word of BR2. The
first two conditions make its original-left and right-before-`z` portions admissible. The third gives `k − 6 − S_j ≥ c`
at the old target and at every farther mark on the new left. The complete retargeted law is therefore admissible, and
reflected GB5 protects the entire closed ray `(−∞, −1]`, starting at the retained old target. […] Integrated uniqueness
identifies the original canonical law through its first visit to `z`").

Here `z = x_k` is a right mark (Lean index `j ≥ 1` of a right list of length `j + 1 + m`) of a distinct separated word
with a left mark; the left partial sums and the right partial sums before `k` exceed `−2`, and the right partial sums at
`k` and beyond are at most `d = κ/2 − 4`.

* `pre_append_ge`, `pre_cons_succ`, `pre_rev_tail`, **`retargetρL_partial_natAdd`**: the transformed left partial sums
  beyond the old target are `κ − 6 − S`, `S` the original partial sums at `k` and beyond (LP9.1 for every far mark);
* `gap_pos_of_newTime_bounds`: a gap to the old target bounded above and below in a finite new horizon keeps the target
  gap `V_k − W` positive (the computation of `far_gap_of_code`);
* **`visit_of_code`** (one path): the separation time is finite, the new horizon is infinite, and the given generating
  trace visits `z` at the separation time (`PullData.isGeneratingTrace_of_top` and the tip identity
  `LP.traceAt_eq_of_isGeneratingTrace`);
* **`ae_visit_core`**: every integrated evolution with a generating trace visits `z` almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

open Zhan Zhan.Retarget Sec7 Sec7.RandRestart

/-! ### Prefix sums of the transformed left weights -/

section PreSums

theorem ite_pos' {c : Prop} [Decidable c] (h : c) {a b : ℝ} : (if c then a else b) = a := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] (h : ¬ c) {a b : ℝ} : (if c then a else b) = b := by simp [h]

theorem pre_append_ge {a b : ℕ} (f : Fin a → ℝ) (g : Fin b → ℝ) {v : ℕ} (hv : a ≤ v) :
    pre (Fin.append f g) v = (∑ l, f l) + pre g (v - a) := by
  unfold pre
  rw [Finset.sum_filter, Fin.sum_univ_add, Finset.sum_filter]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Fin.append_left, ite_pos' (by simp; omega)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    by_cases h : (l : ℕ) < v - a
    · rw [ite_pos' (by omega), ite_pos' h]
    · rw [ite_neg' (by omega), ite_neg' h]

theorem pre_cons_succ {b : ℕ} (c : ℝ) (g : Fin b → ℝ) (v : ℕ) :
    pre (Fin.cons c g : Fin (b + 1) → ℝ) (v + 1) = c + pre g v := by
  unfold pre
  rw [Finset.sum_filter, Fin.sum_univ_succ, Finset.sum_filter]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ]
  rw [ite_pos' (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : (l : ℕ) < v
  · rw [ite_pos' (by omega), ite_pos' h]
  · rw [ite_neg' (by omega), ite_neg' h]

/-- The first `k'` weights of the reversed tail are the last `k'` weights. -/
theorem pre_rev_tail {j m : ℕ} (ρR : Fin (j + 1 + m) → ℝ) {k' : ℕ} (hk : k' ≤ m) :
    pre (fun l : Fin m => ρR (Fin.natAdd (j + 1) l.rev)) k' = (∑ l, ρR l) - pre ρR (j + 1 + m - k') := by
  unfold pre
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun l : Fin (j + 1 + m) => (l : ℕ) < j + 1 + m - k') ρR]
  simp only [add_sub_cancel_left]
  refine Finset.sum_bij (fun l _ => Fin.natAdd (j + 1) l.rev) (fun l hl => ?_) (fun l₁ _ l₂ _ h => ?_)
    (fun i hi => ?_) (fun _ _ => rfl)
  · simp only [mem_filter, Finset.mem_univ, true_and, not_lt, Fin.val_natAdd, Fin.val_rev] at hl ⊢
    omega
  · have := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_rev] at this
    exact Fin.ext (by have := l₁.isLt; have := l₂.isLt; omega)
  · simp only [mem_filter, Finset.mem_univ, true_and, not_lt] at hi
    have hi' := i.isLt
    refine ⟨⟨j + 1 + m - 1 - i, by omega⟩, ?_, Fin.ext ?_⟩
    · simp only [mem_filter, Finset.mem_univ, true_and]; omega
    · simp only [Fin.val_natAdd, Fin.val_rev]; omega

/-- **The transformed left partial sums at and beyond the old target**: `κ − 6 − S`, `S` the original right partial sum
through the far mark reached (LP9.1 for every far mark). -/
theorem retargetρL_partial_natAdd {κ : ℝ} {nL j m : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ)
    (k' : Fin (m + 1)) :
    ∑ l ∈ univ.filter (· ≤ (Fin.natAdd nL k' : Fin (nL + (m + 1)))), LP.retargetρL κ ρL ρR l =
      κ - 6 - pre ρR (j + 1 + m - k') := by
  rw [sum_filter_le_eq_pre]
  simp only [Fin.val_natAdd]
  unfold LP.retargetρL
  rw [pre_append_ge _ _ (by omega), show nL + (k' : ℕ) + 1 - nL = (k' : ℕ) + 1 by omega, pre_cons_succ,
    pre_rev_tail ρR (by have := k'.isLt; omega)]
  ring

end PreSums

/-! ### The target gap from bounds in a finite new horizon -/

section Gap

variable {nL j m : ℕ}

/-- **A gap to the old target bounded above and below in a finite new horizon keeps the target gap positive**: the
relative clock `∫ q⁻² ≤ (n+1)² T̃` is bounded, so `α ≥ x_k e^{−2(n+1)²T̃}` and `q = α/X̃ ≥ α/(n+1)` (the computation of
`far_gap_of_code`). -/
theorem gap_pos_of_newTime_bounds {xR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hd : PullData w (vR (LP.retargetIdx j m)) (LP.retargetPos xR) T)
    (hTn : newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T ≠ ⊤) {n : ℕ}
    (hX : ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T →
      1 / ((n : ℝ) + 1) ≤ newW xR w vR u - newVL xR w vL vR (Fin.natAdd nL 0) u ∧
        newW xR w vR u - newVL xR w vL vR (Fin.natAdd nL 0) u ≤ (n : ℝ) + 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → δ ≤ vR (LP.retargetIdx j m) s - w s := by
  set xk := LP.retargetPos xR with hxk
  set vk := vR (LP.retargetIdx j m) with hvk
  set Tn := (newHorizon xk w vk T).toNNReal with hTndef
  have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hTn
  set c : ℝ := 1 / ((n : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the bounds along the original time
  have hXs : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → c ≤ alpha xk w vk s / gap w vk s ∧
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
          have hu' : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
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

end Gap

/-! ### BR6 sufficiency along one path -/

section Visit

variable {κ : ℝ} {nL j m : ℕ}

/-- **BR6 sufficiency along one path.** For a distinct word with target `z = x_k` (Lean index `j ≥ 1`), left partial
sums `> −2` and right partial sums before `k` `> −2`, Aux. lemma 3's threshold limit at a positive finite lifetime, and
a
continuous path `(w_c, v_c)` agreeing with the transformed driver and old target before the new horizon of the
separation time, with the transient trace event and the gap `w_c − v_c` uniformly positive on compacts: the given
generating trace visits `z` at the (finite) separation time. -/
theorem visit_of_code {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + m), i < LP.retargetIdx j m → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {wc : ℝ≥0 → ℝ} {vLc : Fin (nL + (m + 1)) → ℝ≥0 → ℝ} (hwc : Continuous wc)
    (hvLc : Continuous (vLc (Fin.natAdd nL 0))) (htrc : TraceEvent wc ⊤)
    (hgap : GapPos (Fin.natAdd nL 0) wc vLc ⊤)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
        (sepTime w (vR (LP.retargetIdx j m)) ζ) →
      newW xR w vR t = wc t ∧ newVL xR w vL vR (Fin.natAdd nL 0) t = vLc (Fin.natAdd nL 0) t)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ∧ η t = xR (LP.retargetIdx j m) := by
  set xk := LP.retargetPos xR with hxk
  set vk := vR (LP.retargetIdx j m) with hvk
  set T := sepTime w vk ζ with hTdef
  have hTζ : T ≤ ζ := sepTime_le w vk ζ
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo hTζ) hD hj fun t ht => lt_of_lt_sepTime ht
  have hd : PullData w vk xk T := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  have hxk0 := hd.pos
  have hfp := hp.isForcePath
  -- bounds of the code gap on compacts
  have hbd : ∀ N : ℕ, ∃ n : ℕ, ∀ u : ℝ≥0, u ≤ N → 1 / ((n : ℝ) + 1) ≤ wc u - vLc (Fin.natAdd nL 0) u ∧
      wc u - vLc (Fin.natAdd nL 0) u ≤ (n : ℝ) + 1 := by
    intro N
    obtain ⟨n₁, hn₁⟩ := hgap N
    have hc : ContinuousOn (fun t => wc t - vLc (Fin.natAdd nL 0) t) (Icc 0 (N : ℝ≥0)) :=
      (hwc.sub hvLc).continuousOn
    obtain ⟨t₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le⟩ hc
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge (wc t₂ - vLc (Fin.natAdd nL 0) t₂)
    refine ⟨max n₁ n₂, fun u hu => ⟨?_, ?_⟩⟩
    · exact (one_div_le_of_le (le_max_left _ _)).trans (le_of_forall_rat_le
        (f := fun t => wc t - vLc (Fin.natAdd nL 0) t) hc (fun q hq => hn₁ q ENNReal.coe_lt_top hq) hu)
    · have h1 : wc u - vLc (Fin.natAdd nL 0) u ≤ wc t₂ - vLc (Fin.natAdd nL 0) t₂ := hmax ⟨zero_le, hu⟩
      have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_right _ _
      linarith
  have hceil : ∀ {Tn : ℝ≥0} {u : ℝ≥0}, u < Tn → u ≤ ((⌈(Tn : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    intro Tn u h1
    have h2 : (Tn : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := Nat.le_ceil _
    have h3 : (u : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := (le_of_lt (by exact_mod_cast h1)).trans h2
    exact_mod_cast h3
  -- Step 1: the separation time is finite
  have hTfin : T ≠ ⊤ := by
    intro hT
    have hd' : PullData w vk xk ⊤ := hT ▸ hd
    rw [hT] at hag
    by_cases hTn : newHorizon xk w vk ⊤ = ⊤
    · obtain ⟨η', hη', htr⟩ := htrc
      have hη'' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η' := by
        rw [hTn]; exact IsGeneratingTrace.congr_lt hη' fun t ht => (hag t (by rw [hTn]; exact ht)).1
      exact PullData.false_of_newHorizon_top hd' hη'' (htr rfl) hTn
    · set Tn := (newHorizon xk w vk ⊤).toNNReal with hTndef
      have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk ⊤ := ENNReal.coe_toNNReal hTn
      obtain ⟨n, hn⟩ := hbd ⌈(Tn : ℝ)⌉₊
      have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine hTn (newHorizon_eq_top_of_gap hd'.sep hd'.pos hc fun s => ?_)
      obtain ⟨hu, he⟩ := newTime_gap (vL := vL) hd' (s := s) ENNReal.coe_lt_top
      rw [← he, (hag _ hu).1, (hag _ hu).2]
      exact (hn _ (hceil (by rw [← hTn'] at hu; exact_mod_cast hu))).1
  -- Step 2: the new horizon is infinite
  have hTn : newHorizon xk w vk T = ⊤ := by
    by_contra hTn
    set Tn := (newHorizon xk w vk T).toNNReal with hTndef
    have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hTn
    obtain ⟨n, hn⟩ := hbd ⌈(Tn : ℝ)⌉₊
    obtain ⟨δ, hδ, hgapδ⟩ := gap_pos_of_newTime_bounds (vL := vL) hd hTn (n := n) fun u hu => by
      rw [(hag u hu).1, (hag u hu).2]
      exact hn u (hceil (by rw [← hTn'] at hu; exact_mod_cast hu))
    rcases lt_or_eq_of_le hTζ with hTlt | hTeq
    · -- the driver meets the target at `T < ζ`
      have hc : ContinuousOn (fun t => vk t - w t) {t | (t : ℝ≥0∞) < ζ} :=
        (hfp.continuousOn_vR _).sub hfp.continuousOn_w
      have hTlt' := hTlt
      rw [hTdef, sepTime_eq_firstMeet] at hTlt'
      obtain ⟨t₀, ht₀, ht₀ζ, hle⟩ := exists_eq_firstMeet (W := fun t (_ : Unit) => w t)
        (V := fun t _ => vk t) (ζ := fun _ => ζ) (ω := ()) hc hTlt'
      have hTt₀ : T = (t₀ : ℝ≥0∞) := by rw [hTdef, sepTime_eq_firstMeet]; exact ht₀
      have hle' : vk t₀ ≤ w t₀ := hle
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
      · rw [← h0, hvk, hfp.vR_zero, hfp.w_zero] at hle'
        exact absurd hle' (not_le.2 hxk0)
      · have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
        have hcont := (hc.continuousAt (hopen.mem_nhds ht₀ζ)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t₀))
        have hne : (𝓝[<] t₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h0⟩
        have hge : δ ≤ vk t₀ - w t₀ := ge_of_tendsto hcont (by
          filter_upwards [self_mem_nhdsWithin] with s (hs : s < t₀)
          exact hgapδ s (by rw [hTt₀]; exact_mod_cast hs))
        linarith
    · -- `T = ζ`: the threshold at `ζ` would have to sit at the target
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ ζ) with hζ0 | hζ0
      · have hth := hfp.threshold_of_eq_zero hζ0.symm
        have := vR_eq_of_thresholdCondition hD.1.1 hD.1.2.2.1 hD.1.2.1 hD.1.2.2.2 hL _ hR hth
        exact absurd this (ne_of_gt hxk0)
      · have hζfin : ζ ≠ ⊤ := by rw [← hTeq]; exact hTfin
        set T' := ζ.toNNReal with hT'def
        have hT' : (T' : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζfin
        have hT'0 : 0 < T' := by
          have : (0 : ℝ≥0∞) < (T' : ℝ≥0∞) := by rw [hT']; exact hζ0
          exact_mod_cast this
        obtain ⟨w₀, vL₀, vR₀, htend, hth⟩ := hlim T' hT'0 hT'
        have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T', (t : ℝ≥0∞) < ζ := by
          filter_upwards [self_mem_nhdsWithin] with t (ht : t < T')
          rw [← hT']; exact_mod_cast ht
        have hw := (continuous_fst.tendsto _).comp htend
        have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T') (𝓝 (vL₀ i)) := fun i =>
          ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp
            ((continuous_snd.tendsto _).comp htend))
        have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T') (𝓝 (vR₀ i)) := fun i =>
          ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp
            ((continuous_snd.tendsto _).comp htend))
        have hne : (𝓝[<] T').NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT'0⟩
        have hantiL : Antitone vL₀ := fun i i' h =>
          le_of_tendsto_of_tendsto (hvL i') (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht h)
        have hmonoR : Monotone vR₀ := fun i i' h =>
          le_of_tendsto_of_tendsto (hvR i) (hvR i') (hev.mono fun t ht => hfp.monotone_vR ht h)
        have hLw : ∀ i, vL₀ i ≤ w₀ := fun i =>
          le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
        have hwR : ∀ i, w₀ ≤ vR₀ i := fun i =>
          le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
        have hkeq := vR_eq_of_thresholdCondition hantiL hmonoR hLw hwR hL _ hR hth
        have hge : δ ≤ vR₀ (LP.retargetIdx j m) - w₀ := ge_of_tendsto ((hvR _).sub hw) (by
          filter_upwards [self_mem_nhdsWithin] with s (hs : s < T')
          exact hgapδ s (by rw [hTeq, ← hT']; exact_mod_cast hs))
        rw [hkeq] at hge
        linarith
  -- Step 3: the pulled-back trace ends at `z`, and it is the given trace
  obtain ⟨η', hη', htr⟩ := htrc
  have hη'' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η' := by
    rw [hTn]; exact IsGeneratingTrace.congr_lt hη' fun t ht => (hag t (by rw [hTn]; exact ht)).1
  have hpb := hd.isGeneratingTrace_of_top hη'' hTn (htr rfl)
  set T' := T.toNNReal with hT'def
  have hT' : (T' : ℝ≥0∞) = T := ENNReal.coe_toNNReal hTfin
  have hT'0 : 0 < T' := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T') with h | h
    · exfalso
      have hT0 : T = 0 := by rw [← hT', ← h]; rfl
      rw [hT0, newHorizon_zero] at hTn
      exact ENNReal.zero_ne_top hTn
    · exact h
  refine ⟨T', by rw [hT']; exact hTζ, ?_⟩
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < T} := hfp.continuousOn_w.mono fun s hs =>
    lt_of_lt_of_le hs hTζ
  have heq : ∀ s : ℝ≥0, s < T' →
      η s = (fun t : ℝ≥0 => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t else (xk : ℂ)) s := by
    intro s hs
    have hsT : (s : ℝ≥0∞) < T := by rw [← hT']; exact_mod_cast hs
    rw [← LP.traceAt_eq_of_isGeneratingTrace hη hfp.continuousOn_w hfp.w_zero (lt_of_lt_of_le hsT hTζ),
      LP.traceAt_eq_of_isGeneratingTrace hpb hwc' hfp.w_zero hsT]
  have hne : (𝓝[<] T').NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT'0⟩
  have h1 : Tendsto η (𝓝[<] T') (𝓝 (η T')) := by
    have := hη.2.1 T' (show (T' : ℝ≥0∞) ≤ ζ by rw [hT']; exact hTζ)
    exact this.tendsto.mono_left (nhdsWithin_mono _ fun s (hs : s < T') =>
      show (s : ℝ≥0∞) ≤ ζ from le_trans (by rw [← hT']; exact_mod_cast hs.le) hTζ)
  have h2 : Tendsto (fun t : ℝ≥0 => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t else (xk : ℂ)) (𝓝[<] T')
      (𝓝 ((fun t : ℝ≥0 => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t else (xk : ℂ)) T')) := by
    have := hpb.2.1 T' (show (T' : ℝ≥0∞) ≤ T by rw [hT'])
    exact this.tendsto.mono_left (nhdsWithin_mono _ fun s (hs : s < T') =>
      show (s : ℝ≥0∞) ≤ T by rw [← hT']; exact_mod_cast hs.le)
  have hval : (fun t : ℝ≥0 => if (t : ℝ≥0∞) < T then pullTrace xk w vk η' t else (xk : ℂ)) T' = (xk : ℂ) := by
    simp only [hT', lt_self_iff_false, ↓reduceIte]
  rw [hval] at h2
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s (hs : s < T')
  exact (heq s hs).symm

end Visit

/-! ### BR6 sufficiency for a distinct separated word -/

section Core

variable {κ : ℝ} {nL j m : ℕ}

open Sec2 Sec2.Assembly Sec7.Band

/-- **BR6 sufficiency, core.** For `κ > 4`, a distinct separated word with a left mark and target `z = x_k` (Lean index
`j ≥ 1` of a right list of length `j + 1 + m`), whose left partial sums and right partial sums before `k` exceed `−2`
and whose right partial sums at `k` and beyond are at most `κ/2 − 4`: every integrated evolution with a generating trace
visits `z` almost surely (at its first meeting with the driver). -/
theorem ae_visit_core (hT13 : Exist.Theorem13Statement.{0}) (hκ : 4 < κ) {xL : Fin nL → ℝ}
    {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} (hD : LP.IsDistinctForceWord xL xR)
    (hsep : ∀ i i', xL i < xR i') (hj : 1 ≤ j) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlow : ∀ v : ℕ, j + 1 ≤ v → v ≤ j + 1 + m → pre ρR v ≤ κ / 2 - 4) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ η ω t = xR (LP.retargetIdx j m) := by
  have hκ0 : 0 < κ := by linarith
  have hD' := LP.isDistinctForceWord_retarget hD hj
  have hsep' := retarget_sep hD hj hsep
  -- the transformed partial sums
  have hfar : ∀ k' : Fin (m + 1), κ / 2 - 2 ≤
      ∑ l ∈ univ.filter (· ≤ (Fin.natAdd nL k' : Fin (nL + (m + 1)))), LP.retargetρL κ ρL ρR l := by
    intro k'
    rw [retargetρL_partial_natAdd]
    have := hlow (j + 1 + m - k') (by have := k'.isLt; omega) (by omega)
    linarith
  have hL' : ∀ i : Fin (nL + (m + 1)), -2 < ∑ l ∈ univ.filter (· ≤ i), LP.retargetρL κ ρL ρR l := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [sum_filter_le_castAdd]
      simpa [LP.retargetρL] using hL i
    | right k' => linarith [hfar k']
  have hR' : ∀ i : Fin j, -2 < ∑ l ∈ univ.filter (· ≤ i), LP.retargetρR ρR l := fun i => by
    rw [sum_filter_le_retargetρR]
    exact hR _ (by rw [val_castAdd_castSucc]; exact i.isLt)
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ0 hD'.1 (ρL := LP.retargetρL κ ρL ρR) (ρR := LP.retargetρR ρR)
  have hlife := GW0.ae_lifetime_eq_top_of_neg_two_lt hD'.1 (fun i _ => hL' i) (fun i _ => hR' i) hE₀
  have h13 := hT13 hκ0 hD'.1 hE₀
  have hgb : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → VL₀ (Fin.natAdd nL 0) t ω < W₀ t ω := by
    refine Supp8.GB5.gb5_left hκ0 hD'.1 (Fin.natAdd nL 0) (fun i _ _ => hL' i) (fun i hi _ => ?_) ?_ hE₀
    · induction i using Fin.addCases with
      | left i =>
        exfalso
        rw [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hi
        have := i.isLt; omega
      | right k' => exact hfar k'
    · obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
      have hp := LP.retargetPos_pos hmono hR0 hj
      have e0 : (⟨0, Fin.pos (Fin.natAdd nL (0 : Fin (m + 1)))⟩ : Fin (nL + (m + 1))) =
          Fin.castAdd (m + 1) ⟨0, hnL⟩ := Fin.ext rfl
      rw [e0]
      simp only [LP.retargetXL, Fin.append_left, Fin.append_right, Fin.cons_zero]
      exact Sec7.neg_one_lt_targetChangeReal hp (lt_of_le_of_lt (hL0 _) hp)
  have hW := ae_mem_lawSetS_of_ae hκ0 hsep' hE₀
    (S := (fullTraceSet ∩ {x : XCode (nL + (m + 1)) j | cζ x = ⊤}) ∩ gapPosSet (Fin.natAdd nL 0))
    (Ψ := fun w vL _ τ => (FullTrace w τ ∧ τ = ⊤) ∧ GapPos (Fin.natAdd nL 0) w vL τ)
    ((measurableSet_fullTraceSet.inter (measurableSet_eq_fun measurable_cζ measurable_const)).inter
      (measurableSet_gapPosSet _))
    (fun x hx hl => by
      show (x ∈ fullTraceSet ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x) ↔
        (FullTrace (cw x) (cζ x) ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x)
      rw [mem_fullTraceSet_iff x hx hl])
    (fun w w' vL vL' vR vR' τ h hw => ⟨⟨fullTrace_congr w w' τ (fun t ht => (h t ht).1) hw.1.1, hw.1.2⟩,
      gapPos_congr _ w w' vL vL' vR vR' τ h hw.2⟩)
    (by
      filter_upwards [hlife, hgb, h13, hE₀.ae_isIntegratedSLEPath] with ω hl hg h13 hp
      have hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω := fun t => by rw [hl]; exact ENNReal.coe_lt_top
      refine ⟨⟨fullTrace_of_traceEvent h13.2, hl⟩, ?_⟩
      rw [hl]
      exact gapPos_of_pos _ (continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => hc t))
        (continuousOn_univ.1 ((hp.isForcePath.continuousOn_vL _).mono fun t _ => hc t)) fun t => hg t (hc t))
  obtain ⟨𝓘, β, τ, -, hτ, hloc⟩ := retargetEvolutionStatement.{u} P 𝓕 xL xR ρL ρR W VL VR B ζ hκ0 hD hj hE
  have hcode := ae_exists_code_of_upTo hloc hsep' hW
  have hcode' := Sec7.ae_of_ae_prod_fst (P := P) (Φ := fun ω => ∃ x ∈ CRel κ (LP.retargetXL xL xR) (LP.retargetXR xR)
      (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR),
      x ∈ (fullTraceSet ∩ {x : XCode (nL + (m + 1)) j | cζ x = ⊤}) ∩ gapPosSet (Fin.natAdd nL 0) ∧ τ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → newW xR (fun t => W t ω) (fun i t => VR i t ω) t = cw x t ∧
        (∀ i, newVL xR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) i t = cvL x i t) ∧
        ∀ i, newVR xR (fun t => W t ω) (fun i t => VR i t ω) i t = cvR x i t) hcode
  filter_upwards [hcode', hτ, hE.ae_isIntegratedSLEPath, hE.ae_tendsto_threshold hκ0, hη] with ω hc hτω hp hlim hηω
  obtain ⟨x, hxC, ⟨⟨hxtr, hxζ⟩, hxgap⟩, -, hag⟩ := hc
  have hxp : IsIntegratedSLEPath κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hxζ' : cζ x = ⊤ := hxζ
  have hcx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x := fun t => by rw [hxζ']; exact ENNReal.coe_lt_top
  have hwc : Continuous (cw x) := continuousOn_univ.1 (hxp.isForcePath.continuousOn_w.mono fun t _ => hcx t)
  have hgap' : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) ⊤ := by
    have h : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x) := hxgap
    rwa [hxζ'] at h
  have htrc : TraceEvent (cw x) ⊤ := by
    have hx1 : (cw x, cζ x) ∈ traceSet := hxtr.1
    have hx1' : ratVals (cw x) ∈ transientSet := by
      rcases hx1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hxζ' h
    obtain ⟨η', hη', htr⟩ := (mem_transientSet_iff hwc hxp.1).1 hx1'
    exact ⟨η', hη', fun _ => htr⟩
  exact visit_of_code hp hD hj hL (fun i hi => hR i (by
      rw [Fin.lt_def] at hi; simpa [LP.retargetIdx] using hi)) hlim hwc
    (continuousOn_univ.1 ((hxp.isForcePath.continuousOn_vL _).mono fun t _ => hcx t)) htrc hgap'
    (fun t ht => ⟨(hag t (by rw [hτω]; exact ht)).1, (hag t (by rw [hτω]; exact ht)).2.1 _⟩) hηω

end Core

end BR3Ref

end Theorem14

end InteractingSLE
