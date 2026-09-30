import QuantumZipper.Proofs.Zipper.FlowRegSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, F1/F2 flow regularity: deterministic lemmas on the real forward flow

Tools for the aliveness of real points under the Loewner flow restarted at *every* time
(`FlowRegAlive.lean`). For a continuous driver `V` with `V 0 = 0`:

* `isForwardSol_shift`: the Loewner semigroup property at the level of solutions: a forward
  solution on `[0, a+T]` restarted at time `a` solves the forward equation for the restarted
  driver `s ↦ V (a + max s 0) − V a` from `v a` (Lawler, *Conformally invariant processes in the
  plane* (2005), §4.1, the flow property `g_{a+t} = g^{(a)}_t ∘ g_a`).
* `re_isForwardSol_real`: the real form of the equation for a real start.
* `re_sub_le_of_lt`: real solutions are `1`-Lipschitz in the initial point.
* `re_le_of_small`: a solution started in `(0, c]` stays below `c + 2M + 2a/c` up to time `a`,
  where `M ≥ sup_{[0,a]} |V|`.
* `exists_fwdMap_eq`: if every `y > 0` is alive up to time `a` and `c + 2M + 2a/c < x`, then
  `x = f_a(y)` for some `y > 0` (intermediate value theorem).

Own elementary proofs (standard one-dimensional ODE comparison estimates; searched mathlib and the
repository: only the order preservation `F1.isForwardSol_lt_of_lt` and realness/positivity
`im_isForwardSol_real`, `re_pos_isForwardSol_real` exist, which we use).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

variable {V : ℝ → ℝ}

/-- **Restarting a forward solution** (Loewner semigroup property for solutions). -/
theorem isForwardSol_shift {z : ℂ} {a T : ℝ} {v : ℝ → ℂ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hv : IsForwardSol V z (a + T) v) :
    IsForwardSol (fun s => V (a + max s 0) - V a) (v a) T (fun s => v (a + s)) := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) T, a + s ∈ Icc (0 : ℝ) (a + T) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ha' : a ∈ Icc (0 : ℝ) (a + T) := ⟨ha, by linarith⟩
  have hii : ∀ b c : ℝ, 0 ≤ b → b ≤ c → c ≤ a + T →
      IntervalIntegrable (fun s => 2 / v s) volume b c := fun b c hb hbc hc =>
    ((continuousOn_const.div hv.1 (fun s hs => (hv.2 s hs).1)).mono
      (by rw [uIcc_of_le hbc]; exact Icc_subset_Icc hb hc)).intervalIntegrable
  refine ⟨hv.1.comp (continuousOn_const.add continuousOn_id) (fun s hs => hmem s hs),
    fun t ht => ⟨(hv.2 _ (hmem t ht)).1, ?_⟩⟩
  have e1 := (hv.2 _ (hmem t ht)).2
  have e0 := (hv.2 a ha').2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hii 0 a le_rfl ha ha'.2)
    (hii a (a + t) ha (by linarith [ht.1]) (hmem t ht).2)
  have hshift : (∫ s in (0 : ℝ)..t, 2 / v (a + s)) = ∫ s in a..a + t, 2 / v s := by
    rw [intervalIntegral.integral_comp_add_left (fun s => 2 / v s) a, add_zero]
  simp only [max_eq_left ht.1]
  rw [hshift, e1, ← hsplit, e0]
  push_cast; ring

/-- **Real form of the forward equation** for a real start. -/
theorem re_isForwardSol_real (hV : Continuous V) {x T : ℝ} (hT : 0 ≤ T) {v : ℝ → ℂ}
    (hv : IsForwardSol V (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (v t).re = x - V t + ∫ s in (0 : ℝ)..t, 2 / (v s).re := by
  have him := im_isForwardSol_real hV hT hv
  have hcongr : (∫ s in (0 : ℝ)..t, 2 / v s) = ∫ s in (0 : ℝ)..t, ((2 / (v s).re : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    have hvs : v s = ((v s).re : ℂ) := Complex.ext (by simp) (by simp [him s hs'])
    calc 2 / v s = 2 / ((v s).re : ℂ) := by conv_lhs => rw [hvs]
      _ = ((2 / (v s).re : ℝ) : ℂ) := by push_cast; rfl
  have e := congrArg Complex.re (hv.2 t ht).2
  rw [hcongr, intervalIntegral.integral_ofReal] at e
  simpa using e

/-- **`1`-Lipschitz dependence on the initial point** for real starts `0 < y < y'`. -/
theorem re_sub_le_of_lt (hV : Continuous V) (hV0 : V 0 = 0) {y y' T : ℝ} (hT : 0 ≤ T)
    (hy : 0 < y) (hyy : y < y') {v v' : ℝ → ℂ} (hv : IsForwardSol V (y : ℂ) T v)
    (hv' : IsForwardSol V (y' : ℂ) T v') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (v' t).re - (v t).re ≤ y' - y := by
  have hpos := re_pos_isForwardSol_real hV hT hv (by rw [hV0]; exact hy)
  have hpos' := re_pos_isForwardSol_real hV hT hv' (by rw [hV0]; linarith)
  have hlt := isForwardSol_lt_of_lt hT hyy hv hv'
  rw [re_isForwardSol_real hV hT hv ht, re_isForwardSol_real hV hT hv' ht]
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hu : uIcc 0 t ⊆ Icc 0 T := by rw [uIcc_of_le ht.1]; exact hsub
  have hc : ContinuousOn (fun s => (v s).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hv.1
  have hc' : ContinuousOn (fun s => (v' s).re) (Icc 0 T) :=
    Complex.continuous_re.comp_continuousOn hv'.1
  have hi : IntervalIntegrable (fun s => 2 / (v s).re) volume 0 t :=
    ((continuousOn_const.div hc fun s hs => (hpos s hs).ne').mono hu).intervalIntegrable
  have hi' : IntervalIntegrable (fun s => 2 / (v' s).re) volume 0 t :=
    ((continuousOn_const.div hc' fun s hs => (hpos' s hs).ne').mono hu).intervalIntegrable
  have hle : (∫ s in (0 : ℝ)..t, 2 / (v' s).re) ≤ ∫ s in (0 : ℝ)..t, 2 / (v s).re :=
    intervalIntegral.integral_mono_on ht.1 hi' hi fun s hs =>
      div_le_div_of_nonneg_left (by norm_num) (hpos s (hsub hs)) (hlt s (hsub hs)).le
  linarith

/-- **Small starts stay small**: a real solution from `y ∈ (0, c]` satisfies
`f_a(y) ≤ c + 2M + 2a/c` when `|V| ≤ M` on `[0,a]`. -/
theorem re_le_of_small (hV : Continuous V) (hV0 : V 0 = 0) {y a c M : ℝ} (ha : 0 ≤ a)
    (hy : 0 < y) (hyc : y ≤ c) (hM : ∀ s ∈ Icc (0 : ℝ) a, |V s| ≤ M) {v : ℝ → ℂ}
    (hv : IsForwardSol V (y : ℂ) a v) :
    (v a).re ≤ c + 2 * M + 2 * a / c := by
  have hc0 : 0 < c := hy.trans_le hyc
  have hpos := re_pos_isForwardSol_real hV ha hv (by rw [hV0]; exact hy)
  have hcont : ContinuousOn (fun s => (v s).re) (Icc 0 a) :=
    Complex.continuous_re.comp_continuousOn hv.1
  set S : Set ℝ := Icc (0 : ℝ) a ∩ (fun s => (v s).re) ⁻¹' Iic c with hS
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, ha⟩, ?_⟩
    show (v 0).re ≤ c
    rw [re_isForwardSol_real hV ha hv ⟨le_rfl, ha⟩]
    simp [hV0, hyc]
  have hbdd : BddAbove S := ⟨a, fun s hs => hs.1.2⟩
  set σ := sSup S with hσ
  have hσS : σ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hbdd
  have hσ0 : 0 ≤ σ := hσS.1.1
  have hσa : σ ≤ a := hσS.1.2
  have hgt : ∀ s ∈ Ioo σ a, c < (v s).re := fun s hs => by
    by_contra h
    push Not at h
    exact absurd (le_csSup hbdd ⟨⟨hσ0.trans hs.1.le, hs.2.le⟩, h⟩) (not_le.2 hs.1)
  have hii : ∀ b d : ℝ, 0 ≤ b → b ≤ d → d ≤ a →
      IntervalIntegrable (fun s => 2 / (v s).re) volume b d := fun b d hb hbd hd =>
    ((continuousOn_const.div hcont fun s hs => (hpos s hs).ne').mono
      (by rw [uIcc_of_le hbd]; exact Icc_subset_Icc hb hd)).intervalIntegrable
  have ea := re_isForwardSol_real hV ha hv ⟨ha, le_rfl⟩
  have eσ := re_isForwardSol_real hV ha hv hσS.1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hii 0 σ le_rfl hσ0 hσa)
    (hii σ a hσ0 hσa le_rfl)
  have hint : (∫ s in σ..a, 2 / (v s).re) ≤ ∫ _ in σ..a, 2 / c :=
    intervalIntegral.integral_mono_on_of_le_Ioo hσa (hii σ a hσ0 hσa le_rfl)
      intervalIntegrable_const fun s hs => div_le_div_of_nonneg_left (by norm_num) hc0 (hgt s hs).le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hVa := abs_le.1 (hM a ⟨ha, le_rfl⟩)
  have hVσ := abs_le.1 (hM σ hσS.1)
  have hσc : (v σ).re ≤ c := hσS.2
  have hfrac : (a - σ) * (2 / c) = 2 * a / c - 2 * σ / c := by field_simp
  have hσc' : 0 ≤ 2 * σ / c := by positivity
  linarith

/-- **Hitting a prescribed real point**: if every `y > 0` is alive up to time `a` and
`c + 2M + 2a/c < x` (with `c > 0`, `|V| ≤ M` on `[0,a]`), then `f_a(y) = x` for some `y > 0`. -/
theorem exists_fwdMap_eq (hV : Continuous V) (hV0 : V 0 = 0) {a c M x : ℝ} (ha : 0 ≤ a)
    (hc : 0 < c) (hM : ∀ s ∈ Icc (0 : ℝ) a, |V s| ≤ M) (hx : c + 2 * M + 2 * a / c < x)
    (halive : ∀ y : ℝ, 0 < y → ∃ v, IsForwardSol V (y : ℂ) a v) :
    ∃ y : ℝ, 0 < y ∧ fwdMap V a y = x := by
  set g : ℝ → ℝ := fun y => (fwdMap V a y).re with hgdef
  have hg : ∀ y : ℝ, 0 < y → ∃ v, IsForwardSol V (y : ℂ) a v ∧ fwdMap V a y = v a :=
    fun y hy => by
      obtain ⟨v, hv⟩ := halive y hy
      exact ⟨v, hv, fwdMap_eq_of_isForwardSol hv ⟨ha, le_rfl⟩⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ha⟩)
  have hac : 0 ≤ 2 * a / c := by positivity
  have hlip : ∀ y y' : ℝ, 0 < y → y ≤ y' → g y' - g y ≤ y' - y ∧ g y ≤ g y' := by
    intro y y' hy hyy
    rcases eq_or_lt_of_le hyy with h | h
    · subst h; simp
    obtain ⟨v, hv, he⟩ := hg y hy
    obtain ⟨v', hv', he'⟩ := hg y' (hy.trans h)
    simp only [hgdef, he, he']
    exact ⟨re_sub_le_of_lt hV hV0 ha hy h hv hv' ⟨ha, le_rfl⟩,
      (isForwardSol_lt_of_lt ha h hv hv' a ⟨ha, le_rfl⟩).le⟩
  have hcont : ContinuousOn g (Icc c (x + M)) := by
    refine LipschitzOnWith.continuousOn (K := 1) (LipschitzOnWith.of_dist_le_mul
      fun y hy y' hy' => ?_)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total y y' with h | h
    · obtain ⟨h1, h2⟩ := hlip y y' (hc.trans_le hy.1) h
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      exact h1
    · obtain ⟨h1, h2⟩ := hlip y' y (hc.trans_le hy'.1) h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      exact h1
  have hgc : g c < x := by
    obtain ⟨v, hv, he⟩ := hg c hc
    simp only [hgdef, he]
    linarith [re_le_of_small hV hV0 ha hc le_rfl hM hv]
  have hgx : x ≤ g (x + M) := by
    obtain ⟨v, hv, he⟩ := hg (x + M) (by linarith)
    simp only [hgdef, he]
    rw [re_isForwardSol_real hV ha hv ⟨ha, le_rfl⟩]
    have hpos := re_pos_isForwardSol_real hV ha hv (by rw [hV0]; linarith)
    have hI : 0 ≤ ∫ s in (0 : ℝ)..a, 2 / (v s).re :=
      intervalIntegral.integral_nonneg ha fun s hs => (div_pos two_pos (hpos s hs)).le
    have hVa := (abs_le.1 (hM a ⟨ha, le_rfl⟩)).2
    linarith
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc (by linarith : c ≤ x + M) hcont ⟨hgc.le, hgx⟩
  refine ⟨y, hc.trans_le hy.1, ?_⟩
  obtain ⟨v, hv, he⟩ := hg y (hc.trans_le hy.1)
  have him := im_isForwardSol_real hV ha hv a ⟨ha, le_rfl⟩
  have hre : (v a).re = x := by rw [← hgy]; simp only [hgdef, he]
  rw [he]
  exact Complex.ext (by simp [hre]) (by simp [him])

end F1
end QuantumZipper
