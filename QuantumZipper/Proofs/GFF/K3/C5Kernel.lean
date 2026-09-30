import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# GFF-K3, node C5 (via C5′): the limiting kernel `V_T` (AD-4) and item 5

Blueprint `blueprint/GFF_K3_BLUEPRINT.md` §3.C node C5 (item 5) and `blueprint/EXT_PP_BLUEPRINT.md`
§B (C5′).  For the forward centered Loewner flow `f_t = fwdMap W t`,

`V_T(a,b) := lim_{t ↑ min(τ_a, τ_b, T)} G_ℍ(f_t a, f_t b)`

(Sheffield, arXiv:1012.4797, Theorem 1.1 addendum, p. 12; the monotone limit of AD-4).  Since
`t ↦ G_ℍ(f_t a, f_t b)` is nonincreasing (FD-3, `FwdClock.antitoneOn_greenH_fwdMap`), the limit
is the infimum over the admissible times `vtIdx W T a b = {t ∈ [0,T] : t < τ_a, t < τ_b}`; we take
this infimum as the definition (`VTe`, in `ℝ≥0∞`, and `VT = VTe.toReal`) and prove:

* `tendsto_vtKer_VTe`: along any nondecreasing cofinal sequence of admissible times the kernels
  decrease to `VTe` (in particular along `t_n ↑ τ` inside a bubble swallowed at `τ ≤ T`,
  `tendsto_vtKer_bubble`), and `VTe = G(f_T a, f_T b)` when neither point is swallowed by `T`;
* **item 5** (`VTe_eq_zero_of_swallowTime_lt`, `VTe_eq_zero_of_swallowTime_ne`): `V_T(a,b) = 0`
  when the swallowing times differ and one of them is `≤ T`.

Item 5 follows the blueprint's argument ("continuity of `greenH` at `(0,w)`, `w ∈ ℍ`"), in the
slightly weaker form we need: only `Im f_t(a) → 0` as `t ↑ τ_a` (FD-2,
`FwdClock.exists_im_fwdMap_lt_of_swallowTime`, plus monotonicity of `Im f_t`) is used, together
with the elementary bound `G(x,y) ≤ 2 Im x Im y / |x − y|²` (own elementary proof, from
`|x − ȳ|² = |x − y|² + 4 Im x Im y` and `log u ≤ u − 1`).
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace QuantumZipper.K3

variable {W : ℝ → ℝ} {T : ℝ} {a b : ℂ}

/-- The admissible times for `V_T(a,b)`: `t ∈ [0,T]` before both swallowing times. -/
def vtIdx (W : ℝ → ℝ) (T : ℝ) (a b : ℂ) : Set ℝ :=
  {t | 0 ≤ t ∧ t ≤ T ∧ ENNReal.ofReal t < swallowTime W a ∧ ENNReal.ofReal t < swallowTime W b}

/-- The time-`t` kernel `G_ℍ(f_t a, f_t b)` as an extended nonnegative real. -/
def vtKer (W : ℝ → ℝ) (t : ℝ) (a b : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (greenH (fwdMap W t a) (fwdMap W t b))

/-- **AD-4's monotone limit** `V_T(a,b) = lim_{t ↑ min(τ_a,τ_b,T)} G_ℍ(f_t a, f_t b)`, defined
as the infimum over admissible times (the limit, by `tendsto_vtKer_VTe`). -/
def VTe (W : ℝ → ℝ) (T : ℝ) (a b : ℂ) : ℝ≥0∞ := ⨅ t ∈ vtIdx W T a b, vtKer W t a b

/-- Real-valued `V_T`. -/
def VT (W : ℝ → ℝ) (T : ℝ) (a b : ℂ) : ℝ := (VTe W T a b).toReal

theorem vtIdx_comm : vtIdx W T a b = vtIdx W T b a := by
  ext t; simp only [vtIdx, mem_ofPred_eq]; tauto

theorem vtKer_comm (t : ℝ) : vtKer W t a b = vtKer W t b a := by
  rw [vtKer, vtKer, greenH_symm]

theorem VTe_comm : VTe W T a b = VTe W T b a := by
  simp only [VTe, vtIdx_comm (a := a), vtKer_comm (a := a)]

/-- A point of `ℍ` not swallowed at time `t ≥ 0` has a solution on `[0,t]`. -/
theorem exists_sol_of_lt_swallowTime {z : ℂ} (hz : z ∈ H) {t : ℝ} (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t < swallowTime W z) : ∃ u, IsForwardSol W z t u :=
  exists_isForwardSol_of_not_mem_fwdHull ht hz fun h => (not_le.2 hlt) h.2

/-- `Im f_t(z)` is nonincreasing on `[0,t]` when `z` has a solution on `[0,t]`. -/
theorem im_fwdMap_antitoneOn (hW : Continuous W) {z : ℂ} (hz : z ∈ H) {t : ℝ}
    (hsol : ∃ u, IsForwardSol W z t u) :
    AntitoneOn (fun s => (fwdMap W s z).im) (Icc 0 t) ∧
      ∀ s ∈ Icc (0 : ℝ) t, 0 < (fwdMap W s z).im := by
  obtain ⟨u, hu⟩ := hsol
  exact im_isForwardSol_le hW hz (FwdClock.isForwardSol_fwdMap hW hz hu)

/-- FD-3 on admissible times, including the diagonal `a = b`. -/
theorem vtKer_antitoneOn (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) :
    AntitoneOn (fun t => vtKer W t a b) (vtIdx W T a b) := by
  intro s hs t ht hst
  have hsa := exists_sol_of_lt_swallowTime (W := W) ha ht.1 ht.2.2.1
  have hsb := exists_sol_of_lt_swallowTime (W := W) hb ht.1 ht.2.2.2
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hab : a = b
  · subst hab
    have key : ∀ x : ℂ, 0 < x.im → greenH x x = Real.log (2 * x.im) := by
      intro x hx
      have h1 : x - conj x = ((2 * x.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp; ring
      rw [greenH, sub_self, norm_zero, Real.log_zero, sub_zero, h1, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    obtain ⟨hanti, hpos⟩ := im_fwdMap_antitoneOn hW ha hsa
    rw [key _ (hpos t ⟨ht.1, le_rfl⟩), key _ (hpos s ⟨hs.1, hst⟩)]
    exact Real.log_le_log (by linarith [hpos t ⟨ht.1, le_rfl⟩])
      (by linarith [hanti ⟨hs.1, hst⟩ ⟨ht.1, le_rfl⟩ hst])
  · exact FwdClock.antitoneOn_greenH_fwdMap hW ha hb hab hsa hsb ⟨hs.1, hst⟩ ⟨ht.1, le_rfl⟩ hst

/-- Along a nondecreasing cofinal sequence of admissible times, `G(f_{t_n} a, f_{t_n} b) ↓ V_T`. -/
theorem tendsto_vtKer_VTe (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) {t : ℕ → ℝ}
    (hmono : Monotone t) (hmem : ∀ n, t n ∈ vtIdx W T a b)
    (hcof : ∀ s ∈ vtIdx W T a b, ∃ n, s ≤ t n) :
    Antitone (fun n => vtKer W (t n) a b) ∧
      Tendsto (fun n => vtKer W (t n) a b) atTop (𝓝 (VTe W T a b)) := by
  have hanti : Antitone (fun n => vtKer W (t n) a b) := fun m n hmn =>
    vtKer_antitoneOn hW ha hb (hmem m) (hmem n) (hmono hmn)
  refine ⟨hanti, ?_⟩
  convert tendsto_atTop_iInf hanti using 2
  refine le_antisymm (le_iInf fun n => iInf₂_le _ (hmem n)) (le_iInf₂ fun s hs => ?_)
  obtain ⟨n, hn⟩ := hcof s hs
  exact (iInf_le _ n).trans (vtKer_antitoneOn hW ha hb hs (hmem n) hn)

/-- Bubble case: `a, b` both swallowed at `τ ≤ T`, and `t_n ↑ τ` with `t_n < τ`. -/
theorem tendsto_vtKer_bubble (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) {τ : ℝ}
    (hτa : swallowTime W a = ENNReal.ofReal τ) (hτb : swallowTime W b = ENNReal.ofReal τ)
    (hτT : τ ≤ T) {t : ℕ → ℝ} (hmono : Monotone t) (h0 : ∀ n, 0 ≤ t n) (hlt : ∀ n, t n < τ)
    (hlim : Tendsto t atTop (𝓝 τ)) :
    Antitone (fun n => vtKer W (t n) a b) ∧
      Tendsto (fun n => vtKer W (t n) a b) atTop (𝓝 (VTe W T a b)) := by
  have hτ0 : 0 < τ := (h0 0).trans_lt (hlt 0)
  have hlt' : ∀ n, ENNReal.ofReal (t n) < ENNReal.ofReal τ := fun n =>
    (ENNReal.ofReal_lt_ofReal_iff hτ0).2 (hlt n)
  refine tendsto_vtKer_VTe hW ha hb hmono
    (fun n => ⟨h0 n, (hlt n).le.trans hτT, hτa ▸ hlt' n, hτb ▸ hlt' n⟩) fun s hs => ?_
  have hs' : s < τ := by
    have := hs.2.2.1; rw [hτa] at this; exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hs')).exists
  exact ⟨n, hn.le⟩

/-- `D_T` case: if neither point is swallowed by time `T ≥ 0`, `V_T(a,b) = G(f_T a, f_T b)`. -/
theorem VTe_eq_vtKer_of_lt (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) (hT : 0 ≤ T)
    (hTa : ENNReal.ofReal T < swallowTime W a) (hTb : ENNReal.ofReal T < swallowTime W b) :
    VTe W T a b = vtKer W T a b := by
  have hTm : T ∈ vtIdx W T a b := ⟨hT, le_rfl, hTa, hTb⟩
  exact le_antisymm (iInf₂_le _ hTm)
    (le_iInf₂ fun s hs => vtKer_antitoneOn hW ha hb hs hTm hs.2.1)

/-- Own elementary bound: `G_ℍ(x,y) ≤ 2 Im x Im y / |x − y|²` on `ℍ × ℍ` off the diagonal. -/
theorem greenH_le_im_mul_im {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) (hxy : x ≠ y) :
    greenH x y ≤ 2 * x.im * y.im / ‖x - y‖ ^ 2 := by
  have hB : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hsq : ‖x - conj y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * x.im * y.im := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    ring
  have hA : 0 < ‖x - conj y‖ := by
    have : 0 < ‖x - conj y‖ ^ 2 := by rw [hsq]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) fun h => by rw [← h] at this; simp at this
  have hq : 0 < (‖x - conj y‖ / ‖x - y‖) ^ 2 := by positivity
  have hlog : greenH x y = (1 / 2) * Real.log ((‖x - conj y‖ / ‖x - y‖) ^ 2) := by
    rw [greenH, Real.log_pow, Real.log_div hA.ne' hB.ne']; push_cast; ring
  rw [hlog]
  have h1 := Real.log_le_sub_one_of_pos hq
  have h2 : (‖x - conj y‖ / ‖x - y‖) ^ 2 - 1 = 4 * x.im * y.im / ‖x - y‖ ^ 2 := by
    rw [div_pow, hsq]; field_simp; ring
  rw [h2] at h1
  have : 2 * x.im * y.im / ‖x - y‖ ^ 2 = (1 / 2) * (4 * x.im * y.im / ‖x - y‖ ^ 2) := by ring
  rw [this]; linarith

/-- **Item 5.** If `a` is swallowed at `σ ≤ T` strictly before `b`, then `V_T(a,b) = 0`. -/
theorem VTe_eq_zero_of_swallowTime_lt (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H) {σ : ℝ}
    (hσ : swallowTime W a = ENNReal.ofReal σ) (hσT : σ ≤ T)
    (hab : ENNReal.ofReal σ < swallowTime W b) : VTe W T a b = 0 := by
  have hσ0 : 0 < σ := by
    have := swallowTime_pos hW ha; rw [hσ] at this; exact ENNReal.ofReal_pos.1 this
  have hbK : b ∈ H \ fwdHull W σ := ⟨hb, fun h => (not_le.2 hab) h.2⟩
  have hcont := FwdHolo.continuousOn_fwdMap_time hW hσ0.le hbK
  have hsolb := exists_sol_of_lt_swallowTime (W := W) hb hσ0.le hab
  have hposb := (im_fwdMap_antitoneOn hW hb hsolb).2
  set m := (fwdMap W σ b).im with hm
  have hm0 : 0 < m := hposb σ ⟨hσ0.le, le_rfl⟩
  set K := ‖fwdMap W σ b‖ + m / 4 with hK
  have hK0 : 0 < K := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1
    (hcont σ ⟨hσ0.le, le_rfl⟩) (m / 4) (by positivity)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  set c := min (m / 4) ((ε : ℝ) * m ^ 2 / (8 * K)) with hc
  have hc0 : 0 < c := lt_min (by positivity) (by have : (0 : ℝ) < ε := hε; positivity)
  obtain ⟨t0, ht00, ht0σ, ht0c⟩ := FwdClock.exists_im_fwdMap_lt_of_swallowTime hW ha hσ hc0
  set t := max t0 (σ - δ / 2) with htdef
  have ht0 : 0 ≤ t := ht00.trans (le_max_left _ _)
  have htσ : t < σ := max_lt ht0σ (by linarith)
  have htlt : ENNReal.ofReal t < ENNReal.ofReal σ := (ENNReal.ofReal_lt_ofReal_iff hσ0).2 htσ
  have htm : t ∈ vtIdx W T a b :=
    ⟨ht0, htσ.le.trans hσT, hσ ▸ htlt, htlt.trans hab⟩
  refine (iInf₂_le t htm).trans ?_
  have hsola := exists_sol_of_lt_swallowTime (W := W) ha ht0 (hσ ▸ htlt)
  obtain ⟨hantia, hposa⟩ := im_fwdMap_antitoneOn hW ha hsola
  have hxpos : 0 < (fwdMap W t a).im := hposa t ⟨ht0, le_rfl⟩
  have hxc : (fwdMap W t a).im < c :=
    lt_of_le_of_lt (hantia ⟨ht00, le_max_left _ _⟩ ⟨ht0, le_rfl⟩ (le_max_left _ _)) ht0c
  have hyclose : ‖fwdMap W t b - fwdMap W σ b‖ < m / 4 := by
    have := hball (x := t) ⟨ht0, htσ.le⟩ (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_right t0 (σ - δ / 2)])
    rwa [dist_eq_norm] at this
  have himdiff := Complex.abs_im_le_norm (fwdMap W t b - fwdMap W σ b)
  rw [Complex.sub_im, abs_le] at himdiff
  have hy1 : 3 * m / 4 ≤ (fwdMap W t b).im := by linarith [himdiff.1]
  have hyK : (fwdMap W t b).im ≤ K := by
    have := Complex.im_le_norm (fwdMap W t b)
    have := norm_sub_norm_le (fwdMap W t b) (fwdMap W σ b)
    linarith
  have hcm : c ≤ m / 4 := min_le_left _ _
  have hdist : m / 2 ≤ ‖fwdMap W t a - fwdMap W t b‖ := by
    have := Complex.abs_im_le_norm (fwdMap W t a - fwdMap W t b)
    rw [Complex.sub_im, abs_le] at this
    linarith [this.1]
  have hne : fwdMap W t a ≠ fwdMap W t b := fun h => by
    rw [h, sub_self, norm_zero] at hdist; linarith
  have hG := greenH_le_im_mul_im hxpos (by linarith) hne
  rw [vtKer, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (hG.trans ?_)
  have hD : 0 < ‖fwdMap W t a - fwdMap W t b‖ ^ 2 := pow_pos (by linarith) 2
  rw [div_le_iff₀ hD]
  have hce : c * (8 * K) ≤ (ε : ℝ) * m ^ 2 := by
    have := min_le_right (m / 4) ((ε : ℝ) * m ^ 2 / (8 * K))
    rw [← hc] at this
    rwa [le_div_iff₀ (by positivity)] at this
  have hsq : (m / 2) ^ 2 ≤ ‖fwdMap W t a - fwdMap W t b‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hdist 2
  have hε0 : (0 : ℝ) ≤ ε := hε.le
  calc 2 * (fwdMap W t a).im * (fwdMap W t b).im ≤ 2 * c * K := by
        have := mul_le_mul hxc.le hyK (by linarith) hc0.le
        nlinarith
    _ ≤ (ε : ℝ) * (m / 2) ^ 2 := by nlinarith
    _ ≤ (ε : ℝ) * ‖fwdMap W t a - fwdMap W t b‖ ^ 2 := mul_le_mul_of_nonneg_left hsq hε0

/-- **Item 5 (symmetric form).** Different swallowing times, one of them `≤ T`: `V_T = 0`. -/
theorem VTe_eq_zero_of_swallowTime_ne (hW : Continuous W) (ha : a ∈ H) (hb : b ∈ H)
    (hne : swallowTime W a ≠ swallowTime W b)
    (hle : min (swallowTime W a) (swallowTime W b) ≤ ENNReal.ofReal T) : VTe W T a b = 0 := by
  have key : ∀ {x y : ℂ}, x ∈ H → y ∈ H → swallowTime W x < swallowTime W y →
      swallowTime W x ≤ ENNReal.ofReal T → VTe W T x y = 0 := by
    intro x y hx hy hxy hxT
    have htop : swallowTime W x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxT
    have hT : 0 ≤ T := by
      by_contra h; push Not at h
      rw [ENNReal.ofReal_of_nonpos h.le] at hxT
      exact (swallowTime_pos hW hx).ne' (le_antisymm hxT bot_le)
    refine VTe_eq_zero_of_swallowTime_lt hW hx hy (ENNReal.ofReal_toReal htop).symm ?_
      (by rwa [ENNReal.ofReal_toReal htop])
    rwa [← ENNReal.ofReal_le_ofReal_iff hT, ENNReal.ofReal_toReal htop]
  rcases lt_or_gt_of_ne hne with h | h
  · exact key ha hb h (by rwa [min_eq_left h.le] at hle)
  · rw [VTe_comm]; exact key hb ha h (by rwa [min_eq_right h.le] at hle)

end QuantumZipper.K3
