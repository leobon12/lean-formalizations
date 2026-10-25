import LQGMetric.Topo.RectMeet
import LQGMetric.Topo.Shortcut
import LQGMetric.Topo.CrosscutRadial
import Mathlib.Topology.MetricSpace.CoveringNumbers




set_option autoImplicit false

open Complex Set Metric
open scoped ComplexConjugate

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

lemma key_identity (z m u : ℂ) (hm : m * conj m = 1) (hu : u * conj u = 1) :
    conj u * (z - m * u) * conj (z - m * conj u) =
      conj u * (z * conj z) - z * conj m - conj z * m + u := by
  simp only [map_sub, map_mul, Complex.conj_conj]
  linear_combination (-(z * conj m) - m * conj z + u * (m * conj m)) * hu + u * hm

lemma exp_mul_conj (x : ℝ) : cexp (x * I) * conj (cexp (x * I)) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp

 
noncomputable def g (m u z : ℂ) : ℂ := I * conj u * (z - m * u) / (z - m * conj u)

lemma g_eq (m u z : ℂ) :
    g m u z = I * (conj u * (z - m * u) * conj (z - m * conj u)) /
      ((Complex.normSq (z - m * conj u) : ℝ) : ℂ) := by
  unfold g
  rw [div_eq_mul_inv, Complex.inv_def, div_eq_mul_inv]
  push_cast
  ring

lemma w_im (z m u : ℂ) (hm : m * conj m = 1) (hu : u * conj u = 1) :
    (conj u * (z - m * u) * conj (z - m * conj u)).im = u.im * (1 - Complex.normSq z) := by
  rw [key_identity z m u hm hu]
  have h1 : (z * conj m + conj z * m).im = 0 := by
    have : conj z * m = conj (z * conj m) := by simp [map_mul]
    rw [this]; simp [Complex.conj_im]; ring
  have h2 : (conj u * (z * conj z)).im = - u.im * Complex.normSq z := by
    rw [Complex.mul_conj]; simp [Complex.conj_im]
  have : conj u * (z * conj z) - z * conj m - conj z * m + u =
      conj u * (z * conj z) - (z * conj m + conj z * m) + u := by ring
  rw [this, Complex.add_im, Complex.sub_im, h1, h2]; ring

lemma w_re (z m u : ℂ) (hm : m * conj m = 1) (hu : u * conj u = 1) :
    (conj u * (z - m * u) * conj (z - m * conj u)).re =
      u.re * (1 + Complex.normSq z) - 2 * (z * conj m).re := by
  rw [key_identity z m u hm hu]
  have h1 : (z * conj m + conj z * m).re = 2 * (z * conj m).re := by
    have : conj z * m = conj (z * conj m) := by simp [map_mul]
    rw [this, Complex.add_re, Complex.conj_re]; ring
  have h2 : (conj u * (z * conj z)).re = u.re * Complex.normSq z := by
    rw [Complex.mul_conj]; simp [Complex.conj_re]
  have : conj u * (z * conj z) - z * conj m - conj z * m + u =
      conj u * (z * conj z) - (z * conj m + conj z * m) + u := by ring
  rw [this, Complex.add_re, Complex.sub_re, h1, h2]; ring

lemma g_re (m u z : ℂ) (hm : m * conj m = 1) (hu : u * conj u = 1) :
    (g m u z).re = u.im * (Complex.normSq z - 1) / Complex.normSq (z - m * conj u) := by
  rw [g_eq, Complex.div_ofReal_re]
  rw [show (I * (conj u * (z - m * u) * conj (z - m * conj u))).re
      = -(conj u * (z - m * u) * conj (z - m * conj u)).im by simp [Complex.mul_re]]
  rw [w_im z m u hm hu]; ring

lemma g_im (m u z : ℂ) (hm : m * conj m = 1) (hu : u * conj u = 1) :
    (g m u z).im = (u.re * (1 + Complex.normSq z) - 2 * (z * conj m).re) /
      Complex.normSq (z - m * conj u) := by
  rw [g_eq, Complex.div_ofReal_im]
  rw [show (I * (conj u * (z - m * u) * conj (z - m * conj u))).im
      = (conj u * (z - m * u) * conj (z - m * conj u)).re by simp [Complex.mul_im]]
  rw [w_re z m u hm hu]


lemma conj_exp (x : ℝ) : conj (cexp (x * I)) = cexp ((-x : ℝ) * I) := by
  rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

lemma exp_re_mul_conj (φ μ : ℝ) : (cexp (φ * I) * conj (cexp (μ * I))).re = Real.cos (φ - μ) := by
  rw [conj_exp, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.exp_ofReal_mul_I_re]
  ring_nf

 
lemma cos_arc_one {θ₁ φ₁ θ₂ : ℝ} (h1 : θ₁ < φ₁) (h2 : φ₁ < θ₂) (h' : θ₂ < θ₁ + 2 * Real.pi) :
    Real.cos ((θ₁ - θ₂) / 2) < Real.cos (φ₁ - (θ₁ + θ₂) / 2) := by
  have hx : |φ₁ - (θ₁ + θ₂) / 2| < (θ₂ - θ₁) / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (φ₁ - (θ₁ + θ₂) / 2))
    (by linarith : (θ₂ - θ₁) / 2 ≤ Real.pi) hx
  rw [Real.cos_abs] at this
  rw [show (θ₁ - θ₂) / 2 = -((θ₂ - θ₁) / 2) by ring, Real.cos_neg]
  exact this

lemma cos_arc_two {θ₁ θ₂ φ₂ : ℝ} (h1 : θ₁ < θ₂) (h3 : θ₂ < φ₂) (h4 : φ₂ < θ₁ + 2 * Real.pi) :
    Real.cos (φ₂ - (θ₁ + θ₂) / 2) < Real.cos ((θ₁ - θ₂) / 2) := by
  rw [show (θ₁ - θ₂) / 2 = -((θ₂ - θ₁) / 2) by ring, Real.cos_neg]
  set x := φ₂ - (θ₁ + θ₂) / 2 with hx
  have hlo : (θ₂ - θ₁) / 2 < x := by rw [hx]; linarith
  have hhi : x < 2 * Real.pi - (θ₂ - θ₁) / 2 := by rw [hx]; linarith
  rcases le_or_gt x Real.pi with hle | hlt
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) hle hlo
  · rw [← Real.cos_two_pi_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)

lemma exp_mul_I_ne {a b : ℝ} (h1 : a < b) (h2 : b < a + 2 * Real.pi) :
    cexp (a * I) ≠ cexp (b * I) := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  have hz : ((a : ℂ) - b - n * (2 * Real.pi)) * I = 0 := by linear_combination hn
  have hz' : ((a - b - n * (2 * Real.pi) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.1 hz with h0 | h0
    · push_cast; exact h0
    · exact absurd h0 Complex.I_ne_zero
  have hr : a - b - n * (2 * Real.pi) = 0 := by exact_mod_cast hz'
  have hpi := Real.pi_pos
  have h3 : (n : ℝ) < 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h4 : (-1 : ℝ) < n := by
    by_contra hc; push Not at hc; nlinarith
  have h5 : n < 0 := by exact_mod_cast h3
  have h6 : -1 < n := by exact_mod_cast h4
  omega

noncomputable def mm (θ₁ θ₂ : ℝ) : ℂ := cexp (((θ₁ + θ₂) / 2 : ℝ) * I)
noncomputable def uu (θ₁ θ₂ : ℝ) : ℂ := cexp (((θ₁ - θ₂) / 2 : ℝ) * I)

lemma mm_uu (θ₁ θ₂ : ℝ) : mm θ₁ θ₂ * uu θ₁ θ₂ = cexp (θ₁ * I) := by
  unfold mm uu; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma mm_conj_uu (θ₁ θ₂ : ℝ) : mm θ₁ θ₂ * conj (uu θ₁ θ₂) = cexp (θ₂ * I) := by
  unfold mm uu; rw [conj_exp, ← Complex.exp_add]; congr 1; push_cast; ring

lemma hmm (θ₁ θ₂ : ℝ) : mm θ₁ θ₂ * conj (mm θ₁ θ₂) = 1 := exp_mul_conj _
lemma huu (θ₁ θ₂ : ℝ) : uu θ₁ θ₂ * conj (uu θ₁ θ₂) = 1 := exp_mul_conj _

 
noncomputable def G (θ₁ θ₂ : ℝ) (z : ℂ) : ℂ := g (mm θ₁ θ₂) (uu θ₁ θ₂) z

lemma G_re_nonneg {θ₁ θ₂ : ℝ} (h1 : θ₁ < θ₂) (h' : θ₂ < θ₁ + 2 * Real.pi) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : 0 ≤ (G θ₁ θ₂ z).re := by
  unfold G
  rw [g_re _ _ _ (hmm θ₁ θ₂) (huu θ₁ θ₂)]
  have hu : (uu θ₁ θ₂).im = Real.sin ((θ₁ - θ₂) / 2) := by
    unfold uu; rw [Complex.exp_ofReal_mul_I_im]
  have hs : Real.sin ((θ₁ - θ₂) / 2) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hn : Complex.normSq z ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  rw [hu]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  nlinarith

lemma G_eq_zero {θ₁ θ₂ : ℝ} {z : ℂ} (hzq : z ≠ cexp (θ₂ * I)) (h0 : G θ₁ θ₂ z = 0) :
    z = cexp (θ₁ * I) := by
  unfold G g at h0
  rw [mm_conj_uu, mm_uu] at h0
  have hd : z - cexp (θ₂ * I) ≠ 0 := sub_ne_zero.2 hzq
  have hu : conj (uu θ₁ θ₂) ≠ 0 := by
    intro h; have := huu θ₁ θ₂; rw [h, mul_zero] at this; exact zero_ne_one this
  rcases div_eq_zero_iff.1 h0 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd h Complex.I_ne_zero
      · exact absurd h hu
    · exact sub_eq_zero.1 h
  · exact absurd h hd

lemma G_injOn {θ₁ θ₂ : ℝ} (h1 : θ₁ < θ₂) (h' : θ₂ < θ₁ + 2 * Real.pi) {z w : ℂ}
    (hz : z ≠ cexp (θ₂ * I)) (hw : w ≠ cexp (θ₂ * I)) (h : G θ₁ θ₂ z = G θ₁ θ₂ w) : z = w := by
  unfold G g at h
  rw [mm_conj_uu, mm_uu] at h
  have hz' : z - cexp (θ₂ * I) ≠ 0 := sub_ne_zero.2 hz
  have hw' : w - cexp (θ₂ * I) ≠ 0 := sub_ne_zero.2 hw
  have hu : I * conj (uu θ₁ θ₂) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    intro h; have := huu θ₁ θ₂; rw [h, mul_zero] at this; exact zero_ne_one this
  rw [div_eq_div_iff hz' hw'] at h
  have hpq : cexp (θ₁ * I) - cexp (θ₂ * I) ≠ 0 := sub_ne_zero.2 (exp_mul_I_ne h1 h')
  have key : (I * conj (uu θ₁ θ₂)) * ((z - w) * (cexp (θ₁ * I) - cexp (θ₂ * I))) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hu
  · rcases mul_eq_zero.1 h0 with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hpq

lemma G_norm (θ₁ θ₂ : ℝ) (z : ℂ) :
    ‖G θ₁ θ₂ z‖ = ‖z - cexp (θ₁ * I)‖ / ‖z - cexp (θ₂ * I)‖ := by
  unfold G g
  rw [mm_conj_uu, mm_uu, norm_div, norm_mul, norm_mul, Complex.norm_I]
  have : ‖conj (uu θ₁ θ₂)‖ = 1 := by
    rw [Complex.norm_conj]; unfold uu; exact Complex.norm_exp_ofReal_mul_I _
  rw [this]; ring

lemma G_circle_re (θ₁ θ₂ φ : ℝ) : (G θ₁ θ₂ (cexp (φ * I))).re = 0 := by
  unfold G
  rw [g_re _ _ _ (hmm θ₁ θ₂) (huu θ₁ θ₂)]
  have : Complex.normSq (cexp (φ * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  rw [this]; simp

lemma G_circle_im (θ₁ θ₂ φ : ℝ) : (G θ₁ θ₂ (cexp (φ * I))).im =
    2 * (Real.cos ((θ₁ - θ₂) / 2) - Real.cos (φ - (θ₁ + θ₂) / 2)) /
      Complex.normSq (cexp (φ * I) - cexp (θ₂ * I)) := by
  unfold G
  rw [g_im _ _ _ (hmm θ₁ θ₂) (huu θ₁ θ₂)]
  have h1 : Complex.normSq (cexp (φ * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  have h2 : (uu θ₁ θ₂).re = Real.cos ((θ₁ - θ₂) / 2) := by
    unfold uu; rw [Complex.exp_ofReal_mul_I_re]
  have h3 : (cexp (φ * I) * conj (mm θ₁ θ₂)).re = Real.cos (φ - (θ₁ + θ₂) / 2) := by
    unfold mm; exact exp_re_mul_conj φ _
  rw [h1, h2, h3, mm_conj_uu]; ring

lemma arg_G_one {θ₁ φ₁ θ₂ : ℝ} (h1 : θ₁ < φ₁) (h2 : φ₁ < θ₂) (h' : θ₂ < θ₁ + 2 * Real.pi) :
    (G θ₁ θ₂ (cexp (φ₁ * I))).arg = -(Real.pi / 2) := by
  rw [Complex.arg_eq_neg_pi_div_two_iff]
  refine ⟨G_circle_re _ _ _, ?_⟩
  rw [G_circle_im]
  have hne : cexp (φ₁ * I) - cexp (θ₂ * I) ≠ 0 :=
    sub_ne_zero.2 (exp_mul_I_ne h2 (by linarith))
  have hpos : 0 < Complex.normSq (cexp (φ₁ * I) - cexp (θ₂ * I)) := Complex.normSq_pos.2 hne
  have := cos_arc_one h1 h2 h'
  apply div_neg_of_neg_of_pos _ hpos
  linarith

lemma arg_G_two {θ₁ θ₂ φ₂ : ℝ} (h1 : θ₁ < θ₂) (h3 : θ₂ < φ₂) (h4 : φ₂ < θ₁ + 2 * Real.pi) :
    (G θ₁ θ₂ (cexp (φ₂ * I))).arg = Real.pi / 2 := by
  rw [Complex.arg_eq_pi_div_two_iff]
  refine ⟨G_circle_re _ _ _, ?_⟩
  rw [G_circle_im]
  have hne : cexp (φ₂ * I) - cexp (θ₂ * I) ≠ 0 := by
    refine sub_ne_zero.2 (fun h => exp_mul_I_ne h3 (by linarith) h.symm)
  have hpos : 0 < Complex.normSq (cexp (φ₂ * I) - cexp (θ₂ * I)) := Complex.normSq_pos.2 hne
  have := cos_arc_two h1 h3 h4
  apply div_pos _ hpos
  linarith

 

theorem dcl_unit {θ₁ φ₁ θ₂ φ₂ : ℝ} (h1 : θ₁ < φ₁) (h2 : φ₁ < θ₂) (h3 : θ₂ < φ₂)
    (h4 : φ₂ < θ₁ + 2 * Real.pi) {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hαD : ∀ t ∈ Icc (0:ℝ) 1, ‖α t‖ ≤ 1) (hβD : ∀ t ∈ Icc (0:ℝ) 1, ‖β t‖ ≤ 1)
    (hα0 : α 0 = cexp (θ₁ * I)) (hα1 : α 1 = cexp (θ₂ * I))
    (hβ0 : β 0 = cexp (φ₁ * I)) (hβ1 : β 1 = cexp (φ₂ * I)) :
    ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, α s = β t := by
  by_contra hno
  push Not at hno
  have h12 : θ₁ < θ₂ := h1.trans h2
  have h2' : θ₂ < θ₁ + 2 * Real.pi := h3.trans h4
  set p := cexp (θ₁ * I) with hp
  set q := cexp (θ₂ * I) with hq
  have hpq : p ≠ q := exp_mul_I_ne h12 h2'
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1' : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hβp : ∀ t ∈ Icc (0:ℝ) 1, β t ≠ p := fun t ht h => hno 0 h0 t ht (by rw [hα0, h])
  have hβq : ∀ t ∈ Icc (0:ℝ) 1, β t ≠ q := fun t ht h => hno 1 h1' t ht (by rw [hα1, h])
  
  set F : ℂ → ℂ := fun z => Complex.log (G θ₁ θ₂ z) with hF
  have hslit : ∀ z, ‖z‖ ≤ 1 → z ≠ p → z ≠ q → G θ₁ θ₂ z ∈ slitPlane := by
    intro z hz hzp hzq
    rw [Complex.mem_slitPlane_iff]
    rcases (G_re_nonneg h12 h2' hz).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · right; intro him
      exact hzp (G_eq_zero hzq (Complex.ext (by rw [← heq]; rfl) (by rw [him]; rfl)))
  have hGcont : ∀ z, z ≠ q → ContinuousAt (G θ₁ θ₂) z := by
    intro z hzq
    have e : G θ₁ θ₂ = fun w => I * conj (uu θ₁ θ₂) * (w - p) / (w - q) := by
      funext w; unfold G g; rw [mm_conj_uu, mm_uu]
    rw [e]
    exact (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hzq)
  have hFcont : ∀ z, ‖z‖ ≤ 1 → z ≠ p → z ≠ q → ContinuousAt F z := fun z hz hzp hzq =>
    (hGcont z hzq).clog (hslit z hz hzp hzq)
  have hFim : ∀ z, ‖z‖ ≤ 1 → (F z).im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro z hz
    simp only [hF, Complex.log_im]
    exact abs_le.1 (Complex.abs_arg_le_pi_div_two_iff.2 (G_re_nonneg h12 h2' hz))
  have hFre : ∀ z, (F z).re = Real.log (‖z - p‖ / ‖z - q‖) := by
    intro z; simp only [hF, Complex.log_re, G_norm]; rfl
  have hFinj : ∀ z w, z ≠ p → z ≠ q → w ≠ p → w ≠ q → F z = F w → z = w := by
    intro z w hzp hzq hwp hwq h
    have hGz : G θ₁ θ₂ z ≠ 0 := fun h0 => hzp (G_eq_zero hzq h0)
    have hGw : G θ₁ θ₂ w ≠ 0 := fun h0 => hwp (G_eq_zero hwq h0)
    have := congrArg cexp h
    simp only [hF, Complex.exp_log hGz, Complex.exp_log hGw] at this
    exact G_injOn h12 h2' hzq hwq this
  
  set T0 := Icc (0:ℝ) 1 ∩ α ⁻¹' {p} with hT0
  have hT0c : IsClosed T0 := hα.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hT0b : BddAbove T0 := ⟨1, fun x hx => hx.1.2⟩
  have ht0 : sSup T0 ∈ T0 := hT0c.csSup_mem ⟨0, h0, hα0⟩ hT0b
  set t₀ := sSup T0 with ht₀
  set T1 := Icc t₀ 1 ∩ α ⁻¹' {q} with hT1
  have hT1c : IsClosed T1 := (hα.mono (Icc_subset_Icc ht0.1.1 le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_singleton
  have hT1b : BddBelow T1 := ⟨t₀, fun x hx => hx.1.1⟩
  have ht1 : sInf T1 ∈ T1 := hT1c.csInf_mem ⟨1, ⟨ht0.1.2, le_rfl⟩, hα1⟩ hT1b
  set t₁ := sInf T1 with ht₁
  have hαt0 : α t₀ = p := ht0.2
  have hαt1 : α t₁ = q := ht1.2
  have ht01 : t₀ < t₁ := by
    rcases ht1.1.1.lt_or_eq with h | h
    · exact h
    · exact absurd (hαt0.symm.trans (h ▸ hαt1)) hpq
  have hsub : Ioo t₀ t₁ ⊆ Icc (0:ℝ) 1 := fun x hx => ⟨ht0.1.1.trans hx.1.le, hx.2.le.trans ht1.1.2⟩
  have hmidp : ∀ s ∈ Ioo t₀ t₁, α s ≠ p := by
    intro s hs h
    have : s ≤ t₀ := le_csSup hT0b ⟨hsub hs, h⟩
    linarith [hs.1]
  have hmidq : ∀ s ∈ Ioo t₀ t₁, α s ≠ q := by
    intro s hs h
    have : t₁ ≤ s := csInf_le hT1b ⟨⟨hs.1.le, (hsub hs).2⟩, h⟩
    linarith [hs.2]
  
  have hFα : ContinuousOn (fun s => F (α s)) (Ioo t₀ t₁) := by
    intro s hs
    have hαs : ContinuousAt α s :=
      hα.continuousAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs) hsub)
    exact ((hFcont (α s) (hαD s (hsub hs)) (hmidp s hs) (hmidq s hs)).comp hαs).continuousWithinAt
  have hFβ : ContinuousOn (fun t => F (β t)) (Icc 0 1) := by
    intro t ht
    exact (hFcont (β t) (hβD t ht) (hβp t ht) (hβq t ht)).comp_continuousWithinAt (hβ t ht)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_re.comp_continuousOn hFβ)
  set M := |C| + 1 with hM
  have hMpos : 0 < M := by positivity
  
  have hpqn : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hpq)
  set ε := ‖p - q‖ * Real.exp (-M) / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεle : ε ≤ ‖p - q‖ / 2 := by
    have : Real.exp (-M) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [hε]; nlinarith
  obtain ⟨η, hη, hηα⟩ := Metric.continuousWithinAt_iff.1 (hα t₀ ht0.1) ε hεpos
  have ht1I : t₁ ∈ Icc (0:ℝ) 1 := ⟨ht0.1.1.trans ht1.1.1, ht1.1.2⟩
  obtain ⟨η', hη', hηα'⟩ := Metric.continuousWithinAt_iff.1 (hα t₁ ht1I) ε hεpos
  
  have hmin : 0 < min η (t₁ - t₀) := lt_min hη (by linarith)
  have hmin2 : min η (t₁ - t₀) ≤ t₁ - t₀ := min_le_right _ _
  have hmin3 : min η (t₁ - t₀) ≤ η := min_le_left _ _
  have hmin' : 0 < min η' (t₁ - t₀) := lt_min hη' (by linarith)
  have hmin2' : min η' (t₁ - t₀) ≤ t₁ - t₀ := min_le_right _ _
  have hmin3' : min η' (t₁ - t₀) ≤ η' := min_le_left _ _
  set sL := t₀ + min η (t₁ - t₀) / 2 with hsL
  set sR := t₁ - min η' (t₁ - t₀) / 2 with hsR
  have hsLmem : sL ∈ Ioo t₀ t₁ := ⟨by linarith, by linarith⟩
  have hsRmem : sR ∈ Ioo t₀ t₁ := ⟨by linarith, by linarith⟩
  have hle : sL ≤ sR := by linarith
  have hsLnear : ‖α sL - p‖ < ε := by
    have := hηα (hsub hsLmem) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [dist_eq_norm, hαt0] at this
  have hsRnear : ‖α sR - q‖ < ε := by
    have := hηα' (hsub hsRmem) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [dist_eq_norm, hαt1] at this
  have hlow : (F (α sL)).re ≤ -M := by
    rw [hFre]
    have hnum : 0 < ‖α sL - p‖ := norm_pos_iff.2 (sub_ne_zero.2 (hmidp sL hsLmem))
    have hden : ‖p - q‖ / 2 ≤ ‖α sL - q‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub p (α sL) q
      rw [norm_sub_rev p (α sL)] at this; linarith
    have hdenpos : 0 < ‖α sL - q‖ := by linarith
    have hratio : ‖α sL - p‖ / ‖α sL - q‖ < Real.exp (-M) := by
      rw [div_lt_iff₀ hdenpos]
      calc ‖α sL - p‖ < ε := hsLnear
        _ = Real.exp (-M) * (‖p - q‖ / 2) := by rw [hε]; ring
        _ ≤ Real.exp (-M) * ‖α sL - q‖ := by gcongr
    exact ((Real.log_lt_iff_lt_exp (div_pos hnum hdenpos)).2 hratio).le
  have hhigh : M ≤ (F (α sR)).re := by
    rw [hFre]
    have hnum : 0 < ‖α sR - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (hmidq sR hsRmem))
    have hp2 : ‖p - q‖ / 2 ≤ ‖α sR - p‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub p (α sR) q
      rw [norm_sub_rev p (α sR)] at this; linarith
    have hppos : 0 < ‖α sR - p‖ := by linarith
    have hratio : Real.exp M < ‖α sR - p‖ / ‖α sR - q‖ := by
      rw [lt_div_iff₀ hnum]
      calc Real.exp M * ‖α sR - q‖ < Real.exp M * ε := by gcongr
        _ = ‖p - q‖ / 2 := by
          rw [hε, show Real.exp M * (‖p - q‖ * Real.exp (-M) / 2)
            = ‖p - q‖ / 2 * (Real.exp M * Real.exp (-M)) by ring, ← Real.exp_add, add_neg_cancel,
            Real.exp_zero, mul_one]
        _ ≤ ‖α sR - p‖ := hp2
    exact ((Real.lt_log_iff_exp_lt (div_pos hppos hnum)).2 hratio).le
  
  have hsubIcc : Icc sL sR ⊆ Ioo t₀ t₁ := fun x hx => ⟨hsLmem.1.trans_le hx.1, hx.2.trans_lt hsRmem.2⟩
  obtain ⟨s', t', hs's, hs't, ht's, hfs', hft', hbtw⟩ := LQGMetric.RectCross.exists_sub_crossing
    (f := fun s => (F (α s)).re) hle
    ((Complex.continuous_re.comp_continuousOn hFα).mono hsubIcc) (by linarith : -M ≤ M) hlow hhigh
  have hst'sub : ∀ τ ∈ Icc (0:ℝ) 1, s' + τ * (t' - s') ∈ Icc s' t' := by
    intro τ hτ; constructor <;> nlinarith [hτ.1, hτ.2]
  have hmemI : ∀ τ ∈ Icc (0:ℝ) 1, s' + τ * (t' - s') ∈ Ioo t₀ t₁ := fun τ hτ =>
    hsubIcc ⟨hs's.trans (hst'sub τ hτ).1, (hst'sub τ hτ).2.trans ht's⟩
  have h1τ : ∀ τ ∈ Icc (0:ℝ) 1, 1 - τ ∈ Icc (0:ℝ) 1 := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  set γ : ℝ → ℂ := fun τ => F (α (s' + τ * (t' - s'))) with hγ
  set δ : ℝ → ℂ := fun τ => F (β (1 - τ)) with hδ
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hFα.comp (by fun_prop : Continuous fun τ : ℝ => s' + τ * (t' - s')).continuousOn hmemI
  have hδc : ContinuousOn δ (Icc 0 1) :=
    hFβ.comp (by fun_prop : Continuous fun τ : ℝ => 1 - τ).continuousOn h1τ
  have hγm : MapsTo γ (Icc 0 1) (LQGMetric.RectCross.rect (-M) M (-(Real.pi / 2)) (Real.pi / 2)) :=
    fun τ hτ => ⟨hbtw _ (hst'sub τ hτ), hFim _ (hαD _ (hsub (hmemI τ hτ)))⟩
  have hδm : MapsTo δ (Icc 0 1) (LQGMetric.RectCross.rect (-M) M (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro τ hτ
    refine ⟨?_, hFim _ (hβD _ (h1τ τ hτ))⟩
    have hb := hC (1 - τ) (h1τ τ hτ)
    rw [Real.norm_eq_abs] at hb
    have hCC : C ≤ |C| := le_abs_self C
    have hb' : -C ≤ (F (β (1 - τ))).re ∧ (F (β (1 - τ))).re ≤ C := abs_le.1 hb
    exact ⟨by linarith [hb'.1], by linarith [hb'.2]⟩
  have hγ0 : (γ 0).re = -M := by simp only [hγ, zero_mul, add_zero]; exact hfs'
  have hγ1 : (γ 1).re = M := by simp only [hγ, one_mul, add_sub_cancel]; exact hft'
  have hδ0 : (δ 0).im = Real.pi / 2 := by
    simp only [hδ, sub_zero, hF, Complex.log_im, hβ1]; exact arg_G_two h12 h3 h4
  have hδ1 : (δ 1).im = -(Real.pi / 2) := by
    simp only [hδ, sub_self, hF, Complex.log_im, hβ0]; exact arg_G_one h1 h2 h2'
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, heq⟩ := LQGMetric.RectMeet.rect_crossings_meet (-M) M
    (-(Real.pi / 2)) (Real.pi / 2) γ δ hγc hδc hγm hδm hγ0 hγ1 hδ0 hδ1
  have hx1 := hmemI τ₁ hτ₁
  have hx2 := h1τ τ₂ hτ₂
  exact hno _ (hsub hx1) _ hx2
    (hFinj _ _ (hmidp _ hx1) (hmidq _ hx1) (hβp _ hx2) (hβq _ hx2) heq)

 
theorem dcl {c : ℂ} {R : ℝ} (hR : 0 < R) {θ₁ φ₁ θ₂ φ₂ : ℝ} (h1 : θ₁ < φ₁) (h2 : φ₁ < θ₂)
    (h3 : θ₂ < φ₂) (h4 : φ₂ < θ₁ + 2 * Real.pi) {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hαD : MapsTo α (Icc 0 1) (closedBall c R)) (hβD : MapsTo β (Icc 0 1) (closedBall c R))
    (hα0 : α 0 = c + R * cexp (θ₁ * I)) (hα1 : α 1 = c + R * cexp (θ₂ * I))
    (hβ0 : β 0 = c + R * cexp (φ₁ * I)) (hβ1 : β 1 = c + R * cexp (φ₂ * I)) :
    ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, α s = β t := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnorm : ∀ {γ : ℝ → ℂ}, MapsTo γ (Icc 0 1) (closedBall c R) →
      ∀ t ∈ Icc (0:ℝ) 1, ‖(γ t - c) / R‖ ≤ 1 := by
    intro γ hγ t ht
    have := hγ ht
    rw [mem_closedBall, dist_eq_norm] at this
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_one hR]
    exact this
  have hend : ∀ (θ : ℝ), ((c + R * cexp (θ * I)) - c) / R = cexp (θ * I) := by
    intro θ; field_simp; ring
  obtain ⟨s, hs, t, ht, h⟩ := dcl_unit h1 h2 h3 h4
    (α := fun t => (α t - c) / R) (β := fun t => (β t - c) / R)
    ((hα.sub continuousOn_const).div_const _) ((hβ.sub continuousOn_const).div_const _)
    (hnorm hαD) (hnorm hβD) (by simp only [hα0, hend]) (by simp only [hα1, hend])
    (by simp only [hβ0, hend]) (by simp only [hβ1, hend])
  refine ⟨s, hs, t, ht, ?_⟩
  have h' : α s - c = β t - c := by
    have := congrArg (· * (R : ℂ)) h
    simp only [div_mul_cancel₀ _ hR'] at this
    exact this
  linear_combination h'

 
lemma radial_ne {c : ℂ} {ρ ρ' a b : ℝ} (hρ : 0 < ρ) (hρ' : 0 < ρ') (h1 : a < b)
    (h2 : b < a + 2 * Real.pi) : c + ρ * cexp (a * I) ≠ c + ρ' * cexp (b * I) := by
  intro h
  have h' : (ρ : ℂ) * cexp (a * I) = ρ' * cexp (b * I) := by linear_combination h
  have hn := congrArg norm h'
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, abs_of_pos hρ, abs_of_pos hρ'] at hn
  rw [hn] at h'
  have hρ0 : (ρ' : ℂ) ≠ 0 := by exact_mod_cast hρ'.ne'
  exact exp_mul_I_ne h1 h2 (mul_left_cancel₀ hρ0 h')

lemma norm_radial {c : ℂ} {ρ θ : ℝ} (hρ : 0 ≤ ρ) : ‖c + ρ * cexp (θ * I) - c‖ = ρ := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_nonneg hρ]

 
noncomputable def radPath (c : ℂ) (θ : ℝ) {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    Path (c + R₁ * cexp (θ * I)) (c + R₂ * cexp (θ * I)) :=
  LQGMetric.pathOfIcc (fun ρ : ℝ => c + ρ * cexp (θ * I)) h (by fun_prop)

lemma range_radPath (c : ℂ) (θ : ℝ) {R₁ R₂ : ℝ} (h : R₁ ≤ R₂) :
    range (radPath c θ h) ⊆ (fun ρ : ℝ => c + ρ * cexp (θ * I)) '' Icc R₁ R₂ :=
  LQGMetric.range_pathOfIcc_subset _ h _

 




theorem shadow {c u : ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (h12 : R₁ < R₂)
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hPD : MapsTo P (Icc a b) (closedBall c R₂))
    {θa θb : ℝ}
    (hPa : P a = c + R₁ * cexp (θa * I)) (hPb : P b = c + R₁ * cexp (θb * I))
    (Φ : Set ℝ)
    (hZ : ∀ φ ∈ Φ, ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = u ∧
      γ 1 = c + R₁ * cexp (φ * I) ∧ MapsTo γ (Icc 0 1) (closedBall c R₁) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc a b, γ t ≠ P s) :
    (∀ φ ∈ Φ, θa < φ → φ < θb →
        ∃ s ∈ Icc a b, ∃ ρ ∈ Icc R₁ R₂, P s = c + ρ * cexp (φ * I)) ∨
    (∀ φ ∈ Φ, θb < φ → φ < θa + 2 * Real.pi →
        ∃ s ∈ Icc a b, ∃ ρ ∈ Icc R₁ R₂, P s = c + ρ * cexp (φ * I)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨φ₁, hφ₁Φ, hφ₁a, hφ₁b, hφ₁⟩, ⟨φ₂, hφ₂Φ, hφ₂a, hφ₂b, hφ₂⟩⟩ := hcon
  obtain ⟨γ₁, hγ₁c, hγ₁0, hγ₁1, hγ₁D, hγ₁P⟩ := hZ φ₁ hφ₁Φ
  obtain ⟨γ₂, hγ₂c, hγ₂0, hγ₂1, hγ₂D, hγ₂P⟩ := hZ φ₂ hφ₂Φ
  have hle : R₁ ≤ R₂ := h12.le
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  
  let Pc : Path (c + R₁ * cexp (θa * I)) (c + R₁ * cexp (θb * I)) :=
    (LQGMetric.pathOfIcc P hab hP).cast hPa.symm hPb.symm
  let Z₁ : Path u (c + R₁ * cexp (φ₁ * I)) :=
    (LQGMetric.pathOfIcc γ₁ h01 hγ₁c).cast hγ₁0.symm hγ₁1.symm
  let Z₂ : Path u (c + R₁ * cexp (φ₂ * I)) :=
    (LQGMetric.pathOfIcc γ₂ h01 hγ₂c).cast hγ₂0.symm hγ₂1.symm
  let Q := ((radPath c θa hle).symm.trans Pc).trans (radPath c θb hle)
  let Y := (((radPath c φ₁ hle).symm.trans Z₁.symm).trans Z₂).trans (radPath c φ₂ hle)
  have hQr : range Q ⊆ ((fun ρ : ℝ => c + ρ * cexp (θa * I)) '' Icc R₁ R₂) ∪ P '' Icc a b ∪
      ((fun ρ : ℝ => c + ρ * cexp (θb * I)) '' Icc R₁ R₂) := by
    simp only [Q, Path.trans_range, Path.symm_range, Pc, Path.cast_coe]
    exact union_subset_union (union_subset_union (range_radPath _ _ _)
      (LQGMetric.range_pathOfIcc_subset _ _ _)) (range_radPath _ _ _)
  have hYr : range Y ⊆ ((fun ρ : ℝ => c + ρ * cexp (φ₁ * I)) '' Icc R₁ R₂) ∪ γ₁ '' Icc 0 1 ∪
      γ₂ '' Icc 0 1 ∪ ((fun ρ : ℝ => c + ρ * cexp (φ₂ * I)) '' Icc R₁ R₂) := by
    simp only [Y, Path.trans_range, Path.symm_range, Z₁, Z₂, Path.cast_coe]
    exact union_subset_union (union_subset_union (union_subset_union (range_radPath _ _ _)
      (LQGMetric.range_pathOfIcc_subset _ _ _)) (LQGMetric.range_pathOfIcc_subset _ _ _))
      (range_radPath _ _ _)
  have hradD : ∀ θ : ℝ, (fun ρ : ℝ => c + ρ * cexp (θ * I)) '' Icc R₁ R₂ ⊆ closedBall c R₂ := by
    rintro θ _ ⟨ρ, hρ, rfl⟩
    rw [mem_closedBall, dist_eq_norm, norm_radial (hR₁.le.trans hρ.1)]; exact hρ.2
  have hQD : MapsTo Q.extend (Icc 0 1) (closedBall c R₂) := by
    intro t ht
    have hx : Q.extend t ∈ range Q := by rw [← Path.extend_range]; exact mem_range_self t
    rcases hQr hx with (h | h) | h
    · exact hradD θa h
    · obtain ⟨s, hs, hs'⟩ := h; rw [← hs']; exact hPD hs
    · exact hradD θb h
  have hballsub : closedBall c R₁ ⊆ closedBall c R₂ := closedBall_subset_closedBall hle
  have hYD : MapsTo Y.extend (Icc 0 1) (closedBall c R₂) := by
    intro t ht
    have hx : Y.extend t ∈ range Y := by rw [← Path.extend_range]; exact mem_range_self t
    rcases hYr hx with ((h | h) | h) | h
    · exact hradD φ₁ h
    · obtain ⟨s, hs, hs'⟩ := h; rw [← hs']; exact hballsub (hγ₁D hs)
    · obtain ⟨s, hs, hs'⟩ := h; rw [← hs']; exact hballsub (hγ₂D hs)
    · exact hradD φ₂ h
  obtain ⟨s, hs, t, ht, hst⟩ := dcl (lt_trans hR₁ h12) hφ₁a hφ₁b hφ₂a hφ₂b
    Q.continuous_extend.continuousOn Y.continuous_extend.continuousOn hQD hYD
    (Path.extend_zero _) (Path.extend_one _) (Path.extend_zero _) (Path.extend_one _)
  
  have hxQ : Q.extend s ∈ range Q := by rw [← Path.extend_range]; exact mem_range_self s
  have hxY : Q.extend s ∈ range Y := by
    rw [hst, ← Path.extend_range]; exact mem_range_self t
  have hsep₁a : θa < φ₁ ∧ φ₁ < θa + 2 * Real.pi := ⟨hφ₁a, by linarith⟩
  have hsep₂a : θa < φ₂ ∧ φ₂ < θa + 2 * Real.pi := ⟨by linarith, hφ₂b⟩
  have hsep₁b : φ₁ < θb ∧ θb < φ₁ + 2 * Real.pi := ⟨hφ₁b, by linarith⟩
  have hsep₂b : θb < φ₂ ∧ φ₂ < θb + 2 * Real.pi := ⟨hφ₂a, by linarith⟩
  have hinner : ∀ {θ ρ : ℝ}, ρ ∈ Icc R₁ R₂ → c + ρ * cexp (θ * I) ∈ closedBall c R₁ →
      c + ρ * cexp (θ * I) = c + R₁ * cexp (θ * I) := by
    intro θ ρ hρ hmem
    rw [mem_closedBall, dist_eq_norm, norm_radial (hR₁.le.trans hρ.1)] at hmem
    rw [le_antisymm hmem hρ.1]
  have hPa' : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hPb' : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have key : ∀ x, x ∈ ((fun ρ : ℝ => c + ρ * cexp (θa * I)) '' Icc R₁ R₂) ∪ P '' Icc a b ∪
      ((fun ρ : ℝ => c + ρ * cexp (θb * I)) '' Icc R₁ R₂) →
      x ∈ ((fun ρ : ℝ => c + ρ * cexp (φ₁ * I)) '' Icc R₁ R₂) ∪ γ₁ '' Icc 0 1 ∪
      γ₂ '' Icc 0 1 ∪ ((fun ρ : ℝ => c + ρ * cexp (φ₂ * I)) '' Icc R₁ R₂) → False := by
    intro x hxQ hxY
    simp only [mem_union, mem_image] at hxQ hxY
    rcases hxQ with (⟨ρ, hρ, rfl⟩ | ⟨s', hs', rfl⟩) | ⟨ρ, hρ, rfl⟩ <;>
      rcases hxY with ((⟨ρ', hρ', h'⟩ | ⟨t', ht', h'⟩) | ⟨t', ht', h'⟩) | ⟨ρ', hρ', h'⟩
    · exact radial_ne (hR₁.trans_le hρ.1) (hR₁.trans_le hρ'.1) hsep₁a.1 hsep₁a.2 h'.symm
    · have hm : c + ρ * cexp (θa * I) ∈ closedBall c R₁ := h' ▸ hγ₁D ht'
      exact hγ₁P t' ht' a hPa' (by rw [h', hinner hρ hm, hPa])
    · have hm : c + ρ * cexp (θa * I) ∈ closedBall c R₁ := h' ▸ hγ₂D ht'
      exact hγ₂P t' ht' a hPa' (by rw [h', hinner hρ hm, hPa])
    · exact radial_ne (hR₁.trans_le hρ.1) (hR₁.trans_le hρ'.1) hsep₂a.1 hsep₂a.2 h'.symm
    · exact hφ₁ s' hs' ρ' hρ' h'.symm
    · exact hγ₁P t' ht' s' hs' h'
    · exact hγ₂P t' ht' s' hs' h'
    · exact hφ₂ s' hs' ρ' hρ' h'.symm
    · exact radial_ne (hR₁.trans_le hρ'.1) (hR₁.trans_le hρ.1) hsep₁b.1 hsep₁b.2 h'
    · have hm : c + ρ * cexp (θb * I) ∈ closedBall c R₁ := h' ▸ hγ₁D ht'
      exact hγ₁P t' ht' b hPb' (by rw [h', hinner hρ hm, hPb])
    · have hm : c + ρ * cexp (θb * I) ∈ closedBall c R₁ := h' ▸ hγ₂D ht'
      exact hγ₂P t' ht' b hPb' (by rw [h', hinner hρ hm, hPb])
    · exact radial_ne (hR₁.trans_le hρ.1) (hR₁.trans_le hρ'.1) hsep₂b.1 hsep₂b.2 h'.symm
  exact key _ (hQr hxQ) (hYr hxY)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow


lemma rproj_aux (e f : ℂ) (ρ r : ℝ) (he : Complex.normSq e = 1) (hf : Complex.normSq f = 1)
    (hr : 0 ≤ r) (hρ : r ≤ ρ) :
    Complex.normSq ((r : ℂ) * e - r * f) ≤ Complex.normSq ((ρ : ℂ) * e - r * f) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at *
  nlinarith [sq_nonneg (e.re - f.re), sq_nonneg (e.im - f.im), sq_nonneg (ρ - r),
    mul_nonneg (sub_nonneg.2 hρ) hr]

 

theorem norm_rproj_sub_le {c y z : ℂ} {r : ℝ} (hr : 0 < r) (hy : y ∈ sphere c r)
    (hz : r ≤ ‖z - c‖) :
    ‖LQGMetric.Topo.Crosscut.rproj c r z - y‖ ≤ ‖z - y‖ := by
  rw [mem_sphere, dist_eq_norm] at hy
  have hzc : 0 < ‖z - c‖ := hr.trans_le hz
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ‖z - c‖ := ⟨_, rfl⟩
  rw [← hρdef] at hz hzc
  have hρ0 : (ρ : ℂ) ≠ 0 := by exact_mod_cast hzc.ne'
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = (z - c) / ρ := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℂ, f = (y - c) / r := ⟨_, rfl⟩
  have hen : Complex.normSq e = 1 := by
    rw [Complex.normSq_eq_norm_sq, he, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hzc, ← hρdef, div_self hzc.ne', one_pow]
  have hfn : Complex.normSq f = 1 := by
    rw [Complex.normSq_eq_norm_sq, hf, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr, hy, div_self hr.ne', one_pow]
  have hz' : z = c + ρ * e := by rw [he]; field_simp; ring
  have hy' : y = c + r * f := by rw [hf]; field_simp; ring
  have hproj : LQGMetric.Topo.Crosscut.rproj c r z = c + r * e := by
    unfold LQGMetric.Topo.Crosscut.rproj
    rw [← hρdef, he]; push_cast; ring
  rw [hproj, hz', hy']
  have e1 : c + ↑r * e - (c + ↑r * f) = (r : ℂ) * e - r * f := by ring
  have e2 : c + ↑ρ * e - (c + ↑r * f) = (ρ : ℂ) * e - r * f := by ring
  rw [e1, e2]
  have key := rproj_aux e f ρ r hen hfn hr.le hz
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at key
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 key

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow


 




theorem exists_excursion {c : ℂ} {R : ℝ} {P : ℝ → ℂ} {a b t : ℝ}
    (hP : ContinuousOn P (Icc a b)) (ha : ‖P a - c‖ ≤ R) (hb : ‖P b - c‖ ≤ R)
    (ht : t ∈ Icc a b) (htR : R < ‖P t - c‖) :
    ∃ α β, a ≤ α ∧ α < t ∧ t < β ∧ β ≤ b ∧ ‖P α - c‖ = R ∧ ‖P β - c‖ = R ∧
      (∀ s ∈ Ioo α β, R < ‖P s - c‖) := by
  have hf : ContinuousOn (fun s => ‖P s - c‖) (Icc a b) := (hP.sub continuousOn_const).norm
  
  set S := Icc a t ∩ (fun s => ‖P s - c‖) ⁻¹' Iic R with hS
  have hSc : IsClosed S := (hf.mono (Icc_subset_Icc le_rfl ht.2)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, ht.1⟩, ha⟩
  have hSb : BddAbove S := ⟨t, fun x hx => hx.1.2⟩
  have hαS : sSup S ∈ S := hSc.csSup_mem hSne hSb
  set α := sSup S with hα
  have hαt : α < t := by
    rcases hαS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; have := hαS.2; simp only [mem_preimage, mem_Iic] at this; rw [h] at this; linarith
  have hleft : ∀ s ∈ Ioc α t, R < ‖P s - c‖ := by
    intro s hs
    by_contra hcon; push Not at hcon
    have : s ≤ α := le_csSup hSb ⟨⟨hαS.1.1.trans hs.1.le, hs.2⟩, hcon⟩
    linarith [hs.1]
  
  set T := Icc t b ∩ (fun s => ‖P s - c‖) ⁻¹' Iic R with hT
  have hTc : IsClosed T := (hf.mono (Icc_subset_Icc ht.1 le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_Iic
  have hTne : T.Nonempty := ⟨b, ⟨ht.2, le_rfl⟩, hb⟩
  have hTb : BddBelow T := ⟨t, fun x hx => hx.1.1⟩
  have hβT : sInf T ∈ T := hTc.csInf_mem hTne hTb
  set β := sInf T with hβ
  have htβ : t < β := by
    rcases hβT.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hβT.2; simp only [mem_preimage, mem_Iic] at this; rw [← h] at this; linarith
  have hright : ∀ s ∈ Ico t β, R < ‖P s - c‖ := by
    intro s hs
    by_contra hcon; push Not at hcon
    have : β ≤ s := csInf_le hTb ⟨⟨hs.1, hs.2.le.trans hβT.1.2⟩, hcon⟩
    linarith [hs.2]
  have haα : a ≤ α := hαS.1.1
  have hβb : β ≤ b := hβT.1.2
  
  have hαR : ‖P α - c‖ = R := by
    refine le_antisymm hαS.2 ?_
    by_contra hcon; push Not at hcon
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf α ⟨haα, hαt.le.trans ht.2⟩)
      (R - ‖P α - c‖) (by linarith)
    set s := min (α + δ / 2) t with hs
    have hs1 : α < s := lt_min (by linarith) hαt
    have hs2 : s ≤ t := min_le_right _ _
    have hs3 : s ≤ α + δ / 2 := min_le_left _ _
    have := hδf (x := s) ⟨haα.trans hs1.le, hs2.trans ht.2⟩
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq] at this
    have h1 := hleft s ⟨hs1, hs2⟩
    have h2 := (abs_lt.1 this).2
    linarith
  have hβR : ‖P β - c‖ = R := by
    refine le_antisymm hβT.2 ?_
    by_contra hcon; push Not at hcon
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf β ⟨ht.1.trans htβ.le, hβb⟩)
      (R - ‖P β - c‖) (by linarith)
    set s := max (β - δ / 2) t with hs
    have hs1 : s < β := max_lt (by linarith) htβ
    have hs2 : t ≤ s := le_max_right _ _
    have hs3 : β - δ / 2 ≤ s := le_max_left _ _
    have := hδf (x := s) ⟨ht.1.trans hs2, hs1.le.trans hβb⟩
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq] at this
    have h1 := hright s ⟨hs2, hs1⟩
    have h2 := (abs_lt.1 this).2
    linarith
  refine ⟨α, β, haα, hαt, htβ, hβb, hαR, hβR, fun s hs => ?_⟩
  rcases le_or_gt s t with h | h
  · exact hleft s ⟨hs.1, h⟩
  · exact hright s ⟨h.le, hs.2⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

 
theorem absorb {N q X lam K T A₁ AN : ℝ} (hq : 0 < q) (hK : 1 ≤ K)
    (hT1 : (N - 1) * q ≤ T) (hT2 : T ≤ A₁ + AN)
    (hA1 : A₁ ≤ 2 * lam * X + 4 * K * q) (hAN : AN ≤ 2 * lam * X + 4 * K * q)
    (hN : 16 * K ≤ N - 1) :
    A₁ ≤ 4 * lam * X ∧ A₁ + 2 * q ≤ 5 * lam * X := by
  have hKq : 8 * K * q ≤ 4 * lam * X := by nlinarith
  constructor
  · nlinarith
  · nlinarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow


namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

 

theorem finite_of_compact_separated {X : Type*} [PseudoEMetricSpace X]
    {K S : Set X} (hK : IsCompact K) (hSK : S ⊆ K)
    {ε : NNReal} (hε : ε ≠ 0)
    (hsep : Metric.IsSeparated (↑(2 * ε) : ENNReal) S) : S.Finite := by
  obtain ⟨N, _, hNfinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε hK
  have hS : S.encard ≤ N.encard :=
    (Metric.IsSeparated.encard_le_packingNumber hSK hsep).trans
      ((Metric.packingNumber_two_mul_le_externalCoveringNumber ε K).trans
        hcover.externalCoveringNumber_le_encard)
  exact Set.encard_lt_top_iff.mp
    (lt_of_le_of_lt hS (Set.encard_lt_top_iff.mpr hNfinite))

 


theorem finite_charged_excursions {S : Set (ℝ × ℝ)} {a b δ : ℝ}
    (hδ : 0 < δ)
    (hspan : ∀ e ∈ S, a ≤ e.1 ∧ δ ≤ e.2 - e.1 ∧ e.2 ≤ b)
    (hdisj : ∀ e ∈ S, ∀ f ∈ S, e ≠ f →
      Disjoint (Ioo e.1 e.2) (Ioo f.1 f.2)) : S.Finite := by
  let starts : Set ℝ := Prod.fst '' S
  have hstarts : starts ⊆ Icc a b := by
    rintro x ⟨e, he, rfl⟩
    obtain ⟨ha, hlen, hb⟩ := hspan e he
    exact ⟨ha, by linarith⟩
  have hseparated : ∀ x ∈ starts, ∀ y ∈ starts,
      x ≠ y → δ ≤ dist x y := by
    rintro x ⟨e, he, rfl⟩ y ⟨f, hf, rfl⟩ hxy
    have hef : e ≠ f := fun h => hxy (congrArg Prod.fst h)
    have hsep := (Ioo_disjoint_Ioo).1 (hdisj e he f hf hef)
    obtain ⟨_, heδ, _⟩ := hspan e he
    obtain ⟨_, hfδ, _⟩ := hspan f hf
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have hfe : f.1 < f.2 := by linarith
      have horder : e.2 ≤ f.1 := by
        have hmax : max e.1 f.1 = f.1 := max_eq_right hlt.le
        rw [hmax] at hsep
        rcases le_total e.2 f.2 with h | h
        · rw [min_eq_left h] at hsep; exact hsep
        · rw [min_eq_right h] at hsep; linarith
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      linarith
    · have hee : e.1 < e.2 := by linarith
      have horder : f.2 ≤ e.1 := by
        have hmax : max e.1 f.1 = e.1 := max_eq_left hgt.le
        rw [hmax] at hsep
        rcases le_total e.2 f.2 with h | h
        · rw [min_eq_left h] at hsep; linarith
        · rw [min_eq_right h] at hsep; exact hsep
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      linarith
  let ε : NNReal := ⟨δ / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    change 0 < δ / 4
    positivity
  have hsep : Metric.IsSeparated (↑(2 * ε) : ENNReal) starts := by
    intro x hx y hy hxy
    have hδxy := hseparated x hx y hy hxy
    have hsmall : 2 * (ε : ℝ) < dist x y := by
      change 2 * (δ / 4) < dist x y
      linarith
    have hεeq : (↑(2 * ε) : ENNReal) = ENNReal.ofReal (2 * (ε : ℝ)) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
    rw [hεeq, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_lt_of_le (by positivity) hδxy)).mpr hsmall
  have hfinite : starts.Finite := finite_of_compact_separated isCompact_Icc hstarts hε hsep
  apply hfinite.of_finite_image
  intro e he f hf heq
  by_contra hne
  have hd := hdisj e he f hf hne
  have heδ := (hspan e he).2.1
  have hfδ := (hspan f hf).2.1
  have hm : e.1 + δ / 2 ∈ Ioo e.1 e.2 := by constructor <;> linarith
  have hm' : e.1 + δ / 2 ∈ Ioo f.1 f.2 := by
    rw [← heq]
    constructor <;> linarith
  exact (Set.disjoint_left.mp hd) hm hm'


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow

 

theorem exterior_intervals_disjoint {f : ℝ → ℝ} {R : ℝ}
    {e g : ℝ × ℝ} (he : e.1 < e.2) (hg : g.1 < g.2)
    (he0 : f e.1 = R) (he1 : f e.2 = R)
    (hg0 : f g.1 = R) (hg1 : f g.2 = R)
    (hei : ∀ t ∈ Ioo e.1 e.2, R < f t)
    (hgi : ∀ t ∈ Ioo g.1 g.2, R < f t)
    (hneq : e ≠ g) : Disjoint (Ioo e.1 e.2) (Ioo g.1 g.2) := by
  by_contra hd
  have hcross : max e.1 g.1 < min e.2 g.2 := by
    apply lt_of_not_ge
    intro h
    exact hd ((Ioo_disjoint_Ioo).2 h)
  have hstart : e.1 = g.1 := by
    rcases lt_trichotomy e.1 g.1 with h | h | h
    · have hgstart : g.1 ∈ Ioo e.1 e.2 := ⟨h, by linarith [le_max_right e.1 g.1, min_le_left e.2 g.2]⟩
      linarith [hei g.1 hgstart]
    · exact h
    · have hestart : e.1 ∈ Ioo g.1 g.2 := ⟨h, by linarith [le_max_left e.1 g.1, min_le_right e.2 g.2]⟩
      linarith [hgi e.1 hestart]
  have hend : e.2 = g.2 := by
    rcases lt_trichotomy e.2 g.2 with h | h | h
    · have heend : e.2 ∈ Ioo g.1 g.2 := ⟨by linarith [hstart, he], h⟩
      linarith [hgi e.2 heend]
    · exact h
    · have hgend : g.2 ∈ Ioo e.1 e.2 := ⟨by linarith [hstart, hg], h⟩
      linarith [hei g.2 hgend]
  apply hneq
  exact Prod.ext hstart hend

 

theorem finite_maximal_exterior_excursions {f : ℝ → ℝ} {R a b δ : ℝ}
    (hδ : 0 < δ) {S : Set (ℝ × ℝ)}
    (hS : ∀ e ∈ S, a ≤ e.1 ∧ δ ≤ e.2 - e.1 ∧ e.2 ≤ b ∧
      f e.1 = R ∧ f e.2 = R ∧ ∀ t ∈ Ioo e.1 e.2, R < f t) : S.Finite := by
  apply finite_charged_excursions hδ
  · intro e he
    obtain ⟨ha, hlen, hb, _, _, _⟩ := hS e he
    exact ⟨ha, hlen, hb⟩
  · intro e he g hg hne
    obtain ⟨_, heδ, _, he0, he1, hei⟩ := hS e he
    obtain ⟨_, hgδ, _, hg0, hg1, hgi⟩ := hS g hg
    exact exterior_intervals_disjoint (by linarith) (by linarith)
      he0 he1 hg0 hg1 hei hgi hne


end SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow
