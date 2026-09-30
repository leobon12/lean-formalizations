import QuantumZipper.Proofs.RS.BasePointGen
import QuantumZipper.Proofs.RS.RealAlive

/-!
# RS BP1: the pathwise part (tamed three-point state, monotonicity of `Υ`)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §4, node BP1.

For `0 < y < x` let `X_t = f_t(x)`, `O_t = f_t(y)` (centered forward flow) and
`Υ_t = (X_t − O_t) exp(∫₀ᵗ 2/X_s² ds) = (g_t(x) − g_t(y))/g_t'(x)` (`bpUpsPath`).

* `bpTamed W c x y t = (X̃_t, Õ_t, L̃_t)`: the tamed state (`realTamed` for `x` and `y`,
  `L̃_t = −∫₀ᵗ 2/max(X̃,c)²`); it is the process fed to the super-Dynkin formula.
* `realTamed_eq_of_isForwardSol`: a real forward solution staying `≥ c` is the tamed flow.
* `bpUps_bpTamed_le`: while `X̃, Õ ≥ c`, `Υ̃_t ≤ x − y`; indeed
  `dΥ/dt = −2 Υ (X − O)²/((X − O) X² O)`, i.e. `(D e^{I})' = −2 D² e^{I}/(X² O) ≤ 0` with
  `D = X − O`, `I = ∫ 2/X²`. This is Rohde–Schramm's "`Q(t)` is increasing in `t`"
  (Lemma 7.2 proof, p. 32, `∂_t Q = −2X⁻² + 2X⁻¹O⁻¹`, `Q = −log Υ`).
* `neg_one_le_bp4G`: `G ≥ −1` on `(0,∞)` (own elementary proof; with `bp4G_le_two`, `G` is
  bounded, RS p. 33).

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Lemma 7.2,
pp. 32–33.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace QuantumZipper
namespace RS

open FwdHolo

variable {W : ℝ → ℝ}

/-! ### `G ≥ −1` -/

/-- `G(s) ≥ −1` for `s > 0` (own elementary proof: `G' ≤ 0`, and `G' ≥ −1/u²` on `[1,∞)`). -/
theorem neg_one_le_bp4G {s : ℝ} (hs : 0 < s) : -1 ≤ bp4G s := by
  have hG1 : bp4G 1 = 0 := intervalIntegral.integral_same
  rcases le_total s 1 with h1 | h1
  · have hanti : AntitoneOn bp4G (Ioi 0) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0) continuousOn_bp4G
        (f' := bp4Gd) ?_ ?_
      · intro x hx
        rw [interior_Ioi] at hx
        exact (hasDerivAt_bp4G hx).hasDerivWithinAt
      · intro x hx
        rw [interior_Ioi] at hx
        exact bp4Gd_nonpos hx
    have := hanti (mem_Ioi.2 hs) (mem_Ioi.2 one_pos) h1
    linarith
  · set ψ : ℝ → ℝ := fun u => bp4G u - u⁻¹ with hψ
    have hmono : MonotoneOn ψ (Ici 1) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1) ?_
        (f' := fun u => bp4Gd u + (u ^ 2)⁻¹) ?_ ?_
      · intro u hu
        have hu0 : 0 < u := one_pos.trans_le hu
        exact ((hasDerivAt_bp4G hu0).continuousAt.sub
          (continuousAt_inv₀ hu0.ne')).continuousWithinAt
      · intro u hu
        rw [interior_Ici] at hu
        have hu0 : 0 < u := one_pos.trans hu
        have hd := (hasDerivAt_bp4G hu0).sub (hasDerivAt_inv hu0.ne')
        exact (hd.congr_deriv (by ring)).hasDerivWithinAt
      · intro u hu
        rw [interior_Ici] at hu
        have hu0 : 0 < u := one_pos.trans hu
        have hl := Real.one_sub_inv_le_log_of_pos (show 0 < u / (1 + u) by positivity)
        rw [inv_div, div_eq_mul_inv (1 + u) u, add_mul, one_mul,
          mul_inv_cancel₀ hu0.ne'] at hl
        show 0 ≤ bp4Gd u + (u ^ 2)⁻¹
        unfold bp4Gd
        have h1u : 0 < 1 + u := by linarith
        have key : -(u⁻¹) / (1 + u) + (u ^ 2)⁻¹ ≥ 0 := by
          rw [ge_iff_le, ← sub_nonpos]
          field_simp
          nlinarith
        have : -(u⁻¹) / (1 + u) ≤ Real.log (u / (1 + u)) / (1 + u) :=
          div_le_div_of_nonneg_right (by linarith) h1u.le
        linarith
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h1) h1
    simp only [hψ, hG1, inv_one] at this
    have : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
    linarith

/-! ### Continuity of the tamed flow in `ℝ≥0` time -/

theorem continuous_realTamed_toNNReal (hW : Continuous W) {c : ℝ} (hc : 0 < c) (x : ℝ) :
    Continuous fun r : ℝ => realTamed W c x (r.toNNReal : ℝ) := by
  rw [continuous_iff_continuousAt]
  intro r0
  have hN : (0 : ℝ) ≤ |r0| + 1 := by positivity
  have h1 : Continuous fun r => realTamed W c x (projIcc 0 (|r0| + 1) hN r) :=
    (continuousOn_realTamed hW hc hN x).comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) fun r => (projIcc 0 _ hN r).2
  refine h1.continuousAt.congr ?_
  have hlt : r0 < |r0| + 1 := by linarith [le_abs_self r0]
  filter_upwards [Iio_mem_nhds hlt] with r hr
  simp only [projIcc, Real.coe_toNNReal']
  rw [min_eq_right (le_of_lt hr), max_comm]

/-! ### Uniqueness: real forward solutions are tamed flows -/

/-- A forward solution from a real `x`, with real part `≥ c` on `[0,T]`, is the tamed real
flow there. -/
theorem realTamed_eq_of_isForwardSol (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ}
    (hT : 0 ≤ T) {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    (hge : ∀ s ∈ Icc (0 : ℝ) T, c ≤ (u s).re) :
    ∀ s ∈ Icc (0 : ℝ) T, u s = (realTamed W c x s : ℂ) := by
  have him := im_isForwardSol_real hW hT hu
  have hreal : ∀ s ∈ Icc (0 : ℝ) T, u s = ((u s).re : ℂ) := fun s hs =>
    Complex.ext (by simp) (by simp [him s hs])
  have hV : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun r => (u r).re + W r)
      (realVf W c s ((u s).re + W s)) (Icc 0 T) s := by
    intro s hs
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (hasDerivWithinAt_shift hu hs)
    have e1 : (fun r => (u r).re + W r) = Complex.reCLM ∘ fun r => u r + (W r : ℂ) := by
      funext r; simp
    have e2 : realVf W c s ((u s).re + W s) = Complex.reCLM (2 / u s) := by
      rw [hreal s hs]
      simp only [realVf, add_sub_cancel_right, Complex.reCLM_apply, Complex.ofReal_re]
      rw [realDrift_of_le (hge s hs)]
      norm_cast
    rw [e1, e2]; exact h
  have hV0 : (u 0).re + W 0 = x := by
    rw [sol_zero hu hT]; simp
  have heq := realTamedUnc_eq_of_sol hW hc hV0 hV
  intro s hs
  rw [hreal s hs, realTamed, heq s hs]
  simp

/-! ### The tamed state and `Υ` -/

/-- `L̃_t = −∫₀ᵗ 2/max(X̃_s, c)²`. -/
def bpTamedL (W : ℝ → ℝ) (c x t : ℝ) : ℝ :=
  -∫ s in (0 : ℝ)..t, 2 / max (realTamed W c x s) c ^ 2

/-- The tamed state `(X̃_t, Õ_t, L̃_t)`. -/
def bpTamed (W : ℝ → ℝ) (c x y t : ℝ) : ℝ × ℝ × ℝ :=
  (realTamed W c x t, realTamed W c y t, bpTamedL W c x t)

/-- `Υ_t = (X_t − O_t) exp(∫₀ᵗ 2/X_s²)` for forward solutions `u` (from `x`) and `v`
(from `y`); `= (g_t(x) − g_t(y))/g_t'(x)`. -/
def bpUpsPath (u v : ℝ → ℂ) (t : ℝ) : ℝ :=
  ((u t).re - (v t).re) * Real.exp (∫ s in (0 : ℝ)..t, 2 / (u s).re ^ 2)

theorem bpUps_bpTamed (W : ℝ → ℝ) (c x y t : ℝ) :
    bpUps (bpTamed W c x y t) = (realTamedUnc W c x t - realTamedUnc W c y t) *
      Real.exp (∫ s in (0 : ℝ)..t, 2 / max (realTamed W c x s) c ^ 2) := by
  simp only [bpUps, bpTamed, bpTamedL, neg_neg, realTamed]
  ring_nf

/-- **Monotonicity of `Υ`** (RS Lemma 7.2 proof, p. 32: `Q = −log Υ` is increasing): while the
tamed flows of `x` and `y` stay `≥ c`, `Υ̃_t ≤ Υ̃_0 = x − y`. -/
theorem bpUps_bpTamed_le (hW : Continuous W) {c : ℝ} (hc : 0 < c) {t : ℝ}
    (ht : 0 ≤ t) (x y : ℝ)
    (hge : ∀ s ∈ Icc (0 : ℝ) t, c ≤ realTamed W c x s ∧ c ≤ realTamed W c y s) :
    ∀ s ∈ Icc (0 : ℝ) t, bpUps (bpTamed W c x y s) ≤ x - y := by
  set g : ℝ → ℝ := fun s => 2 / max (realTamed W c x s) c ^ 2 with hg
  have hXc := continuousOn_realTamed hW hc ht x
  have hgc : ContinuousOn g (Icc 0 t) := by
    refine ContinuousOn.div continuousOn_const (((continuous_id.max continuous_const).comp_continuousOn hXc).pow 2) ?_
    intro s _
    exact (pow_pos (hc.trans_le (le_max_right _ _)) 2).ne'
  set f : ℝ → ℝ := fun s => (realTamedUnc W c x s - realTamedUnc W c y s) *
    Real.exp (∫ r in (0 : ℝ)..s, g r) with hf
  have hfe : ∀ s, bpUps (bpTamed W c x y s) = f s := fun s => bpUps_bpTamed W c x y s
  have hI : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, g r) (Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := g) (a := 0) (b := t) (by rw [uIcc_of_le ht]; exact hgc.integrableOn_Icc)
    rwa [uIcc_of_le ht] at this
  have hfc : ContinuousOn f (Icc 0 t) :=
    ((continuousOn_realTamedUnc hW hc ht x).sub (continuousOn_realTamedUnc hW hc ht y)).mul
      (Real.continuous_exp.comp_continuousOn hI)
  have hanti : AntitoneOn f (Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hfc
      (f' := fun s => (realDrift c (realTamed W c x s) - realDrift c (realTamed W c y s)) *
        Real.exp (∫ r in (0 : ℝ)..s, g r) + (realTamedUnc W c x s - realTamedUnc W c y s) *
        (Real.exp (∫ r in (0 : ℝ)..s, g r) * g s)) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      have hsI := Ioo_subset_Icc_self hs
      have hn := Icc_mem_nhds hs.1 hs.2
      have hdx := (realTamedUnc_hasDerivWithinAt hW hc ht x s hsI).hasDerivAt hn
      have hdy := (realTamedUnc_hasDerivWithinAt hW hc ht y s hsI).hasDerivAt hn
      have hdI : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, g r) (g s) s := by
        refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
        · refine (hgc.mono ?_).intervalIntegrable
          rw [uIcc_of_le hs.1.le]; exact Icc_subset_Icc_right hs.2.le
        · exact (hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
        · exact hgc.continuousAt hn
      exact ((hdx.sub hdy).mul hdI.exp).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨h1, h2⟩ := hge s (Ioo_subset_Icc_self hs)
      have hX : 0 < realTamed W c x s := hc.trans_le h1
      have hO : 0 < realTamed W c y s := hc.trans_le h2
      rw [realDrift_of_le h1, realDrift_of_le h2]
      have hgs : g s = 2 / realTamed W c x s ^ 2 := by simp only [hg, max_eq_left h1]
      rw [hgs]
      have hD : realTamedUnc W c x s - realTamedUnc W c y s =
          realTamed W c x s - realTamed W c y s := by simp only [realTamed]; ring
      rw [hD]
      set X := realTamed W c x s
      set O := realTamed W c y s
      have key : (2 / X - 2 / O) + (X - O) * (2 / X ^ 2) = -(2 * (X - O) ^ 2 / (X ^ 2 * O)) := by
        field_simp; ring
      have hE := Real.exp_pos (∫ r in (0 : ℝ)..s, g r)
      have : (2 / X - 2 / O) * Real.exp (∫ r in (0 : ℝ)..s, g r) +
          (X - O) * (Real.exp (∫ r in (0 : ℝ)..s, g r) * (2 / X ^ 2)) =
          -(2 * (X - O) ^ 2 / (X ^ 2 * O)) * Real.exp (∫ r in (0 : ℝ)..s, g r) := by
        rw [← key]; ring
      rw [this]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity)) hE.le
  intro s hs
  have h0 : f 0 = x - y := by
    simp only [hf, intervalIntegral.integral_same, Real.exp_zero, mul_one,
      realTamedUnc_zero hW hc]
  rw [hfe, ← h0]
  exact hanti ⟨le_rfl, ht⟩ hs hs.1

/-- On `[0,t]`, if the forward solutions agree with the tamed flows, `Υ` agrees too. -/
theorem bpUpsPath_eq_bpUps (hW : Continuous W) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    {x y : ℝ} {u v : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) t u)
    (hv : IsForwardSol W (y : ℂ) t v)
    (hge : ∀ s ∈ Icc (0 : ℝ) t, c ≤ (u s).re ∧ c ≤ (v s).re) :
    bpUpsPath u v t = bpUps (bpTamed W c x y t) ∧
      ∀ s ∈ Icc (0 : ℝ) t, c ≤ realTamed W c x s ∧ c ≤ realTamed W c y s := by
  have eu := realTamed_eq_of_isForwardSol hW hc ht hu fun s hs => (hge s hs).1
  have ev := realTamed_eq_of_isForwardSol hW hc ht hv fun s hs => (hge s hs).2
  have hre : ∀ s ∈ Icc (0 : ℝ) t, (u s).re = realTamed W c x s ∧ (v s).re = realTamed W c y s :=
    fun s hs => ⟨by rw [eu s hs]; simp, by rw [ev s hs]; simp⟩
  refine ⟨?_, fun s hs => ⟨(hre s hs).1 ▸ (hge s hs).1, (hre s hs).2 ▸ (hge s hs).2⟩⟩
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  simp only [bpUpsPath, bpUps, bpTamed, bpTamedL, neg_neg, (hre t htt).1, (hre t htt).2]
  congr 2
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  have h1 := (hre s hs).1
  have h2 := (hge s hs).1
  rw [h1] at h2 ⊢
  simp only [max_eq_left h2]

end RS
end QuantumZipper
