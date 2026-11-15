import InteractingSLE.Foundations.Harmonic.MaxPrinciple
import InteractingSLE.Foundations.Harmonic.HarmonicMeasure
import QuantumZipper.Proofs.Thm18.LWBeurlingMain
import QuantumZipper.Proofs.Thm18.LWFarPocketFar

/-!
# Harmonic measure from infinity of a small set

Packet PROVE-YUAN-M23, the analytic core of [Law05, Proposition 3.76] for simple paths. A bounded
harmonic function `φ ∈ [0, 1]` on an open set `V ⊆ ℍ`, vanishing at the boundary points of `V`
outside `B̄(c, d)` and at `∞`, where the complement of `V` contains a continuum from `c` to `∞`
(the real line together with a path ending at `c`), is at most `C √(d/R)` times the half-plane
harmonic measure of `[−10 R, 10 R]` outside `B̄(c, 4R)` (`le_mul_harmonicMeasureH`). Seen from
`iY`, `Y → ∞`, this bounds the harmonic measure from infinity of the part of `∂V` near `c`
([Law05], proof of Proposition 3.76: "it must first reach `B(γ(0), 1)` without leaving `ℍ \ A`,
this probability is bounded above by `c/y`; given that it has done this, Corollary 3.72 shows
that the probability that the Brownian motion visits `B` is bounded above by `c d^{1/2}`").

## Main results

* `farBeurling`: **Beurling's estimate seen from far away**: `φ(x) ≤ C₀ √(d / |x − c|)` for
  `|x − c| ≥ 4d` (QuantumZipper's analytic Beurling estimate `beurlingHarmStmt_holds` after the
  inversion `z ↦ 1/(z − c)`; unlike QuantumZipper's pocket form, `V` may be unbounded).
* `le_mul_harmonicMeasureH`: the comparison (Lindelöf's maximum principle on `V \ B̄(c, 4R)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped Real

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace YuanCharacterisation

/-- If `L \ {c}` is connected, so is the closure of its inversion about `c`. -/
theorem isConnected_closure_inv_image {L : Set ℂ} {c : ℂ} (hL : IsConnected (L \ {c})) :
    IsConnected (closure ((fun z => (z - c)⁻¹) '' (L \ {c}))) := by
  refine (hL.image _ ?_).closure
  intro z hz
  exact ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.2 hz.2)).continuousWithinAt

/-- **Beurling's estimate seen from far away.** There is a universal `C₀` such that: let `V` be
open, `c ∉ V`, `0 < d`, and let `L` be a closed set disjoint from `V`, unbounded, with `L \ {c}`
connected and containing a point of `B̄(c, d/2)`. Let `h` be harmonic on `V` with values in
`[0, 1]`, tending to `0` at the boundary points of `V` outside `B̄(c, d)` and at `∞`. Then
`h(x) ≤ C₀ √(d / |x − c|)` for every `x ∈ V` with `|x − c| ≥ 4d`. -/
theorem farBeurling : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (V L : Set ℂ) (c x : ℂ) (d : ℝ) (h : ℂ → ℝ),
    IsOpen V → c ∉ V → x ∈ V → 0 < d → 4 * d ≤ ‖x - c‖ → IsClosed L → Disjoint L V →
    IsConnected (closure ((fun z => (z - c)⁻¹) '' (L \ {c}))) → ¬ Bornology.IsBounded L →
    (∃ z ∈ L, z ≠ c ∧ ‖z - c‖ ≤ d / 2) →
    InnerProductSpace.HarmonicOnNhd h V → (∀ z ∈ V, 0 ≤ h z ∧ h z ≤ 1) →
    (∀ p ∈ frontier V, d < ‖p - c‖ → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ V, dist z p < δ → h z ≤ ε) →
    (∀ ε > 0, ∃ M : ℝ, ∀ z ∈ V, M ≤ ‖z‖ → h z ≤ ε) →
    h x ≤ C₀ * √(d / ‖x - c‖) := by
  obtain ⟨C, hC, hB⟩ := QuantumZipper.Thm18Asm.LWFar.beurlingHarmStmt_holds
  refine ⟨2 * C, by positivity, ?_⟩
  intro V L c x d h hV hcV hxV hd hxc hLc hLV hLconn hLub hLnear hh hh01 hdec hinf
  have hxc0 : x ≠ c := fun he => hcV (he ▸ hxV)
  have hxcpos : 0 < ‖x - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hxc0)
  set ψ : ℂ → ℂ := fun v => c + v⁻¹ with hψ
  have hψc : ∀ v : ℂ, v ≠ 0 → ContinuousAt ψ v := fun v hv =>
    continuousAt_const.add (continuousAt_inv₀ hv)
  have hψinv : ∀ z : ℂ, z ≠ c → ψ (z - c)⁻¹ = z := fun z hz => by
    simp [hψ]
  set D' : Set ℂ := {v | v ≠ 0 ∧ ψ v ∈ V} with hD'
  have hD'o : IsOpen D' := by
    have : D' = {v : ℂ | v ≠ 0} ∩ ψ ⁻¹' V := rfl
    rw [this]
    exact (ContinuousOn.isOpen_inter_preimage (fun v hv => (hψc v hv).continuousWithinAt)
      isOpen_ne hV)
  set w' : ℂ := (x - c)⁻¹ with hw'
  have hw'0 : w' ≠ 0 := inv_ne_zero (sub_ne_zero.2 hxc0)
  have hw'D : w' ∈ D' := ⟨hw'0, by rw [hψinv x hxc0]; exact hxV⟩
  have hnw' : ‖w'‖ = ‖x - c‖⁻¹ := norm_inv _
  set d' : ℝ := 2 * ‖w'‖ with hd'
  set ρ' : ℝ := 1 / (2 * d) with hρ'
  have hd'pos : 0 < d' := by rw [hd']; positivity
  have hd'ρ' : d' ≤ ρ' := by
    rw [hd', hρ', hnw', le_div_iff₀ (by positivity)]
    rw [show 2 * ‖x - c‖⁻¹ * (2 * d) = 4 * d / ‖x - c‖ by field_simp; ring]
    rw [div_le_one hxcpos]; exact hxc
  set K : Set ℂ := closure ((fun z => (z - c)⁻¹) '' (L \ {c})) with hK
  have hKconn : IsConnected K := hLconn
  have hKD : Disjoint K D' := by
    refine Set.disjoint_left.2 fun v hvK hvD => ?_
    have h1 := mem_closure_image (hψc v hvD.1) hvK
    have h2 : ψ '' ((fun z => (z - c)⁻¹) '' (L \ {c})) = L \ {c} := by
      rw [image_image]
      refine (image_congr fun z hz => hψinv z hz.2).trans (image_id' _)
    rw [h2] at h1
    exact Set.disjoint_left.1 hLV (hLc.closure_subset (closure_mono sdiff_subset h1)) hvD.2
  have h0K : (0 : ℂ) ∈ K := by
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨z, hzL, hzbig⟩ : ∃ z ∈ L, ‖c‖ + 1 / ε + 1 < ‖z‖ := by
      by_contra hcon
      push Not at hcon
      exact hLub ((Metric.isBounded_iff_subset_closedBall 0).2 ⟨_, fun z hz => by
        rw [mem_closedBall, dist_zero_right]; exact hcon z hz⟩)
    have hzc : z ≠ c := fun he => by rw [he] at hzbig; linarith [one_div_pos.2 hε]
    refine ⟨(z - c)⁻¹, ⟨z, ⟨hzL, hzc⟩, rfl⟩, ?_⟩
    rw [dist_zero_left, norm_inv]
    have h1 : 1 / ε + 1 < ‖z - c‖ := by
      have := norm_sub_norm_le z c
      linarith
    have h2 : 0 < ‖z - c‖ := by linarith [one_div_pos.2 hε]
    rw [inv_lt_comm₀ h2 hε]
    calc ε⁻¹ = 1 / ε := by ring
      _ < ‖z - c‖ := by linarith
  have hKd : (K ∩ closedBall w' d').Nonempty := by
    refine ⟨0, h0K, ?_⟩
    rw [mem_closedBall, dist_zero_left, hd']
    linarith [norm_nonneg w']
  have hKρ : (K \ ball w' ρ').Nonempty := by
    obtain ⟨z, hzL, hzc, hzd⟩ := hLnear
    refine ⟨(z - c)⁻¹, subset_closure ⟨z, ⟨hzL, hzc⟩, rfl⟩, fun hball => ?_⟩
    rw [mem_ball, dist_eq_norm] at hball
    have hzc' : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
    have h1 : 2 / d ≤ ‖(z - c)⁻¹‖ := by
      rw [norm_inv, le_inv_comm₀ (by positivity) hzc']
      calc (2 / d)⁻¹ = d / 2 := by field_simp
        _ ≥ ‖z - c‖ := hzd
    have h2 : ‖w'‖ ≤ 1 / (4 * d) := by
      rw [hnw', inv_le_comm₀ hxcpos (by positivity)]
      calc (1 / (4 * d))⁻¹ = 4 * d := by field_simp
        _ ≤ ‖x - c‖ := hxc
    have h3 := norm_sub_norm_le (z - c)⁻¹ w'
    have h4 : ρ' = 1 / (2 * d) := rfl
    have h5 : 1 / (2 * d) + 1 / (4 * d) < 2 / d := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) hd]
      nlinarith
    linarith
  set h' : ℂ → ℝ := fun v => h (ψ v) with hh'
  set Vc := connectedComponentIn (D' ∩ ball w' ρ') w' with hVc
  have hVcD : Vc ⊆ D' := (connectedComponentIn_subset _ _).trans inter_subset_left
  have hharm : InnerProductSpace.HarmonicOnNhd h' Vc := by
    intro v hv
    have hvD := hVcD hv
    have hψa : AnalyticAt ℂ ψ v :=
      analyticAt_const.add (analyticAt_id.inv hvD.1)
    exact QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp hψa (hh _ hvD.2)
  have hbnd : ∀ v ∈ Vc, 0 ≤ h' v ∧ h' v ≤ 1 := fun v hv => hh01 _ (hVcD hv).2
  have hdecay : ∀ x₀ ∈ frontier D' ∩ ball w' ρ', ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v ∈ Vc, dist v x₀ < δ → h' v ≤ ε := by
    rintro x₀ ⟨hx₀fr, hx₀b⟩ ε hε
    by_cases hx₀0 : x₀ = 0
    · obtain ⟨M, hM⟩ := hinf ε hε
      refine ⟨1 / (|M| + ‖c‖ + 1), by positivity, fun v hv hvx => ?_⟩
      rw [hx₀0, dist_zero_right] at hvx
      have hv0 := (hVcD hv).1
      have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
      refine hM _ (hVcD hv).2 ?_
      have h1 : |M| + ‖c‖ + 1 < ‖v⁻¹‖ := by
        rw [norm_inv, lt_inv_comm₀ (by positivity) hvpos]
        calc (|M| + ‖c‖ + 1)⁻¹ = 1 / (|M| + ‖c‖ + 1) := by ring
          _ > ‖v‖ := hvx
      have h2 : ‖v⁻¹‖ - ‖c‖ ≤ ‖c + v⁻¹‖ := by
        have := norm_sub_norm_le v⁻¹ (-c)
        rw [norm_neg, sub_neg_eq_add, add_comm] at this
        linarith
      show M ≤ ‖c + v⁻¹‖
      linarith [le_abs_self M]
    · set p := ψ x₀ with hp
      have hD'fr : frontier D' = closure D' \ D' := hD'o.frontier_eq
      rw [hD'fr] at hx₀fr
      have hpcl : p ∈ closure V := by
        have h1 := mem_closure_image (hψc x₀ hx₀0) hx₀fr.1
        have hsub : ψ '' D' ⊆ V := by rintro _ ⟨v, hv, rfl⟩; exact hv.2
        exact closure_mono hsub h1
      have hpV : p ∉ V := fun hpV => hx₀fr.2 ⟨hx₀0, hpV⟩
      have hpfr : p ∈ frontier V := by rw [hV.frontier_eq]; exact ⟨hpcl, hpV⟩
      have hpc : d < ‖p - c‖ := by
        have h1 : ‖p - c‖ = ‖x₀‖⁻¹ := by simp [hp, hψ, norm_inv]
        have hx₀pos : 0 < ‖x₀‖ := norm_pos_iff.2 hx₀0
        have h2 : ‖x₀‖ < 3 / (4 * d) := by
          have := norm_le_of_mem_closedBall (ball_subset_closedBall hx₀b)
          have h3 : ‖w'‖ ≤ 1 / (4 * d) := by
            rw [hnw', inv_le_comm₀ hxcpos (by positivity)]
            calc (1 / (4 * d))⁻¹ = 4 * d := by field_simp
              _ ≤ ‖x - c‖ := hxc
          rw [mem_ball, dist_eq_norm] at hx₀b
          have h4 := norm_le_norm_add_norm_sub' x₀ w'
          have h5 : 1 / (2 * d) + 1 / (4 * d) = 3 / (4 * d) := by field_simp; ring
          linarith
        rw [h1, lt_inv_comm₀ hd hx₀pos]
        calc ‖x₀‖ < 3 / (4 * d) := h2
          _ < d⁻¹ := by rw [div_lt_iff₀ (by positivity)]; field_simp; norm_num
      obtain ⟨δ₁, hδ₁, hδ₁'⟩ := hdec p hpfr hpc ε hε
      obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 (hψc x₀ hx₀0) δ₁ hδ₁
      exact ⟨δ, hδ, fun v hv hvx => hδ₁' _ (hVcD hv).2 (hδ' hvx)⟩
  have hres := hB D' K w' d' ρ' h' hD'o hw'D hd'pos hd'ρ' hKconn hKD hKd hKρ hharm hbnd hdecay
  have hxeq : h' w' = h x := by simp only [hh', hw', hψinv x hxc0]
  rw [hxeq] at hres
  have hratio : d' / ρ' = 4 * (d / ‖x - c‖) := by
    rw [hd', hρ', hnw']; field_simp; norm_num
  rw [hratio, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num),
    show √(4 : ℝ) = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hres
  linarith

/-! ### Half-plane harmonic measure of an interval -/

/-- The half-plane harmonic measure of the interval `(p, q)`, seen from `z`. -/
def hmIoo (p q : ℝ) (z : ℂ) : ℝ := (harmonicMeasureH z (Ioo p q)).toReal

theorem harmonicOnNhd_hmIoo (p q : ℝ) : InnerProductSpace.HarmonicOnNhd (hmIoo p q) H :=
  PrimeEnd.harmonicOnNhd_harmonicMeasureH measurableSet_Ioo

theorem hmIoo_nonneg (p q : ℝ) (z : ℂ) : 0 ≤ hmIoo p q z := ENNReal.toReal_nonneg

theorem hmIoo_le_one (p q : ℝ) {z : ℂ} (hz : z ∈ H) : hmIoo p q z ≤ 1 := by
  have := isProbabilityMeasure_harmonicMeasureH hz
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- Upper bound from a bound on the Poisson kernel. -/
theorem hmIoo_le {p q A : ℝ} (hpq : p ≤ q) (hA : 0 ≤ A) {z : ℂ}
    (hP : ∀ t ∈ Ioo p q, poissonKernelH z t ≤ A) : hmIoo p q z ≤ A * (q - p) := by
  unfold hmIoo harmonicMeasureH
  rw [withDensity_apply _ measurableSet_Ioo]
  have h1 : ∫⁻ t in Ioo p q, ENNReal.ofReal (poissonKernelH z t) ≤
      ∫⁻ _t in Ioo p q, ENNReal.ofReal A :=
    setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal (hP t ht)
  rw [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hA] at h1
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h1

/-- Lower bound from a bound on the Poisson kernel. -/
theorem le_hmIoo {p q A : ℝ} (hA : 0 ≤ A) {z : ℂ} (hz : z ∈ H)
    (hP : ∀ t ∈ Ioo p q, A ≤ poissonKernelH z t) : A * (q - p) ≤ hmIoo p q z := by
  have hfin : harmonicMeasureH z (Ioo p q) ≠ ⊤ := by
    have := isProbabilityMeasure_harmonicMeasureH hz
    exact measure_ne_top _ _
  unfold hmIoo
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin]
  unfold harmonicMeasureH
  rw [withDensity_apply _ measurableSet_Ioo]
  have h1 : ∫⁻ _t in Ioo p q, ENNReal.ofReal A ≤
      ∫⁻ t in Ioo p q, ENNReal.ofReal (poissonKernelH z t) :=
    setLIntegral_mono (by unfold poissonKernelH; fun_prop) fun t ht =>
      ENNReal.ofReal_le_ofReal (hP t ht)
  rwa [setLIntegral_const, Real.volume_Ioo, ← ENNReal.ofReal_mul hA] at h1

/-- Seen from a point at height at most `L` above the centre of an interval of half-length `L`,
the harmonic measure of the interval is at least `1/2` (Thales). -/
theorem one_half_le_hmIoo {z : ℂ} (hz : z ∈ H) {L : ℝ} (hL : z.im ≤ L) :
    1 / 2 ≤ hmIoo (z.re - L) (z.re + L) z := by
  have hy : 0 < z.im := hz
  have hLpos : 0 < L := hy.trans_le hL
  have hab : z.re - L ≤ z.re + L := by linarith
  unfold hmIoo
  rw [harmonicMeasureH_Ioo hz hab]
  set w₁ := z - ((z.re + L : ℝ) : ℂ) with hw₁
  set w₂ := z - ((z.re - L : ℝ) : ℂ) with hw₂
  have hw₁re : w₁.re = -L := by simp [hw₁]
  have hw₂re : w₂.re = L := by simp [hw₂]
  have hw₁im : w₁.im = z.im := by simp [hw₁]
  have hw₂im : w₂.im = z.im := by simp [hw₂]
  have hn : ‖w₁‖ = ‖w₂‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply, hw₁re, hw₂re, hw₁im, hw₂im]
    ring
  have hw₂pos : 0 < ‖w₂‖ := norm_pos_iff.2 fun h => by
    have := congrArg Complex.im h; rw [hw₂im, zero_im] at this; linarith
  rw [arg_of_im_pos (by rw [hw₁im]; exact hy), arg_of_im_pos (by rw [hw₂im]; exact hy), hw₁re,
    hw₂re, hn, neg_div, Real.arccos_neg]
  have hkey : Real.arccos (L / ‖w₂‖) ≤ π / 4 := by
    rw [Real.arccos_le_pi_div_four, le_div_iff₀ hw₂pos]
    have h2 : ‖w₂‖ ^ 2 = L ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, normSq_apply, hw₂re, hw₂im]; ring
    have h3 : (√2 / 2 * ‖w₂‖) ^ 2 ≤ L ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), h2]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hLpos.le (by norm_num)).1 h3
  rw [ENNReal.toReal_ofReal (by
    have := Real.arccos_le_pi (L / ‖w₂‖)
    have := Real.pi_pos
    apply div_nonneg _ this.le
    linarith)]
  rw [le_div_iff₀ Real.pi_pos]
  linarith

/-! ### The comparison -/

theorem harmonicOnNhd_log_norm_add_I' :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖z + I‖) H := by
  intro z hz
  have hz' : z + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hz0 : 0 < z.im := hz
    linarith
  exact (analyticAt_id.add analyticAt_const).harmonicAt_log_norm hz'

theorem one_le_norm_add_I' {z : ℂ} (hz : z ∈ H) : 1 ≤ ‖z + I‖ := by
  have hz0 : 0 < z.im := hz
  calc (1 : ℝ) ≤ |(z + I).im| := by
        simp only [add_im, I_im]
        rw [abs_of_pos (by linarith)]
        linarith
    _ ≤ ‖z + I‖ := Complex.abs_im_le_norm _

/-- **Harmonic measure from infinity of a small boundary piece.** There is a universal `C₁` such
that: let `V ⊆ ℍ` be open, `c ∉ V` with `|c| ≤ R`, `0 < d ≤ R`, and let `L` be a closed set
disjoint from `V`, unbounded, with `L \ {c}` connected and meeting `B̄(c, d/2)`. Let `h ∈ [0, 1]`
be harmonic on `V`, tending to `0` at the boundary points of `V` outside `B̄(c, d)` and at `∞`.
Then `h(z) ≤ C₁ √(d/R) ω_ℍ(z, (−10R, 10R))` for `z ∈ V`, `|z − c| > 4R`. -/
theorem le_mul_hmIoo : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (V L : Set ℂ) (c : ℂ) (d R : ℝ) (h : ℂ → ℝ),
    IsOpen V → V ⊆ H → c ∉ V → 0 < d → d ≤ R → ‖c‖ ≤ R → IsClosed L → Disjoint L V →
    IsConnected (closure ((fun z => (z - c)⁻¹) '' (L \ {c}))) → ¬ Bornology.IsBounded L →
    (∃ z ∈ L, z ≠ c ∧ ‖z - c‖ ≤ d / 2) →
    InnerProductSpace.HarmonicOnNhd h V → (∀ z ∈ V, 0 ≤ h z ∧ h z ≤ 1) →
    (∀ p ∈ frontier V, d < ‖p - c‖ → ∀ ε > 0, ∃ δ > 0, ∀ z ∈ V, dist z p < δ → h z ≤ ε) →
    (∀ ε > 0, ∃ M : ℝ, ∀ z ∈ V, M ≤ ‖z‖ → h z ≤ ε) →
    ∀ z ∈ V, 4 * R < ‖z - c‖ → h z ≤ C₁ * √(d / R) * hmIoo (-10 * R) (10 * R) z := by
  obtain ⟨C₀, hC₀, hFB⟩ := farBeurling
  refine ⟨C₀, hC₀, ?_⟩
  intro V L c d R h hV hVH hcV hd hdR hcR hLc hLV hLconn hLub hLnear hh hh01 hdec hinf
  have hR : 0 < R := hd.trans_le hdR
  set ρ := 4 * R with hρ
  set Mc := C₀ * √(d / ρ) with hMc
  have hMc0 : 0 ≤ Mc := by positivity
  set v : ℂ → ℝ := fun z => 2 * hmIoo (-10 * R) (10 * R) z with hv
  set Ω := V ∩ {z | ρ < ‖z - c‖} with hΩ
  have hΩo : IsOpen Ω := hV.inter (isOpen_lt continuous_const (by fun_prop))
  have hΩH : Ω ⊆ H := fun z hz => hVH hz.1
  set f : ℂ → ℝ := fun z => h z - Mc * v z with hf
  have hvharm : InnerProductSpace.HarmonicOnNhd v H := fun z hz =>
    (harmonicOnNhd_hmIoo _ _ z hz).const_smul (c := (2 : ℝ))
  have hfharm : InnerProductSpace.HarmonicOnNhd f Ω := fun z hz =>
    (hh z hz.1).sub ((hvharm z (hΩH hz)).const_smul (c := Mc))
  have hfbd : BddAbove (f '' Ω) := ⟨1, by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := (hh01 z hz.1).2
    have h2 : 0 ≤ v z := by simp only [hv]; have := hmIoo_nonneg (-10 * R) (10 * R) z; linarith
    show h z - Mc * v z ≤ 1
    nlinarith⟩
  -- `v ≥ 1` on the circle `|z − c| = ρ` in `ℍ`
  have hvcirc : ∀ z ∈ H, ‖z - c‖ ≤ ρ → 1 ≤ v z := by
    intro z hz hzc
    have hzn : ‖z‖ ≤ 5 * R := by
      have := norm_le_norm_add_norm_sub' z c
      linarith
    have him : z.im ≤ 5 * R := (le_abs_self _).trans ((abs_im_le_norm z).trans hzn)
    have hre : |z.re| ≤ 5 * R := (abs_re_le_norm z).trans hzn
    have h1 := one_half_le_hmIoo hz him
    have hsub : Ioo (z.re - 5 * R) (z.re + 5 * R) ⊆ Ioo (-10 * R) (10 * R) := by
      rw [abs_le] at hre
      exact Ioo_subset_Ioo (by linarith) (by linarith)
    have h2 : hmIoo (z.re - 5 * R) (z.re + 5 * R) z ≤ hmIoo (-10 * R) (10 * R) z := by
      have := isProbabilityMeasure_harmonicMeasureH hz
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    simp only [hv]
    linarith
  have hfr : ∀ x₀ ∈ frontier Ω, x₀ ∉ (∅ : Finset ℂ) → ∀ ε > 0, ∀ᶠ y in 𝓝[Ω] x₀, f y ≤ ε := by
    intro x₀ hx₀ _ ε hε
    have hx₀cl : x₀ ∈ closure Ω := hx₀.1
    have hx₀Ω : x₀ ∉ Ω := by rw [hΩo.frontier_eq] at hx₀; exact hx₀.2
    have hclρ : ρ ≤ ‖x₀ - c‖ := by
      have : closure Ω ⊆ {z | ρ ≤ ‖z - c‖} :=
        closure_minimal (fun z hz => show ρ ≤ ‖z - c‖ from le_of_lt hz.2)
          (isClosed_le continuous_const (by fun_prop))
      exact this hx₀cl
    have hx₀V : x₀ ∈ closure V := closure_mono inter_subset_left hx₀cl
    by_cases hx₀V' : x₀ ∈ V
    · -- on the circle
      have hx₀c : ‖x₀ - c‖ = ρ := by
        by_contra hne
        exact hx₀Ω ⟨hx₀V', lt_of_le_of_ne hclρ (Ne.symm hne)⟩
      have hFBx := hFB V L c x₀ d h hV hcV hx₀V' hd (by rw [hx₀c, hρ]; linarith) hLc hLV hLconn
        hLub hLnear hh hh01 hdec hinf
      rw [hx₀c] at hFBx
      have hv1 := hvcirc x₀ (hVH hx₀V') hx₀c.le
      have hfx₀ : f x₀ ≤ 0 := by
        simp only [hf]
        nlinarith
      have hcont : ContinuousAt f x₀ :=
        (hh x₀ hx₀V').1.continuousAt.sub (continuousAt_const.mul
          (hvharm x₀ (hVH hx₀V')).1.continuousAt)
      have := hcont.eventually (gt_mem_nhds (show f x₀ < ε by linarith))
      exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds this).mono fun y hy => hy.le
    · have hpfr : x₀ ∈ frontier V := by rw [hV.frontier_eq]; exact ⟨hx₀V, hx₀V'⟩
      obtain ⟨δ, hδ, hδ'⟩ := hdec x₀ hpfr (by linarith) ε hε
      filter_upwards [inter_mem_nhdsWithin Ω (ball_mem_nhds x₀ hδ)] with y hy
      have h1 := hδ' y hy.1.1 hy.2
      have h2 : 0 ≤ v y := by
        simp only [hv]; have := hmIoo_nonneg (-10 * R) (10 * R) y; linarith
      simp only [hf]
      nlinarith
  have hb : InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log ‖z + I‖) Ω := fun z hz =>
    harmonicOnNhd_log_norm_add_I' z (hΩH hz)
  have hb0 : ∀ y ∈ Ω, 0 ≤ Real.log ‖y + I‖ := fun y hy =>
    Real.log_nonneg (one_le_norm_add_I' (hΩH hy))
  have hbinf : ∀ M : ℝ, ∃ R' : ℝ, ∀ y ∈ Ω, R' ≤ ‖y‖ → M ≤ Real.log ‖y + I‖ := by
    intro M
    refine ⟨Real.exp M + 1, fun y _ hy => ?_⟩
    rw [Real.le_log_iff_exp_le (by
      have := norm_sub_norm_le y (-I); simp at this
      have := Real.exp_pos M; nlinarith [norm_nonneg y])]
    have := norm_sub_norm_le y (-I)
    rw [sub_neg_eq_add, norm_neg, Complex.norm_I] at this
    linarith
  have hle := harmonic_le_zero_of_barrier ∅ hΩo hfharm hfbd hfr hb hb0 hbinf
  intro z hzV hzc
  have := hle z ⟨hzV, hzc⟩
  simp only [hf, hv] at this
  have hrat : Mc * 2 = C₀ * √(d / R) := by
    rw [hMc, hρ]
    have : √(d / (4 * R)) = √(d / R) / 2 := by
      rw [show d / (4 * R) = (d / R) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [this]; ring
  have heq : Mc * (2 * hmIoo (-10 * R) (10 * R) z) =
      C₀ * √(d / R) * hmIoo (-10 * R) (10 * R) z := by rw [← hrat]; ring
  linarith

end YuanCharacterisation

end InteractingSLE
