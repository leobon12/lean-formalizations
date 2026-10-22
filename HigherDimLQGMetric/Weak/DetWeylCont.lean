import HigherDimLQGMetric.Weak.DetWeylSym

/-! Port of DF Lemma 7.1 to `Rd dim`, with local weight control and a proper limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

/-- Final bookkeeping: from `X ≤ e^ω C + N c` and `C < Y + η₀` with `Y` finite. -/
theorem dfl71_final {X Y C : ℝ≥0∞} {ω η₀ c Bd : ℝ} {N : ℕ} (hc : 0 ≤ c) (hη₀ : 0 ≤ η₀)
    (hX : X ≤ ENNReal.ofReal (Real.exp ω) * C + N * ENNReal.ofReal c)
    (hC : C < Y + ENNReal.ofReal η₀) (hY : Y ≤ ENNReal.ofReal Bd) :
    X.toReal ≤ Real.exp ω * (Y.toReal + η₀) + N * c := by
  have hYt : Y ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hY
  have hC' : C ≤ ENNReal.ofReal (Y.toReal + η₀) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hη₀, ENNReal.ofReal_toReal hYt]; exact hC.le
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hX.trans ?_)
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  gcongr

/-- **DF Lemma 7.1** (DF:1280–1285 with the remark DF:1344), in the adapted form of DFGPS
Lemma 2.12 (T:1036–1051), `Blueprint.DFLem7_1`. -/
theorem l6d_weylCont : L6d_weylCont := by
  intro dim ξ Dn D fn f hDn hD hproper hconvD hconvf hbounded R hR
  obtain ⟨M₀, hM₀⟩ := hbounded
  set M : ℝ := |M₀| + 2 with hMdef
  have hfM : ∀ z : Rd dim, |f z| ≤ M := fun z => by
    have := hM₀ z
    linarith [le_abs_self M₀]
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : Rd dim) R).prod
    (isCompact_closedBall (0 : Rd dim) R)).exists_bound_of_continuousOn D.1.continuous.continuousOn
  set s : ℝ := max B 0 with hsdef
  have hs : ∀ u ∈ closedBall (0 : Rd dim) R, ∀ v ∈ closedBall (0 : Rd dim) R,
      D.1 (u,v) ≤ s := fun u hu v hv =>
    (Real.le_norm_self _).trans ((hB (u,v) ⟨hu,hv⟩).trans (le_max_left _ _))
  have hs0 : 0 ≤ s := le_max_right _ _
  obtain ⟨r', hRr', hd'⟩ := hproper.exists_sphere_barrier D (by linarith : 0 < R + 1)
    (Real.exp (2 * |ξ| * M) * s + 1)
  have hRr' : R < r' := by linarith
  set d : ℝ := Real.exp (2 * |ξ| * M) * s + 1 with hddef
  have hd : ∀ u ∈ closedBall (0 : Rd dim) R, ∀ y ∈ sphere (0 : Rd dim) r',
      d ≤ D.1 (u,y) := fun u hu y hy => hd' u
        (closedBall_subset_closedBall (by linarith) hu) y hy
  have hsd : Real.exp (2 * |ξ| * M) * s < d := by dsimp [d]; linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hξ := abs_nonneg ξ
  set E1 := Real.exp (|ξ| * M) with hE1
  set E2 := Real.exp (2 * |ξ| * M) with hE2
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE2pos : 0 < E2 := Real.exp_pos _
  have hE2ge : 1 ≤ E2 := by
    rw [hE2, ← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  have hEs : s ≤ E2 * s := by
    simpa using mul_le_mul_of_nonneg_right hE2ge hs0
  have hR0 : (0 : Rd dim) ∈ closedBall (0 : Rd dim) R := mem_closedBall_self hR.le
  have hgap : 0 < d - E2 * s := by linarith
  obtain ⟨d₁, hd₁, hgap1⟩ := dfl71_sphere_gap D (lt_add_one r')
  have hr'1 : 0 < r' + 1 := by linarith
  have hRK : ∀ u ∈ closedBall (0 : Rd dim) R, u ∈ closedBall (0 : Rd dim) (r' + 1) := fun u hu =>
    closedBall_subset_closedBall (by linarith) hu
  have hrK : ∀ u ∈ sphere (0 : Rd dim) r', u ∈ closedBall (0 : Rd dim) (r' + 1) := fun u hu =>
    closedBall_subset_closedBall (by linarith) (sphere_subset_closedBall hu)
  set Bd := E1 * (s + 1) with hBddef
  set Lmax := E1 * (E1 * (s + 1) + 1) with hLmaxdef
  have hBd : 0 ≤ Bd := by positivity
  have hLmax0 : 0 ≤ Lmax := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε₀ hε₀
  -- the oscillation parameter `ω` (DF's `2 ω(f, ·)`)
  set ω := min 1 (ε₀ / (8 * (Bd + 1))) with hωdef
  have hω : 0 < ω := lt_min one_pos (by positivity)
  have hω1 : ω ≤ 1 := min_le_left _ _
  have hωB : 2 * ω * Bd ≤ ε₀ / 4 := by
    have h := min_le_right 1 (ε₀ / (8 * (Bd + 1)))
    rw [← hωdef, le_div_iff₀ (by positivity)] at h
    linarith
  have hexpω : Real.exp ω ≤ 1 + 2 * ω := by
    have h := Real.abs_exp_sub_one_le (x := ω) (by rw [abs_of_pos hω]; exact hω1)
    rw [abs_of_pos hω] at h
    linarith [(abs_le.1 h).2]
  -- near-optimality `η₀`
  set η₀ := min 1 (min (ε₀ / 12) ((d - E2 * s) / (4 * E1))) with hη₀def
  have hη₀ : 0 < η₀ := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hη₀1 : η₀ ≤ 1 := min_le_left _ _
  have hη₀ε : η₀ ≤ ε₀ / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hη₀g : E1 * η₀ ≤ (d - E2 * s) / 4 := by
    have h : η₀ ≤ (d - E2 * s) / (4 * E1) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  -- the modulus of continuity of `f` (DF:1307)
  set θ := ω / (4 * (|ξ| + 1)) with hθdef
  have hθ : 0 < θ := by positivity
  have hθω : 2 * |ξ| * θ ≤ ω / 2 := by
    have h : θ * (4 * (|ξ| + 1)) = ω := div_mul_cancel₀ ω (by positivity)
    linarith
  obtain ⟨δ, hδ, hmod⟩ := dfl71_modulus D f (isCompact_closedBall (0 : Rd dim) (r' + 1)) hθ
  set μ := min δ d₁ with hμdef
  have hμ : 0 < μ := lt_min hδ hd₁
  -- the number of pieces
  set N : ℕ := ⌈4 * Lmax / μ⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hNge : 4 * Lmax ≤ μ * N := by
    have h1 : 4 * Lmax / μ ≤ N := (Nat.le_ceil _).trans (by rw [hNdef]; push_cast; linarith)
    rw [div_le_iff₀ hμ] at h1
    linarith
  have hLN : ∀ L : ℝ, L ≤ Lmax → L / N ≤ μ / 4 := by
    intro L hL
    rw [div_le_iff₀ hNr]
    linarith
  set EB := Real.exp (|ξ| * M + 1) with hEBdef
  have hEB : 0 < EB := Real.exp_pos _
  set κ := min (μ / 8) (ε₀ / (16 * N * EB)) with hκdef
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  have hκμ : κ ≤ μ / 8 := min_le_left _ _
  have hκε : N * EB * κ ≤ ε₀ / 16 := by
    have h : κ ≤ ε₀ / (16 * N * EB) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  set ε₁ := min κ (min θ (min 1 ((d - E2 * s) / (4 * (E2 + 1))))) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hκ (lt_min hθ (lt_min one_pos (by positivity)))
  have hε₁κ : ε₁ ≤ κ := min_le_left _ _
  have hε₁θ : ε₁ ≤ θ := (min_le_right _ _).trans (min_le_left _ _)
  have hε₁1 : ε₁ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₁g : E2 * ε₁ + ε₁ ≤ (d - E2 * s) / 4 := by
    have h : ε₁ ≤ (d - E2 * s) / (4 * (E2 + 1)) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hpieces : ∀ L : ℝ, L ≤ Lmax → L / N + 3 * ε₁ + κ ≤ δ ∧ L / N + 3 * ε₁ + κ < d₁ := by
    intro L hL
    have h1 := hLN L hL
    have h2 : μ ≤ δ := min_le_left _ _
    have h3 : μ ≤ d₁ := min_le_right _ _
    constructor <;> linarith
  -- uniform closeness on `B̄_{r'+1}(0)` for large `n`
  have hDc : ∀ᶠ n in atTop, ∀ u ∈ closedBall (0 : Rd dim) (r' + 1), ∀ v ∈ closedBall (0 : Rd dim) (r' + 1),
      |(Dn n).1 (u, v) - D.1 (u, v)| ≤ ε₁ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconvD (r' + 1) hr'1) ε₁ hε₁]
      with n hn u hu v hv
    have := hn (u, v) (mk_mem_prod hu hv)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hfc : ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : Rd dim) (r' + 1), |fn n z - f z| ≤ ε₁ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hconvf (r' + 1) hr'1) ε₁ hε₁]
      with n hn z hz
    have := hn z hz
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  clear_value ε₁ κ EB N μ θ η₀ ω Lmax Bd E1 E2
  filter_upwards [hDc, hfc] with n hDn' hfn'
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  show dist (weylScale ξ f D z w).toReal (weylScale ξ (fn n) (Dn n) z w).toReal < ε₀
  have hA := dfl71_abs_le (ξ := ξ) hfM
  have hfnM : ∀ x ∈ closedBall (0 : Rd dim) (r' + 1), |fn n x| ≤ M := by
    intro x hx
    have h := abs_le.1 (hfn' x hx)
    have hf := hM₀ x
    have hε := hε₁1
    have hab := abs_le.1 hf
    have hM₀le : M₀ ≤ |M₀| := le_abs_self _
    apply abs_le.2
    rw [hMdef]
    constructor <;> linarith
  have hc0 : 0 ≤ EB * (2 * ε₁ + κ) := by positivity
  -- upper bound: a near-optimal path for `e^{ξ f}·D` (DF:1310–1322)
  obtain ⟨L, P, hL, -, hu, h0, h1, hcost, hLb, hin⟩ :=
    dfl71_loc hD (g := f) (fun x _ => hfM x) hRr' hη₀ hs hd (by rw [← hE1, ← hE2]; linarith) hz hw
  rw [← hE1] at hLb
  have hLm : L ≤ Lmax := hLb.trans (by
    rw [hLmaxdef]; exact mul_le_mul_of_nonneg_left (by linarith) hE1pos.le)
  have hup := dfl71_sym (D := D) (D' := Dn n) (hDn n) (Dref := ⇑D.1) (g := f) (g' := fn n)
    (F := f) hfM (r' := r') hε₁.le hω1 (fun u _ v _ => by simp [hε₁.le]) hDn'
    (fun z _ => by simp [hε₁.le]) hfn' hε₁θ hθω hmod hgap1 hL hu hin hN hκ
    (hpieces L hLm).1 (hpieces L hLm).2
  rw [h0, h1, ← hEBdef] at hup
  have hWb : weylScale ξ f D z w ≤ ENNReal.ofReal Bd :=
    (dfl71_weylScale_le_of_local hD hRr' (fun x _ => hfM x) hs hd (by linarith) hz hw).trans
      (ENNReal.ofReal_le_ofReal (by
        rw [hBddef, hE1]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le))
  have hx := dfl71_final hc0 hη₀.le hup hcost hWb
  -- lower bound: a near-optimal path for `e^{ξ f_n}·D_n` (DF:1330–1342)
  have hsn : ∀ u ∈ closedBall (0 : Rd dim) R, ∀ v ∈ closedBall (0 : Rd dim) R,
      (Dn n).1 (u, v) ≤ s + ε₁ := fun u hu v hv => by
    linarith [hs u hu v hv, (abs_le.1 (hDn' u (hRK u hu) v (hRK v hv))).2]
  have hdn : ∀ u ∈ closedBall (0 : Rd dim) R, ∀ y ∈ sphere (0 : Rd dim) r',
      d - ε₁ ≤ (Dn n).1 (u, y) := fun u hu y hy => by
    linarith [hd u hu y hy, (abs_le.1 (hDn' u (hRK u hu) y (hrK y hy))).1]
  obtain ⟨L', P', hL', -, hu', h0', h1', hcost', hLb', hin'⟩ :=
    dfl71_loc (hDn n) (g := fn n) (fun x hx => hfnM x (ball_subset_closedBall (ball_subset_ball (by linarith) hx))) hRr' hη₀ hsn hdn
      (by rw [← hE1, ← hE2]; linarith) hz hw
  rw [← hE1] at hLb'
  have hE1ε : E1 * ε₁ ≤ E1 := mul_le_of_le_one_right hE1pos.le hε₁1
  have hLm' : L' ≤ Lmax := hLb'.trans (by
    rw [hLmaxdef]; exact mul_le_mul_of_nonneg_left (by linarith) hE1pos.le)
  have hlo := dfl71_sym (D := Dn n) (D' := D) hD (Dref := ⇑D.1) (g := fn n) (g' := f)
    (F := f) hfM (r' := r') hε₁.le hω1 hDn' (fun u _ v _ => by simp [hε₁.le])
    hfn' (fun z _ => by simp [hε₁.le]) hε₁θ hθω hmod hgap1 hL' hu' hin' hN hκ
    (hpieces L' hLm').1 (hpieces L' hLm').2
  rw [h0', h1', ← hEBdef] at hlo
  have hWnb : weylScale ξ (fn n) (Dn n) z w ≤ ENNReal.ofReal Bd :=
    (dfl71_weylScale_le_of_local (hDn n) hRr'
      (fun x hx => hfnM x (ball_subset_closedBall (ball_subset_ball (by linarith) hx)))
      hsn hdn (by
        have hEε : ε₁ ≤ E2 * ε₁ := by
          simpa using mul_le_mul_of_nonneg_right hE2ge hε₁.le
        linarith [hε₁g]) hz hw).trans
      (ENNReal.ofReal_le_ofReal (by
        rw [hBddef, hE1]
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le))
  have hy := dfl71_final hc0 hη₀.le hlo hcost' hWnb
  -- conclusion
  set X := (weylScale ξ (fn n) (Dn n) z w).toReal
  set Y := (weylScale ξ f D z w).toReal
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hXB : X ≤ Bd := ENNReal.toReal_le_of_le_ofReal hBd hWnb
  have hYB : Y ≤ Bd := ENNReal.toReal_le_of_le_ofReal hBd hWb
  have hNc : (N : ℝ) * (EB * (2 * ε₁ + κ)) ≤ 3 * ε₀ / 16 := by
    have h1 : (N : ℝ) * (EB * (2 * ε₁ + κ)) ≤ (N * EB) * (3 * κ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have key : ∀ U V : ℝ, 0 ≤ V → V ≤ Bd →
      Real.exp ω * (V + η₀) ≤ V + 3 * η₀ + 2 * ω * Bd := by
    intro U V hV0 hVB
    have ha : Real.exp ω * (V + η₀) ≤ (1 + 2 * ω) * (V + η₀) :=
      mul_le_mul_of_nonneg_right hexpω (by linarith)
    have hb : ω * V ≤ ω * Bd := mul_le_mul_of_nonneg_left hVB hω.le
    have hc : ω * η₀ ≤ η₀ := mul_le_of_le_one_left hη₀.le hω1
    linarith
  have k1 := key 0 Y hY0 hYB
  have k2 := key 0 X hX0 hXB
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end HigherDimLQGMetric
