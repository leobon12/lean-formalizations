import QuantumZipper.Proofs.Zipper.UnifACFlowDetBasic
import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.LQG.CoordChangeDet

/-!
# UNIF-ACFLOW-DET (2): the family `ψ_s`, uniform in `s`

Task ACFLOW-DET. The deterministic maps of `AnchorFlowFamStmt` (`UnifACFamFlow.lean`) are

  `ψ_s = acMap κ B ω q s = revMapExt (Vr κ s B ω) (s − q)`,  `s ∈ [q,T]`,

where `Vr κ s B ω = vrev (drive κ B ω) s` (`B2Defs`). Writing `V := vrev W T` for the reversed
driver of the full horizon and `F_t := revMapExt V t`, we prove that the family is the anchored
flow in the moving coordinates:

* `isRealRevSol_shift_vrev`, `isLive_vrev_of_live`: the `s`-flow solution from `F_s x` is the
  `V`-flow solution from `x` shifted by `T − s`, so the moving window `J_s = F_s (u,v)` is **live**
  for the `s`-flow at time `s − q`, uniformly in `s` (this uses that the restarted `V`-driver
  agrees with `vrev W s` on `[0,s]`, `vrev_restart_eqOn`);
* `realRevMap_vrev_flow_detfam`: **covariance of the family**, `ψ_s (F_s x) = F_q x` on the live window
  (the real trace of the anchored identity `acMap_unif_weld`);
* `deriv_revMapExt_vrev`, `exists_unif_family_deriv_bounds`: on the moving window the derivative
  of `ψ_s` is the real, positive number `exp (∫_{T−s}^{T−q} 2/(F_σ x)² dσ)`, bounded above and
  below **uniformly in `s`** (`1 ≤ ‖ψ_s'‖ ≤ exp (2T/c²)` and `‖1/ψ_s'‖ ≤ exp (2T/c²)`), so the
  family is uniformly bi-Lipschitz on the live windows;
* `continuousOn_family_window`: continuous dependence on `s` of the window placement (the image of
  the window under `ψ_s` is *constant*: `ψ_s (F_s x) = F_q x`);
* `exists_coordChangeData_unif`: the uniform-in-`s` version of node M4-T4's local data
  `CoordChange.Data` for the anchored carrier family `F_t`, `t ∈ [0,T−q]`: one `δ`, one `m`, one
  `C` for all times, on the **fixed** live window `[u,v]`.

Sources: Sheffield, arXiv:1012.4797, §5 (coordinate change along the unzipping flow);
Duplantier–Sheffield, arXiv:0808.1560, Prop. 3.1 (node M4-T4, `CoordChange.Data`); the extension
lemma is A2-ext (`RevMapExtension.exists_revMapExt_extension`, after Cara–Rohde). The uniformity
and the family bookkeeping are own arguments; see the report for the DEVIATIONS entry.
-/

noncomputable section

open Set Metric Filter Topology Complex ComplexConjugate intervalIntegral
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 RevMapExtension CaraR

variable {W : ℝ → ℝ}

/-! ### The restarted driver and the shifted solution -/

/-- The reversed driver of horizon `s` is the driver of the `V`-flow (`V = vrev W T`) restarted at
time `T − s`, on `[0,s]`. -/
theorem vrev_restart_eqOn (W : ℝ → ℝ) {T s : ℝ} (hsT : s ≤ T) :
    EqOn (fun r => vrev W T ((T - s) + r) - vrev W T (T - s)) (vrev W s) (Icc 0 s) := by
  intro r hr
  have h1 : min (max (T - s + r) 0) T = T - s + r := by
    rw [max_eq_left (by linarith [hr.1]), min_eq_left (by linarith [hr.2])]
  have h2 : min (max (T - s) 0) T = T - s := by
    rw [max_eq_left (by linarith [hr.1, hr.2]), min_eq_left (by linarith [hr.1, hr.2])]
  have h3 : min (max r 0) s = r := by rw [max_eq_left hr.1, min_eq_left hr.2]
  simp only [vrev, h1, h2, h3]
  rw [show T - (T - s + r) = s - r by ring, show T - (T - s) = s by ring]
  ring

/-- Reverse solutions only depend on the driver on the time interval of the solution. -/
theorem isRealRevSol_congr_driver {W W' : ℝ → ℝ} {x T : ℝ} {u : ℝ → ℝ}
    (h : IsRealRevSol W x T u) (hWW : EqOn W W' (Icc 0 T)) : IsRealRevSol W' x T u := by
  refine ⟨h.1, fun t ht => ⟨(h.2 t ht).1, ?_⟩⟩
  rw [(h.2 t ht).2, hWW ht]

/-- **Solution transfer with a surplus.** If `x` is live at time `T − q` for `V = vrev W T` and
`0 < q ≤ s ≤ T`, then the `s`-flow has a solution from `F_s x = realRevMap V (T−s) x` on
`[0, s − q + ε]` for some `ε > 0`, whose values on `[0, s−q]` are `realRevMap V (T − s + r) x`. -/
theorem exists_isRealRevSol_shift_vrev (hW : Continuous W) {T q s x : ℝ} (hq0 : 0 < q)
    (hqs : q ≤ s) (hsT : s ≤ T) (hx : ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) :
    ∃ ε > 0, ε ≤ q ∧
      ∃ w, IsRealRevSol (vrev W s) (realRevMap (vrev W T) (T - s) x) (s - q + ε) w ∧
        ∀ r ∈ Icc (0 : ℝ) (s - q), w r = realRevMap (vrev W T) (T - s + r) x := by
  obtain ⟨T', h1⟩ := lt_iSup_iff.1 hx
  obtain ⟨hT'0, h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨⟨u₀, hu₀⟩, h3⟩ := lt_iSup_iff.1 h2
  have hlt : T - q < T' := (ENNReal.ofReal_lt_ofReal_iff'.1 h3).1
  have hshift : IsRealRevSol (fun r => vrev W T ((T - s) + r) - vrev W T (T - s))
      (u₀ (T - s)) (T' - (T - s)) (fun r => u₀ ((T - s) + r)) :=
    CaraR.isRealRevSol_shift (s := T - s) (T := T' - (T - s)) (by linarith) (by linarith)
      (by convert hu₀ using 1; ring)
  set eps := min (T' - (T - q)) q / 2 with hepsdef
  have hepspos : 0 < eps := by
    have h4 : 0 < min (T' - (T - q)) q := lt_min (by linarith) hq0
    rw [hepsdef]; linarith
  have hepsq : eps ≤ q := by
    have h4 : min (T' - (T - q)) q ≤ q := min_le_right _ _
    rw [hepsdef]; linarith
  have hy : realRevMap (vrev W T) (T - s) x = u₀ (T - s) :=
    RealLine.realRevMap_eq (continuous_vrev hW T) hu₀ (by linarith) (by linarith)
  refine ⟨eps, hepspos, hepsq, fun r => u₀ ((T - s) + r), ?_, ?_⟩
  · rw [hy]
    refine isRealRevSol_congr_driver (RealLine.isRealRevSol_restrict hshift ?_) fun r hr =>
      (vrev_restart_eqOn W (s := s) hsT ⟨hr.1, by linarith [hr.2, hepsq]⟩)
    have h5 : min (T' - (T - q)) q ≤ T' - (T - q) := min_le_left _ _
    rw [hepsdef] at *; linarith
  · intro r hr
    have h7 : realRevMap (vrev W T) (T - s + r) x = u₀ (T - s + r) :=
      RealLine.realRevMap_eq (continuous_vrev hW T) hu₀ (by linarith [hr.1])
        (by linarith [hr.2])
    rw [h7]

/-- **Liveness of the moving window.** The image window point `F_s x` is live for the `s`-flow at
time `s − q`, for every `s ∈ [q,T]`, as soon as `x` is live for `V` at time `T − q`. -/
theorem isLive_vrev_of_live (hW : Continuous W) {T q s x : ℝ} (hq0 : 0 < q) (hqs : q ≤ s)
    (hsT : s ≤ T) (hx : ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) :
    ENNReal.ofReal (s - q) < realHitTime (vrev W s) (realRevMap (vrev W T) (T - s) x) := by
  obtain ⟨eps, heps, -, w, hw, -⟩ := exists_isRealRevSol_shift_vrev hW hq0 hqs hsT hx
  have hpos : 0 < s - q + eps := by linarith
  refine lt_of_lt_of_le (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, hpos⟩) ?_
  exact RealLine.ofReal_le_realHitTime hpos.le hw

/-! ### Covariance of the family -/

/-- **Covariance.** `ψ_s (F_s x) = F_q x` on the live window: the family `ψ_s` is the anchored flow
`F_q` in the coordinates of `F_s`. -/
theorem realRevMap_vrev_flow_detfam (hW : Continuous W) {T q s x : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s)
    (hsT : s ≤ T) (hx : ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) :
    realRevMap (vrev W T) (T - q) x =
      realRevMap (vrev W s) (s - q) (realRevMap (vrev W T) (T - s) x) := by
  obtain ⟨T', h1⟩ := lt_iSup_iff.1 hx
  obtain ⟨hT'0, h2⟩ := lt_iSup_iff.1 h1
  obtain ⟨⟨u₀, hu₀⟩, h3⟩ := lt_iSup_iff.1 h2
  have hlt : T - q < T' := (ENNReal.ofReal_lt_ofReal_iff'.1 h3).1
  have hshift : IsRealRevSol (fun r => vrev W T ((T - s) + r) - vrev W T (T - s))
      (u₀ (T - s)) (T' - (T - s)) (fun r => u₀ ((T - s) + r)) :=
    CaraR.isRealRevSol_shift (s := T - s) (T := T' - (T - s)) (by linarith) (by linarith)
      (by convert hu₀ using 1; ring)
  have hres : IsRealRevSol (vrev W s) (u₀ (T - s)) (s - q) (fun r => u₀ ((T - s) + r)) :=
    isRealRevSol_congr_driver (RealLine.isRealRevSol_restrict hshift (by linarith)) fun r hr =>
      (vrev_restart_eqOn W (s := s) hsT ⟨hr.1, hr.2.trans (by linarith)⟩)
  have hL : realRevMap (vrev W T) (T - q) x = u₀ (T - q) :=
    RealLine.realRevMap_eq (continuous_vrev hW T) hu₀ (by linarith) (by linarith)
  have hR : realRevMap (vrev W T) (T - s) x = u₀ (T - s) :=
    RealLine.realRevMap_eq (continuous_vrev hW T) hu₀ (by linarith) (by linarith)
  rw [hL, hR]
  have hval : realRevMap (vrev W s) (s - q) (u₀ (T - s)) = u₀ (T - q) := by
    have h6 : realRevMap (vrev W s) (s - q) (u₀ (T - s)) = (fun r => u₀ ((T - s) + r)) (s - q) :=
      RealLine.realRevMap_eq (continuous_vrev hW s) hres (by linarith) le_rfl
    have h7 : (fun r => u₀ ((T - s) + r)) (s - q) = u₀ (T - q) := by
      show u₀ ((T - s) + (s - q)) = u₀ (T - q)
      rw [show (T - s) + (s - q) = T - q by ring]
    rw [h6, h7]
  rw [hval]

/-! ### Derivatives: the family on the moving windows -/

/-- Uniform clearance of the carrier on the live window (all horizons at once). -/
theorem exists_unif_clearance {V : ℝ → ℝ} (hVc : Continuous V) {T : ℝ} (hT : 0 ≤ T) {u v : ℝ}
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal T < realHitTime V x) :
    ∃ c > 0, ∀ x ∈ Icc u v, ∀ σ ∈ Icc (0 : ℝ) T, c ≤ ‖realRevMap V σ x‖ := by
  obtain ⟨ρ, hρ, c, hc, hgood⟩ := exists_unif_ball_isCRevSol hVc hT (J := Icc u v) isCompact_Icc hLive
  refine ⟨c, hc, fun x hx σ hσ => ?_⟩
  obtain ⟨u, hu, hub⟩ := hgood x hx T ⟨hT, le_rfl⟩ x (Metric.mem_ball_self hρ)
  obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hLive x hx)
  have h1 : u σ = (w σ : ℂ) :=
    isCRevSol_unique (isCRevSol_restrict hu hσ.2)
      (isCRevSol_ofReal (RealLine.isRealRevSol_restrict hw hσ.2)) ⟨hσ.1, le_rfl⟩
  have h2 : realRevMap V σ x = w σ := RealLine.realRevMap_eq hVc hw hσ.1 hσ.2
  have h3 : |w σ| = ‖u σ‖ := by
    have h4 : ‖(w σ : ℂ)‖ = ‖u σ‖ := by rw [← h1]
    rwa [Complex.norm_real] at h4
  rw [h2, Real.norm_eq_abs, h3]
  exact hub σ hσ

/-- **Derivative of the family on the moving window.** On the image window point `F_s x` the
derivative of `ψ_s` is the real positive number `exp (∫₀^{s−q} 2/(F_{T−s+r} x)² dr)` — the carrier
integrand, so the uniform clearance of the carrier bounds it uniformly in `s`. -/
theorem deriv_revMapExt_vrev (hW : Continuous W) {T q s x : ℝ} (hq0 : 0 < q) (hqs : q ≤ s)
    (hsT : s ≤ T) (hx : ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) :
    deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x) =
      ((Real.exp (∫ r in (0 : ℝ)..(s - q),
        2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2) : ℝ) : ℂ) := by
  have hlive := isLive_vrev_of_live hW hq0 hqs hsT hx
  have h1 := deriv_revMapExt_eq_of_live (W := vrev W s) (T := s - q) (continuous_vrev hW s)
    (by linarith) hlive (t := s - q) ⟨by linarith, le_rfl⟩
  have h2 : (∫ r in (0 : ℝ)..(s - q),
        2 / (realRevMap (vrev W s) r (realRevMap (vrev W T) (T - s) x)) ^ 2)
      = ∫ r in (0 : ℝ)..(s - q), 2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2 :=
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le (by linarith)] at hr
      have hflow := realRevMap_vrev_flow_detfam hW (T := T) (s := s) (q := s - r) (x := x)
        (by linarith [hr.1, hr.2, hq0]) (by linarith [hr.1]) hsT
        ((ENNReal.ofReal_le_ofReal (by linarith [hr.2])).trans_lt hx)
      rw [show s - (s - r) = r by ring, show T - (s - r) = T - s + r by ring] at hflow
      rw [← hflow]
  rw [h1, h2]

/-- **Uniform-in-`s` derivative bounds on the moving windows.** There are constants: for every
`s ∈ [q,T]` and every point `x` of the live window, `ψ_s'(F_s x)` is real and positive with
`1 ≤ ‖ψ_s'(F_s x)‖ ≤ exp (2T/c²)` and `‖1/ψ_s'(F_s x)‖ ≤ exp (2T/c²)`, where `c` is the uniform
clearance of the carrier. -/
theorem exists_unif_family_deriv_bounds (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q)
    (hqT : q ≤ T) {u v : ℝ}
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) :
    ∃ M : ℝ, 0 < M ∧ ∀ s ∈ Icc q T, ∀ x ∈ Icc u v,
      1 ≤ ‖deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x)‖ ∧
      ‖deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x)‖ ≤ M ∧
      ‖1 / deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x)‖ ≤ M ∧
      (deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x)).im = 0 ∧
      0 < (deriv (revMapExt (vrev W s) (s - q)) (realRevMap (vrev W T) (T - s) x)).re := by
  obtain ⟨c₀, hc₀, hclear⟩ := exists_unif_clearance (V := vrev W T) (continuous_vrev hW T)
    (T := T - q) (by linarith) hLive
  have hMpos : 0 < Real.exp (2 * T / c₀ ^ 2) := Real.exp_pos _
  refine ⟨Real.exp (2 * T / c₀ ^ 2), hMpos, fun s hs x hx => ?_⟩
  have hpt : ∀ r ∈ Icc (0 : ℝ) (s - q),
      2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2 ≤ 2 / c₀ ^ 2 := by
    intro r hr
    have hσI : T - s + r ∈ Icc (0 : ℝ) (T - q) :=
      ⟨by linarith [hr.1, hs.2], by linarith [hr.2]⟩
    have hcs : c₀ ≤ |realRevMap (vrev W T) (T - s + r) x| := by
      have h2 := hclear x hx (T - s + r) hσI
      rwa [Real.norm_eq_abs] at h2
    have hcs2 : c₀ ^ 2 ≤ (realRevMap (vrev W T) (T - s + r) x) ^ 2 := by
      have h2 := pow_le_pow_left₀ hc₀.le hcs 2
      rwa [sq_abs] at h2
    rw [div_le_div_iff₀ (lt_of_lt_of_le (pow_pos hc₀ 2) hcs2) (pow_pos hc₀ 2)]
    nlinarith
  have hnonneg : 0 ≤ ∫ r in (0 : ℝ)..(s - q),
      2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith [hs.1]) fun r _ =>
      div_nonneg (by norm_num) (sq_nonneg _)
  have hIle : (∫ r in (0 : ℝ)..(s - q), 2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2)
      ≤ 2 * T / c₀ ^ 2 := by
    have h1 : |∫ r in (0 : ℝ)..(s - q), 2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2|
        ≤ 2 / c₀ ^ 2 * (s - q) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s - q)
        (C := 2 / c₀ ^ 2) (f := fun r => 2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2)
        (fun r hr => by
          rw [uIoc_of_le (by linarith [hs.1])] at hr
          rw [Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (by norm_num) (sq_nonneg _))]
          exact hpt r ⟨hr.1.le, hr.2⟩)
      rwa [sub_zero, abs_of_nonneg (by linarith [hs.1])] at this
    rw [abs_of_nonneg hnonneg] at h1
    refine h1.trans ?_
    rw [show 2 / c₀ ^ 2 * (s - q) = 2 * (s - q) / c₀ ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by linarith [hs.2]) (by positivity)
  rw [deriv_revMapExt_vrev hW hq0 hs.1 hs.2 (hLive x hx)]
  set I := ∫ r in (0 : ℝ)..(s - q), 2 / (realRevMap (vrev W T) (T - s + r) x) ^ 2 with hI
  have hnorm : ‖((Real.exp I : ℝ) : ℂ)‖ = Real.exp I := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos I)]
  have him : (((Real.exp I : ℝ) : ℂ)).im = 0 := by simp
  have hre : (((Real.exp I : ℝ) : ℂ)).re = Real.exp I := by
    rw [Complex.ofReal_exp, Complex.exp_re, Complex.ofReal_re, Complex.ofReal_im,
      Real.cos_zero, mul_one]
  have hge1 : 1 ≤ ‖((Real.exp I : ℝ) : ℂ)‖ := by
    rw [hnorm]
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp I := Real.exp_le_exp.2 hnonneg
  have hle : ‖((Real.exp I : ℝ) : ℂ)‖ ≤ Real.exp (2 * T / c₀ ^ 2) := by
    rw [hnorm]
    exact Real.exp_le_exp.2 (by rw [hI]; exact hIle)
  have hinv : ‖1 / ((Real.exp I : ℝ) : ℂ)‖ ≤ Real.exp (2 * T / c₀ ^ 2) := by
    rw [norm_div, norm_one]
    have h1 : 1 / ‖((Real.exp I : ℝ) : ℂ)‖ ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le one_pos hge1)]
      exact hge1
    exact h1.trans (Real.one_le_exp (by
      have hT0 : 0 < T := lt_of_lt_of_le hq0 hqT
      positivity))
  exact ⟨hge1, hle, hinv, him, by rw [hre]; positivity⟩

/-! ### Continuous dependence on `s`, and the uniform `CoordChange.Data` -/

end RegUnif
end QuantumZipper
