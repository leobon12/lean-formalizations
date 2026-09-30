import QuantumZipper.Proofs.Zipper.SWCoreB5Main
import QuantumZipper.Proofs.Zipper.SWCoreWinR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (1): uniform boundary transport over a set of class maps (family version of SWC-B5)

Decision D64. The proof of SWC-B5 (`SWCoreB5Main.transport_nonneg`,
`SWCoreB5Stmt.bdryTransportUnifGood_of_window`) uses the class core `BdryDistClassGood` only for
the maps it transports. Here it is restated with the distortion bound assumed only on a set
`S ⊆ BdryClass a b ρ M m` (e.g. a finite-parameter family covered by `swcn2_bdryDistFam`).
The proof text is that of SWC-B5 (Sheffield–Wang, arXiv:1605.06171, proof of Thm 4.3, p. 19),
with the one use of the class core replaced.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

set_option maxHeartbeats 1000000 in
/-- **Uniform transport over a set of class maps, nonnegative test functions** (one field
sample): `transport_nonneg` with the class core replaced by the distortion bound on `S`. -/
theorem transport_nonneg_fam {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} {c c' : ℕ → ℝ}
    (hc : Tendsto c atTop (𝓝 1)) (hc' : Tendsto c' atTop (𝓝 1))
    (hWin : F1.BdryWindowLimits γ x c c') (hx : IsRegularSample x)
    [IsLocallyFiniteMeasure (qBoundaryMeasure γ x)] (a b ρ M m : ℚ) (hρ : (0 : ℝ) < ρ) (hm : (0 : ℝ) < m)
    {S : Set (ℂ → ℂ)} (hS : S ⊆ BdryClass a b ρ M m)
    (hDS : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ S, ∀ t ∈ Icc (a : ℝ) b,
      |avgReg (coordChange x ψ (Qc γ)) k (t : ℂ) - Qc γ * CoordChange.cc ψ t (radius k) -
        evalReg x (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤ η)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo (a : ℝ) b) (hf0 : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ ψ ∈ S,
      ∫⁻ t, ENNReal.ofReal (f t) ∂bdryApprox γ (coordChange x ψ (Qc γ)) k ≤
          ENNReal.ofReal ((∫ u in Icc (ψ (a : ℝ)).re (ψ (b : ℝ)).re,
            f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc (a : ℝ) b) u)
              ∂qBoundaryMeasure γ x) + ε) ∧
        ENNReal.ofReal ((∫ u in Icc (ψ (a : ℝ)).re (ψ (b : ℝ)).re,
            f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc (a : ℝ) b) u)
              ∂qBoundaryMeasure γ x) - ε) ≤
          ∫⁻ t, ENNReal.ofReal (f t) ∂bdryApprox γ (coordChange x ψ (Qc γ)) k := by
  set ν := qBoundaryMeasure γ x with hν
  rcases le_or_gt (b : ℝ) a with hba | hab
  · have hf_zero : ∀ t, f t = 0 := fun t => image_eq_zero_of_notMem_tsupport fun h => by
      have := hfs h; linarith [this.1, this.2]
    refine Eventually.of_forall fun k ψ _ => ⟨?_, ?_⟩ <;> simp [hf_zero, hε.le]
  rcases le_or_gt 0 (M : ℝ) with hM | hM
  swap
  · refine Eventually.of_forall fun k ψ hψS => absurd ?_ (not_le.2 hM)
    have hψ := hS hψS
    exact (norm_nonneg _).trans
      (hψ.2.1 _ (self_subset_thickening hρ _ (ofReal_mem_segC ⟨le_rfl, hab.le⟩)))
  obtain ⟨d0, hd0, hfs'⟩ := exists_inner hab hfc hfs
  obtain ⟨a', ha'def⟩ : ∃ a' : ℝ, a' = (a : ℝ) + d0 := ⟨_, rfl⟩
  obtain ⟨b', hb'def⟩ : ∃ b' : ℝ, b' = (b : ℝ) - d0 := ⟨_, rfl⟩
  have ha' : (a : ℝ) < a' := by linarith
  have hb' : b' < b := by linarith
  set δD := min ((ρ : ℝ) / 8) (min ((a' - a) / 4) ((b - b') / 4)) with hδD
  set CD : ℝ := 32 * M / ρ ^ 2 with hCD
  have hCD0 : 0 ≤ CD := by positivity
  have hδD0 : 0 < δD := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  set r0 := CoordChange.Data.r0 δD m CD with hr0
  have hr00 : 0 < r0 := lt_min hδD0 (div_pos hm (by positivity))
  set V := ν.real (Icc (-(M : ℝ) - 1) (M + 1)) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  obtain ⟨Fm, hFm⟩ := hf.bounded_above_of_compact_support hfc
  have hFm' : ∀ t, f t ≤ Fm := fun t => (le_abs_self _).trans (by simpa using hFm t)
  have hFm0 : 0 ≤ Fm := (hf0 0).trans (hFm' 0)
  set B := Fm * V with hB
  have hB0 : 0 ≤ B := mul_nonneg hFm0 hV0
  set θ := ε / (3 * B + 3 + ε) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by positivity)]; linarith
  have hθB : θ * (B + ε / 3) ≤ ε / 3 := by
    rw [hθ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  set ω := ε / (3 * (2 * V + 1)) with hω
  have hω0 : 0 < ω := by positivity
  have hωV : 2 * ω * V + ω = ε / 3 := by rw [hω]; field_simp
  obtain ⟨N, hN, hcN, hc'N⟩ : ∃ N : ℕ, 1 ≤ N ∧ c N ∈ Ioo (1 - θ / 4) (1 + θ / 4) ∧
      c' N ∈ Ioo (1 - θ / 4) (1 + θ / 4) :=
    ((eventually_ge_atTop 1).and ((hc.eventually (Ioo_mem_nhds (by linarith) (by linarith))).and
      (hc'.eventually (Ioo_mem_nhds (by linarith) (by linarith))))).exists
  set η := Real.log (1 + θ / 4) with hη
  have hη0 : 0 < η := Real.log_pos (by linarith)
  have heη : Real.exp η = 1 + θ / 4 := Real.exp_log (by linarith)
  obtain ⟨δf, hδf, hδf'⟩ :=
    Metric.uniformContinuous_iff.1 (hfc.uniformContinuous_of_continuous hf) ω hω0
  have hunif : ∀ s t : ℝ, |s - t| < δf → |f s - f t| ≤ ω := fun s t hst => by
    have := hδf' (a := s) (b := t) (by rwa [Real.dist_eq])
    rw [Real.dist_eq] at this
    exact this.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set h : ℝ := min (1 / 2) (min (m * d0 / 2) (min (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1)))))) with hh
  have hh0 : 0 < h := lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity))))
  have hh1 : h ≤ 1 / 2 := min_le_left _ _
  have hh2 := min_le_right (1 / 2) (min (m * d0 / 2) (min (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1))))))
  have hh3 := min_le_right (m * d0 / 2) (min (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1)))))
  have hh4 := min_le_right (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1))))
  have hh5 := min_le_right (m * r0 / 2) (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1)))
  have hhd : 2 * h ≤ m * d0 := by
    have := min_le_left (m * d0 / 2) (min (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1))))); linarith
  have hhf : 2 * h ≤ m * δf := by
    have := min_le_left (m * δf / 2) (min (m * r0 / 2)
      (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1)))); linarith
  have hhr : 2 * h ≤ m * r0 := by
    have := min_le_left (m * r0 / 2) (Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1))); linarith
  have hhl : 4 * CD / m * (2 * h / m) ≤ Real.log 2 / (2 * N) := by
    have h6 : h ≤ Real.log 2 / (2 * N) * m ^ 2 / (8 * (CD + 1)) := by linarith
    rw [le_div_iff₀ (by positivity)] at h6
    have e : 4 * CD / m * (2 * h / m) = 8 * CD * h / m ^ 2 := by field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨T, φ, hφc, hφs, hφ0, hφ1, hφle, hφsupp⟩ := exists_fine_partition (M : ℝ) hh0
  set ε₁ := ω / (T.card * (Fm + ω) + 1) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  have hε₁T : ε₁ * (T.card * (Fm + ω)) ≤ ω := by
    rw [hε₁, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) hω0.le
  set ilo := ⌈-Real.log (max (4 * (M : ℝ) / ρ) m) / (Real.log 2 / N) + 1 / 2⌉ with hilo
  set ihi := ⌈-Real.log (m : ℝ) / (Real.log 2 / N) + 1 / 2⌉ with hihi
  have E4 : ∀ᶠ k : ℕ in atTop, ∀ n : T, ∀ i ∈ Finset.Icc ilo ihi,
      ((Int.toNat ((k : ℤ) * N + i - 2) : ℕ) : ℤ) = (k : ℤ) * N + i - 2 ∧
      ENNReal.ofReal (c N) * ∫⁻ u, F1.bSupWin γ x N (Int.toNat ((k : ℤ) * N + i - 2)) u *
          ENNReal.ofReal (φ n u) ≤ ENNReal.ofReal ((∫ u, φ n u ∂ν) + ε₁) ∧
      ENNReal.ofReal ((∫ u, φ n u ∂ν) - ε₁) ≤ ENNReal.ofReal (c' N) *
        ∫⁻ u, F1.bInfWin γ x N (Int.toNat ((k : ℤ) * N + i - 2)) u *
          ENNReal.ofReal (φ n u) := by
    refine eventually_all.2 fun n => (eventually_all_finset _).2 fun i _ => ?_
    have hJ : ∀ᶠ k : ℕ in atTop,
        ((Int.toNat ((k : ℤ) * N + i - 2) : ℕ) : ℤ) = (k : ℤ) * N + i - 2 := by
      filter_upwards [eventually_ge_atTop (Int.toNat (2 - i))] with k hk
      have h2 := Int.self_le_toNat (2 - i)
      have hkN : (k : ℤ) ≤ (k : ℤ) * N :=
        le_mul_of_one_le_right (by positivity) (by exact_mod_cast hN)
      have hk' : ((Int.toNat (2 - i) : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
      exact Int.toNat_of_nonneg (by linarith)
    have hJt : Tendsto (fun k : ℕ => Int.toNat ((k : ℤ) * N + i - 2)) atTop atTop := by
      refine tendsto_atTop.2 fun B' => ?_
      filter_upwards [hJ, eventually_ge_atTop (B' + Int.toNat (2 - i))] with k hk hkB
      have h2 := Int.self_le_toNat (2 - i)
      have hkN : (k : ℤ) ≤ (k : ℤ) * N :=
        le_mul_of_one_le_right (by positivity) (by exact_mod_cast hN)
      have hkB' : ((B' : ℕ) : ℤ) + ((Int.toNat (2 - i) : ℕ) : ℤ) ≤ k := by exact_mod_cast hkB
      have : ((B' : ℕ) : ℤ) ≤ ((Int.toNat ((k : ℤ) * N + i - 2) : ℕ) : ℤ) := by
        rw [hk]; linarith
      exact_mod_cast this
    obtain ⟨W1, W2⟩ := hWin N hN (φ n) (hφc n) (hφs n) (hφ0 n)
    have T1 := W1.comp hJt
    have T2 := W2.comp hJt
    have hν0 : 0 ≤ ∫ u, φ n u ∂ν := integral_nonneg (hφ0 n)
    have U1 := T1.eventually (gt_mem_nhds
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith : (∫ u, φ n u ∂ν) <
        (∫ u, φ n u ∂ν) + ε₁)))
    have U2 : ∀ᶠ k : ℕ in atTop, ENNReal.ofReal ((∫ u, φ n u ∂ν) - ε₁) ≤
        ENNReal.ofReal (c' N) * ∫⁻ u, F1.bInfWin γ x N (Int.toNat ((k : ℤ) * N + i - 2)) u *
          ENNReal.ofReal (φ n u) := by
      by_cases hp : 0 < (∫ u, φ n u ∂ν) - ε₁
      · exact (T2.eventually (lt_mem_nhds
          ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)))).mono
          fun k hk => hk.le
      · exact Eventually.of_forall fun k => by
          rw [ENNReal.ofReal_of_nonpos (not_lt.1 hp)]; exact zero_le
    filter_upwards [hJ, U1, U2] with k h1 h2 h3
    exact ⟨h1, h2.le, h3⟩
  have E1 := hDS (η / γ) (by positivity)
  have E2 : ∀ᶠ k in atTop, radius k ≤ r0 := F1.tendsto_radius_zero.eventually (ge_mem_nhds hr00)
  have E3 : ∀ᶠ k in atTop, |Qc γ| * (4 * CD / m * radius k) ≤ η / γ := by
    have : Tendsto (fun k => |Qc γ| * (4 * CD / m * radius k)) atTop (𝓝 0) := by
      simpa using (F1.tendsto_radius_zero.const_mul (4 * CD / m)).const_mul (|Qc γ|)
    exact this.eventually (ge_mem_nhds (by positivity))
  filter_upwards [E1, E2, E3, E4] with k hk1 hk2 hk3 hk4
  intro ψ hψS
  have hψ := hS hψS
  have hDd := data_of_class hψ hρ hm ha' hb'
  have hΔ : ∀ t ∈ Icc a' b', |avgReg (coordChange x ψ (Qc γ)) k (t : ℂ) -
      Qc γ * Real.log ‖deriv ψ t‖ -
        evalReg x (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤
      2 * η / γ := by
    intro t ht
    have htab : t ∈ Icc (a : ℝ) b := ⟨ha'.le.trans ht.1, ht.2.trans hb'.le⟩
    have hcc := hDd.abs_cc_sub_log_le ht (radius_pos k) hk2
    rw [← hDd.norm_deriv ht] at hcc
    have h1 := hk1 ψ hψS t htab
    have h2 : |Qc γ| * |CoordChange.cc ψ t (radius k) - Real.log ‖deriv ψ t‖| ≤ η / γ :=
      (mul_le_mul_of_nonneg_left hcc (abs_nonneg _)).trans hk3
    calc _ ≤ η / γ + η / γ := abs_dist_le h1 h2
      _ = 2 * η / γ := by ring
  have hfs'' : ∀ t, f t ≠ 0 → t ∈ Icc a' b' := fun t ht => by
    have := hfs' t ht; exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hdpos : ∀ t ∈ Icc a' b', 0 < ‖deriv ψ t‖ := fun t ht =>
    hm.trans_le (hψ.2.2.2.2 t ⟨ha'.le.trans ht.1, ht.2.trans hb'.le⟩)
  obtain ⟨cmp1, cmp2⟩ := cmp_of_dist hγ hf hf0 hfs'' hdpos hΔ
  have hcont : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc (a : ℝ) b) :=
    Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun t ht =>
        self_subset_thickening hρ _ (ofReal_mem_segC ht))
  set Φ := CoordChange.extIso hab.le hcont hψ.2.2.2.1 with hΦdef
  have hΦ : ∀ t ∈ Icc (a : ℝ) b, Φ t = (ψ t).re := fun t ht => CoordChange.extIso_eq _ _ _ ht
  rw [target_eq_of_iso Φ hΦ hfs ν hab.le]
  obtain ⟨Yu, Yl, hYu, hYl, hUp, hLo⟩ := perMap_sandwich (γ := γ) hx hψ hρ hm ha' hb'
    (a'' := a + 2 * d0) (b'' := b - 2 * d0) (by linarith) (by linarith) hDd hCD0 Φ hΦ hf hfc
    hf0 hfs' hFm' (d0 := d0) (by linarith) (by linarith) hω0 hunif hN hh0 hh1 hhd hhf hhr hhl
    hφc hφs hφ0 hφ1 hφle hφsupp ν hε₁0.le hk4
  set L := ∫ u, f (Φ.symm u) ∂ν with hL
  have hL0 : 0 ≤ L := integral_nonneg fun u => hf0 _
  have hK : IsCompact (Icc (-(M : ℝ) - 1) (M + 1)) := isCompact_Icc
  have hLB : L ≤ B := by
    calc L ≤ ∫ u, Fm * (Icc (-(M : ℝ) - 1) (M + 1)).indicator 1 u ∂ν := by
          refine integral_mono ((hf.comp Φ.symm.continuous).integrable_of_hasCompactSupport
            (hfc.comp_homeomorph Φ.symm.toHomeomorph))
            (((integrable_indicator_iff hK.isClosed.measurableSet).2
              (integrableOn_const hK.measure_lt_top.ne)).const_mul _) fun u => ?_
          by_cases hu : f (Φ.symm u) = 0
          · show f (Φ.symm u) ≤ _
            rw [hu]
            have : 0 ≤ (Icc (-(M : ℝ) - 1) (M + 1)).indicator (1 : ℝ → ℝ) u :=
              indicator_nonneg (fun _ _ => zero_le_one) u
            positivity
          have ht := hfs' _ hu
          have htab : Φ.symm u ∈ Icc (a : ℝ) b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
          have hre : (ψ (Φ.symm u)).re = u := by rw [← hΦ _ htab]; simp
          have hMb := hψ.2.1 _ (self_subset_thickening hρ _ (ofReal_mem_segC htab))
          have h2 := (Complex.abs_re_le_norm (ψ (Φ.symm u))).trans hMb
          rw [hre] at h2
          show f (Φ.symm u) ≤ _
          rw [indicator_of_mem (show u ∈ Icc (-(M : ℝ) - 1) (M + 1) from
            ⟨by linarith [(abs_le.1 h2).1], by linarith [(abs_le.1 h2).2]⟩), Pi.one_apply,
            mul_one]
          exact hFm' _
      _ = B := by rw [integral_const_mul, integral_indicator_one hK.isClosed.measurableSet]
  have hYu' : Yu ≤ L + ε / 3 := by linarith
  have hYl' : L - ε / 3 ≤ Yl := by linarith
  have hcN0 : 0 < c N := by linarith [hcN.1]
  constructor
  · have hA : cmpInt γ x ψ f a' b' k ≤ ENNReal.ofReal (1 / c N) * ENNReal.ofReal Yu := by
      calc cmpInt γ x ψ f a' b' k = ENNReal.ofReal (1 / c N) *
            (ENNReal.ofReal (c N) * cmpInt γ x ψ f a' b' k) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hcN0.ne',
              ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    have hr0' : 0 ≤ Real.exp η * (1 / c N) := by positivity
    calc _ ≤ ENNReal.ofReal (Real.exp η) * cmpInt γ x ψ f a' b' k := cmp1
      _ ≤ ENNReal.ofReal (Real.exp η) * (ENNReal.ofReal (1 / c N) * ENNReal.ofReal Yu) := by
          gcongr
      _ = ENNReal.ofReal (Real.exp η * (1 / c N) * Yu) := by
          rw [ENNReal.ofReal_mul hr0', ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      _ ≤ _ := ENNReal.ofReal_le_ofReal
          (up_arith hL0 hLB hYu' hε hθ0.le hθ1 hθB hcN.1 heη)
  · by_cases hLε : 0 < L - ε
    swap
    · rw [ENNReal.ofReal_of_nonpos (not_lt.1 hLε)]; exact zero_le
    have hc'0 : 0 < c' N := by linarith [hc'N.1]
    have hq : ENNReal.ofReal (c' N * Real.exp η) * ENNReal.ofReal (L - ε) ≤
        ENNReal.ofReal (c' N * Real.exp η) *
          ∫⁻ t, ENNReal.ofReal (f t) ∂bdryApprox γ (coordChange x ψ (Qc γ)) k := by
      calc _ = ENNReal.ofReal (c' N * Real.exp η * (L - ε)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal Yl := ENNReal.ofReal_le_ofReal
            (lo_arith hLB hYl' hLε hθ0.le hθ1 hθB hε hc'0 hc'N.2 heη)
        _ ≤ ENNReal.ofReal (c' N) * cmpInt γ x ψ f a' b' k := hLo
        _ ≤ ENNReal.ofReal (c' N) * (ENNReal.ofReal (Real.exp η) *
            ∫⁻ t, ENNReal.ofReal (f t) ∂bdryApprox γ (coordChange x ψ (Qc γ)) k) := by gcongr
        _ = _ := by rw [ENNReal.ofReal_mul hc'0.le, mul_assoc]
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).1 hq

/-- **Uniform boundary transport over a set of class maps** (one field sample, signed test
functions; family version of `bdryTransportUnifGood_of_window`). -/
theorem transport_fam {γ : ℝ} (hγ : 0 < γ) {x : FieldSample}
    {c c' : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 1)) (hc' : Tendsto c' atTop (𝓝 1))
    (hWin : F1.BdryWindowLimits γ x c c') (hx : IsRegularSample x)
    [IsLocallyFiniteMeasure (qBoundaryMeasure γ x)] (a b ρ M m : ℚ) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {S : Set (ℂ → ℂ)} (hS : S ⊆ BdryClass a b ρ M m)
    (hDS : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ S, ∀ t ∈ Icc (a : ℝ) b,
      |avgReg (coordChange x ψ (Qc γ)) k (t : ℂ) - Qc γ * CoordChange.cc ψ t (radius k) -
        evalReg x (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤ η)
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioo (a : ℝ) b)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ψ ∈ S,
      |∫ t, f t ∂bdryApprox γ (coordChange x ψ (Qc γ)) k -
        ∫ u in Icc (ψ (a : ℝ)).re (ψ (b : ℝ)).re,
          f (Function.invFunOn (fun t : ℝ => (ψ t).re) (Icc (a : ℝ) b) u) ∂qBoundaryMeasure γ x| ≤ η := by
  set ν := qBoundaryMeasure γ x with hν
  rcases le_or_gt (b : ℝ) a with hba | hab
  · have hf_zero : ∀ t, f t = 0 := fun t => image_eq_zero_of_notMem_tsupport fun h => by
      have := hfs h; linarith [this.1, this.2]
    refine Eventually.of_forall fun k ψ _ => ?_
    simp [hf_zero, hη.le]
  set fp : ℝ → ℝ := (fun y => max y 0) ∘ f with hfp
  set fn : ℝ → ℝ := (fun y => max (-y) 0) ∘ f with hfn
  have hfpc : Continuous fp := (continuous_id.max continuous_const).comp hf
  have hfnc : Continuous fn := (continuous_neg.max continuous_const).comp hf
  have hfpcs : HasCompactSupport fp := hfc.comp_left (by simp)
  have hfncs : HasCompactSupport fn := hfc.comp_left (by simp)
  have hfps : tsupport fp ⊆ Ioo (a : ℝ) b := (tsupport_comp_subset (by simp) f).trans hfs
  have hfns : tsupport fn ⊆ Ioo (a : ℝ) b := (tsupport_comp_subset (by simp) f).trans hfs
  have ep : ∀ t, ENNReal.ofReal (fp t) = ENNReal.ofReal (f t) := fun t => F1.ofReal_max_zero _
  have en : ∀ t, ENNReal.ofReal (fn t) = ENNReal.ofReal (-f t) := fun t => F1.ofReal_max_zero _
  have hsplit : ∀ t, f t = fp t - fn t := fun t => by
    simp only [hfp, hfn, Function.comp_apply]; exact (max_zero_sub_max_neg_zero_eq_self _).symm
  have Pp := transport_nonneg_fam hγ hc hc' hWin hx a b ρ M m hρ hm hS hDS hfpc hfpcs hfps
    (fun t => le_max_right _ _) (ε := η / 4) (by positivity)
  have Pn := transport_nonneg_fam hγ hc hc' hWin hx a b ρ M m hρ hm hS hDS hfnc hfncs hfns
    (fun t => le_max_right _ _) (ε := η / 4) (by positivity)
  filter_upwards [Pp, Pn] with k hp hn ψ hψS
  have hψ := hS hψS
  obtain ⟨hp1, hp2⟩ := hp ψ hψS
  obtain ⟨hn1, hn2⟩ := hn ψ hψS
  set μ := bdryApprox γ (coordChange x ψ (Qc γ)) k with hμ
  -- the targets through an order isomorphism
  have hcont : ContinuousOn (fun t : ℝ => (ψ t).re) (Icc (a : ℝ) b) :=
    Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun t ht =>
        self_subset_thickening hρ _ (ofReal_mem_segC ht))
  set Φ := CoordChange.extIso hab.le hcont hψ.2.2.2.1 with hΦdef
  have hΦ : ∀ t ∈ Icc (a : ℝ) b, Φ t = (ψ t).re := fun t ht => CoordChange.extIso_eq _ _ _ ht
  rw [target_eq_of_iso Φ hΦ hfps ν hab.le] at hp1 hp2
  rw [target_eq_of_iso Φ hΦ hfns ν hab.le] at hn1 hn2
  rw [target_eq_of_iso Φ hΦ hfs ν hab.le]
  set Lp := ∫ u, fp (Φ.symm u) ∂ν with hLp
  set Ln := ∫ u, fn (Φ.symm u) ∂ν with hLn
  have hLp0 : 0 ≤ Lp := integral_nonneg fun u => le_max_right _ _
  have hLn0 : 0 ≤ Ln := integral_nonneg fun u => le_max_right _ _
  have hL : ∫ u, f (Φ.symm u) ∂ν = Lp - Ln := by
    rw [hLp, hLn, ← integral_sub (f := fun u => fp (Φ.symm u)) (g := fun u => fn (Φ.symm u))
      ((hfpc.comp Φ.symm.continuous).integrable_of_hasCompactSupport
        (hfpcs.comp_homeomorph Φ.symm.toHomeomorph))
      ((hfnc.comp Φ.symm.continuous).integrable_of_hasCompactSupport
        (hfncs.comp_homeomorph Φ.symm.toHomeomorph))]
    exact integral_congr_ae (ae_of_all _ fun u => hsplit _)
  rw [hL]
  simp_rw [ep] at hp1 hp2
  simp_rw [en] at hn1 hn2
  have hpt : ∫⁻ t, ENNReal.ofReal (f t) ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp1
  have hnt : ∫⁻ t, ENNReal.ofReal (-f t) ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hn1
  have ip : Integrable fp μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable hfpc.aestronglyMeasurable
      (Eventually.of_forall fun t => le_max_right _ _)).1 ?_
    simp_rw [ep]; exact hpt
  have in' : Integrable fn μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable hfnc.aestronglyMeasurable
      (Eventually.of_forall fun t => le_max_right _ _)).1 ?_
    simp_rw [en]; exact hnt
  have hi : Integrable f μ := by
    have : f = fun t => fp t - fn t := funext hsplit
    rw [this]; exact ip.sub in'
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
  have u1 := ENNReal.toReal_le_of_le_ofReal (by positivity) hp1
  have u2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hn1
  have l1 := (ENNReal.ofReal_le_iff_le_toReal hpt).1 hp2
  have l2 := (ENNReal.ofReal_le_iff_le_toReal hnt).1 hn2
  rw [abs_le]
  constructor <;> linarith

end SWCore
end QuantumZipper
