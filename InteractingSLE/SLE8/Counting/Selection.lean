import InteractingSLE.SLE8.Counting.ChangeOfMeasure
import QuantumZipper.Proofs.Zipper.UnzipInvariance

/-!
# Steps 1–3 of the proof of Proposition 4.1: selection of a terminal time (deterministic)

SLE₈ note `source/sle8-continuity.pdf`, §4, pp. 8–9 (transcription `source/sle8/sle8-continuity.md`,
anchor `prop-4.1-proof`, Steps 1–3).

Everything here is deterministic (one sample path). The driver is a continuous `W` with `W 0 = 0` in the
event `Ω_M` of (2.11) (`DriverBound M W`). For every grid time `T` the reverse flow from `(T, iy)` is
driven by a continuous extension `V T` of the reversed driver `s ↦ W_{T-s} - W_T` on `[0, T]`
(`IsRevExt`; in the probabilistic part `V T = √8 · revBM B T`, a Brownian motion for all nonnegative
times, as in the note's §3.1).

## Main results

* `gridT_gridT`: nesting of the grids (4.5);
* `reverse_bounds`: the bounds (4.6) and the transfer (4.10) of the finest large derivative;
* `smallImage_of_lt`: Step 2, a small image height gives the two-point event of Lemma 3.2 at a dyadic
  box (4.8)–(4.11);
* `trialEventAt_of_many`: Step 3, many large scales without small image heights give the trial event
  `E_{k_*,T}` of (4.22) ((4.14)–(4.21));
* `selection`: the resulting dichotomy for every `t` with `|𝓘_n(t)| > r⁷`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

open QuantumZipper

/-! ## The extended reversed driver -/

/-- `V` extends the reversed driver `s ↦ W_{T-s} - W_T` of (2.5) from `[0, T]`. -/
def IsRevExt (W V : ℝ → ℝ) (T : ℝ) : Prop := ∀ s ∈ Icc 0 T, V s = revDriver W T s

section Driver

variable {W V : ℝ → ℝ} {T : ℝ}

theorem revMap_eq_of_isRevExt (h : IsRevExt W V T) {s : ℝ} (hs : s ∈ Icc 0 T) (z : ℂ) :
    revMap V s z = revMap (revDriver W T) s z :=
  ReverseFlow.revMap_congr_drive z fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩

theorem revFlow_eq_of_isRevExt (h : IsRevExt W V T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    revFlow V s = revFlow (revDriver W T) s := by
  funext z
  rw [revFlow_def, revFlow_def, revMap_eq_of_isRevExt h hs z, h s hs]

/-- **(2.7)** for an extended reversed driver: `|F_T'(z)| = Φ_s(z) |F'_{T-s}(Z_s(z))|`. -/
theorem norm_deriv_fwdMapInv_eq_mul_of_isRevExt (hW : Continuous W) (hW0 : W 0 = 0)
    (h : IsRevExt W V T) {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) {z : ℂ} (hz : z ∈ H) :
    ‖deriv (fwdMapInv W T) z‖ =
      ‖deriv (revFlow V s) z‖ * ‖deriv (fwdMapInv W (T - s)) (revMap V s z)‖ := by
  rw [norm_deriv_fwdMapInv_eq_mul hW hW0 hs hsT hz, revFlow_eq_of_isRevExt h ⟨hs, hsT⟩,
    revMap_eq_of_isRevExt h ⟨hs, hsT⟩, deriv_revFlow]

/-- `|F_T'(iy)| = Φ_T(iy)` for an extended reversed driver. -/
theorem norm_deriv_fwdMapInv_eq_rfPhi (hW : Continuous W) (hW0 : W 0 = 0) (h : IsRevExt W V T)
    (hT : 0 ≤ T) {y : ℝ} (hy : 0 < y) :
    ‖deriv (fwdMapInv W T) ((y : ℂ) * I)‖ = rfPhi V y T := by
  rw [norm_deriv_fwdMapInv_eq_norm_deriv_revFlow hW hW0 hT (mul_I_mem_H hy),
    ← revFlow_eq_of_isRevExt h ⟨hT, le_rfl⟩]
  rfl

/-- The Brownian extension `√8 · revBM B T` of the reversed driver (QuantumZipper's `revBM`). -/
theorem isRevExt_drive_revBM {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) {T : ℝ} (hT : 0 ≤ T) :
    IsRevExt (drive 8 B ω) (drive 8 (UnzipInvariance.revBM B T.toNNReal) ω) T := by
  intro s hs
  have hle : s.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal hs.2
  have hsub : T.toNNReal - s.toNNReal = (T - s).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_sub hle, Real.coe_toNNReal _ hT, Real.coe_toNNReal _ hs.1,
      Real.coe_toNNReal _ (by linarith [hs.2])]
  simp only [drive, revDriver_apply, UnzipInvariance.revBM_apply, max_eq_right hle, hsub]
  ring

/-- On `Ω_M`, the reversed driver over `[0, s]` with `s ≤ h ≤ 1` is at most `M √(h log(e/h))`. -/
theorem abs_revDriver_le {M : ℝ} (hM : DriverBound M W) (hT1 : T ≤ 1) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) {h : ℝ} (hsh : s ≤ h) (hh1 : h ≤ 1) :
    |revDriver W T s| ≤ M * Real.sqrt (h * Real.log (Real.exp 1 / h)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM.1 0 ⟨le_rfl, zero_le_one⟩)
  rcases hs.eq_or_lt with rfl | hspos
  · simp only [revDriver_apply, sub_zero, sub_self, abs_zero]; positivity
  · have h1 := hM.2 (T - s) T (by linarith) (by linarith) hT1
    rw [show T - (T - s) = s by ring] at h1
    rw [revDriver_apply, abs_sub_comm]
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hM0)
    exact mul_log_exp_div_le hspos hsh hh1

end Driver

/-! ## The grids -/

/-- The grid time `t_k = 4^{-k} ⌊4^k t⌋` of (4.2). -/
def gridT (k : ℕ) (t : ℝ) : ℝ := ((4 : ℝ) ^ k)⁻¹ * ⌊(4 : ℝ) ^ k * t⌋

theorem gridT_le (k : ℕ) (t : ℝ) : gridT k t ≤ t := by
  unfold gridT
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  rw [inv_mul_le_iff₀ h4]
  exact Int.floor_le _

theorem sub_gridT_lt (k : ℕ) (t : ℝ) : t - gridT k t < ((4 : ℝ) ^ k)⁻¹ := by
  unfold gridT
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have h := Int.lt_floor_add_one ((4 : ℝ) ^ k * t)
  have : t < ((4 : ℝ) ^ k)⁻¹ * (⌊(4 : ℝ) ^ k * t⌋ + 1) := by
    rw [lt_inv_mul_iff₀ h4]; exact h
  linarith

theorem gridT_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gridT k t := by
  unfold gridT
  have : (0 : ℝ) ≤ ⌊(4 : ℝ) ^ k * t⌋ := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
  positivity

/-- **Nesting of the grids (4.5).** For `k ≤ k'`, `t_k(t_{k'}(t)) = t_k(t)`. -/
theorem gridT_gridT {k k' : ℕ} (hkk' : k ≤ k') (t : ℝ) : gridT k (gridT k' t) = gridT k t := by
  unfold gridT
  congr 2
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  have h4 : (4 : ℝ) ^ (k + d) = 4 ^ k * 4 ^ d := pow_add _ _ _
  have hd : ((4 ^ d : ℕ) : ℝ) = (4 : ℝ) ^ d := by push_cast; ring
  have hk0 : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hd0 : (4 : ℝ) ^ d ≠ 0 := by positivity
  have e1 : (4 : ℝ) ^ k * (((4 : ℝ) ^ (k + d))⁻¹ * ⌊(4 : ℝ) ^ (k + d) * t⌋) =
      ((⌊(4 : ℝ) ^ (k + d) * t⌋ : ℤ) : ℝ) / ((4 ^ d : ℕ) : ℝ) := by
    rw [hd, h4]; field_simp
  have e2 : (4 : ℝ) ^ k * t = (4 : ℝ) ^ (k + d) * t / ((4 ^ d : ℕ) : ℝ) := by
    rw [hd, h4]; field_simp
  rw [e1, e2, Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]

theorem gridT_mem_range {k : ℕ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ j ∈ Finset.range (4 ^ k + 1), gridT k t = (j : ℝ) / 4 ^ k := by
  refine ⟨⌊(4 : ℝ) ^ k * t⌋₊, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), ?_⟩
  · have : (4 : ℝ) ^ k * t ≤ ((4 ^ k : ℕ) : ℝ) := by
      push_cast; nlinarith [ht.2, pow_pos (by norm_num : (0 : ℝ) < 4) k]
    exact (Nat.floor_le_floor this).trans (by rw [Nat.floor_natCast])
  · unfold gridT
    rw [← Int.natCast_floor_eq_floor (by have := ht.1; positivity)]
    push_cast; ring

theorem dyadicHeight_sq (k : ℕ) : dyadicHeight k ^ 2 = ((4 : ℝ) ^ k)⁻¹ := by
  unfold dyadicHeight
  rw [inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num

theorem dyadicHeight_anti {k k' : ℕ} (h : k ≤ k') : dyadicHeight k' ≤ dyadicHeight k := by
  unfold dyadicHeight
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-! ## Step 1: the reverse flow from the finest large scale ((4.6), (4.10)) -/

/-- **(4.6) and (4.10).** Let `T ∈ [0, 1]`, `V` an extension of the reversed driver from `[0, T]`,
`k ≤ k'`, `y = y_{k'}` and `s = T - t_k(T)`. Then `0 ≤ s ≤ T`, `s ≤ y_k²`, `y ≤ Y_s ≤ √5 y_k`,
`|X_s| ≤ 2 M y_k √(1 + 2k log 2)` on `Ω_M`, and `y |F_T'(iy)| ≤ Y_s |F'_{t_k}(Z_s(iy))|`. -/
theorem reverse_bounds {W V : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {M : ℝ}
    (hM : DriverBound M W) (hV : Continuous V) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1)
    (hext : IsRevExt W V T) {k k' : ℕ} (hkk' : k ≤ k') :
    0 ≤ T - gridT k T ∧ T - gridT k T ≤ T ∧ T - gridT k T ≤ dyadicHeight k ^ 2 ∧
      dyadicHeight k' ≤ rfY V (dyadicHeight k') (T - gridT k T) ∧
      rfY V (dyadicHeight k') (T - gridT k T) ≤ Real.sqrt 5 * dyadicHeight k ∧
      |rfX V (dyadicHeight k') (T - gridT k T)| ≤
        2 * M * dyadicHeight k * Real.sqrt (1 + 2 * k * Real.log 2) ∧
      dyadicHeight k' * ‖deriv (fwdMapInv W T) ((dyadicHeight k' : ℂ) * I)‖ ≤
        rfY V (dyadicHeight k') (T - gridT k T) *
          ‖deriv (fwdMapInv W (gridT k T)) (revMap V (T - gridT k T) ((dyadicHeight k' : ℂ) * I))‖ := by
  set y := dyadicHeight k' with hydef
  set s := T - gridT k T with hsdef
  have hy : 0 < y := dyadicHeight_pos k'
  have hyk : y ≤ dyadicHeight k := dyadicHeight_anti hkk'
  have hk0 : 0 < dyadicHeight k := dyadicHeight_pos k
  have hs0 : 0 ≤ s := sub_nonneg.2 (gridT_le k T)
  have hsT : s ≤ T := by linarith [gridT_nonneg k hT.1]
  have hsy : s ≤ dyadicHeight k ^ 2 := by
    rw [dyadicHeight_sq]; exact (sub_gridT_lt k T).le
  have hy2 : dyadicHeight k ^ 2 ≤ 1 := pow_le_one₀ hk0.le (dyadicHeight_le_one k)
  have hz : (y : ℂ) * I ∈ H := mul_I_mem_H hy
  have hYb := im_revMap_mem_Icc hV hz hs0
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at hYb
  refine ⟨hs0, hsT, hsy, hYb.1, ?_, ?_, ?_⟩
  · refine hYb.2.trans ?_
    rw [show Real.sqrt 5 * dyadicHeight k = Real.sqrt (5 * dyadicHeight k ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hk0.le]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · have hm : ∀ v ∈ Icc 0 s, |V v| ≤
        M * Real.sqrt (dyadicHeight k ^ 2 * Real.log (Real.exp 1 / dyadicHeight k ^ 2)) := by
      intro v hv
      rw [hext v ⟨hv.1, hv.2.trans hsT⟩]
      exact abs_revDriver_le hM hT.2 hv.1 (hv.2.trans hsT) (hv.2.trans hsy) hy2
    have h := abs_re_revMap_mul_I_le hV hy hs0 hm
    have he : Real.log (Real.exp 1 / dyadicHeight k ^ 2) = 1 + 2 * k * Real.log 2 := by
      rw [Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp, log_dyadicHeight_sq]
      ring
    rw [he, Real.sqrt_mul (by positivity), Real.sqrt_sq hk0.le] at h
    unfold rfX
    linarith
  · have h27 := norm_deriv_fwdMapInv_eq_mul_of_isRevExt hW hW0 hext hs0 hsT hz
    have hTs : T - s = gridT k T := by rw [hsdef]; ring
    rw [hTs] at h27
    rw [h27]
    have hPhi : ‖deriv (revFlow V s) ((y : ℂ) * I)‖ ≤ rfY V y s / y := by
      have := norm_deriv_revFlow_le hV hz hs0
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at this
      exact this
    calc y * (‖deriv (revFlow V s) ((y : ℂ) * I)‖ *
          ‖deriv (fwdMapInv W (gridT k T)) (revMap V s ((y : ℂ) * I))‖)
        ≤ y * (rfY V y s / y * ‖deriv (fwdMapInv W (gridT k T)) (revMap V s ((y : ℂ) * I))‖) := by
          gcongr
      _ = rfY V y s * ‖deriv (fwdMapInv W (gridT k T)) (revMap V s ((y : ℂ) * I))‖ := by
          field_simp

/-! ## Step 2: small image heights ((4.8)–(4.11)) -/

/-- **Koebe distortion on a dyadic box (4.11).** There is a universal `K ≥ 1` such that for the centred
inverse map `F = F_{t'}`, every `v > 0`, `m ∈ ℤ` and `w = X + iY` with `v < Y ≤ 2v` and
`|X - m v| ≤ v`: `|F'(w)| ≤ K |F'((m + i) v)|`. -/
theorem exists_koebe_box : ∃ K : ℝ, 1 ≤ K ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ∀ t' : ℝ, 0 ≤ t' → ∀ w : ℂ, ∀ v : ℝ, 0 < v → ∀ m : ℤ, v < w.im → w.im ≤ 2 * v →
      |w.re - m * v| ≤ v →
        ‖deriv (fwdMapInv W t') w‖ ≤ K * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖ := by
  obtain ⟨C, hC1, hkd⟩ := RS.kd_distortion
  refine ⟨C * 2 ^ C * C, by
    have : (1 : ℝ) ≤ 2 ^ C := Real.one_le_rpow (by norm_num) (by linarith)
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC1 this) hC1, ?_⟩
  intro W hW hW0 t' ht' w v hv m hYlo hYhi hX
  set c : ℂ := (((m : ℝ) * v : ℝ) : ℂ) with hcdef
  set f : ℂ → ℂ := fun z => fwdMapInv W t' (z + c) with hfdef
  have hmaps : MapsTo (fun z : ℂ => z + c) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
    intro z hz; simpa [hcdef] using hz
  have hfd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} :=
    (RS.differentiableOn_fwdMapInv hW hW0 ht').comp (differentiableOn_id.add_const c) hmaps
  have hfi : InjOn f {z : ℂ | 0 < z.im} := by
    intro z₁ h₁ z₂ h₂ h
    have := RS.injOn_fwdMapInv hW hW0 ht' (hmaps h₁) (hmaps h₂) h
    simpa using this
  have hderiv : ∀ z, deriv f z = deriv (fwdMapInv W t') (z + c) := fun z => deriv_comp_add_const _ _ _
  set Y := w.im with hYdef
  have hY : 0 < Y := hv.trans hYlo
  set x := (w.re - m * v) / Y with hxdef
  -- horizontal step at height `Y`
  obtain ⟨-, h2, -⟩ := hkd f hfd hfi Y hY x
  -- vertical step from `v` to `Y`
  obtain ⟨h1, -, -⟩ := hkd f hfd hfi v hv 0
  have hs : Y / v ∈ Icc (1 / 2 : ℝ) 2 := by
    constructor
    · rw [le_div_iff₀ hv]; linarith
    · rw [div_le_iff₀ hv]; linarith
  obtain ⟨h1', -⟩ := h1 (Y / v) hs
  rw [div_mul_cancel₀ Y hv.ne'] at h1'
  have hw : (Y : ℂ) * ((x : ℂ) + I) + c = w := by
    apply Complex.ext
    · simp only [hxdef, hcdef, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, add_im,
        sub_zero, zero_mul, add_zero]
      field_simp; ring
    · simp [hxdef, hcdef, hYdef]
  have hYc : (Y : ℂ) * I + c = (m * v : ℝ) + Y * I := by rw [hcdef]; ring
  have hvc : (v : ℂ) * I + c = ((m : ℂ) + I) * (v : ℂ) := by rw [hcdef]; push_cast; ring
  rw [hderiv, hw] at h2
  rw [hderiv, hderiv, hvc] at h1'
  have hx2 : (1 + x ^ 2) ^ C ≤ (2 : ℝ) ^ C := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    have : |x| ≤ 1 := by
      rw [hxdef, abs_div, abs_of_pos hY, div_le_one hY]; linarith
    nlinarith [abs_nonneg x, sq_abs x]
  have hC0 : 0 ≤ C := by linarith
  calc ‖deriv (fwdMapInv W t') w‖
      ≤ C * (1 + x ^ 2) ^ C * ‖deriv f ((Y : ℂ) * I)‖ := h2
    _ ≤ C * 2 ^ C * ‖deriv f ((Y : ℂ) * I)‖ := by gcongr
    _ = C * 2 ^ C * ‖deriv (fwdMapInv W t') ((Y : ℂ) * I + c)‖ := by rw [hderiv]
    _ ≤ C * 2 ^ C * (C * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖) := by
        gcongr
    _ = C * 2 ^ C * C * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖ := by ring

theorem log_dyadicHeight (j : ℕ) : Real.log (dyadicHeight j) = -(j * Real.log 2) := by
  unfold dyadicHeight; rw [Real.log_inv, Real.log_pow]

theorem dyadicHeight_div {k ℓ : ℕ} (h : k ≤ ℓ) :
    dyadicHeight k / dyadicHeight ℓ = (2 : ℝ) ^ (ℓ - k) := by
  unfold dyadicHeight
  rw [inv_div_inv, pow_sub₀ _ two_ne_zero h, div_eq_mul_inv]

/-- **Step 2 (4.8)–(4.11).** Let `w = Z_{s_k}(iy_*)` be the reverse image of the finest scale, with
`y_{k'} ≤ Y < e^{-r} y_k`, `|X| ≤ M' y_k`, and `a ≤ Y |F'_{t'}(w)|` (4.10). Choose the dyadic height
`v = 2^{-ℓ}` with `v < Y ≤ 2v` and `m = round(X/v)`. Then `ℓ ≤ k' + 1`, `(ℓ - k) log 2 ≥ r`,
`|m| ≤ M' 2^{ℓ-k} + 1` and `v |F'_{t'}((m + i) v)| ≥ a / (2K)` with the Koebe constant `K`. -/
theorem smallImage_of_lt {W : ℝ → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hKb : ∀ t' : ℝ, 0 ≤ t' → ∀ w : ℂ, ∀ v : ℝ, 0 < v → ∀ m : ℤ, v < w.im → w.im ≤ 2 * v →
      |w.re - m * v| ≤ v →
        ‖deriv (fwdMapInv W t') w‖ ≤ K * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖)
    {t' : ℝ} (ht' : 0 ≤ t') {w : ℂ} {k k' : ℕ} {a r M' : ℝ} (hr : 0 < r)
    (hYlo : dyadicHeight k' ≤ w.im) (hYhi : w.im < Real.exp (-r) * dyadicHeight k)
    (hX : |w.re| ≤ M' * dyadicHeight k) (ha : a ≤ w.im * ‖deriv (fwdMapInv W t') w‖) :
    ∃ ℓ : ℕ, k < ℓ ∧ ℓ ≤ k' + 1 ∧ r ≤ ((ℓ : ℝ) - k) * Real.log 2 ∧ ∃ m : ℤ,
      |(m : ℝ)| ≤ M' * 2 ^ (ℓ - k) + 1 ∧
      a / (2 * K) ≤ dyadicHeight ℓ *
        ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖ := by
  set Y := w.im with hYdef
  have hY : 0 < Y := (dyadicHeight_pos k').trans_le hYlo
  have hY1 : Y < 1 := hYhi.trans_le (by
    have h1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 := dyadicHeight_le_one k
    have h3 := (dyadicHeight_pos k).le
    nlinarith)
  obtain ⟨p, hp1, hp2⟩ := exists_nat_pow_near (one_le_one_div hY hY1.le) (one_lt_two (α := ℝ))
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ℓ := p + 1 with hℓ
  set v := dyadicHeight ℓ with hvdef
  have hv : 0 < v := dyadicHeight_pos ℓ
  have hvY : v < Y := by
    rw [hvdef, dyadicHeight, hℓ]
    rw [one_div] at hp2
    exact inv_lt_of_inv_lt₀ hY hp2
  have hY2v : Y ≤ 2 * v := by
    have h2v : 2 * v = ((2 : ℝ) ^ p)⁻¹ := by
      rw [hvdef, dyadicHeight, hℓ, pow_succ]; field_simp
    rw [h2v]
    rw [one_div] at hp1
    exact (le_inv_comm₀ (by positivity) hY).1 hp1
  -- `ℓ ≤ k' + 1`
  have hpk' : p ≤ k' := by
    have h1 : (2 : ℝ) ^ p ≤ 2 ^ k' := by
      calc (2 : ℝ) ^ p ≤ 1 / Y := hp1
        _ ≤ 1 / dyadicHeight k' := one_div_le_one_div_of_le (dyadicHeight_pos k') hYlo
        _ = 2 ^ k' := by rw [dyadicHeight, one_div, inv_inv]
    exact (pow_le_pow_iff_right₀ one_lt_two).1 h1
  -- `(ℓ - k) log 2 > r`
  have hlog : r < ((ℓ : ℝ) - k) * Real.log 2 := by
    have h1 : Real.log v < Real.log (Real.exp (-r) * dyadicHeight k) :=
      Real.log_lt_log hv (hvY.trans hYhi)
    rw [Real.log_mul (Real.exp_pos _).ne' (dyadicHeight_pos k).ne', Real.log_exp, hvdef,
      log_dyadicHeight, log_dyadicHeight] at h1
    linarith
  have hkℓ : k < ℓ := by
    have : (k : ℝ) < ℓ := by
      by_contra hcon
      have : ((ℓ : ℝ) - k) * Real.log 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hl2.le
      linarith
    exact_mod_cast this
  refine ⟨ℓ, hkℓ, by omega, hlog.le, ?_⟩
  -- the horizontal index `m`
  set m : ℤ := round (w.re / v) with hmdef
  have hround : |w.re / v - m| ≤ 1 / 2 := abs_sub_round _
  have hXm : |w.re - m * v| ≤ v := by
    have : w.re - m * v = v * (w.re / v - m) := by field_simp
    rw [this, abs_mul, abs_of_pos hv]
    nlinarith [abs_nonneg (w.re / v - m)]
  refine ⟨m, ?_, ?_⟩
  · have h1 : |(m : ℝ)| ≤ |w.re / v| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub (m : ℝ) (w.re / v)
      rw [abs_sub_comm] at this
      linarith
    have h2 : |w.re / v| ≤ M' * 2 ^ (ℓ - k) := by
      rw [abs_div, abs_of_pos hv, div_le_iff₀ hv, ← dyadicHeight_div hkℓ.le, hvdef]
      calc |w.re| ≤ M' * dyadicHeight k := hX
        _ = M' * (dyadicHeight k / dyadicHeight ℓ) * dyadicHeight ℓ := by
            field_simp [(dyadicHeight_pos ℓ).ne']
    linarith
  · have hKw := hKb t' ht' w v hv m hvY hY2v hXm
    have hK0 : 0 < K := by linarith
    rw [div_le_iff₀ (by positivity)]
    calc a ≤ Y * ‖deriv (fwdMapInv W t') w‖ := ha
      _ ≤ (2 * v) * (K * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖) :=
          mul_le_mul hY2v hKw (norm_nonneg _) (by positivity)
      _ = v * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖ * (2 * K) := by ring

/-! ## Step 3: many remaining scales force many visits ((4.14)–(4.21)) -/

theorem abs_arsinh_le_log_two_mul_add_one (x : ℝ) : |Real.arsinh x| ≤ Real.log (2 * |x| + 1) := by
  have habs : |Real.arsinh x| = Real.arsinh |x| := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx, abs_of_nonneg (Real.arsinh_nonneg_iff.2 hx)]
    · rw [abs_of_neg hx, abs_of_neg (Real.arsinh_neg_iff.2 hx), Real.arsinh_neg]
  rw [habs, Real.arsinh]
  have h0 := abs_nonneg x
  have hs : Real.sqrt (1 + |x| ^ 2) ≤ 1 + |x| := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hpos : 0 < |x| + Real.sqrt (1 + |x| ^ 2) := by
    have : 0 < Real.sqrt (1 + |x| ^ 2) := Real.sqrt_pos.2 (by positivity)
    linarith
  exact Real.log_le_log hpos (by linarith)

/-- **Step 3 ((4.14)–(4.21)).** Let `y = y_{k'}` be the finest scale, `T ∈ [0, 1]`, and `I` a set of
scales `N < k ≤ k'` at which the reverse images `w_k = Z_{s_k}(iy)`, `s_k = T - t_k(T)`, satisfy
`e^{-r} y_k ≤ Y_{s_k} ≤ √5 y_k` (no small image height) and `|X_{s_k}| ≤ M' y_k`. If `y Φ_T ≥ a`, the
consequences (3.3) of Lemma 3.1 hold, and the parameter inequalities `hL1`–`hL4` hold (they hold for all
large `n`), then `|I| > (⌈r⌉ - 1)(R + 1)` forces the trial event `E_{k',T}` of (4.22) with `⌈r⌉` trials. -/
theorem trialEventAt_of_many {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : T ∈ Icc (0 : ℝ) 1)
    {k' : ℕ} {I : Finset ℕ} {N r a Cocc M' : ℝ} (hN : 0 ≤ N) (hr2 : 2 ≤ r)
    (hI : ∀ k ∈ I, N < k ∧ k ≤ k')
    (hsT : ∀ k ∈ I, 0 ≤ T - gridT k T ∧ T - gridT k T ≤ T)
    (hYlo : ∀ k ∈ I, Real.exp (-r) * dyadicHeight k ≤ rfY V (dyadicHeight k') (T - gridT k T))
    (hYhi : ∀ k ∈ I, rfY V (dyadicHeight k') (T - gridT k T) ≤ Real.sqrt 5 * dyadicHeight k)
    (hX : ∀ k ∈ I, |rfX V (dyadicHeight k') (T - gridT k T)| ≤ M' * dyadicHeight k)
    (hphi : a ≤ dyadicHeight k' * rfPhi V (dyadicHeight k') T)
    (h33a : Real.log a ≤ heightTau V (dyadicHeight k') T)
    (h33b : volume {u | u ∈ Icc (Real.log (dyadicHeight k')) (heightTau V (dyadicHeight k') T) ∧
        |heightJ V (dyadicHeight k') u| ≤ 1} ≤ ENNReal.ofReal (Cocc * (1 + Real.log (1 / a))))
    (hL1 : Real.log (2 * (M' * Real.exp r) + 1) ≤ 2 * r)
    (hL2 : ((⌈r⌉₊ : ℝ) - 1) * ((2 * r ^ 5 + r + Real.log (Real.sqrt 5)) / Real.log 2 + 1) <
      I.card)
    (hL3 : -(N * Real.log 2) + Real.log (Real.sqrt 5) + 2 * r ^ 5 < Real.log a)
    (hL4 : Cocc * (1 + Real.log (1 / a)) ≤ r) :
    trialEventAt V (dyadicHeight k') T a r ⌈r⌉₊ := by
  set y := dyadicHeight k' with hydef
  have hy : 0 < y := dyadicHeight_pos k'
  have hy1 : y ∈ Ioc (0 : ℝ) 1 := ⟨hy, dyadicHeight_le_one k'⟩
  set u₀ := Real.log y with hu₀
  set τ := heightTau V y T with hτdef
  set f := jPath V y T with hfdef
  set L := r ^ 5 with hLdef
  have hL : 0 ≤ L := by positivity
  have hfc : Continuous f := continuous_jPath hV hy hT.1
  have hτm := heightTau_mem hV hy1 hT
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set Kbar := trialHorizon y with hKbar
  have hKbar0 : 0 ≤ Kbar := by rw [hKbar, trialHorizon]; linarith [hτm.1, hτm.2]
  set K₀ := -(N * Real.log 2) + Real.log (Real.sqrt 5) - u₀ with hK₀
  have hK₀K : K₀ ≤ Kbar := by
    rw [hK₀, hKbar, trialHorizon]; nlinarith
  -- the visit times
  set φ : ℕ → ℝ := fun k => Real.log (rfY V y (T - gridT k T)) - u₀ with hφdef
  have hYpos : ∀ k ∈ I, 0 < rfY V y (T - gridT k T) := fun k hk => rfY_pos hV hy (hsT k hk).1
  have hφ0 : ∀ k ∈ I, 0 ≤ φ k := by
    intro k hk
    have h := im_revMap_mem_Icc hV (mul_I_mem_H hy) (hsT k hk).1
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at h
    have : Real.log y ≤ Real.log (rfY V y (T - gridT k T)) := Real.log_le_log hy h.1
    simp only [hφdef]; linarith
  have hlogY : ∀ k ∈ I, -r - k * Real.log 2 ≤ Real.log (rfY V y (T - gridT k T)) ∧
      Real.log (rfY V y (T - gridT k T)) ≤ Real.log (Real.sqrt 5) - k * Real.log 2 := by
    intro k hk
    have hk0 := dyadicHeight_pos k
    constructor
    · have := Real.log_le_log (by positivity) (hYlo k hk)
      rwa [Real.log_mul (Real.exp_pos _).ne' hk0.ne', Real.log_exp, log_dyadicHeight] at this
    · have := Real.log_le_log (hYpos k hk) (hYhi k hk)
      rwa [Real.log_mul (by positivity) hk0.ne', log_dyadicHeight] at this
  have hφK : ∀ k ∈ I, φ k ≤ K₀ := by
    intro k hk
    have h1 := (hlogY k hk).2
    have h2 : N * Real.log 2 ≤ k * Real.log 2 :=
      mul_le_mul_of_nonneg_right (hI k hk).1.le hl2.le
    simp only [hφdef, hK₀]; linarith
  have hφτ : ∀ k ∈ I, φ k ≤ τ - u₀ := by
    intro k hk
    have hmono := (strictMonoOn_rfY hV hy).monotoneOn (hsT k hk).1 hT.1 (hsT k hk).2
    have := Real.log_le_log (hYpos k hk) hmono
    simp only [hφdef, hτdef, heightTau]; linarith
  have hφv : ∀ k ∈ I, |f (φ k)| ≤ 2 * r := by
    intro k hk
    rw [hfdef, jPath_eq (hφτ k hk)]
    have he : u₀ + φ k = Real.log (rfY V y (T - gridT k T)) := by simp only [hφdef]; ring
    rw [he, heightJ_log hV hy (hsT k hk).1]
    refine (abs_arsinh_le_log_two_mul_add_one _).trans
      (le_trans (Real.log_le_log (by positivity) ?_) hL1)
    have hk0 := dyadicHeight_pos k
    have hratio : |rfX V y (T - gridT k T) / rfY V y (T - gridT k T)| ≤ M' * Real.exp r := by
      rw [abs_div, abs_of_pos (hYpos k hk), div_le_iff₀ (hYpos k hk)]
      calc |rfX V y (T - gridT k T)| ≤ M' * dyadicHeight k := hX k hk
        _ = M' * Real.exp r * (Real.exp (-r) * dyadicHeight k) := by
            rw [show M' * Real.exp r * (Real.exp (-r) * dyadicHeight k) =
              M' * (Real.exp r * Real.exp (-r)) * dyadicHeight k by ring, ← Real.exp_add]
            simp
        _ ≤ M' * Real.exp r * rfY V y (T - gridT k T) := by
            have hM' : 0 ≤ M' * Real.exp r := by
              have := (abs_nonneg _).trans (hX k hk)
              have hM'0 : 0 ≤ M' := by
                by_contra hneg
                have : M' * dyadicHeight k < 0 := mul_neg_of_neg_of_pos (not_le.1 hneg) hk0
                linarith
              positivity
            exact mul_le_mul_of_nonneg_left (hYlo k hk) hM'
    linarith
  -- two scales in a common window are close
  set R := (2 * L + r + Real.log (Real.sqrt 5)) / Real.log 2 with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    have : 0 ≤ Real.log (Real.sqrt 5) :=
      Real.log_nonneg (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
    positivity
  have hwin : ∀ k ∈ I, ∀ k'' ∈ I, ∀ b, φ k ∈ Ico b (b + 2 * L) → φ k'' ∈ Ico b (b + 2 * L) →
      (k : ℝ) - k'' ≤ R := by
    intro k hk k'' hk'' b h1 h2
    have e1 := (hlogY k hk).2
    have e2 := (hlogY k'' hk'').1
    have hdiff : φ k'' - φ k < 2 * L := by linarith [h1.1, h2.2]
    rw [hRdef, le_div_iff₀ hl2]
    simp only [hφdef] at hdiff
    nlinarith
  -- the `⌈r⌉`-th entrance time is at most `u_end`
  have hm1 : 1 ≤ ⌈r⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero]; linarith)
  have hent : entrance f (2 * r) L Kbar (⌈r⌉₊ - 1) ≤ K₀ := by
    by_contra hcon
    have hcard := card_le_of_entrance_gt hfc hR0 hK₀K hφ0 hφK hφv hwin (not_le.1 hcon)
    rw [Nat.cast_sub hm1, Nat.cast_one] at hcard
    linarith
  -- the trial event
  have hmono := entrance_mono hfc hL hKbar0 (f := f) (c := 2 * r)
  have hτu : τ ≤ Real.log (Real.sqrt 5) := hτm.2
  have hcomp : ∀ j < ⌈r⌉₊, entrance f (2 * r) L Kbar j + 2 * L ≤ τ - u₀ := by
    intro j hj
    have h1 : entrance f (2 * r) L Kbar j ≤ entrance f (2 * r) L Kbar (⌈r⌉₊ - 1) :=
      hmono (Nat.le_sub_one_of_lt hj)
    have h2 : entrance f (2 * r) L Kbar j ≤ K₀ := h1.trans hent
    rw [hK₀] at h2
    linarith
  refine ⟨hphi, fun j hj => ⟨(hcomp j hj).trans (by
    show τ - u₀ ≤ trialHorizon y
    unfold trialHorizon; linarith), ?_⟩, hcomp⟩
  -- each trial occupation is at most the total occupation
  have he0 : 0 ≤ entrance f (2 * r) L Kbar j := entrance_nonneg hfc hL hKbar0 j
  have hsub : {v | v ∈ Icc (entrance f (2 * r) L Kbar j) (entrance f (2 * r) L Kbar j + 2 * L) ∧
        |f v| ≤ 1} ⊆ (fun v => u₀ + v) ⁻¹' {u | u ∈ Icc u₀ τ ∧ |heightJ V y u| ≤ 1} := by
    rintro v ⟨hv, hfv⟩
    have hvτ : v ≤ τ - u₀ := hv.2.trans (hcomp j hj)
    refine ⟨⟨by linarith [hv.1], by linarith⟩, ?_⟩
    rw [hfdef, jPath_eq hvτ] at hfv
    exact hfv
  calc occupation f (entrance f (2 * r) L Kbar j) (2 * L)
      ≤ volume ((fun v => u₀ + v) ⁻¹' {u | u ∈ Icc u₀ τ ∧ |heightJ V y u| ≤ 1}) :=
        measure_mono hsub
    _ = volume {u | u ∈ Icc u₀ τ ∧ |heightJ V y u| ≤ 1} := measure_preimage_add _ _ _
    _ ≤ ENNReal.ofReal (Cocc * (1 + Real.log (1 / a))) := h33b
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hL4

/-! ## The parameters (4.1) and the selection dichotomy -/

/-- `N = 2ⁿ` of (4.1). -/
def bigN (n : ℕ) : ℝ := (2 : ℝ) ^ n

/-- `r = N^δ` of (4.1). -/
def scaleR (δ : ℝ) (n : ℕ) : ℝ := bigN n ^ δ

/-- `a = exp(-r/n²)` of (4.1). -/
def levelA (δ : ℝ) (n : ℕ) : ℝ := Real.exp (-(scaleR δ n / (n : ℝ) ^ 2))

/-- The set `𝓘_n(t) = {k : N < k ≤ 2N, A_k(t_k) ≥ a}` of (4.2). -/
def scaleSet (W : ℝ → ℝ) (δ : ℝ) (n : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k => levelA δ n ≤ normalizedDeriv W k (gridT k t)

/-- The parameter inequalities used in Steps 1–3; they hold for all large `n` (`eventually_selectionParams`). -/
structure SelectionParams (M Cocc δ : ℝ) (n : ℕ) : Prop where
  two_le_r : 2 ≤ scaleR δ n
  hL1 : Real.log (2 * (4 * M * Real.sqrt (bigN n) * Real.exp (scaleR δ n)) + 1) ≤ 2 * scaleR δ n
  hL2 : ((⌈scaleR δ n⌉₊ : ℝ) - 1) *
      ((2 * scaleR δ n ^ 5 + scaleR δ n + Real.log (Real.sqrt 5)) / Real.log 2 + 1) ≤
      scaleR δ n ^ 7
  hL3 : -(bigN n * Real.log 2) + Real.log (Real.sqrt 5) + 2 * scaleR δ n ^ 5 <
      -(scaleR δ n / (n : ℝ) ^ 2)
  hL4 : Cocc * (1 + scaleR δ n / (n : ℝ) ^ 2) ≤ scaleR δ n

theorem levelA_mem (δ : ℝ) (n : ℕ) (hr : 0 < scaleR δ n) (hn : 1 ≤ n) :
    levelA δ n ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_lt_zero.2 (div_pos hr (by positivity)))⟩

theorem log_one_div_levelA (δ : ℝ) (n : ℕ) : Real.log (1 / levelA δ n) = scaleR δ n / (n : ℝ) ^ 2 := by
  rw [levelA, one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem bigN_pos (n : ℕ) : 0 < bigN n := by unfold bigN; positivity

theorem cast_two_pow (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = bigN n := by unfold bigN; push_cast; ring

/-- **The selection dichotomy (Steps 1–3).** On `Ω_M`, if `|𝓘_n(t)| > r⁷` for some `t ∈ [0, 1]`, then
either (Step 2) some coarse scale `k` with grid time `j/4^k` and some dyadic box `(ℓ, m)` realize the
two-point event of Lemma 3.2 (with `c₀ = 1/(2K)`), or (Step 3) some deterministic pair `(k_*, j/4^{k_*})`
realizes the trial event `E_{k_*,T}` of (4.22) with `⌈r⌉` trials. -/
theorem selection {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {M : ℝ}
    (hM : DriverBound M W) {V : ℝ → ℝ → ℝ}
    (hV : ∀ T ∈ Icc (0 : ℝ) 1, Continuous (V T) ∧ IsRevExt W (V T) T) {Cocc : ℝ}
    (h33 : ∀ T ∈ Icc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ a ∈ Ioo (0 : ℝ) 1,
      a ≤ y * rfPhi (V T) y T → Real.log a ≤ heightTau (V T) y T ∧
        volume {u | u ∈ Icc (Real.log y) (heightTau (V T) y T) ∧ |heightJ (V T) y u| ≤ 1} ≤
          ENNReal.ofReal (Cocc * (1 + Real.log (1 / a))))
    {K : ℝ} (hK : 1 ≤ K)
    (hKb : ∀ t' : ℝ, 0 ≤ t' → ∀ w : ℂ, ∀ v : ℝ, 0 < v → ∀ m : ℤ, v < w.im → w.im ≤ 2 * v →
      |w.re - m * v| ≤ v →
        ‖deriv (fwdMapInv W t') w‖ ≤ K * ‖deriv (fwdMapInv W t') (((m : ℂ) + I) * (v : ℂ))‖)
    {δ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hpar : SelectionParams M Cocc δ n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hbad : scaleR δ n ^ 7 < (scaleSet W δ n t).card) :
    (∃ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ∃ j ∈ Finset.range (4 ^ k + 1),
      ∃ ℓ ∈ (Finset.Ioc k (2 * 2 ^ n + 1) : Finset ℕ), scaleR δ n ≤ ((ℓ : ℝ) - k) * Real.log 2 ∧
      ∃ m : ℤ, |(m : ℝ)| ≤ 4 * M * Real.sqrt (bigN n) * 2 ^ (ℓ - k) + 1 ∧
        levelA δ n ≤ dyadicHeight k *
          ‖deriv (fwdMapInv W ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
        levelA δ n / (2 * K) ≤ dyadicHeight ℓ *
          ‖deriv (fwdMapInv W ((j : ℝ) / 4 ^ k)) (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖) ∨
    (∃ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ∃ j ∈ Finset.range (4 ^ k + 1),
      trialEventAt (V ((j : ℝ) / 4 ^ k)) (dyadicHeight k) ((j : ℝ) / 4 ^ k) (levelA δ n)
        (scaleR δ n) ⌈scaleR δ n⌉₊) := by
  set Is := scaleSet W δ n t with hIdef
  set r := scaleR δ n with hrdef
  set a := levelA δ n with hadef
  set N := bigN n with hNdef
  have hr2 : 2 ≤ r := hpar.two_le_r
  have ha : a ∈ Ioo (0 : ℝ) 1 := levelA_mem δ n (by linarith) hn
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM.1 0 ⟨le_rfl, zero_le_one⟩)
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hne : Is.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Is.card := lt_of_le_of_lt (by positivity) hbad
    exact_mod_cast this
  set kstar := Is.max' hne with hkstar
  have hkstarI : kstar ∈ Is := Is.max'_mem hne
  have hmemI : ∀ k ∈ Is, (2 ^ n < k ∧ k ≤ 2 * 2 ^ n) ∧ a ≤ normalizedDeriv W k (gridT k t) := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hk
    exact ⟨Finset.mem_Ioc.1 h1, h2⟩
  set T := gridT kstar t with hTdef
  have hT : T ∈ Icc (0 : ℝ) 1 := ⟨gridT_nonneg _ ht.1, (gridT_le _ t).trans ht.2⟩
  obtain ⟨jstar, hjstar, hTj⟩ := gridT_mem_range (k := kstar) ht
  obtain ⟨hVc, hext⟩ := hV T hT
  set ystar := dyadicHeight kstar with hystar
  -- the finest derivative is large
  have hastar : a ≤ ystar * ‖deriv (fwdMapInv W T) ((ystar : ℂ) * I)‖ := (hmemI kstar hkstarI).2
  -- bounds for every `k ∈ I`
  have hkle : ∀ k ∈ Is, k ≤ kstar := fun k hk => Is.le_max' k hk
  have hgrid : ∀ k ∈ Is, gridT k T = gridT k t := fun k hk => gridT_gridT (hkle k hk) t
  have hsqrt : ∀ k ∈ Is, 2 * M * dyadicHeight k * Real.sqrt (1 + 2 * k * Real.log 2) ≤
      4 * M * Real.sqrt N * dyadicHeight k := by
    intro k hk
    have hk2N : (k : ℝ) ≤ 2 * N := by
      have := (hmemI k hk).1.2
      rw [hNdef, ← cast_two_pow]; exact_mod_cast this
    have hl2 : Real.log 2 ≤ 3 / 4 := by
      have := Real.log_two_lt_d9; linarith
    have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
    have h1 : Real.sqrt (1 + 2 * k * Real.log 2) ≤ 2 * Real.sqrt N := by
      rw [show 2 * Real.sqrt N = Real.sqrt (4 * N) by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hk0 := (dyadicHeight_pos k).le
    calc 2 * M * dyadicHeight k * Real.sqrt (1 + 2 * k * Real.log 2)
        ≤ 2 * M * dyadicHeight k * (2 * Real.sqrt N) := by gcongr
      _ = 4 * M * Real.sqrt N * dyadicHeight k := by ring
  by_cases hsmall : ∃ k ∈ Is,
      rfY (V T) ystar (T - gridT k T) < Real.exp (-r) * dyadicHeight k
  · -- Step 2
    left
    obtain ⟨k, hk, hlt⟩ := hsmall
    obtain ⟨hs0, hsT, -, hYlo, -, hXb, h410⟩ :=
      reverse_bounds hW hW0 hM hVc hT hext (hkle k hk)
    have ht' : 0 ≤ gridT k T := gridT_nonneg k hT.1
    have hw := smallImage_of_lt hK hKb ht' (w := revMap (V T) (T - gridT k T) ((ystar : ℂ) * I))
      (k := k) (k' := kstar) (a := a) (r := r) (M' := 4 * M * Real.sqrt N) (by linarith) hYlo hlt
      ((hXb.trans (hsqrt k hk))) (hastar.trans h410)
    obtain ⟨ℓ, hkℓ, hℓ, hlog, m, hm, hderiv⟩ := hw
    obtain ⟨j, hj, hgj⟩ := gridT_mem_range (k := k) ht
    have hkstar2 : kstar ≤ 2 * 2 ^ n := (hmemI kstar hkstarI).1.2
    refine ⟨k, Finset.mem_Ioc.2 (hmemI k hk).1, j, hj, ℓ, Finset.mem_Ioc.2 ⟨hkℓ, by omega⟩, hlog,
      m, hm, ?_, ?_⟩
    · rw [← hgj]; exact (hmemI k hk).2
    · rw [← hgj, ← hgrid k hk]; exact hderiv
  · -- Step 3
    right
    push Not at hsmall
    refine ⟨kstar, Finset.mem_Ioc.2 (hmemI kstar hkstarI).1, jstar, hjstar, ?_⟩
    rw [← hTj]
    have hphi : a ≤ ystar * rfPhi (V T) ystar T := by
      rw [← norm_deriv_fwdMapInv_eq_rfPhi hW hW0 hext hT.1 (dyadicHeight_pos kstar)]
      exact hastar
    obtain ⟨h33a, h33b⟩ := h33 T hT ystar ⟨dyadicHeight_pos _, dyadicHeight_le_one _⟩ a ha hphi
    have hcardI : ((⌈r⌉₊ : ℝ) - 1) * ((2 * r ^ 5 + r + Real.log (Real.sqrt 5)) / Real.log 2 + 1) <
        Is.card := lt_of_le_of_lt hpar.hL2 hbad
    refine trialEventAt_of_many hVc hT (I := Is) (N := N) (M' := 4 * M * Real.sqrt N) (Cocc := Cocc)
      (bigN_pos n).le hr2 (fun k hk => ⟨?_, hkle k hk⟩)
      (fun k hk => ⟨(reverse_bounds hW hW0 hM hVc hT hext (hkle k hk)).1,
        (reverse_bounds hW hW0 hM hVc hT hext (hkle k hk)).2.1⟩)
      (fun k hk => hsmall k hk)
      (fun k hk => (reverse_bounds hW hW0 hM hVc hT hext (hkle k hk)).2.2.2.2.1)
      (fun k hk => (reverse_bounds hW hW0 hM hVc hT hext (hkle k hk)).2.2.2.2.2.1.trans
        (hsqrt k hk))
      hphi h33a h33b ?_ hcardI ?_ ?_
    · have := (hmemI k hk).1.1
      rw [hNdef, ← cast_two_pow]; exact_mod_cast this
    · have h := hpar.hL1
      rw [← hrdef, ← hNdef] at h
      convert h using 3
    · have h := hpar.hL3
      rw [hadef, levelA, Real.log_exp]; exact h
    · rw [hadef, log_one_div_levelA]; exact hpar.hL4

end InteractingSLE.SLE8
