import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Foundations.Loewner.YuanCorollary13Markov
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# [Yua22] Corollary 1.3 before a finite horizon

Packet PROVE-YUAN-M1. A continuous Loewner trace before a horizon `T` (`IsLoewnerTraceLT W T η`,
`Spec/Dimension/TraceBridge.lean`: the frozen `IsGeneratingTrace` with a finite lifetime) is
extended past any `T' < T` by freezing the driver (`extDrive W T' t = W(min t T')`) and continuing
the trace by the image of the vertical slit (`extTrace`): `η'(T' + u) = F̄_{T'}(2i√u)`. This is a
continuous Loewner trace on `[0, ∞)` (`IsLoewnerTraceLT.isLoewnerTrace_ext`), to which Corollary 1.3
(`YuanCorollary13.lean`) applies; the drivers, hulls and maps agree before `T'`.

## Main results

* `IsLoewnerTraceLT.isLoewnerTrace_ext`: the slit extension is a continuous Loewner trace.
* `IsLoewnerTraceLT.isLoewnerTraceLT_shift`: **[Yua22] Corollary 1.3 before the horizon**: for
  `0 ≤ a < T`, the shifted tips `γ_a` form a continuous Loewner trace of `W(a + ·) − W(a)` before
  `T − a`, with `F̄_a(γ_a(u)) = η(a + u)`.
* `IsLoewnerTraceLT.hasContinuousOwnFuture`: property (ii) of [Yua22, Theorem 1.1] on `[0, S]`,
  `S < T`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanCorollary13

/-! ### The slit extension -/

/-- The driver frozen after `T'`. -/
def extDrive (W : ℝ → ℝ) (T' : ℝ) (t : ℝ) : ℝ := W (min t T')

/-- The trace continued after `T'` by the image of the vertical slit. -/
def extTrace (W : ℝ → ℝ) (η : ℝ → ℂ) (T' : ℝ) (t : ℝ) : ℂ :=
  if t ≤ T' then η t
  else extendFrom H (fwdMapInv W T') (((2 * Real.sqrt (t - T') : ℝ) : ℂ) * I)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T T' : ℝ}

theorem continuous_extDrive (hW : Continuous W) : Continuous (extDrive W T') := by
  unfold extDrive; fun_prop

theorem extDrive_zero (hW0 : W 0 = 0) (hT' : 0 ≤ T') : extDrive W T' 0 = 0 := by
  rw [extDrive, min_eq_left hT', hW0]

theorem extDrive_eq {t : ℝ} (ht : t ≤ T') : extDrive W T' t = W t := by
  rw [extDrive, min_eq_left ht]

theorem shiftDrive_extDrive_eq_zero {r : ℝ} (hr : 0 ≤ r) : shiftDrive (extDrive W T') T' r = 0 := by
  simp only [shiftDrive, extDrive, min_eq_right (le_add_of_nonneg_right hr), min_self, sub_self]

theorem extTrace_eq {t : ℝ} (ht : t ≤ T') : extTrace W η T' t = η t := by
  simp only [extTrace, ht, ite_true]

/-- The set `S_u = {iy : 0 < y ≤ 2√u}` (the hull of the zero driver). -/
def slitSet (u : ℝ) : Set ℂ := {w | w ∈ H ∧ w.re = 0 ∧ w.im ≤ 2 * Real.sqrt u}

theorem im_segment_ge {p q w : ℂ} (hw : w ∈ segment ℝ p q) : min p.im q.im ≤ w.im := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have : (a • p + b • q).im = a * p.im + b * q.im := by simp [Complex.real_smul]
  rw [this]
  have h1 := mul_le_mul_of_nonneg_left (min_le_left p.im q.im) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right p.im q.im) hb
  have h3 : min p.im q.im = a * min p.im q.im + b * min p.im q.im := by
    rw [← add_mul, hab, one_mul]
  linarith

theorem re_segment_eq {p q w : ℂ} (hpq : p.re = q.re) (hw : w ∈ segment ℝ p q) : w.re = p.re := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have : (a • p + b • q).re = a * p.re + b * q.re := by simp [Complex.real_smul]
  rw [this, ← hpq, ← add_mul, hab, one_mul]

/-- `ℍ` minus a vertical slit at `0` is preconnected. -/
theorem isPreconnected_H_diff_slitSet (u : ℝ) : IsPreconnected (H \ slitSet u) := by
  have hY₀pos : 0 < 2 * Real.sqrt u + 1 := by positivity
  have hgood : ∀ w : ℂ, 2 * Real.sqrt u < w.im → w ∈ H \ slitSet u := fun w hw =>
    ⟨show 0 < w.im by linarith [Real.sqrt_nonneg u], fun h => by linarith [h.2.2]⟩
  refine isPreconnected_of_forall (((2 * Real.sqrt u + 1 : ℝ) : ℂ) * I) fun y hy => ?_
  have hy0 : 0 < y.im := hy.1
  obtain ⟨Y, hYim, hYY₀⟩ : ∃ Y : ℝ, y.im ≤ Y ∧ 2 * Real.sqrt u + 1 ≤ Y :=
    ⟨max y.im (2 * Real.sqrt u + 1), le_max_left _ _, le_max_right _ _⟩
  have h₁ : segment ℝ y ((y.re : ℂ) + (Y : ℂ) * I) ⊆ H \ slitSet u := by
    intro w hw
    have hre := re_segment_eq (by simp) hw
    have him := im_segment_ge hw
    have hmin : min y.im ((y.re : ℂ) + (Y : ℂ) * I).im = y.im := by simp [hYim]
    rw [hmin] at him
    refine ⟨show 0 < w.im by linarith, fun hS => ?_⟩
    by_cases hre0 : y.re = 0
    · exact hy.2 ⟨hy.1, hre0, by linarith [hS.2.2]⟩
    · exact hre0 (hre ▸ hS.2.1)
  have h₂ : segment ℝ ((y.re : ℂ) + (Y : ℂ) * I) ((Y : ℂ) * I) ⊆ H \ slitSet u := by
    intro w hw
    have him := im_segment_ge hw
    have hmin : min ((y.re : ℂ) + (Y : ℂ) * I).im ((Y : ℂ) * I).im = Y := by simp
    rw [hmin] at him
    exact hgood w (by linarith)
  have h₃ : segment ℝ ((Y : ℂ) * I) (((2 * Real.sqrt u + 1 : ℝ) : ℂ) * I) ⊆ H \ slitSet u := by
    intro w hw
    have him := im_segment_ge hw
    have hmin : min ((Y : ℂ) * I).im (((2 * Real.sqrt u + 1 : ℝ) : ℂ) * I).im =
        2 * Real.sqrt u + 1 := by simp [hYY₀]
    rw [hmin] at him
    exact hgood w (by linarith)
  refine ⟨_ ∪ _ ∪ _, union_subset (union_subset h₁ h₂) h₃, Or.inr (right_mem_segment _ _ _),
    Or.inl (Or.inl (left_mem_segment _ _ _)), ?_⟩
  refine IsPreconnected.union ((Y : ℂ) * I) (Or.inr (right_mem_segment _ _ _))
    (left_mem_segment _ _ _) ?_ (convex_segment _ _).isPreconnected
  exact IsPreconnected.union ((y.re : ℂ) + (Y : ℂ) * I) (right_mem_segment _ _ _)
    (left_mem_segment _ _ _) (convex_segment _ _).isPreconnected (convex_segment _ _).isPreconnected

/-! ### The slit extension is a continuous Loewner trace -/

/-- The slit extension is continuous on `[0, ∞)`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.continuousOn_extTrace (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT' : 0 ≤ T') (hT'T : T' < T) :
    ContinuousOn (extTrace W η T') (Ici 0) := by
  have hFbc : ContinuousOn (extendFrom H (fwdMapInv W T')) Hbar :=
    (hη.hasBdryLimits hW hW0 hT' hT'T).continuousOn
  have hFb0 := hη.extendFrom_zero hW hW0 hT' hT'T
  have hg : Continuous fun t : ℝ =>
      extendFrom H (fwdMapInv W T') (((2 * Real.sqrt (t - T') : ℝ) : ℂ) * I) := by
    refine hFbc.comp_continuous (by fun_prop) fun t => ?_
    show 0 ≤ (((2 * Real.sqrt (t - T') : ℝ) : ℂ) * I).im
    simp [Real.sqrt_nonneg]
  refine ContinuousOn.if (fun t ht => ?_) ?_ hg.continuousOn
  · have hfr : frontier {t : ℝ | t ≤ T'} = {T'} := by
      rw [show {t : ℝ | t ≤ T'} = Iic T' from rfl, frontier_Iic]
    rw [hfr] at ht
    rw [mem_singleton_iff.1 ht.2, sub_self, Real.sqrt_zero, mul_zero, ofReal_zero, zero_mul,
      hFb0]
  · refine (hη.2.1.mono ?_)
    rintro t ⟨ht0, ht⟩
    rw [show {t : ℝ | t ≤ T'} = Iic T' from rfl, closure_Iic] at ht
    exact ⟨ht0, lt_of_le_of_lt ht hT'T⟩

/-- Hulls of the extension before `T'`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.fwdHull_extDrive_of_le (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hT'T : T' < T) {t : ℝ} (ht : 0 ≤ t) (htT' : t ≤ T') :
    fwdHull (extDrive W T') t = fillH (extTrace W η T' '' Icc 0 t) := by
  rw [fwdHull_eq_of_eqOn_Icc (continuous_extDrive hW) hW ht fun r hr => extDrive_eq
    (hr.2.trans htT'), hη.2.2 t ht (lt_of_le_of_lt htT' hT'T)]
  congr 1
  exact (Set.EqOn.image_eq fun r hr => extTrace_eq (hr.2.trans htT')).symm

/-- Hulls of the extension after `T'`: `K_{T'} ∪ F_{T'}(S_u)`. -/
theorem fwdHull_extDrive_add (hW : Continuous W) (hW0 : W 0 = 0) (hT' : 0 ≤ T') {u : ℝ}
    (hu : 0 ≤ u) :
    fwdHull (extDrive W T') (T' + u) = fwdHull W T' ∪ fwdMapInv W T' '' slitSet u := by
  have hW' := continuous_extDrive (T' := T') hW
  have hK : fwdHull (extDrive W T') T' = fwdHull W T' :=
    fwdHull_eq_of_eqOn_Icc hW' hW hT' fun r hr => extDrive_eq hr.2
  have hM : ∀ z, fwdMap (extDrive W T') T' z = fwdMap W T' z := fun z =>
    fwdMap_eq_of_eqOn hT' fun r hr => extDrive_eq hr.2
  have hZ : fwdHull (fun r => extDrive W T' (T' + r) - extDrive W T' T') u =
      fwdHull (fun _ => (0 : ℝ)) u :=
    fwdHull_eq_of_eqOn_Icc (by fun_prop) continuous_const hu fun r hr =>
      shiftDrive_extDrive_eq_zero hr.1
  have hdiff := QuantumZipper.fwdHull_add_diff hW' hT' hu
  rw [hZ, hK] at hdiff
  ext z
  constructor
  · intro hz
    by_cases hzK : z ∈ fwdHull W T'
    · exact Or.inl hzK
    · have h1 : z ∈ fwdHull (extDrive W T') (T' + u) \ fwdHull (extDrive W T') T' :=
        ⟨hz, hK ▸ hzK⟩
      rw [hK, hdiff] at h1
      obtain ⟨hzD, hzS⟩ := h1
      rw [hM] at hzS
      have hGH : fwdMap W T' z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT' hzD
      refine Or.inr ⟨fwdMap W T' z, ⟨hGH, (mem_fwdHull_zero_iff hu hGH).1 hzS⟩, ?_⟩
      exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT' hzD
  · rintro (hz | ⟨w, hw, rfl⟩)
    · exact (QuantumZipper.fwdHull_mono (W := extDrive W T')).1 (by linarith) (hK ▸ hz)
    · have hFw := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT' hw.1
      have h1 : fwdMapInv W T' w ∈ fwdHull (extDrive W T') (T' + u) \
          fwdHull (extDrive W T') T' := by
        rw [hK, hdiff]
        refine ⟨hFw, ?_⟩
        rw [hM, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT' hw.1]
        exact (mem_fwdHull_zero_iff hu hw.1).2 hw.2
      exact h1.1

/-- The filling of the extended trace after `T'`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.fillH_extTrace_add (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT' : 0 ≤ T') (hT'T : T' < T) {u : ℝ} (hu : 0 ≤ u) :
    fillH (extTrace W η T' '' Icc 0 (T' + u)) = fwdHull W T' ∪ fwdMapInv W T' '' slitSet u := by
  set P := extTrace W η T' '' Icc 0 (T' + u) with hP
  set A := η '' Icc 0 T' with hA
  set F := fwdMapInv W T' with hF
  set K := fwdHull W T' with hKdef
  have hKA : K = fillH A := hη.2.2 T' hT' hT'T
  have hFb0 := hη.extendFrom_zero hW hW0 hT' hT'T
  have hcb := isConformalBijection_fwdMapInv hW hW0 hT'
  have hFeq : ∀ w ∈ H, extendFrom H F w = F w := fun w hw =>
    extendFrom_H_eq hcb.1.continuousOn hw
  have hPc : IsCompact P := isCompact_Icc.image_of_continuousOn
    ((hη.continuousOn_extTrace hW hW0 hT' hT'T).mono fun t ht => ht.1)
  have hAP : A ⊆ P := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, extTrace_eq ht.2⟩
  have hSP : F '' slitSet u ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩
    have hw0 : 0 < w.im := hw.1
    have hwI : w = ((w.im : ℝ) : ℂ) * I := Complex.ext (by simp [hw.2.1]) (by simp)
    have hle : w.im ^ 2 / 4 ≤ u := by
      have h1 : w.im ^ 2 ≤ (2 * Real.sqrt u) ^ 2 := pow_le_pow_left₀ hw0.le hw.2.2 2
      rw [mul_pow, Real.sq_sqrt hu] at h1
      linarith
    refine ⟨T' + w.im ^ 2 / 4, ⟨by positivity, by linarith⟩, ?_⟩
    have hgt : ¬ (T' + w.im ^ 2 / 4 ≤ T') := by
      have : 0 < w.im ^ 2 / 4 := by positivity
      linarith
    simp only [extTrace, hgt, ite_false, add_sub_cancel_left]
    have hsq : 2 * Real.sqrt (w.im ^ 2 / 4) = w.im := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), Real.sqrt_sq hw0.le,
        show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      ring
    rw [hsq, ← hwI]
    exact hFeq w hw.1
  -- the points of `P`
  have hPsub : ∀ v ∈ P, v ∈ A ∨ ∃ y : ℝ, 0 ≤ y ∧ y ≤ 2 * Real.sqrt u ∧
      v = extendFrom H F ((y : ℂ) * I) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases htT' : t ≤ T'
    · exact Or.inl ⟨t, ⟨ht.1, htT'⟩, (extTrace_eq htT').symm⟩
    · refine Or.inr ⟨2 * Real.sqrt (t - T'), by positivity, ?_, ?_⟩
      · gcongr; linarith [ht.2]
      · simp only [extTrace, htT', ite_false]
        rfl
  -- `P` is disjoint from `F(ℍ \ S_u)`
  have hAK : ∀ v ∈ A, v ∈ H → v ∈ K := fun v hv hvH => by
    rw [hKA]; exact ⟨hvH, Or.inl (subset_closure hv)⟩
  have hdisj : F '' (H \ slitSet u) ⊆ H \ closure P := by
    rintro _ ⟨w, hw, rfl⟩
    have hFw := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT' hw.1
    refine ⟨hFw.1, fun hcl => ?_⟩
    rw [hPc.isClosed.closure_eq] at hcl
    rcases hPsub _ hcl with hA' | ⟨y, hy0, hyu, hyv⟩
    · exact hFw.2 (hAK _ hA' hFw.1)
    · rcases hy0.eq_or_lt with hy | hy
      · rw [← hy, ofReal_zero, zero_mul, hFb0] at hyv
        have hmemA : F w ∈ A := by rw [hyv]; exact ⟨T', ⟨hT', le_rfl⟩, rfl⟩
        exact hFw.2 (hAK _ hmemA hFw.1)
      · have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy
        rw [hFeq _ hyH] at hyv
        have := hcb.2.injOn hw.1 hyH hyv
        exact hw.2 (this ▸ ⟨hyH, by simp, by simpa using hyu⟩)
  -- `F(ℍ \ S_u)` is preconnected and unbounded
  have hEc : IsPreconnected (F '' (H \ slitSet u)) :=
    (isPreconnected_H_diff_slitSet u).image _ (hcb.1.continuousOn.mono sdiff_subset)
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT'
  have hEb : ¬ Bornology.IsBounded (F '' (H \ slitSet u)) := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set y : ℝ := 2 * Real.sqrt u + |R| + |C| + 1 with hy
    have hy0 : 0 < y := by positivity
    have hyH : (y : ℂ) * I ∈ H := show 0 < ((y : ℂ) * I).im by simpa using hy0
    have hyS : (y : ℂ) * I ∉ slitSet u := fun h => by
      have := h.2.2
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero] at this
      linarith [abs_nonneg R, abs_nonneg C]
    have h1 := hR ⟨_, ⟨hyH, hyS⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 : ‖F ((y : ℂ) * I) - (y : ℂ) * I‖ ≤ C := hC _ hyH
    have h3 : ‖(y : ℂ) * I‖ = y := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    have h4 := norm_le_norm_add_norm_sub' ((y : ℂ) * I) (F ((y : ℂ) * I))
    rw [norm_sub_rev] at h4
    rw [h3] at h4
    linarith [le_abs_self R, le_abs_self C, Real.sqrt_nonneg u]
  have hEsub := subset_H_diff_fillH_of_isPreconnected hPc.isBounded hEc hdisj hEb
  apply Subset.antisymm
  · intro z hz
    by_contra hcon
    have hzH : z ∈ H := hz.1
    have hzK : z ∉ K := fun h => hcon (Or.inl h)
    have hzD : z ∈ H \ K := ⟨hzH, hzK⟩
    have hGz := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT' hzD
    have hFG : F (fwdMap W T' z) = z := QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT' hzD
    by_cases hS : fwdMap W T' z ∈ slitSet u
    · exact hcon (Or.inr ⟨_, hS, hFG⟩)
    · exact (hEsub ⟨_, ⟨hGz, hS⟩, hFG⟩).2 hz
  · rintro z (hz | hz)
    · rw [hKA] at hz
      exact fillH_mono hAP hz
    · obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨(QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT' hw.1).1,
        Or.inl (subset_closure (hSP ⟨w, hw, rfl⟩))⟩

/-- **The slit extension is a continuous Loewner trace** of the frozen driver. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.isLoewnerTrace_ext (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT' : 0 ≤ T') (hT'T : T' < T) :
    IsLoewnerTrace (extDrive W T') (extTrace W η T') := by
  refine ⟨by rw [extTrace_eq hT', hη.1], hη.continuousOn_extTrace hW hW0 hT' hT'T,
    fun t ht => ?_⟩
  by_cases htT' : t ≤ T'
  · exact hη.fwdHull_extDrive_of_le hW hT'T ht htT'
  · have hu : 0 ≤ t - T' := by linarith [not_le.1 htT']
    have ht' : t = T' + (t - T') := by ring
    rw [ht', fwdHull_extDrive_add hW hW0 hT' hu, hη.fillH_extTrace_add hW hW0 hT' hT'T hu]

/-! ### Corollary 1.3 before the horizon -/

theorem shiftDrive_extDrive_eq {a r : ℝ} (ha : a ≤ T') (hr : a + r ≤ T') :
    shiftDrive (extDrive W T') a r = shiftDrive W a r := by
  simp only [shiftDrive, extDrive_eq ha, extDrive_eq hr]

/-- The shifted chain of the slit extension agrees with the original one before `T' − a`. -/
theorem loewnerTip_shift_extDrive {a u : ℝ} (ha : a ≤ T') (hu : 0 ≤ u) (huT' : u < T' - a) :
    loewnerTip (shiftDrive (extDrive W T') a) u = loewnerTip (shiftDrive W a) u := by
  unfold loewnerTip
  rw [fwdMapInv_eq_of_eqOn hu huT' fun r hr => shiftDrive_extDrive_eq ha (by linarith [hr.2])]

/-- **[Yua22] Corollary 1.3 before a finite horizon.** If `η` is a continuous Loewner trace of `W`
before `T` and `a ≥ 0`, the shifted tips `γ_a = loewnerTip (shiftDrive W a)` form a continuous
Loewner trace of the shifted driver before `T − a`, and `F̄_a(γ_a(u)) = η(a + u)`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.isLoewnerTraceLT_shift (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) :
    IsLoewnerTraceLT (shiftDrive W a) (T - a) (loewnerTip (shiftDrive W a)) ∧
      ∀ u, 0 ≤ u → u < T - a →
        extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) u) = η (a + u) := by
  -- the global result for the slit extension at an intermediate horizon `T'`
  have key : ∀ u, 0 ≤ u → u < T - a → ∃ T', a + u < T' ∧ T' < T ∧
      ContinuousOn (loewnerTip (shiftDrive (extDrive W T') a)) (Ici 0) ∧
      EqOn (loewnerTip (shiftDrive W a)) (loewnerTip (shiftDrive (extDrive W T') a))
        (Ico 0 (T' - a)) ∧
      extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) u) = η (a + u) ∧
      fwdHull (shiftDrive W a) u = fillH (loewnerTip (shiftDrive W a) '' Icc 0 u) := by
    intro u hu huT
    set T' := (a + u + T) / 2 with hT'def
    have h1 : a + u < T' := by rw [hT'def]; linarith
    have h2 : T' < T := by rw [hT'def]; linarith
    have hT'0 : 0 ≤ T' := by linarith
    have haT' : a < T' := by linarith
    have hext := hη.isLoewnerTrace_ext hW hW0 hT'0 h2
    have hW' := continuous_extDrive (T' := T') hW
    have hW'0 := extDrive_zero (T' := T') hW0 hT'0
    obtain ⟨hcor, hfib⟩ := hext.isLoewnerTrace_shift_and_extendFrom hW' hW'0 ha
    have heq : EqOn (loewnerTip (shiftDrive W a)) (loewnerTip (shiftDrive (extDrive W T') a))
        (Ico 0 (T' - a)) := fun r hr =>
      (loewnerTip_shift_extDrive haT'.le hr.1 hr.2).symm
    have huT' : u < T' - a := by linarith
    refine ⟨T', h1, h2, hcor.2.1, heq, ?_, ?_⟩
    · have hF : fwdMapInv W a = fwdMapInv (extDrive W T') a :=
        fwdMapInv_eq_of_eqOn ha haT' fun r hr => (extDrive_eq hr.2).symm
      rw [hF, heq ⟨hu, huT'⟩, hfib u hu, extTrace_eq (by linarith)]
    · rw [fwdHull_eq_of_eqOn hu huT' fun r hr =>
        (shiftDrive_extDrive_eq haT'.le (by linarith [hr.2])).symm, hcor.2.2 u hu]
      congr 1
      exact (Set.EqOn.image_eq fun r hr => heq ⟨hr.1, by linarith [hr.2]⟩).symm
  refine ⟨⟨loewnerTip_shiftDrive_zero hW a, fun u₀ hu₀ => ?_, fun u hu huT => ?_⟩,
    fun u hu huT => ?_⟩
  rotate_left
  · obtain ⟨-, -, -, -, -, -, h⟩ := key u hu huT
    exact h
  · obtain ⟨-, -, -, -, -, h, -⟩ := key u hu huT
    exact h
  obtain ⟨T', h1, -, hc, heq, -⟩ := key u₀ hu₀.1 hu₀.2
  have hc' := (hc u₀ hu₀.1).mono (show Ico 0 (T - a) ⊆ Ici 0 from fun r hr => hr.1)
  refine hc'.congr_of_eventuallyEq ?_ (heq ⟨hu₀.1, by linarith⟩)
  have hmem : Ico 0 (T' - a) ∈ 𝓝[Ico 0 (T - a)] u₀ :=
    mem_nhdsWithin.2 ⟨Iio (T' - a), isOpen_Iio, show u₀ < T' - a by linarith,
      fun r hr => ⟨hr.2.1, hr.1⟩⟩
  filter_upwards [hmem] with r hr
  exact heq hr

/-- **Property (ii) of [Yua22, Theorem 1.1] before a finite horizon**: a continuous Loewner trace
before `T` has continuous own futures on every `[0, S]`, `S < T`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.hasContinuousOwnFuture (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {S : ℝ} (hST : S < T) :
    YuanCharacterisation.HasContinuousOwnFuture η S := by
  intro s hs
  have hS0 : 0 < S := lt_of_le_of_lt hs.1 hs.2
  set T' := (S + T) / 2 with hT'def
  have hST' : S < T' := by rw [hT'def]; linarith
  have hT'T : T' < T := by rw [hT'def]; linarith
  have hext := hη.isLoewnerTrace_ext hW hW0 (by linarith) hT'T
  obtain ⟨β, hβc, hβH, hβ⟩ := hext.hasContinuousOwnFuture (continuous_extDrive hW)
    (extDrive_zero hW0 (by linarith)) S s hs
  have hfill : fillH (extTrace W η T' '' Icc 0 s) = fillH (η '' Icc 0 s) := by
    congr 1
    exact Set.EqOn.image_eq fun r hr => extTrace_eq (by linarith [hr.2, hs.2])
  refine ⟨β, hβc, hβH, fun u hu => ?_⟩
  have h := hβ u hu
  rw [hfill, extTrace_eq (by linarith [hu.2])] at h
  exact h

end YuanCorollary13

end InteractingSLE
