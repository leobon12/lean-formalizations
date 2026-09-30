import QuantumZipper.Proofs.GFF.Existence

/-!
# DOM-a by annulus features (D34), nodes AN2/AN3: norm bounds for free vectors

`exists_norm_freeVec_le_an`: the free vector `v̂_ρ` of an admissible measure is bounded in norm
by a constant depending only on a support radius `Rb`, a bound `C` on the singular logarithmic
potential of `ρ` (the admissibility constant) and a mass bound `m`.

Proof: `‖v̂_ρ‖² = kernelCov2 neumannH (ρ, ρ(ℂ)·ρ₀) (ρ, ρ(ℂ)·ρ₀)` (the reference part has zero free
vector), and each of the four `kernelCov neumannH` terms is bounded by splitting
`|log r| ≤ log⁻ r + log(1 + 2Rb)` for `r ≤ 2Rb`. Own elementary argument (cost rule).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ENNReal ComplexConjugate

namespace QuantumZipper

namespace Prop16Asm

open GFFExist

/-- `ofReal |log a| ≤ ofReal (-log a) + ofReal (log (1 + 2 Rb))` for `0 ≤ a ≤ 2 Rb`. -/
theorem ofReal_abs_log_le_an {a Rb : ℝ} (ha : 0 ≤ a) (haR : a ≤ 2 * Rb) :
    ENNReal.ofReal |Real.log a| ≤
      ENNReal.ofReal (-Real.log a) + ENNReal.ofReal (Real.log (1 + 2 * Rb)) := by
  have hRb : 0 ≤ Rb := by linarith
  rcases le_or_gt a 1 with h1 | h1
  · rw [abs_of_nonpos (Real.log_nonpos ha h1)]; exact le_self_add
  · rw [abs_of_nonneg (Real.log_nonneg h1.le)]
    refine le_add_left (ENNReal.ofReal_le_ofReal ?_)
    exact Real.log_le_log (by linarith) (by linarith)

/-- Bound on `kernelCov neumannH` for measures carried by a ball, via the log-potential bound of
the second measure. -/
theorem abs_kernelCov_neumannH_le_an {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Rb : ℝ} (hμB : ∀ᵐ x ∂μ, ‖x‖ ≤ Rb) (hνB : ∀ᵐ y ∂ν, ‖y‖ ≤ Rb)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hνC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂ν ≤ C) :
    |kernelCov neumannH μ ν| ≤
      (2 * C.toReal + 2 * Real.log (1 + 2 * Rb) * ν.real univ) * μ.real univ := by
  set L := Real.log (1 + 2 * Rb) with hLdef
  have hbd : ∀ x, ‖x‖ ≤ Rb → ‖∫ y, neumannH x y ∂ν‖ ≤ 2 * C.toReal + 2 * L * ν.real univ := by
    intro x hx
    have hRb : 0 ≤ Rb := (norm_nonneg _).trans hx
    have hL : 0 ≤ L := Real.log_nonneg (by linarith)
    have hpt : ∀ᵐ y ∂ν, ENNReal.ofReal ‖neumannH x y‖ ≤ ENNReal.ofReal (-Real.log ‖y - x‖) +
        ENNReal.ofReal (-Real.log ‖y - conj x‖) + ENNReal.ofReal (2 * L) := by
      filter_upwards [hνB] with y hy
      have h1 : ‖x - y‖ ≤ 2 * Rb := (norm_sub_le _ _).trans (by linarith)
      have h2 : ‖x - conj y‖ ≤ 2 * Rb :=
        (norm_sub_le _ _).trans (by rw [Complex.norm_conj]; linarith)
      have a1 := ofReal_abs_log_le_an (norm_nonneg (x - y)) h1
      have a2 := ofReal_abs_log_le_an (norm_nonneg (x - conj y)) h2
      rw [← hLdef] at a1 a2
      rw [norm_sub_rev y x, ← norm_sub_conj_comm x y]
      have hN : ‖neumannH x y‖ ≤ |Real.log ‖x - y‖| + |Real.log ‖x - conj y‖| := by
        rw [neumannH, Real.norm_eq_abs]
        calc |-Real.log ‖x - y‖ - Real.log ‖x - conj y‖|
            ≤ |-Real.log ‖x - y‖| + |Real.log ‖x - conj y‖| := abs_sub _ _
          _ = _ := by rw [abs_neg]
      calc ENNReal.ofReal ‖neumannH x y‖
          ≤ ENNReal.ofReal (|Real.log ‖x - y‖| + |Real.log ‖x - conj y‖|) :=
            ENNReal.ofReal_le_ofReal hN
        _ ≤ ENNReal.ofReal |Real.log ‖x - y‖| + ENNReal.ofReal |Real.log ‖x - conj y‖| :=
            ENNReal.ofReal_add_le
        _ ≤ (ENNReal.ofReal (-Real.log ‖x - y‖) + ENNReal.ofReal L) +
            (ENNReal.ofReal (-Real.log ‖x - conj y‖) + ENNReal.ofReal L) := add_le_add a1 a2
        _ = _ := by
            rw [show 2 * L = L + L by ring, ENNReal.ofReal_add hL hL]; ring
    have hm1 : Measurable fun y : ℂ => ENNReal.ofReal (-Real.log ‖y - x‖) := by fun_prop
    have hlin : ∫⁻ y, ENNReal.ofReal ‖neumannH x y‖ ∂ν ≤
        C + C + ENNReal.ofReal (2 * L) * ν univ := by
      calc ∫⁻ y, ENNReal.ofReal ‖neumannH x y‖ ∂ν
          ≤ ∫⁻ y, (ENNReal.ofReal (-Real.log ‖y - x‖) +
              ENNReal.ofReal (-Real.log ‖y - conj x‖) + ENNReal.ofReal (2 * L)) ∂ν :=
            lintegral_mono_ae hpt
        _ = ∫⁻ y, ENNReal.ofReal (-Real.log ‖y - x‖) ∂ν +
              ∫⁻ y, ENNReal.ofReal (-Real.log ‖y - conj x‖) ∂ν +
              ENNReal.ofReal (2 * L) * ν univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_add_left hm1, lintegral_const]
        _ ≤ C + C + ENNReal.ofReal (2 * L) * ν univ := by
            gcongr
            · exact hνC x
            · exact hνC (conj x)
    have hfin : C + C + ENNReal.ofReal (2 * L) * ν univ ≠ ⊤ := by
      have := measure_ne_top ν univ
      finiteness
    refine (norm_integral_le_lintegral_norm _).trans ((ENNReal.toReal_mono hfin hlin).trans ?_)
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add hC hC,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]
    ring_nf; rfl
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x => ∫ y, neumannH x y ∂ν) (C := 2 * C.toReal + 2 * L * ν.real univ)
    (by filter_upwards [hμB] with x hx; exact hbd x hx)
  rwa [Real.norm_eq_abs] at h

/-- The reference part of a free vector vanishes. -/
theorem freeVec_freeRef_an (ρ : AdmT) :
    freeVec ⟨freeRef ρ.1, freeRef_admissible ρ.2⟩ = 0 := by
  have hr : freeRef (freeRef ρ.1) = freeRef ρ.1 := by
    simp only [freeRef, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [freeVec, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [(freeMemLp ⟨freeRef ρ.1, freeRef_admissible ρ.2⟩).coeFn_toLp] with q hq
  rw [hq]
  simp only [hkFeat, hr, sub_self, mul_zero, Pi.zero_apply]

/-- `‖v̂_ρ‖² = kernelCov2 neumannH (ρ, ρ(ℂ)·ρ₀) (ρ, ρ(ℂ)·ρ₀)`. -/
theorem norm_freeVec_sq_an (ρ : AdmT) :
    ‖freeVec ρ‖ ^ 2 = kernelCov2 neumannH (ρ.1, freeRef ρ.1) (ρ.1, freeRef ρ.1) := by
  have hm : ρ.1 univ = (freeRef ρ.1) univ := by
    simp only [freeRef, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have h := freeVec_inner ρ ⟨freeRef ρ.1, freeRef_admissible ρ.2⟩ ρ
    ⟨freeRef ρ.1, freeRef_admissible ρ.2⟩ hm hm
  rw [freeVec_freeRef_an, sub_zero, real_inner_self_eq_norm_sq] at h
  exact h

/-- **Uniform norm bound for free vectors.** -/
theorem exists_norm_freeVec_le_an (Rb : ℝ) {C : ℝ≥0∞} (hC : C ≠ ⊤) (m : ℝ) :
    ∃ B : ℝ, ∀ ρ : AdmT, (∀ᵐ x ∂ρ.1, ‖x‖ ≤ Rb) →
      (∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂ρ.1 ≤ C) → ρ.1.real univ ≤ m →
        ‖freeVec ρ‖ ≤ B := by
  obtain ⟨-, ⟨K, hK, -, hK0⟩, Cr, hCr, hbr⟩ := gffEx_admissible_ref
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  set R' := max (max Rb r) 0 with hR'
  set m' := max m 0 with hm'
  set Ct := C + ENNReal.ofReal m' * Cr with hCt
  have hCt' : Ct ≠ ⊤ := by rw [hCt]; exact ENNReal.add_ne_top.2 ⟨hC, by finiteness⟩
  set L := Real.log (1 + 2 * R') with hL
  set Q := (2 * Ct.toReal + 2 * L * m') * m' with hQ
  refine ⟨Real.sqrt (4 * Q), fun ρ hρB hρC hρm => ?_⟩
  set a := ρ.1 with ha
  have := ρ.2.1
  set b := freeRef a with hb
  have : IsFiniteMeasure b := (freeRef_admissible ρ.2).1
  have hae_ref : ∀ᵐ x ∂gffExRef, ‖x‖ ≤ R' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hK0] with x hx
    have := hr (not_not.mp hx)
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  have haB : ∀ᵐ x ∂a, ‖x‖ ≤ R' := by
    filter_upwards [hρB] with x hx using hx.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hbB : ∀ᵐ x ∂b, ‖x‖ ≤ R' := by
    rw [hb, freeRef]; exact Measure.ae_smul_measure hae_ref _
  have hma : a.real univ ≤ m' := hρm.trans (le_max_left _ _)
  have hmb : b.real univ ≤ m' := by rw [hb, freeRef_real_univ]; exact hma
  have haC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂a ≤ Ct :=
    fun y => (hρC y).trans le_self_add
  have hbC : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂b ≤ Ct := by
    intro y
    rw [hb, freeRef, lintegral_smul_measure]
    refine le_add_left (mul_le_mul' ?_ (hbr y))
    rw [← ofReal_measureReal (measure_ne_top a univ)]
    exact ENNReal.ofReal_le_ofReal hma
  have hm0 : 0 ≤ m' := le_max_right _ _
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [le_max_right (max Rb r) 0])
  have hE : ∀ (x y : Measure ℂ) [IsFiniteMeasure x] [IsFiniteMeasure y], (∀ᵐ z ∂x, ‖z‖ ≤ R') →
      (∀ᵐ z ∂y, ‖z‖ ≤ R') → (∀ w, ∫⁻ z, ENNReal.ofReal (-Real.log ‖z - w‖) ∂y ≤ Ct) →
      x.real univ ≤ m' → y.real univ ≤ m' → |kernelCov neumannH x y| ≤ Q := by
    intro x y _ _ hx hy hyC hxm hym
    refine (abs_kernelCov_neumannH_le_an hx hy hCt' hyC).trans ?_
    rw [hQ]
    exact mul_le_mul (by gcongr) hxm measureReal_nonneg (by positivity)
  have h1 := hE a a haB haB haC hma hma
  have h2 := hE a b haB hbB hbC hma hmb
  have h3 := hE b a hbB haB haC hmb hma
  have h4 := hE b b hbB hbB hbC hmb hmb
  have hsq : ‖freeVec ρ‖ ^ 2 ≤ 4 * Q := by
    rw [norm_freeVec_sq_an, kernelCov2]
    rw [abs_le] at h1 h2 h3 h4
    linarith [h1.2, h2.1, h3.1, h4.2]
  have := Real.abs_le_sqrt hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at this

end Prop16Asm

end QuantumZipper
