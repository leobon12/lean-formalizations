/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIMean
import InteractingSLE.Spec.Restart.FlowStopIdentCMIShift
import InteractingSLE.Spec.Restart.FCAux79MeanFlow
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Spec.Zhan.StripTailPullback
import InteractingSLE.Spec.ZhanGT4.D9Clear
import InteractingSLE.Spec.Restart.FlowStopIdentCMContactTilt

/-!
# The mean identity of Lemma G3 along one path (step (c), the two halves joined)

Packet PROVE-L1-CMI (continuation). Lemma G3's proof (p. 493): off the hull, the mean of the shifted field is the
reference word's mean. In the chart of the seed `y`, for a continuous driver `w` with `w 0 = 0` and a time `t > 0` whose
hull closure lies in the (translated) buffer `N`, with the marks of both flow-line words at their **geometric images**
`ΦL x = −rightImg(−w)(−x) t − w t`, `ΦR x = rightImg w x t − w t`:

* `geomL`, `geomR`; `geomL_eq_fwdMap`, `geomR_eq_fwdMap`: an alive mark sits at `f_t(x)`;
* **`couplingMean_sub_eq_greenPot`**: `M^{bR}_t = M^{b}_t + G_{ℍ∖K_t}(1_ℍ gD F_y.f) + q(· + y) − F_y.f` on `ℍ ∖ K_t`
  (`couplingMean_flowLine_sub`, the marks off `O` alive and at `f_t(p − y)`, `compFun_eq_zero_of_cut`);
* **`integral_couplingMean_shift_eq`**: for a test `φ` off `K_t`,
  `∫ M^{b}_t φ − G_t(φ, F_y.src) + ∫ (q(· + y) − F_y.f) φ = ∫ M^{bR}_t φ` — the identity that turns the tilted
  kernel (`FlowStopIdentCM.ae_condExp_withDensity_add_of_coupling`) into the reference word's kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH)
open MartChar.RealFlow (rightImg gImg)

/-! ### Geometric images of the marks -/

/-- The geometric image of a left mark at time `t`, centred. -/
def geomL (w : ℝ → ℝ) (t x : ℝ) : ℝ := -rightImg (fun s => -w s) (-x) t - w t

/-- The geometric image of a right mark at time `t`, centred. -/
def geomR (w : ℝ → ℝ) (t x : ℝ) : ℝ := rightImg w x t - w t

variable {w : ℝ → ℝ}

theorem geomR_nonneg (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : 0 ≤ geomR w t x := by
  have := MartChar.RealFlow.le_rightImg hw x ht
  rw [geomR]; linarith

theorem geomL_nonpos (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : geomL w t x ≤ 0 := by
  have := MartChar.RealFlow.le_rightImg (w := fun s => -w s) hw.neg (-x) ht
  rw [geomL]; linarith

/-- **An alive right point sits at its forward image.** -/
theorem geomR_eq_fwdMap (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 < x)
    {v : ℝ → ℂ} (hv : IsForwardSol w (x : ℂ) t v) : ((geomR w t x : ℝ) : ℂ) = fwdMap w t (x : ℂ) := by
  have hal := Sec7.Lemma76E.alive_of_isForwardSol hw ht (by rw [hw0]; exact hx) hv
  obtain ⟨u, hu, hut⟩ := FCAux79.exists_isForwardSol_of_alive hw hw0 ht hal
  rw [Zhan.fwdMap_ofReal_eq hw ht hu, hut, geomR, MartChar.RealFlow.rightImg_eq_gImg hw ht hal]

/-- **An alive left point sits at its forward image** (reflection `x ↦ −x`). -/
theorem geomL_eq_fwdMap (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : x < 0)
    {v : ℝ → ℂ} (hv : IsForwardSol w (x : ℂ) t v) : ((geomL w t x : ℝ) : ℂ) = fwdMap w t (x : ℂ) := by
  have hv' : IsForwardSol (fun s => -w s) (((-x : ℝ)) : ℂ) t (fun s => -v s) := by
    have := QuantumZipper.RS.isForwardSol_neg hv
    simpa using this
  have hwn : Continuous fun s => -w s := hw.neg
  have hwn0 : (fun s => -w s) 0 = 0 := by simp [hw0]
  have hR := geomR_eq_fwdMap hwn hwn0 ht (by linarith) hv'
  rw [Zhan.fwdMap_ofReal_eq hwn ht hv'] at hR
  rw [Zhan.fwdMap_ofReal_eq hw ht hv]
  have e : geomL w t x = -geomR (fun s => -w s) t (-x) := by
    simp only [geomL, geomR]; ring
  rw [e, Complex.ofReal_neg, hR, neg_neg]

/-! ### The mean identity along one path -/

section Mean

variable {κ : ℝ} {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ} [DecidablePred (· ∈ O)]

/-- The marks off `O`, read in the chart of the seed `y`. -/
def chartP (J Ĵ : Finset ℝ) (O : Set ℝ) [DecidablePred (· ∈ O)] (y : ℝ) : ↥(offMarks J Ĵ O) → ℝ :=
  fun j => (j : ℝ) - y

/-- The marks off `O` are alive through `t` when the hull closure lies in the chart buffer. -/
theorem marksAlive_chartP (hw : Continuous w) (hw0 : w 0 = 0) {N : Set ℂ}
    (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O) {y : ℝ} (hy : y ∈ O) {t : ℝ} (ht : 0 ≤ t)
    (hKN : closure (fwdHull w t) ⊆ (fun z => z + y) ⁻¹' N) : GB7a.MarksAlive w (chartP J Ĵ O y) t := by
  intro j
  have hjO : (j : ℝ) ∉ O := (Finset.mem_filter.1 j.2).2
  have hx : ((chartP J Ĵ O y j : ℝ) : ℂ) ∉ closure (fwdHull w t) := fun h => by
    have h1 := hKN h
    simp only [mem_preimage, chartP] at h1
    have h2 := hNO _ h1 (by simp)
    simp only [Complex.add_re, Complex.ofReal_re, sub_add_cancel] at h2
    exact hjO h2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hx
  have hd : Disjoint (ball ((chartP J Ĵ O y j : ℝ) : ℂ) r) (fwdHull w t) :=
    Set.disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)
  have hne : chartP J Ĵ O y j ≠ w 0 := by
    rw [hw0, chartP, sub_ne_zero]
    exact fun h => hjO (h ▸ hy)
  exact ZhanGT4.exists_isForwardSol_of_disjoint_ball_gen hw hne ht hr hd

/-- **The coupling means of the two words differ by the comparison field** (Lemma G3, p. 493; Aux. lemma 61): for
`z ∈ ℍ ∖ K_t`, `M^{bR}_t(z) = M^{b}_t(z) + G_{ℍ∖K_t}(1_ℍ gD F_y.f)(z) + q(z + y) − F_y.f(z)`, the marks of both words
at their geometric images. -/
theorem couplingMean_sub_eq_greenPot (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O)
    (θ : ℝ) {F : CMCut} {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {N : Set ℂ}
    (hNo : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O) (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z)
    (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) (hyN : (y : ℂ) ∈ N) (hw : Continuous w)
    (hw0 : w 0 = 0) {t : ℝ} (ht : 0 < t) {η : ℝ → ℂ} (hηc : ContinuousOn η (Icc 0 t))
    (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull w s = fillH (η '' Icc 0 s))
    (hKN : closure (fwdHull w t) ⊆ (fun z => z + y) ⁻¹' N) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL w t (flowLineXL bR Ĵ y i)) (fun j => geomR w t (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL w t (flowLineXL bR Ĵ y i)) (fun j => geomR w t (flowLineXR bR Ĵ y j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => geomL w t (flowLineXL b J y i)) (fun j => geomR w t (flowLineXR b J y j)))
      (forceJumpSet (fun i => geomL w t (flowLineXL b J y i)) (fun j => geomR w t (flowLineXR b J y j))) u)
    {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    couplingMean κ w t uR z = couplingMean κ w t u z +
      GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity (F.shift y).f)) t z + q (z + y) -
        (F.shift y).f z := by
  classical
  have hfz : fwdMap w t z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht.le hz
  have hdiff := couplingMean_flowLine_sub hκ hb hbR hO hbO hy θ (geomL w t) (geomR w t)
    (fun i => geomL_nonpos hw ht.le _) (fun j => geomR_nonneg hw ht.le _)
    (fun i => geomL_nonpos hw ht.le _) (fun j => geomR_nonneg hw ht.le _) huR hu hfz
  have halive := marksAlive_chartP (J := J) (Ĵ := Ĵ) hw hw0 hNO hy ht.le hKN
  -- the alive marks sit at their forward images
  have hpos : ∀ p ∈ offMarks J Ĵ O, ((((if p < y then geomL w t (p - y) else geomR w t (p - y)) : ℝ)) : ℂ) =
      fwdMap w t ((p - y : ℝ) : ℂ) := by
    intro p hp
    obtain ⟨v, hv⟩ := halive ⟨p, hp⟩
    have hpy : p ≠ y := fun h => (Finset.mem_filter.1 hp).2 (h ▸ hy)
    simp only [chartP] at hv
    split_ifs with h
    · exact geomL_eq_fwdMap hw hw0 ht.le (by linarith) hv
    · exact geomR_eq_fwdMap hw hw0 ht.le (lt_of_le_of_ne (not_lt.1 h) (Ne.symm hpy) |> sub_pos.2) hv
  -- the arg sum in the chart
  have hargS : ∀ s : ℝ, GB7a.argSum w (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) s z =
      ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
        (jmp bR p - jmp b p) / Real.pi * Complex.arg (fwdMap w s z - fwdMap w s ((p - y : ℝ) : ℂ))) := by
    intro s
    rw [GB7a.argSum, argC₀, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_coe_sort (offMarks J Ĵ O)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [argC, chartP]
    ring
  have hM : couplingMean κ w t uR z - couplingMean κ w t u z =
      GB7a.argSum w (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) t z := by
    rw [hdiff, hargS t]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hpos p hp]
  -- Aux. 61 in the chart
  set N' : Set ℂ := (fun z => z + y) ⁻¹' N with hN'
  have hN'o : IsOpen N' := hNo.preimage (continuous_id.add continuous_const)
  have h0N' : (0 : ℂ) ∈ N' := by simp only [hN', mem_preimage, zero_add]; exact hyN
  have harg0 : ∀ x : ℂ, x ∈ H → GB7a.argSum0 (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) x =
      q (x + y) := fun x hx => by
    have e := argSum0_shift (argP J Ĵ O) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) y x
    have hxy : x + (y : ℂ) ∈ H := Exist.add_real_mem_H hx y
    have e2 : chartP J Ĵ O y = fun j => argP J Ĵ O j - y := rfl
    rw [e2, e, argSum0_eq hb hbR hO hbO hq hy hxy]
  have hfN : ∀ x ∈ N', x ∈ H → (F.shift y).f x =
      GB7a.argSum0 (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) x := fun x hxN hx => by
    rw [CMCut.shift_f, harg0 x hx, hFq _ hxN (Exist.add_real_mem_H hx y)]
  have hΔN : ∀ x ∈ N', QuantumZipper.K3.greenDensity (F.shift y).f x = 0 := fun x hx => by
    rw [CMCut.greenDensity_shift]; exact hFΔ _ hx
  have hseed : argC₀ b bR J Ĵ O y + Real.pi *
      ∑ j ∈ Finset.univ.filter (fun j => 0 < chartP J Ĵ O y j), argC b bR J Ĵ O j = 0 := by
    rw [argC₀, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_coe_sort (offMarks J Ĵ O), ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [chartP, argC, sub_pos]
    split_ifs <;> field_simp <;> ring
  have hcomp := compFun_eq_zero_of_cut (F.shift y) hN'o h0N' hfN hΔN hseed hw hw0 ht hηc hfill hKN halive
    ⟨ht, le_rfl⟩ hz
  have h0 : GB7a.argSum w (chartP J Ĵ O y) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) 0 z = q (z + y) := by
    have hz0 : z ≠ 0 := fun h => by
      have : (0 : ℝ) < z.im := hz.1
      rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this
    rw [← harg0 z hz.1, GB7a.argSum, GB7a.argSum0, GB7a.fwdMap_zero_time hw hw0 hz0]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have hp0 : ((chartP J Ĵ O y j : ℝ) : ℂ) ≠ 0 := by
      obtain ⟨v, hv⟩ := halive j
      exact GB7a.ne_zero_of_isForwardSol hw0 ht.le hv
    rw [GB7a.fwdMap_zero_time hw hw0 hp0]
  rw [h0] at hcomp
  linarith

/-- The chart shift `(q − F.f)(· + y)` as a distribution. -/
def chartShift (F : CMCut) (q : ℂ → ℝ) (y : ℝ) : LQGMetric.DistOn upperHalfPlaneOpens :=
  SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens fun z => q (z + y) - (F.shift y).f z

/-- **The mean identity against a test off the hull** (the form produced by the Cameron–Martin tilt): for a driver
`rpath w'` with `w'` continuous and `w' 0 = 0`, `∫ M^{b}_t φ − G_t(φ, F_y.src) + T_y(φ) = ∫ M^{bR}_t φ`,
`T_y = chartShift F q y`. -/
theorem integral_couplingMean_shift_eq (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O)
    (θ : ℝ) {F : CMCut} {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {N : Set ℂ}
    (hNo : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O) (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z)
    (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) (hyN : (y : ℂ) ∈ N) {w' : ℝ≥0 → ℝ}
    (hw' : Continuous w') (hw0 : w' 0 = 0) {t : ℝ≥0} (ht : 0 < t) {η : ℝ → ℂ} (hηc : ContinuousOn η (Icc 0 t))
    (hfill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull (Ito.rpath w') s = fillH (η '' Icc 0 s))
    (hKN : closure (fwdHull (Ito.rpath w') t) ⊆ (fun z => z + y) ⁻¹' N) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR bR Ĵ y j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i)) (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') t (flowLineXL b J y i))
        (fun j => geomR (Ito.rpath w') t (flowLineXR b J y j))) u)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') t)) :
    (∫ z, couplingMean κ (Ito.rpath w') t u z * φ z) - LocalExt.greenCross (Ito.rpath w') t φ (F.shift y).src +
        chartShift F q y φ = ∫ z, couplingMean κ (Ito.rpath w') t uR z * φ z := by
  set w : ℝ → ℝ := Ito.rpath w' with hwdef
  have hw : Continuous w := hw'.comp continuous_real_toNNReal
  have hw00 : w 0 = 0 := by simp [hwdef, Ito.rpath, hw0]
  have hwc : ContinuousOn w (Icc 0 (t : ℝ)) := hw.continuousOn
  set v : ℂ → ℝ := H.indicator (QuantumZipper.K3.greenDensity (F.shift y).f) with hv
  set G : ℂ → ℝ := GB7a.greenPot w v t with hG
  have hφH : ∀ z, φ z ≠ 0 → z ∈ H \ fwdHull w t := fun z hz =>
    ⟨φ.tsupport_subset (subset_tsupport _ hz), fun hK => Set.disjoint_left.1 hφ (subset_tsupport _ hz) hK⟩
  -- pointwise identity
  have hpt : ∀ z, couplingMean κ w t uR z * φ z = couplingMean κ w t u z * φ z + G z * φ z +
      φ z * (q (z + y) - (F.shift y).f z) := fun z => by
    by_cases hz : φ z = 0
    · simp [hz]
    · rw [couplingMean_sub_eq_greenPot hκ hb hbR hO hbO hy θ hq hNo hNO hFq hFΔ hyN hw hw00 (by exact_mod_cast ht)
        hηc hfill hKN huR hu (hφH z hz)]
      ring
  -- integrability
  have iR := LocalExt.integrable_couplingMean_mul (κ := κ) hwc huR.1 hφ
  have iB := LocalExt.integrable_couplingMean_mul (κ := κ) hwc hu.1 hφ
  have hqyc : ContinuousOn (fun z => q (z + y) - (F.shift y).f z) H := by
    have h1 : ContinuousOn q H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
    refine (h1.comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz y).sub
      (F.shift y).smooth.continuous.continuousOn
  have iT : Integrable fun z => φ z * (q (z + y) - (F.shift y).f z) :=
    (LocalExt.integrable_mul_testOn hqyc φ).congr (ae_of_all _ fun z => mul_comm _ _)
  have iG : Integrable fun z => G z * φ z := by
    refine ((iR.sub iB).sub iT).congr (ae_of_all _ fun z => ?_)
    simp only [Pi.sub_apply]
    rw [hpt z]; ring
  -- the cross term
  have hcross : LocalExt.greenCross w t φ (F.shift y).src = -∫ z, G z * φ z := by
    unfold LocalExt.greenCross
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e : (fun z => φ x * greenH (fwdMap w t x) (fwdMap w t z) * (F.shift y).src z) =
        fun z => -(φ x * (greenH (fwdMap w t x) (fwdMap w t z) * v z)) := by
      funext z
      simp only [CMCut.src, hv]
      ring
    simp only at e ⊢
    rw [e, integral_neg, integral_const_mul]
    simp only [hG, GB7a.greenPot]
    ring
  have hT : chartShift F q y φ = ∫ z, φ z * (q (z + y) - (F.shift y).f z) :=
    SupercriticalConformalCovariance.GM24.smoothDist_apply hqyc φ
  have iBG : Integrable fun z => couplingMean κ w t u z * φ z + G z * φ z := iB.add iG
  rw [hcross, hT, sub_neg_eq_add, ← integral_add iB iG, ← integral_add iBG iT]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  exact (hpt z).symm

/-- The geometric images at time `0` are the starting points. -/
theorem geomL_zero (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : x ≤ 0) : geomL w 0 x = x := by
  have h := MartChar.RealFlow.rightImg_zero (w := fun s => -w s) hw.neg (by simp [hw0]) (x := -x) (by linarith)
  rw [geomL, h, hw0]; ring

theorem geomR_zero (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x) : geomR w 0 x = x := by
  rw [geomR, MartChar.RealFlow.rightImg_zero hw hw0 hx, hw0, sub_zero]

/-- **The mean identity at time `0`** (no hull): `∫ M^{b}_0 φ − G_0(φ, F_y.src) + T_y(φ) = ∫ M^{bR}_0 φ`. -/
theorem integral_couplingMean_shift_eq_zero (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O)
    (θ : ℝ) (F : CMCut) {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {w' : ℝ≥0 → ℝ}
    (hw' : Continuous w') (hw0 : w' 0 = 0) {uR u : ℂ → ℝ}
    (huR : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ)
        (fun i => geomL (Ito.rpath w') 0 (flowLineXL bR Ĵ y i)) (fun j => geomR (Ito.rpath w') 0 (flowLineXR bR Ĵ y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') 0 (flowLineXL bR Ĵ y i))
        (fun j => geomR (Ito.rpath w') 0 (flowLineXR bR Ĵ y j))) uR)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        (fun i => geomL (Ito.rpath w') 0 (flowLineXL b J y i)) (fun j => geomR (Ito.rpath w') 0 (flowLineXR b J y j)))
      (forceJumpSet (fun i => geomL (Ito.rpath w') 0 (flowLineXL b J y i))
        (fun j => geomR (Ito.rpath w') 0 (flowLineXR b J y j))) u)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    (∫ z, couplingMean κ (Ito.rpath w') 0 u z * φ z) - LocalExt.greenCross (Ito.rpath w') 0 φ (F.shift y).src +
        chartShift F q y φ = ∫ z, couplingMean κ (Ito.rpath w') 0 uR z * φ z := by
  classical
  set w : ℝ → ℝ := Ito.rpath w' with hwdef
  have hw : Continuous w := hw'.comp continuous_real_toNNReal
  have hw00 : w 0 = 0 := by simp [hwdef, Ito.rpath, hw0]
  have hwc : ContinuousOn w (Icc 0 ((0 : ℝ≥0) : ℝ)) := hw.continuousOn
  have hK0 : fwdHull w 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hw
  have hφ : Disjoint (tsupport φ) (fwdHull (Ito.rpath w') ((0 : ℝ≥0) : ℝ)) := by
    rw [NNReal.coe_zero, ← hwdef, hK0]; exact disjoint_empty _
  have hfix : ∀ z : ℂ, z ∈ H → fwdMap w 0 z = z := fun z hz => by
    have hz0 : z ≠ ((w 0 : ℝ) : ℂ) := by
      rw [hw00, Complex.ofReal_zero]; intro h; have : (0 : ℝ) < z.im := hz; rw [h] at this; simp at this
    rw [QuantumZipper.B5.fwdMap_zero_time w hz0, hw00, Complex.ofReal_zero, sub_zero]
  -- pointwise: `M^{bR}_0 − M^{b}_0 = q(· + y)` on `ℍ`
  have hpt : ∀ z, z ∈ H → couplingMean κ w 0 uR z - couplingMean κ w 0 u z = q (z + y) := fun z hz => by
    have hfz : fwdMap w 0 z ∈ H := by rw [hfix z hz]; exact hz
    rw [couplingMean_flowLine_sub hκ hb hbR hO hbO hy θ (geomL w 0) (geomR w 0)
      (fun i => geomL_nonpos hw le_rfl _) (fun j => geomR_nonneg hw le_rfl _)
      (fun i => geomL_nonpos hw le_rfl _) (fun j => geomR_nonneg hw le_rfl _) huR hu hfz,
      eq_offSum hb hbR hO hbO hq hy (Exist.add_real_mem_H hz y), hfix z hz]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpos : (((if p < y then geomL w 0 (p - y) else geomR w 0 (p - y)) : ℝ) : ℂ) = ((p - y : ℝ) : ℂ) := by
      split_ifs with h
      · rw [geomL_zero hw hw00 (by linarith)]
      · rw [geomR_zero hw hw00 (by linarith [not_lt.1 h])]
    rw [hpos]
    congr 3
    push_cast; ring
  have iR := LocalExt.integrable_couplingMean_mul (κ := κ) hwc huR.1 hφ
  have iB := LocalExt.integrable_couplingMean_mul (κ := κ) hwc hu.1 hφ
  simp only [NNReal.coe_zero] at iR iB
  have hqyc : ContinuousOn (fun z => q (z + y) - (F.shift y).f z) H := by
    have h1 : ContinuousOn q H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
    refine (h1.comp (continuousOn_id.add continuousOn_const) fun z hz => Exist.add_real_mem_H hz y).sub
      (F.shift y).smooth.continuous.continuousOn
  have iT : Integrable fun z => φ z * (q (z + y) - (F.shift y).f z) :=
    (LocalExt.integrable_mul_testOn hqyc φ).congr (ae_of_all _ fun z => mul_comm _ _)
  have iF : Integrable fun z => φ z * (F.shift y).f z :=
    (φ.continuous.mul (F.shift y).smooth.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hcross : LocalExt.greenCross w 0 φ (F.shift y).src = -∫ z, φ z * (F.shift y).f z := by
    have e : fwdMap w 0 = fwdMap (fun _ => (0 : ℝ)) 0 := by
      funext z
      exact InteractingSLE.fwdMap_eq_of_eqOn le_rfl fun r hr => by
        have : r = 0 := le_antisymm hr.2 hr.1
        rw [this, hw00]
    rw [LocalExt.greenCross_congr e, CMCut.greenCross_zero_src]
  have hT : chartShift F q y φ = ∫ z, φ z * (q (z + y) - (F.shift y).f z) :=
    SupercriticalConformalCovariance.GM24.smoothDist_apply hqyc φ
  have iBF : Integrable fun z => couplingMean κ w 0 u z * φ z + φ z * (F.shift y).f z := iB.add iF
  rw [hcross, hT, sub_neg_eq_add, ← integral_add iB iF, ← integral_add iBF iT]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show couplingMean κ w 0 u z * φ z + φ z * (F.shift y).f z + φ z * (q (z + y) - (F.shift y).f z) =
    couplingMean κ w 0 uR z * φ z
  by_cases hz : φ z = 0
  · simp [hz]
  · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ hz)
    have := hpt z hzH
    rw [show couplingMean κ w 0 uR z = couplingMean κ w 0 u z + q (z + y) by linarith]
    ring

end Mean

end FlowStopIdentCMI

end Restart

end InteractingSLE
