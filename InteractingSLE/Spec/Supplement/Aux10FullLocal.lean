/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullChain
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.WangWu.ReverseContactBdryChart
import InteractingSLE.Spec.Sec6.DrivingArgLift

/-!
# Aux. lemma 10: localization of the inverse Loewner map near the hull interval

Packet PROVE-T14-BR9. Specification Aux. lemma 10, proof (pp. 69–71): the comparison map `R_t = g̃ ∘ φ ∘ g_t⁻¹`
reflects across the real interval `I_t` representing the old filled hull. The reflection needs to know where
`f_t⁻¹` sends a neighbourhood of that interval. Let `x_a < 0 < x_b` be real points not swallowed by time `t`
(alive), with images `y_a = f_t(x_a)`, `y_b = f_t(x_b)`.

* `exists_local`: for every open `S` containing `closure K_t` and `[x_a, x_b]`, there is `r > 0` such that every
  `z ∈ ℍ \ K_t` with `f_t(z)` within `r` of `[y_a, y_b]` lies in `S` (compactness: a limit point outside `S` is either
  in `ℍ \ K_t`, where `f_t` is continuous with values in `ℍ`, or an alive real point outside `[x_a, x_b]`, whose image
  lies outside `[y_a, y_b]` by the monotonicity of the real flow).
* `exists_eq_of_le` / `exists_eq_of_ge`: every real `y ≤ y_a` (resp. `y ≥ y_b`) is the image of an alive real point
  `x' ≤ x_a` (resp. `x' ≥ x_b`), by the intermediate value theorem for the real flow (continuous in the starting
  point by Grönwall, `f_t(x) ≤ x − W_t` on the left).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H IsForwardSol)

namespace InteractingSLE

namespace Aux10

variable {W : ℝ → ℝ}

/-- `f_t` moves points of `ℍ \ K_t` by a bounded amount. -/
theorem exists_norm_fwdMap_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ z ∈ H \ QuantumZipper.fwdHull W t, ‖QuantumZipper.fwdMap W t z - z‖ ≤ C := by
  rcases ht.lt_or_eq with ht' | rfl
  · obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn (hW.continuousOn (s := Icc 0 t))).isBounded.exists_norm_le
    refine ⟨24 * M + 8 * Real.sqrt t, fun z hz => QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform hW hW0 ht'
      (fun s hs => ?_) hz⟩
    have := hM _ (mem_image_of_mem W hs)
    rwa [Real.norm_eq_abs] at this
  · refine ⟨0, fun z hz => ?_⟩
    have h := Sec5.CrossRestart.gmap_zero_apply hW hz.1
    simp only [ConformalImage.gmap, hW0, ofReal_zero, add_zero] at h
    rw [h, sub_self, norm_zero]

/-- A real point `x ≠ 0` outside `closure K_t` is alive at time `t`. -/
theorem exists_isForwardSol_of_notMem_closure (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {x : ℝ}
    (hx : x ≠ 0) (hxK : (x : ℂ) ∉ closure (QuantumZipper.fwdHull W t)) : ∃ v, IsForwardSol W x t v := by
  obtain ⟨r, hr, hd⟩ := Supp8.GB6.exists_ball_disjoint_of_notMem_closure hxK
  exact ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hx ht hr hd

/-- **Localization.** Points of `ℍ \ K_t` whose `f_t`-image is close to `[f_t(x_a), f_t(x_b)]` lie in any prescribed
open neighbourhood of `closure K_t ∪ [x_a, x_b]`. -/
theorem exists_local (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {xa xb : ℝ} (hxa : xa < 0)
    (hxb : 0 < xb) {va vb : ℝ → ℂ} (hva : IsForwardSol W xa t va) (hvb : IsForwardSol W xb t vb) {S : Set ℂ}
    (hSo : IsOpen S) (hS : closure (QuantumZipper.fwdHull W t) ⊆ S) (hS' : ∀ x ∈ Icc xa xb, (x : ℂ) ∈ S) :
    ∃ r > 0, ∀ z ∈ H \ QuantumZipper.fwdHull W t, ∀ y ∈ Icc (va t).re (vb t).re,
      ‖QuantumZipper.fwdMap W t z - y‖ < r → z ∈ S := by
  set K := QuantumZipper.fwdHull W t with hKdef
  by_contra hcon
  push Not at hcon
  choose z hz y hy hfy hzS using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hW hW0 ht
  set B : ℝ := |(va t).re| + |(vb t).re| with hB
  have hyb : ∀ n, |y n| ≤ B := fun n => by
    rw [hB, abs_le]
    obtain ⟨h1, h2⟩ := hy n
    constructor <;> linarith [neg_abs_le (va t).re, le_abs_self (vb t).re, abs_nonneg (va t).re,
      abs_nonneg (vb t).re]
  have hzb : ∀ n, z n ∈ closedBall (0 : ℂ) (B + 1 + C) := fun n => by
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC (z n) (hz n)
    have h2 : ‖QuantumZipper.fwdMap W t (z n) - y n‖ ≤ 1 := (hfy n).le.trans (by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    have h3 : ‖((y n : ℝ) : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hyb n
    calc ‖z n‖ = ‖(QuantumZipper.fwdMap W t (z n) - y n) + (y n : ℂ) -
          (QuantumZipper.fwdMap W t (z n) - z n)‖ := by ring_nf
      _ ≤ ‖QuantumZipper.fwdMap W t (z n) - y n‖ + ‖((y n : ℝ) : ℂ)‖ +
          ‖QuantumZipper.fwdMap W t (z n) - z n‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ B + 1 + C := by linarith
  obtain ⟨p, hp, φs, hφs, hlim⟩ := ((isCompact_closedBall (0 : ℂ) (B + 1 + C)).prod
    (isCompact_Icc (a := (va t).re) (b := (vb t).re))).tendsto_subseq (x := fun n => (z n, y n))
    (fun n => ⟨hzb n, hy n⟩)
  have hzl : Tendsto (fun n => z (φs n)) atTop (𝓝 p.1) := (continuous_fst.tendsto _).comp hlim
  have hyl : Tendsto (fun n => y (φs n)) atTop (𝓝 p.2) := (continuous_snd.tendsto _).comp hlim
  have hfz : Tendsto (fun n => QuantumZipper.fwdMap W t (z (φs n))) atTop (𝓝 ((p.2 : ℝ) : ℂ)) := by
    have hy' : Tendsto (fun n => ((y (φs n) : ℝ) : ℂ)) atTop (𝓝 ((p.2 : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp hyl
    have hd : Tendsto (fun n => QuantumZipper.fwdMap W t (z (φs n)) - y (φs n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hfy (φs n)).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφs.tendsto_atTop
    have := hd.add hy'
    simpa using this
  have hpS : p.1 ∉ S := fun h => by
    obtain ⟨n, hn⟩ := (hzl.eventually (hSo.mem_nhds h)).exists
    exact hzS _ hn
  have hpH : 0 ≤ p.1.im :=
    (isClosed_le continuous_const continuous_im).mem_of_tendsto hzl
      (Eventually.of_forall fun n => show 0 ≤ (z (φs n)).im from (hz (φs n)).1.le)
  rcases hpH.lt_or_eq with hpos | hzero
  · have hpK : p.1 ∈ H \ K := ⟨hpos, fun h => hpS (hS (subset_closure h))⟩
    have hc : ContinuousAt (QuantumZipper.fwdMap W t) p.1 :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).differentiableAt
        ((QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht).mem_nhds hpK)).continuousAt
    have heq := tendsto_nhds_unique (hc.tendsto.comp hzl) hfz
    have him : 0 < (QuantumZipper.fwdMap W t p.1).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hpK
    rw [heq, ofReal_im] at him
    exact lt_irrefl _ him
  · set x := p.1.re with hxdef
    have hpx : p.1 = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [hzero.symm])
    have hxK : (x : ℂ) ∉ closure K := fun h => hpS (hpx ▸ hS h)
    have hxI : x ∉ Icc xa xb := fun h => hpS (hpx ▸ hS' x h)
    have hx0 : x ≠ 0 := fun h => hxI ⟨by rw [h]; exact hxa.le, by rw [h]; exact hxb.le⟩
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_notMem_closure hW hW0 ht hx0 hxK
    have hzH : Tendsto (fun n => z (φs n)) atTop (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hpx ▸ hzl, Eventually.of_forall fun n => (hz (φs n)).1⟩
    have hval := tendsto_nhds_unique ((tendsto_fwdMap_of_isForwardSol hW ht hv).comp hzH) hfz
    have hvt := fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩
    have hpI := hp.2
    rcases not_and_or.1 hxI with hlt | hgt
    · push Not at hlt
      have h := WangWu.re_fwdMap_lt_re_fwdMap hW hW0 ht hlt (Or.inr hxa) hv hva
      rw [hvt, fwdMap_eq_of_isForwardSol hW hva ⟨ht, le_rfl⟩, hval, ofReal_re] at h
      exact absurd hpI.1 (not_le.2 h)
    · push Not at hgt
      have h := WangWu.re_fwdMap_lt_re_fwdMap hW hW0 ht hgt (Or.inl hxb) hvb hv
      rw [hvt, fwdMap_eq_of_isForwardSol hW hvb ⟨ht, le_rfl⟩, hval, ofReal_re] at h
      exact absurd hpI.2 (not_le.2 h)

/-- A real solution started at `x < 0` stays negative. -/
theorem re_neg_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (hx : x < 0) {u : ℝ → ℂ}
    (hu : IsForwardSol W x t u) : ∀ s ∈ Icc (0 : ℝ) t, (u s).re < 0 := by
  intro s hs
  by_contra hge
  push Not at hge
  have h0 : (u 0).re = x := by
    rw [(hu.2 0 ⟨le_rfl, hs.1.trans hs.2⟩).2]
    simp [hW0]
  have hc : ContinuousOn (fun r => (u r).re) (Icc 0 s) :=
    (continuous_re.comp_continuousOn hu.1).mono (Icc_subset_Icc_right hs.2)
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hs.1 hc ⟨by rw [h0]; exact hx.le, hge⟩
  have hrT : r ∈ Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans hs.2⟩
  have him := im_eq_zero_of_isForwardSol_real hW hu hrT
  exact (hu.2 r hrT).1 (Complex.ext hr0 him)

/-- A real solution started at `x > 0` stays positive. -/
theorem re_pos_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (hx : 0 < x) {u : ℝ → ℂ}
    (hu : IsForwardSol W x t u) : ∀ s ∈ Icc (0 : ℝ) t, 0 < (u s).re := by
  intro s hs
  by_contra hle
  push Not at hle
  have h0 : (u 0).re = x := by
    rw [(hu.2 0 ⟨le_rfl, hs.1.trans hs.2⟩).2]
    simp [hW0]
  have hc : ContinuousOn (fun r => (u r).re) (Icc 0 s) :=
    (continuous_re.comp_continuousOn hu.1).mono (Icc_subset_Icc_right hs.2)
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 hc ⟨hle, by rw [h0]; exact hx.le⟩
  have hrT : r ∈ Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans hs.2⟩
  have him := im_eq_zero_of_isForwardSol_real hW hu hrT
  exact (hu.2 r hrT).1 (Complex.ext hr0 him)

/-- The drift integral of a real solution, real part. -/
theorem re_eq_of_isForwardSol {x t : ℝ} (ht : 0 ≤ t) {u : ℝ → ℂ} (hu : IsForwardSol W x t u) :
    (u t).re = x - W t + ∫ s in (0 : ℝ)..t, (2 / u s).re := by
  have hint : IntervalIntegrable (fun s => 2 / u s) MeasureTheory.volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht]
    exact continuousOn_const.div hu.1 fun s hs => (hu.2 s hs).1
  rw [(hu.2 t ⟨ht, le_rfl⟩).2, add_re, sub_re, ofReal_re, ofReal_re]
  congr 1
  exact (intervalIntegral.intervalIntegral_re hint).symm

/-- On the left of the driver the real flow is below the driven translation: `f_t(x) ≤ x − W_t`. -/
theorem re_le_of_isForwardSol_neg (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (ht : 0 ≤ t) (hx : x < 0)
    {u : ℝ → ℂ} (hu : IsForwardSol W x t u) : (u t).re ≤ x - W t := by
  have hneg := re_neg_of_isForwardSol hW hW0 hx hu
  have hle : ∫ s in (0 : ℝ)..t, (2 / u s).re ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) ht (f := fun s => -(2 / u s).re)
      fun s hs => by
      have h1 := hneg s hs
      have h2 : (2 / u s).re = 2 * (u s).re / Complex.normSq (u s) := by simp [Complex.div_re]
      rw [h2, neg_nonneg]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Complex.normSq_nonneg _)
    rw [intervalIntegral.integral_neg] at h
    linarith
  rw [re_eq_of_isForwardSol ht hu]
  linarith

/-- On the right of the driver the real flow is above the driven translation: `f_t(x) ≥ x − W_t`. -/
theorem le_re_of_isForwardSol_pos (hW : Continuous W) (hW0 : W 0 = 0) {x t : ℝ} (ht : 0 ≤ t) (hx : 0 < x)
    {u : ℝ → ℂ} (hu : IsForwardSol W x t u) : x - W t ≤ (u t).re := by
  have hpos := re_pos_of_isForwardSol hW hW0 hx hu
  have hle : 0 ≤ ∫ s in (0 : ℝ)..t, (2 / u s).re :=
    intervalIntegral.integral_nonneg ht fun s hs => by
      have h1 := hpos s hs
      have h2 : (2 / u s).re = 2 * (u s).re / Complex.normSq (u s) := by simp [Complex.div_re]
      rw [h2]
      exact div_nonneg (by linarith) (Complex.normSq_nonneg _)
  rw [re_eq_of_isForwardSol ht hu]
  linarith

/-- The real flow `x ↦ f_t(x)` is continuous (Grönwall) on any set of alive real points. -/
theorem continuousOn_re_fwdMap_real (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) {S : Set ℝ}
    (hS : ∀ x ∈ S, ∃ v, IsForwardSol W x t v) :
    ContinuousOn (fun x : ℝ => (QuantumZipper.fwdMap W t x).re) S := by
  intro x₀ hx₀
  obtain ⟨u, hu⟩ := hS x₀ hx₀
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hE
  have hEpos : 0 < E := Real.exp_pos _
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (δ / E) (ε / E) / 2, by positivity, fun x hx hxd => ?_⟩
  obtain ⟨v, hv⟩ := hS x hx
  have hxx : ‖((x : ℂ) - x₀)‖ = dist x x₀ := by rw [← ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have hd1 : dist x x₀ * E < δ := by
    have : dist x x₀ < δ / E := hxd.trans_le ((half_le_self (by positivity)).trans (min_le_left _ _))
    rwa [lt_div_iff₀ hEpos] at this
  have hd2 : dist x x₀ * E < ε := by
    have : dist x x₀ < ε / E := hxd.trans_le ((half_le_self (by positivity)).trans (min_le_right _ _))
    rwa [lt_div_iff₀ hEpos] at this
  have hb := norm_sub_le_of_isForwardSol hW hu hv hδ ht le_rfl hlow (by rw [hxx]; exact hd1) t ⟨ht, le_rfl⟩
  rw [fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu ⟨ht, le_rfl⟩,
    Real.dist_eq, ← sub_re]
  refine (abs_re_le_norm _).trans_lt ?_
  rw [hxx] at hb
  linarith

/-- **Every real `y ≤ f_t(x_a)` is the image of an alive real point `x' ≤ x_a`.** -/
theorem exists_eq_of_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {xa : ℝ} (hxa : xa < 0)
    (hK : ∀ x ≤ xa, (x : ℂ) ∉ closure (QuantumZipper.fwdHull W t)) {y : ℝ}
    (hy : y ≤ (QuantumZipper.fwdMap W t xa).re) :
    ∃ x' ≤ xa, (∃ v, IsForwardSol W x' t v) ∧ QuantumZipper.fwdMap W t x' = (y : ℂ) := by
  have halive : ∀ x ∈ Iic xa, ∃ v, IsForwardSol W x t v := fun x hx =>
    exists_isForwardSol_of_notMem_closure hW hW0 ht (by linarith [mem_Iic.1 hx]) (hK x hx)
  set x'' := min xa (y + W t) with hx''
  have hx''a : x'' ≤ xa := min_le_left _ _
  obtain ⟨v'', hv''⟩ := halive x'' hx''a
  have hF'' : (QuantumZipper.fwdMap W t x'').re ≤ y := by
    rw [fwdMap_eq_of_isForwardSol hW hv'' ⟨ht, le_rfl⟩]
    have := re_le_of_isForwardSol_neg hW hW0 ht (hx''a.trans_lt hxa) hv''
    linarith [min_le_right xa (y + W t)]
  have hc := (continuousOn_re_fwdMap_real hW ht halive).mono (Icc_subset_Iic_self (a := x''))
  obtain ⟨x', hx', hFx'⟩ := intermediate_value_Icc hx''a hc ⟨hF'', hy⟩
  obtain ⟨v, hv⟩ := halive x' hx'.2
  refine ⟨x', hx'.2, ⟨v, hv⟩, ?_⟩
  have him := im_eq_zero_of_isForwardSol_real hW hv ⟨ht, le_rfl⟩
  rw [← fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩] at him
  exact Complex.ext (by simpa using hFx') (by simpa using him)

/-- **Every real `y ≥ f_t(x_b)` is the image of an alive real point `x' ≥ x_b`.** -/
theorem exists_eq_of_ge (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {xb : ℝ} (hxb : 0 < xb)
    (hK : ∀ x ≥ xb, (x : ℂ) ∉ closure (QuantumZipper.fwdHull W t)) {y : ℝ}
    (hy : (QuantumZipper.fwdMap W t xb).re ≤ y) :
    ∃ x' ≥ xb, (∃ v, IsForwardSol W x' t v) ∧ QuantumZipper.fwdMap W t x' = (y : ℂ) := by
  have halive : ∀ x ∈ Ici xb, ∃ v, IsForwardSol W x t v := fun x hx =>
    exists_isForwardSol_of_notMem_closure hW hW0 ht (by linarith [mem_Ici.1 hx]) (hK x hx)
  set x'' := max xb (y + W t) with hx''
  have hx''b : xb ≤ x'' := le_max_left _ _
  obtain ⟨v'', hv''⟩ := halive x'' hx''b
  have hF'' : y ≤ (QuantumZipper.fwdMap W t x'').re := by
    rw [fwdMap_eq_of_isForwardSol hW hv'' ⟨ht, le_rfl⟩]
    have := le_re_of_isForwardSol_pos hW hW0 ht (hxb.trans_le hx''b) hv''
    linarith [le_max_right xb (y + W t)]
  have hc := (continuousOn_re_fwdMap_real hW ht halive).mono (show Icc xb x'' ⊆ Ici xb from Icc_subset_Ici_self)
  obtain ⟨x', hx', hFx'⟩ := intermediate_value_Icc hx''b hc ⟨hy, hF''⟩
  obtain ⟨v, hv⟩ := halive x' hx'.1
  refine ⟨x', hx'.1, ⟨v, hv⟩, ?_⟩
  have him := im_eq_zero_of_isForwardSol_real hW hv ⟨ht, le_rfl⟩
  rw [← fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩] at him
  exact Complex.ext (by simpa using hFx') (by simpa using him)

end Aux10

end InteractingSLE
