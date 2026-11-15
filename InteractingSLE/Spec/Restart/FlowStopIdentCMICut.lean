/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMISrc
import InteractingSLE.Spec.Restart.FlowStopIdentCMIWord
import InteractingSLE.Spec.Supplement.Aux61Cutoff
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Sec2.MartingaleCoupling
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The explicit Cameron–Martin cutoff of the difference of two piecewise constant data

Packet PROVE-L1-CMI (Lemma G3's proof, supplement §7.3, pp. 492–493: "`f = v` on `U` and on a neighbourhood of its
closure"; Aux. lemma 62's proof, p. 262: "The reflected boundary cutoff construction at 3.2 provides `f ∈ H¹₀(ℍ)`").
For data `b`, `bR` agreeing on an open `O ⊆ ℝ`:

* **`eq_offSum`**: the bounded harmonic extension `q` of `bR − b` is, on `ℍ`, the arg sum
  `q(w) = ∑_{p ∈ M} (Δ p [y < p] − (Δ p / π) arg (w − p))` over the jump candidates `M` off `O`, for every `y ∈ O`
  (the difference of the explicit means of the two flow-line words from `y` at time `0`,
  `FlowStopIdentCMI.meanHarmonic_flowLine_sub`); in particular the constant does not depend on `y ∈ O`
  (`offConst_eq`);
* `argP`, `argC`, `argC₀`: these arg-sum data (`GB7a.argSum0` form), `argSum0_eq`;
* **`exists_cmCut`**: for a compact `K` whose real points lie in `O`, an open buffer `N ⊇ K` whose real points lie in
  `O` and a cutoff field `F : CMCut` (smooth, compactly supported, odd) with `F.f = q` on `N ∩ ℍ` and
  `Δ F.f = 0` on `N`: `F.f = χ · oddExt q` with `χ` smooth, even in `Im`, `1` on `N` and vanishing near the real
  points off `O`; `oddExt q` is analytic across `O` (`GB7a.oddExt_eventuallyEq_core`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian Manifold

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentCMI

open QuantumZipper (H Hbar)
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The flow-line marks lie on the correct sides of the seed -/

theorem flowLineXL_nonpos' (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ) (i : Fin (flowLineNL b J y)) :
    flowLineXL b J y i ≤ 0 := by
  revert i
  unfold flowLineXL flowLineNL
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ]
    have hmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (· < y)) rfl (Fin.rev j)
    have := (Finset.mem_filter.1 hmem).2
    linarith

theorem flowLineXR_nonneg' (b : ℝ → ℝ) (J : Finset ℝ) (y : ℝ) (i : Fin (flowLineNR b J y)) :
    0 ≤ flowLineXR b J y i := by
  revert i
  unfold flowLineXR flowLineNR
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ]
    have hmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (y < ·)) rfl j
    have := (Finset.mem_filter.1 hmem).2
    linarith

/-! ### The arg-sum representation of the harmonic extension of `bR − b` -/

section Rep

variable {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ}

/-- The difference of two bounded harmonic extensions is a bounded harmonic extension of the difference. -/
theorem isBoundedHarmonicExtension_sub {u v : ℂ → ℝ} {S S' : Set ℝ} (hu : IsBoundedHarmonicExtension bR S u)
    (hv : IsBoundedHarmonicExtension b S' v) : IsBoundedHarmonicExtension (fun x => bR x - b x) (S ∪ S')
      (fun z => u z - v z) := by
  obtain ⟨Cu, hCu⟩ := hu.2.1
  obtain ⟨Cv, hCv⟩ := hv.2.1
  refine ⟨hu.1.sub hv.1, ⟨Cu + Cv, fun z hz => (abs_sub _ _).trans (add_le_add (hCu z hz) (hCv z hz))⟩,
    fun x hx => ?_⟩
  exact (hu.2.2 x fun h => hx (Or.inl h)).sub (hv.2.2 x fun h => hx (Or.inr h))

theorem isBoundedHarmonicExtension_mono' {g : ℝ → ℝ} {S S' : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hSS' : S ⊆ S') : IsBoundedHarmonicExtension g S' u :=
  ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x fun h => hx (hSS' h)⟩

/-- **The bounded harmonic extension of `bR − b` is an arg sum over the marks off `O`**, with the constant read at
any seed `y ∈ O`. -/
theorem eq_offSum (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) [DecidablePred (· ∈ O)] {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {y : ℝ} (hy : y ∈ O)
    {w : ℂ} (hw : w ∈ H) :
    q w = ∑ p ∈ offMarks J Ĵ O, ((jmp bR p - jmp b p) * (if y < p then 1 else 0) -
      (jmp bR p - jmp b p) / Real.pi * Complex.arg (w - (p : ℂ))) := by
  classical
  have hκ : (0 : ℝ) < 1 := one_pos
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨uR, huR, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbR
  -- `q = uR − u` on `ℍ`
  have hsub := isBoundedHarmonicExtension_sub huR hu
  have hq' : IsBoundedHarmonicExtension (fun x => bR x - b x) ((Ĵ : Set ℝ) ∪ (J : Set ℝ)) q :=
    isBoundedHarmonicExtension_mono' hq (by simp only [Finset.coe_union]; exact (union_comm _ _).subset)
  have hqe := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
    ((Ĵ.finite_toSet).union J.finite_toSet) hsub hq' hw
  -- the explicit means of the two flow-line words at time `0`
  set z : ℂ := w - y with hz
  have hzH : z ∈ H := by
    have := Exist.add_real_mem_H hw (-y)
    simpa [hz, sub_eq_add_neg] using this
  have hmean : ∀ (c : ℝ → ℝ) (K : Finset ℝ) (uc : ℂ → ℝ), IsPiecewiseConstantBoundaryData c K →
      IsBoundedHarmonicExtension c K uc →
      uc (z + y) + 0 * QuantumZipper.chiC 1 = Ito.meanHarmonic 1 (flowLineRhoL 1 c K y 0)
        (flowLineRhoR 1 c K y 0) (fun i => flowLineXL c K y i) (fun j => flowLineXR c K y j) z := by
    intro c K uc hc huc
    have hm := MartChar.isBoundedHarmonicExtension_meanExt 1 (flowLineRhoL 1 c K y 0) (flowLineRhoR 1 c K y 0) 0
      (flowLineXL c K y) (flowLineXR c K y)
    simp only [sub_zero] at hm
    have e1 := Exist.eqOn_flowLine_harmonicExtension hκ hc y 0 huc hm hzH
    have e2 := Ito.eqOn_meanHarmonic (flowLineXL_nonpos' c K y) (flowLineXR_nonneg' c K y) hm hzH
    exact e1.symm.trans e2
  have hb' := hmean b J u hb hu
  have hbR' := hmean bR Ĵ uR hbR huR
  have hdiff := meanHarmonic_flowLine_sub hκ hb hbR hO hbO hy 0 id id z
  simp only [id, ite_self] at hdiff
  have hzy : z + y = w := by rw [hz]; ring
  rw [hzy] at hb' hbR'
  rw [hqe]
  simp only [zero_mul, add_zero] at hb' hbR'
  show uR w - u w = _
  rw [hb', hbR', hdiff]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 3
  rw [hz]
  push_cast
  ring

/-- **The constant of the arg sum does not depend on the seed in `O`.** -/
theorem offConst_eq (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) [DecidablePred (· ∈ O)] {x y : ℝ} (hx : x ∈ O) (hy : y ∈ O) :
    ∑ p ∈ offMarks J Ĵ O, (jmp bR p - jmp b p) * (if x < p then 1 else 0) =
      ∑ p ∈ offMarks J Ĵ O, (jmp bR p - jmp b p) * (if y < p then 1 else 0) := by
  obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨uR, huR, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbR
  have hq := isBoundedHarmonicExtension_mono' (isBoundedHarmonicExtension_sub huR hu)
    (show (Ĵ : Set ℝ) ∪ (J : Set ℝ) ⊆ ((J ∪ Ĵ : Finset ℝ) : Set ℝ) by
      simp only [Finset.coe_union]; exact (union_comm _ _).subset)
  have hI : Complex.I ∈ H := show (0 : ℝ) < Complex.I.im by simp
  have h1 := eq_offSum hb hbR hO hbO hq hx hI
  have h2 := eq_offSum hb hbR hO hbO hq hy hI
  rw [h1, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h2
  linarith

end Rep

/-! ### The arg-sum data and the odd extension -/

section ArgData

variable (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ) (O : Set ℝ) [DecidablePred (· ∈ O)]

/-- The positions of the marks off `O`. -/
def argP : ↥(offMarks J Ĵ O) → ℝ := fun j => (j : ℝ)

/-- The coefficients `−Δ p / π` of the marks off `O`. -/
def argC : ↥(offMarks J Ĵ O) → ℝ := fun j => -(jmp bR j - jmp b j) / Real.pi

/-- The constant `∑_{p ∈ M, y < p} Δ p` read at the seed `y`. -/
def argC₀ (y : ℝ) : ℝ := ∑ p ∈ offMarks J Ĵ O, (jmp bR p - jmp b p) * (if y < p then 1 else 0)

end ArgData

section Odd

variable {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ} [DecidablePred (· ∈ O)]

/-- The arg sum of the data is the harmonic extension of `bR − b` on `ℍ`. -/
theorem argSum0_eq (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {y : ℝ} (hy : y ∈ O)
    {w : ℂ} (hw : w ∈ H) :
    GB7a.argSum0 (argP J Ĵ O) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) w = q w := by
  rw [eq_offSum hb hbR hO hbO hq hy hw, GB7a.argSum0, argC₀, Finset.sum_sub_distrib, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  rw [← Finset.sum_coe_sort (offMarks J Ĵ O)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [argC, argP]
  ring

/-- **The odd extension is analytic across the real points of `O`**: near such a point it is the imaginary part of
an analytic function (the boundary value of the arg sum vanishes on `O`). -/
theorem oddExt_local_hol (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {y : ℝ} (hy : y ∈ O) {z : ℂ} (hz : z.im = 0 → z.re ∈ O) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      GB7a.oddExt (argP J Ĵ O) (argC b bR J Ĵ O) (argC₀ b bR J Ĵ O y) =ᶠ[𝓝 z] fun u => (g u).im := by
  classical
  by_cases him : z.im ≠ 0
  · exact GB7a.oddExt_eventuallyEq_off him
  · push Not at him
    have hzO := hz him
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO z.re hzO
    set l := z.re - ε / 2 with hl
    set r := z.re + ε / 2 with hr
    have hmarks : ∀ j : ↥(offMarks J Ĵ O), argP J Ĵ O j ≤ l ∨ r ≤ argP J Ĵ O j := by
      intro j
      by_contra hcon
      push Not at hcon
      have hjO : (j : ℝ) ∉ O := (Finset.mem_filter.1 j.2).2
      apply hjO
      apply hball
      rw [Real.ball_eq_Ioo]
      exact ⟨by simp only [argP] at hcon; linarith [hcon.1], by simp only [argP] at hcon; linarith [hcon.2]⟩
    have hdata : argC₀ b bR J Ĵ O y + Real.pi *
        ∑ j ∈ Finset.univ.filter (fun j => r ≤ argP J Ĵ O j), argC b bR J Ĵ O j = 0 := by
      have hfilt : ∀ j : ↥(offMarks J Ĵ O), r ≤ argP J Ĵ O j ↔ z.re < (j : ℝ) := fun j => by
        simp only [argP]
        constructor
        · intro h; linarith
        · intro h
          rcases hmarks j with h' | h'
          · simp only [argP] at h'; linarith
          · simpa [argP] using h'
      have e1 : ∑ j ∈ Finset.univ.filter (fun j => r ≤ argP J Ĵ O j), argC b bR J Ĵ O j =
          -(1 / Real.pi) * argC₀ b bR J Ĵ O z.re := by
        rw [Finset.sum_filter, argC₀, Finset.mul_sum, ← Finset.sum_coe_sort (offMarks J Ĵ O)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hfilt j, argC]
        split_ifs <;> ring
      have e2 : argC₀ b bR J Ĵ O z.re = argC₀ b bR J Ĵ O y := offConst_eq hb hbR hO hbO hzO hy
      rw [e1, e2]
      field_simp
      ring
    have hl' : l < z.re := by rw [hl]; linarith
    have hr' : z.re < r := by rw [hr]; linarith
    obtain ⟨ha, he⟩ := GB7a.oddExt_eventuallyEq_core hmarks hdata hl' hr'
    exact ⟨_, ha, he⟩

end Odd

/-! ### The cutoff -/

section Cutoff

/-- A smooth compactly supported cutoff (`Foundations.Brownian.Harmonic`'s `exists_cutoff` with `C^∞` in place of
`C³`). -/
theorem exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ)
    (n := (⊤ : ℕ∞)) hK.isClosed hKL
  have hfc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f : ℂ → ℝ) := contMDiff_iff_contDiff.1 f.contMDiff
  have hsupp : tsupport (f : ℂ → ℝ) ⊆ L := by
    refine closure_minimal (fun x hx => ?_) hL.isClosed
    by_contra hxL
    exact hx (hf0 x hxL)
  exact ⟨f, hfc, HasCompactSupport.intro hL (fun x hx => hf0 x hx), hsupp.trans hLU, hf1⟩

theorem mem_thickening_conj {K : Set ℂ} (hK : ∀ z ∈ K, conj z ∈ K) {r : ℝ} {z : ℂ} (hz : z ∈ thickening r K) :
    conj z ∈ thickening r K := by
  obtain ⟨w, hw, hd⟩ := Metric.mem_thickening_iff.1 hz
  refine Metric.mem_thickening_iff.2 ⟨conj w, hK w hw, ?_⟩
  rw [Complex.dist_conj_conj]
  exact hd

variable {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {O : Set ℝ} [DecidablePred (· ∈ O)]

/-- **The explicit Cameron–Martin cutoff.** For a compact `K` whose real points lie in `O`, an open buffer `N ⊇ K`
whose real points lie in `O`, and a cutoff field `F` (smooth, compactly supported, odd) with `F.f = q` on `N ∩ ℍ` and
`Δ F.f = 0` on `N`. -/
theorem exists_cmCut (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ)
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q) {y₀ : ℝ} (hy₀ : y₀ ∈ O)
    {K : Set ℂ} (hK : IsCompact K) (hKO : ∀ z ∈ K, z.im = 0 → z.re ∈ O) :
    ∃ (N : Set ℂ) (F : CMCut), IsOpen N ∧ K ⊆ N ∧ (∀ z ∈ N, z.im = 0 → z.re ∈ O) ∧
      (∀ z ∈ N, z ∈ H → F.f z = q z) ∧ (∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) := by
  classical
  set K' : Set ℂ := K ∪ (fun z => conj z) '' K with hK'
  have hK'c : IsCompact K' := hK.union (hK.image Complex.continuous_conj)
  have hK'conj : ∀ z ∈ K', conj z ∈ K' := by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact Or.inr ⟨z, hz, rfl⟩
    · rw [Complex.conj_conj]; exact Or.inl hw
  have hK'O : ∀ z ∈ K', z.im = 0 → z.re ∈ O := by
    rintro z (hz | ⟨w, hw, rfl⟩) h0
    · exact hKO z hz h0
    · rw [Complex.conj_re]
      rw [Complex.conj_im, neg_eq_zero] at h0
      exact hKO w hw h0
  set U' : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re ∉ O}ᶜ with hU'def
  have hU'o : IsOpen U' :=
    ((isClosed_eq Complex.continuous_im continuous_const).inter
      (hO.isClosed_compl.preimage Complex.continuous_re)).isOpen_compl
  have hK'U' : K' ⊆ U' := fun z hz hz' => hz'.2 (hK'O z hz hz'.1)
  obtain ⟨δ, hδ, hδU'⟩ := hK'c.exists_cthickening_subset_open hU'o hK'U'
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨χ, hχs, hχc, hχU, hχ1⟩ := exists_smooth_cutoff (hK'c.cthickening (r := δ / 2)) hU'o
    ((cthickening_mono (half_le_self hδ.le) K').trans hδU')
  have hχ1' : ∀ z ∈ cthickening (δ / 2) K', χ z = 1 := fun z hz =>
    (eventually_nhdsSet_iff_forall.1 hχ1 z hz).self_of_nhds
  set N : Set ℂ := thickening (δ / 2) K' with hNdef
  have hNo : IsOpen N := isOpen_thickening
  have hKN : K ⊆ N := fun z hz => self_subset_thickening hδ2 K' (Or.inl hz)
  have hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O := by
    intro z hz hz0
    by_contra h
    exact hδU' (thickening_subset_cthickening_of_le (half_le_self hδ.le) K' hz) ⟨hz0, h⟩
  -- the even cutoff
  set χe : ℂ → ℝ := fun z => (χ z + χ (conj z)) / 2 with hχe
  have hconj_s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : ℂ => conj z :=
    Complex.conjCLE.toContinuousLinearMap.contDiff
  have hχes : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χe := (hχs.add (hχs.comp hconj_s)).div_const 2
  have hχec : HasCompactSupport χe := by
    have h2 : HasCompactSupport fun z => χ (conj z) :=
      hχc.comp_homeomorph Complex.conjLIE.toHomeomorph
    have h3 : HasCompactSupport fun z => χ z + χ (conj z) := hχc.add h2
    have e : χe = fun z => (1 / 2 : ℝ) * (χ z + χ (conj z)) := funext fun z => by simp only [hχe]; ring
    rw [e]
    exact h3.mul_left
  have hχe_conj : ∀ z, χe (conj z) = χe z := fun z => by
    simp only [hχe, Complex.conj_conj]; ring
  have hχeN : ∀ z ∈ N, χe z = 1 := fun z hz => by
    have h1 := hχ1' z (thickening_subset_cthickening _ _ hz)
    have h2 := hχ1' (conj z) (thickening_subset_cthickening _ _ (mem_thickening_conj hK'conj hz))
    simp only [hχe, h1, h2]; norm_num
  have hχe0 : ∀ x : ℝ, x ∉ O → χe =ᶠ[𝓝 (x : ℂ)] 0 := by
    intro x hx
    have hxU : (x : ℂ) ∉ tsupport χ := fun h => hχU h ⟨by simp, by simpa using hx⟩
    have h1 : χ =ᶠ[𝓝 (x : ℂ)] 0 := notMem_tsupport_iff_eventuallyEq.1 hxU
    have h2 : (fun z => χ (conj z)) =ᶠ[𝓝 (x : ℂ)] 0 := by
      have hc : Tendsto (fun z : ℂ => conj z) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
        have := Complex.continuous_conj.tendsto (x : ℂ)
        rwa [Complex.conj_ofReal] at this
      exact hc.eventually h1
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hχe, Pi.zero_apply] at hz1 hz2 ⊢
    rw [hz1, hz2]; norm_num
  -- the cutoff field
  set p := argP J Ĵ O
  set c := argC b bR J Ĵ O
  set c₀ := argC₀ b bR J Ĵ O y₀
  set f : ℂ → ℝ := fun z => χe z * GB7a.oddExt p c c₀ z with hf
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z.im = 0 → z.re ∈ O
    · obtain ⟨g, hg, he⟩ := oddExt_local_hol hb hbR hO hbO hy₀ hz
      have hgd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (g u).im) z :=
        Complex.imCLM.contDiff.contDiffAt.comp z (hg.contDiffAt.restrict_scalars ℝ)
      exact (hχes.contDiffAt.mul hgd).congr_of_eventuallyEq (he.mono fun u hu => by
        show χe u * GB7a.oddExt p c c₀ u = χe u * (g u).im
        rw [hu])
    · push Not at hz
      obtain ⟨hz0, hzO⟩ := hz
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
      have hev := hχe0 z.re hzO
      rw [← hzr] at hev
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with u hu
      simp only [hf, hu, Pi.zero_apply, zero_mul]
  set F : CMCut :=
    { f := f
      smooth := hfs
      compact := hχec.mul_right
      odd := fun z => by simp only [hf, hχe_conj, GB7a.oddExt_conj, mul_neg] } with hF
  refine ⟨N, F, hNo, hKN, hNO, fun z hz hzH => ?_, fun z hz => ?_⟩
  · show χe z * GB7a.oddExt p c c₀ z = q z
    rw [hχeN z hz, one_mul, GB7a.oddExt_of_pos hzH]
    exact argSum0_eq hb hbR hO hbO hq hy₀ hzH
  · have heq : F.f =ᶠ[𝓝 z] GB7a.oddExt p c c₀ := by
      filter_upwards [hNo.mem_nhds hz] with w hw
      show χe w * GB7a.oddExt p c c₀ w = _
      rw [hχeN w hw, one_mul]
    obtain ⟨g, hg, he⟩ := oddExt_local_hol hb hbR hO hbO hy₀ (hNO z hz)
    have hH := hg.harmonicAt_im
    rw [QuantumZipper.K3.greenDensity,
      (InnerProductSpace.laplacian_congr_nhds (heq.trans he)).eq_of_nhds, hH.2.eq_of_nhds, Pi.zero_apply,
      mul_zero]

end Cutoff

end FlowStopIdentCMI

end Restart

end InteractingSLE
