/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CovGlue
import InteractingSLE.Spec.Analysis.SchwarzHarmonic

/-!
# The odd cutoff of the relative mean `q` (from the harmonic Schwarz reflection principle)

Packet PROVE-AUX61-R2C. Astra's follow-up 4 L229–L231 ("The reflected cutoff construction of [S], Section 3.2, gives
one `f ∈ H¹₀(ℍ)` equal to `v` on a neighborhood of the closed buffer"), spec Aux. lemma 62's proof (p. 262). In the
corrected restart fibre (`Aux61R2.RefFibre`) the function to be cut off is `q = M − M^c`, the difference of the actual
and the reference means at the restart: harmonic on `ℍ`, with zero boundary values on a real window `O` (the seed
neighbourhood, by the canonical seed cancellation, and the comparison interval, where the two boundary heights
agree).

* `oddRefl q`: the odd reflection (`q` on `ℍ`, `−q ∘ conj` on the lower half-plane, `0` on `ℝ`);
  `reflDom O = ℂ ∖ (ℝ ∖ O)`;
* **`schwarzReflStatement`**: the odd reflection of a harmonic function on `ℍ` with zero boundary values on an open
  `O ⊆ ℝ` is harmonic on `reflDom O` (the harmonic Schwarz reflection principle, PROVE-SCHWARZ's
  `Analysis.SchwarzHarmonic.harmonicOnNhd_oddExtension_halfPlane`, through `oddRefl_eq_oddExtension` and
  `reflDom_eq_reflectionDomain`);
* **`exists_cmCut_of_harmonic`**: for every compact `K` whose real points lie in `O` there are an open `N ⊇ K` and a
  cutoff `F : CMCut` with `IsCutoffOn F q N O` and a bound `|q| ≤ C` on the support of `F`'s source — exactly the
  cutoff fields of `RefFibre` (`Fq`, `Nq`, `cut`, `Cq`, `q_bdd`). The construction is that of
  `Restart.FlowStopIdentCMI.exists_cmCut` (an even smooth bump `χ = 1` near `K ∪ conj K`, supported in `reflDom O`,
  times the odd reflection), with the Schwarz reflection in place of the explicit arg sums.

R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Laplacian

namespace InteractingSLE.Sec5.Aux61Cov

open QuantumZipper (H)
open Restart.FlowStopIdentCMI (CMCut exists_smooth_cutoff mem_thickening_conj)
open Aux61Win (IsCutoffOn)

/-- **The odd reflection** of a function on `ℍ`: `q` on `ℍ`, `−q ∘ conj` on the lower half-plane, `0` on `ℝ`. -/
def oddRefl (q : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then q z else if z.im < 0 then -q (conj z) else 0

/-- **The reflected domain** `ℂ ∖ (ℝ ∖ O)`. -/
def reflDom (O : Set ℝ) : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re ∉ O}ᶜ

theorem oddRefl_of_pos {q : ℂ → ℝ} {z : ℂ} (hz : 0 < z.im) : oddRefl q z = q z := by
  simp only [oddRefl, hz, ↓reduceIte]

theorem oddRefl_conj (q : ℂ → ℝ) (z : ℂ) : oddRefl q (conj z) = -oddRefl q z := by
  simp only [oddRefl, Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy z.im 0 with h | h | h
  · have h1 : 0 < -z.im := by linarith
    have h2 : ¬ 0 < z.im := by linarith
    simp only [h1, h2, h, ↓reduceIte, neg_neg]
  · simp only [h, neg_zero, lt_irrefl, ↓reduceIte]
  · have h1 : ¬ 0 < -z.im := by linarith
    have h2 : -z.im < 0 := by linarith
    simp only [h1, h2, h, ↓reduceIte]

theorem isOpen_reflDom {O : Set ℝ} (hO : IsOpen O) : IsOpen (reflDom O) :=
  ((isClosed_eq Complex.continuous_im continuous_const).inter
    (hO.isClosed_compl.preimage Complex.continuous_re)).isOpen_compl

theorem H_subset_reflDom (O : Set ℝ) : H ⊆ reflDom O := fun _ hz h => (ne_of_gt hz) h.1

/-- **The harmonic Schwarz reflection principle** (in this file's notation): a harmonic function on `ℍ` with zero
boundary values at the points of an open `O ⊆ ℝ` has a harmonic odd reflection on `ℂ ∖ (ℝ ∖ O)`. -/
def SchwarzReflStatement : Prop :=
  ∀ (q : ℂ → ℝ) (O : Set ℝ), IsOpen O → InnerProductSpace.HarmonicOnNhd q H →
    (∀ x ∈ O, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0)) → InnerProductSpace.HarmonicOnNhd (oddRefl q) (reflDom O)

theorem oddRefl_eq_oddExtension (q : ℂ → ℝ) : oddRefl q = Analysis.SchwarzHarmonic.oddExtension q := by
  funext z
  rcases lt_trichotomy z.im 0 with h | h | h
  · have h1 : ¬ 0 < z.im := by linarith
    rw [Analysis.SchwarzHarmonic.oddExtension_of_neg h]
    simp only [oddRefl, h1, h, ↓reduceIte]
  · rw [Analysis.SchwarzHarmonic.oddExtension_of_im_eq_zero h]
    simp only [oddRefl, h, lt_irrefl, ↓reduceIte]
  · rw [Analysis.SchwarzHarmonic.oddExtension_of_pos h, oddRefl_of_pos h]

theorem reflDom_eq_reflectionDomain (O : Set ℝ) : reflDom O = Analysis.SchwarzHarmonic.reflectionDomain O := by
  ext z
  simp only [reflDom, Analysis.SchwarzHarmonic.reflectionDomain, mem_compl_iff, mem_ofPred_eq, not_and_or, not_not]

/-- **The harmonic Schwarz reflection principle holds** (PROVE-SCHWARZ). -/
theorem schwarzReflStatement : SchwarzReflStatement := by
  intro q O hO hq hq0
  rw [oddRefl_eq_oddExtension, reflDom_eq_reflectionDomain]
  exact Analysis.SchwarzHarmonic.harmonicOnNhd_oddExtension_halfPlane hO hq hq0

/-- **The cutoff of a harmonic function with zero boundary values on `O`** (through the Schwarz reflection): for a
compact `K` whose real points lie in `O`, an open `N ⊇ K`, a cutoff `F` with `IsCutoffOn F q N O`, and a bound on `q`
where `F`'s source does not vanish. -/
theorem exists_cmCut_of_harmonic {q : ℂ → ℝ} {O : Set ℝ} (hO : IsOpen O)
    (hq : InnerProductSpace.HarmonicOnNhd q H) (hq0 : ∀ x ∈ O, Tendsto q (𝓝[H] (x : ℂ)) (𝓝 0))
    {K : Set ℂ} (hK : IsCompact K) (hKO : ∀ z ∈ K, z.im = 0 → z.re ∈ O) :
    ∃ (N : Set ℂ) (F : CMCut) (C : ℝ), K ⊆ N ∧ IsCutoffOn F q N O ∧ ∀ z, F.src z ≠ 0 → |q z| ≤ C := by
  classical
  have hR := schwarzReflStatement q O hO hq hq0
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
  set U' : Set ℂ := reflDom O with hU'def
  have hU'o : IsOpen U' := isOpen_reflDom hO
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
  have hNU : N ⊆ U' := fun z hz => hδU' (thickening_subset_cthickening_of_le (half_le_self hδ.le) K' hz)
  have hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O := by
    intro z hz hz0
    by_contra h
    exact hNU hz ⟨hz0, h⟩
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
  -- the support of the even cutoff lies in the reflected domain
  have hconjU : ∀ z, z ∈ U' → conj z ∈ U' := fun z hz h => hz ⟨by
    have := h.1; rwa [Complex.conj_im, neg_eq_zero] at this, by simpa using h.2⟩
  have hχe0 : ∀ z, z ∉ U' → χe =ᶠ[𝓝 z] 0 := by
    intro z hz
    have hzU : z ∉ tsupport χ := fun h => hz (hχU h)
    have h1 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hzU
    have hzU' : conj z ∉ tsupport χ := fun h => hz (by
      have := hconjU _ (hχU h); rwa [Complex.conj_conj] at this)
    have h1' : χ =ᶠ[𝓝 (conj z)] 0 := notMem_tsupport_iff_eventuallyEq.1 hzU'
    have h2 : (fun w => χ (conj w)) =ᶠ[𝓝 z] 0 :=
      (Complex.continuous_conj.tendsto z).eventually h1'
    filter_upwards [h1, h2] with w hw1 hw2
    simp only [hχe, Pi.zero_apply] at hw1 hw2 ⊢
    rw [hw1, hw2]; norm_num
  have hsuppU : tsupport χe ⊆ U' := fun z hz => by
    by_contra hzU
    exact (notMem_tsupport_iff_eventuallyEq.2 (hχe0 z hzU)) hz
  -- the cutoff field
  set f : ℂ → ℝ := fun z => χe z * oddRefl q z with hf
  have hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ U'
    · have ha : AnalyticAt ℝ (oddRefl q) z := _root_.HarmonicAt.analyticAt (hR z hz)
      exact hχes.contDiffAt.mul ha.contDiffAt
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hχe0 z hz] with u hu
      simp only [hf, hu, Pi.zero_apply, zero_mul]
  set F : CMCut :=
    { f := f
      smooth := hfs
      compact := hχec.mul_right
      odd := fun z => by simp only [hf, hχe_conj, oddRefl_conj, mul_neg] } with hF
  -- the bound on `q` on the support of the cutoff
  have hcont : ContinuousOn (oddRefl q) U' := fun z hz => (hR z hz).1.continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hχec.isCompact.exists_bound_of_continuousOn (hcont.mono hsuppU)
  refine ⟨N, F, C, hKN, ⟨hNo, hNO, fun z hz hzH => ?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · show χe z * oddRefl q z = q z
    rw [hχeN z hz, one_mul, oddRefl_of_pos hzH]
  · have heq : F.f =ᶠ[𝓝 z] oddRefl q := by
      filter_upwards [hNo.mem_nhds hz] with w hw
      show χe w * oddRefl q w = _
      rw [hχeN w hw, one_mul]
    rw [QuantumZipper.K3.greenDensity, (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,
      (hR z (hNU hz)).2.eq_of_nhds, Pi.zero_apply, mul_zero]
  · obtain ⟨hzH, hzs⟩ := F.mem_of_src_ne_zero hz
    have hzχ : z ∈ tsupport χe := by
      by_contra hzχ
      have h0 : F.f =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzχ] with w hw
        show χe w * oddRefl q w = 0
        rw [hw, Pi.zero_apply, zero_mul]
      have hgd : QuantumZipper.K3.greenDensity F.f =ᶠ[𝓝 z] 0 := by
        filter_upwards [InnerProductSpace.laplacian_congr_nhds h0] with w hw
        rw [QuantumZipper.K3.greenDensity, hw, InnerProductSpace.laplacian_const]
        simp
      exact (notMem_tsupport_iff_eventuallyEq.2 hgd) hzs
    have h := hC z hzχ
    rwa [Real.norm_eq_abs, oddRefl_of_pos hzH] at h

end InteractingSLE.Sec5.Aux61Cov
