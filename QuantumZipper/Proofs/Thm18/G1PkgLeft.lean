import QuantumZipper.Proofs.Thm18.G1PkgLeftBV

/-!
# G1 package: existence of left-normalized uniformizers (`LeftUnifExistStmt`)

For a simple chord `η` and a normalized uniformizer `φ₀` of the left component (U4,
`CA.Uniformizer.exists_normalizedUniformizer_leftComponent`), the real boundary values `b` on
`(−∞,0)` (`exists_boundary_values_normalized`) are negative: at each `x < 0` the Schwarz
reflection `G` of `φ₀` across a small segment around `x` (Ahlfors, *Complex Analysis*, 3rd ed.,
Ch. 4 §6.5 Thm 24, `CA.exists_reflection_extension`) has a real derivative `c` with
`Re c ≥ 0` (difference quotients along `iℝ₊` have nonnegative real part since `φ₀(D) ⊆ ℍ`), so
`b' ≥ 0` and `b` is nondecreasing on `(−∞,0)`; since `b(x) → 0` as `x → 0⁻` and `b ≠ 0`, `b < 0`.
Then `φ = (−1/b(−1)) φ₀` is left-normalized (`φ(−1) = −1`).

This is the orientation step behind the route of `CA.Kernel.leftReflection` (KernelChordR.lean),
where `b(−1) = −1` was assumed; the derivative computation is copied from there (`Φ'(−1) > 0`),
applied at every `x < 0`. Own elementary argument apart from the cited reflection principle.
-/

noncomputable section

open Set Metric Filter Topology Complex Function Bornology
open QuantumZipper.CA QuantumZipper.CA.Uniformizer QuantumZipper.CA.Kernel
open scoped ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

variable {η : ℝ → ℂ}

theorem boundary_neg_of_normalized (hη : IsSimpleChord η) {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (leftComponent η) φ) {b : ℝ → ℝ}
    (hb : ∀ x : ℝ, x < 0 → Tendsto φ (𝓝[leftComponent η] (x : ℂ)) (𝓝 (b x : ℂ)))
    (hb0 : ∀ x : ℝ, x < 0 → b x ≠ 0) : ∀ x : ℝ, x < 0 → b x < 0 := by
  obtain ⟨hbij, hd, h0, hinf⟩ := hφ
  set D := leftComponent η with hDdef
  have hDo : IsOpen D := isOpen_leftComponent hη
  set N : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re < 0} with hNdef
  set B : Set ℂ := D ∪ N ∪ {0} with hBdef
  have hre : ∀ z : ℂ, z.im = 0 → z = (z.re : ℂ) := fun z h => Complex.ext (by simp) (by simp [h])
  have hBcl : B ⊆ closure D := by
    rintro z ((hz | ⟨h0z, hneg⟩) | hz)
    · exact subset_closure hz
    · rw [hre z h0z]; exact ofReal_mem_closure_leftComponent hη hneg
    · rw [mem_singleton_iff.1 hz]; exact zero_mem_closure_leftComponent hη
  have hlim : ∀ z ∈ B, ∃ y, Tendsto φ (𝓝[D] z) (𝓝 y) := by
    rintro z ((hz | ⟨h0z, hneg⟩) | hz)
    · exact ⟨φ z, (hd.continuousOn.continuousAt (hDo.mem_nhds hz)).tendsto.mono_left
        nhdsWithin_le_nhds⟩
    · rw [hre z h0z]; exact ⟨_, hb z.re hneg⟩
    · rw [mem_singleton_iff.1 hz]; exact ⟨0, h0⟩
  set φt := extendFrom D φ with hφtdef
  have hcont : ContinuousOn φt B := continuousOn_extendFrom hBcl hlim
  have hφtD : ∀ z ∈ D, φt z = φ z := extendFrom_extends hd.continuousOn
  have hφtN : ∀ x : ℝ, x < 0 → φt x = (b x : ℂ) := fun x hx =>
    extendFrom_eq (ofReal_mem_closure_leftComponent hη hx) (hb x hx)
  have hφt0 : φt 0 = 0 := extendFrom_eq (zero_mem_closure_leftComponent hη) h0
  -- small values near `0⁻`
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ a : ℝ, -δ < a → a < 0 → |b a| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hH⟩ := Metric.continuousWithinAt_iff.1 (hcont 0 (Or.inr rfl)) ε hε
    refine ⟨δ, hδ, fun a ha1 ha2 => ?_⟩
    have hmem : ((a : ℝ) : ℂ) ∈ B := Or.inl (Or.inr ⟨by simp, by simpa using ha2⟩)
    have hdist : dist ((a : ℝ) : ℂ) 0 < δ := by
      rw [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_neg ha2]; linarith
    have := hH hmem hdist
    rwa [hφt0, dist_zero_right, hφtN _ ha2, norm_real, Real.norm_eq_abs] at this
  -- `b` has a nonnegative derivative on `(−∞,0)`
  have hderiv : ∀ x : ℝ, x < 0 → ∃ c : ℝ, 0 ≤ c ∧ HasDerivAt b c x := by
    intro x hx
    obtain ⟨δ, hδ, hnear⟩ := mem_leftComponent_of_near_neg hη hx
    set r := min δ (-x) with hrdef
    have hr : 0 < r := lt_min hδ (by linarith)
    have hsub : H ∩ ball (x : ℂ) r ⊆ D := fun w hw =>
      hnear w hw.1 (lt_of_lt_of_le hw.2 (min_le_left _ _))
    have hHb : Hbar ∩ ball (x : ℂ) r ⊆ B := by
      rintro w ⟨hw0, hw⟩
      rcases (show (0 : ℝ) ≤ w.im from hw0).eq_or_lt with h0w | h0w
      · refine Or.inl (Or.inr ⟨h0w.symm, ?_⟩)
        have h1 := abs_re_le_norm (w - x)
        rw [mem_ball, dist_eq_norm] at hw
        simp only [sub_re, ofReal_re] at h1
        have := (abs_lt.1 (lt_of_le_of_lt h1 (lt_of_lt_of_le hw (min_le_right _ _)))).2
        linarith
      · exact Or.inl (Or.inl (hsub ⟨h0w, hw⟩))
    have hdiff : DifferentiableOn ℂ φt (H ∩ ball (x : ℂ) r) :=
      (hd.mono hsub).congr fun w hw => hφtD w (hsub hw)
    have hreal : ∀ w ∈ ball (x : ℂ) r, w.im = 0 → (φt w).im = 0 := fun w hw h0w => by
      have hwB := hHb ⟨show (0 : ℝ) ≤ w.im by rw [h0w], hw⟩
      rcases hwB with (hwD | ⟨-, hwneg⟩) | hw0
      · have : 0 < w.im := leftComponent_subset_H η hwD
        linarith
      · rw [hre w h0w, hφtN _ hwneg]; simp
      · rw [mem_singleton_iff.1 hw0, hφt0]; simp
    obtain ⟨G, hGd, hGeq, -⟩ := CA.exists_reflection_extension hdiff (hcont.mono hHb) hreal
    have hGx : HasDerivAt G (deriv G (x : ℂ)) (x : ℂ) :=
      (hGd.differentiableAt (ball_mem_nhds _ hr)).hasDerivAt
    set c := deriv G (x : ℂ) with hcdef
    have hGr : ∀ t : ℝ, |t - x| < r → G t = (b t : ℂ) := fun t ht => by
      have ht0 : t < 0 := by
        have := (abs_lt.1 ht).2
        have : r ≤ -x := min_le_right _ _
        linarith
      have hmem : (t : ℂ) ∈ Hbar ∩ ball (x : ℂ) r := ⟨show (0 : ℝ) ≤ (t : ℂ).im by simp, by
        rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]; exact ht⟩
      rw [hGeq hmem, hφtN t ht0]
    have hb' : HasDerivAt b c.re x := by
      have h1 : HasDerivAt (fun y : ℝ => (G y).re) c.re x := hGx.real_of_complex
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x hr] with y hy
      have : |y - x| < r := by rwa [mem_ball, Real.dist_eq] at hy
      rw [hGr y this]; simp
    have hGx0 : G x = (b x : ℂ) := hGr x (by simpa using hr)
    have hcre : 0 ≤ c.re := by
      have hl : HasDerivAt (fun s : ℝ => (x : ℂ) + (s : ℂ) * I) I 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const I).const_add (x : ℂ)
      have hc' : HasDerivAt G c ((fun s : ℝ => (x : ℂ) + (s : ℂ) * I) 0) := by simpa using hGx
      have h := hasDerivAt_iff_tendsto_slope.1 (hc'.comp (0 : ℝ) hl)
      have h' := h.mono_left (nhdsWithin_mono _ fun t (ht : t ∈ Ioi (0 : ℝ)) => ne_of_gt ht)
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (G ∘ fun s : ℝ => (x : ℂ) + (s : ℂ) * I) 0 t ∈
          {w : ℂ | 0 ≤ w.im} := by
        filter_upwards [Ioo_mem_nhdsGT hr] with t ht
        have hH : (x : ℂ) + (t : ℂ) * I ∈ H := show 0 < ((x : ℂ) + (t : ℂ) * I).im by
          simpa using ht.1
        have hball : (x : ℂ) + (t : ℂ) * I ∈ ball (x : ℂ) r := by
          rw [mem_ball, dist_eq_norm, show (x : ℂ) + (t : ℂ) * I - x = (t : ℂ) * I by ring,
            norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
          exact ht.2
        have hpos' : 0 < (G ((x : ℂ) + (t : ℂ) * I)).im := by
          rw [hGeq ⟨show (0 : ℝ) ≤ ((x : ℂ) + (t : ℂ) * I).im from le_of_lt hH, hball⟩,
            hφtD _ (hsub ⟨hH, hball⟩)]
          exact hbij.mapsTo (hsub ⟨hH, hball⟩)
        simp only [slope_def_module, Function.comp_apply, ofReal_zero, zero_mul, add_zero, hGx0,
          smul_im, sub_im, ofReal_im, sub_zero, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 ht.1.le) hpos'.le
      have := (isClosed_le continuous_const continuous_im).mem_of_tendsto h' hev
      simpa using this
    exact ⟨c.re, hcre, hb'⟩
  choose! cb hcb hcbd using hderiv
  have hmono : MonotoneOn b (Iio 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Iio 0) (fun x hx => ?_) ?_ ?_
    · exact (hcbd x hx).continuousAt.continuousWithinAt
    · rw [interior_Iio]
      exact fun x hx => (hcbd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Iio]
      intro x hx
      rw [(hcbd x hx).deriv]
      exact hcb x hx
  intro x hx
  by_contra hpos
  have hpos : 0 < b x := lt_of_le_of_ne (not_lt.1 hpos) (hb0 x hx).symm
  obtain ⟨δ, hδ, hsm⟩ := hsmall (b x) hpos
  set a : ℝ := max (-(δ / 2)) (x / 2) with hadef
  have ha1 : -δ < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ha2 : a < 0 := max_lt (by linarith) (by linarith)
  have hxa : x ≤ a := le_trans (by linarith) (le_max_right _ _)
  have h1 := hmono (show x ∈ Iio 0 from hx) (show a ∈ Iio 0 from ha2) hxa
  have h2 := hsm a ha1 ha2
  have := le_abs_self (b a)
  linarith

/-- **Left-normalized uniformizers exist.** -/
theorem leftUnifExistStmt : LeftUnifExistStmt := by
  intro η hη
  obtain ⟨φ₀, hφ₀⟩ := exists_normalizedUniformizer_leftComponent hη
  obtain ⟨b, hb, -, hb0⟩ := exists_boundary_values_normalized hη hφ₀
  have hc : b (-1) < 0 := boundary_neg_of_normalized hη hφ₀ hb hb0 (-1) (by norm_num)
  set a : ℝ := -1 / b (-1) with hadef
  have ha : 0 < a := div_pos_of_neg_of_neg (by norm_num) hc
  obtain ⟨hbij, hd, h0, hinf⟩ := hφ₀
  have hmul : BijOn (fun w : ℂ => (a : ℂ) * w) H H := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    refine ⟨fun w hw => G1.mul_mem_H ha hw, fun w _ w' _ h => mul_left_cancel₀ ha' h,
      fun w hw => ⟨((a⁻¹ : ℝ) : ℂ) * w, G1.mul_mem_H (inv_pos.2 ha) hw, ?_⟩⟩
    simp only
    rw [← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ ha.ne', ofReal_one, one_mul]
  refine ⟨fun z => (a : ℂ) * φ₀ z, ⟨hmul.comp hbij, (differentiableOn_const _).mul hd, ?_, ?_⟩, ?_⟩
  · simpa using h0.const_mul (a : ℂ)
  · have := Tendsto.const_mul_atTop ha hinf
    refine this.congr fun z => ?_
    simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos ha]
  · have h1 := (hb (-1) (by norm_num)).const_mul (a : ℂ)
    have e : (a : ℂ) * (b (-1) : ℂ) = -1 := by
      rw [← ofReal_mul, hadef, div_mul_cancel₀ _ hc.ne]; simp
    rw [e] at h1
    simpa using h1

end G1Chord

/-- **`G1PsiSelStmt` holds.** -/
theorem g1PsiSelStmt : G1PsiSelStmt := g1PsiSelStmt_of_leftUnifExist G1Chord.leftUnifExistStmt

/-- **G1's regularity half from the RC2 half and the rest** (selection discharged). -/
theorem g1RegRepStmt_of_rc2_rest (h2 : G1RegRepRC2Stmt) (h3 : G1RegRepRestStmt) :
    G1RegRepStmt :=
  g1RegRepStmt_of_parts g1PsiSelStmt h2 h3

end Thm18Asm
end QuantumZipper
