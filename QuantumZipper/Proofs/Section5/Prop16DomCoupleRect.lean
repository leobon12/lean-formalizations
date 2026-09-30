import QuantumZipper.Proofs.Section5.Prop16DomCoupleKolm
import QuantumZipper.Proofs.Section5.Prop16DomCoupleVersion

/-!
# Proposition 1.6, node DOM-COUPLE (part 6): rational rectangles for the localisation

Elementary tools (own elementary proofs) for localising the global continuous-version lemma
`isoW_contVersion_global` to a relatively open subset `O ∩ Hbar` of the closed half-plane:
closed rectangles `rectQ p` with rational corners, the clamp `clampQ p` onto them (Lipschitz,
the identity on the rectangle), relative neighbourhoods (`exists_rectQ_nhdsWithin`) and density of
the rational points of a rectangle intersection (`eq_on_inter_of_rat`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- The closed rectangle `[a₁, a₂] × [b₁, b₂]` with rational corners `p = (a₁, a₂, b₁, b₂)`. -/
def rectQ (p : ℚ × ℚ × ℚ × ℚ) : Set ℂ :=
  Complex.equivRealProd ⁻¹' (Icc (p.1 : ℝ) p.2.1 ×ˢ Icc (p.2.2.1 : ℝ) p.2.2.2)

theorem mem_rectQ {p : ℚ × ℚ × ℚ × ℚ} {w : ℂ} :
    w ∈ rectQ p ↔ ((p.1 : ℝ) ≤ w.re ∧ w.re ≤ p.2.1) ∧ ((p.2.2.1 : ℝ) ≤ w.im ∧ w.im ≤ p.2.2.2) := by
  simp only [rectQ, mem_preimage, Complex.equivRealProd_apply, mem_prod, mem_Icc]

theorem isCompact_rectQ (p : ℚ × ℚ × ℚ × ℚ) : IsCompact (rectQ p) :=
  (Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage).2 (isCompact_Icc.prod isCompact_Icc)

/-- Clamp of a real number into `[a, b]`. -/
def clampR (a b x : ℝ) : ℝ := max a (min b x)

theorem abs_clampR_sub_le (a b x y : ℝ) : |clampR a b x - clampR a b y| ≤ |x - y| := by
  unfold clampR
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

theorem clampR_eq {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : clampR a b x = x := by
  simp [clampR, h1, h2]

theorem clampR_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clampR a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem continuous_clampR (a b : ℝ) : Continuous (clampR a b) := by
  unfold clampR; fun_prop

/-- The clamp onto a rational rectangle. -/
def clampQ (p : ℚ × ℚ × ℚ × ℚ) (w : ℂ) : ℂ :=
  ⟨clampR p.1 p.2.1 w.re, clampR p.2.2.1 p.2.2.2 w.im⟩

theorem clampQ_eq {p : ℚ × ℚ × ℚ × ℚ} {w : ℂ} (hw : w ∈ rectQ p) : clampQ p w = w := by
  rw [mem_rectQ] at hw
  apply Complex.ext <;> simp [clampQ, clampR_eq, hw]

theorem clampQ_mem {p : ℚ × ℚ × ℚ × ℚ} (h1 : (p.1 : ℝ) ≤ p.2.1) (h2 : (p.2.2.1 : ℝ) ≤ p.2.2.2)
    (w : ℂ) : clampQ p w ∈ rectQ p := by
  rw [mem_rectQ]
  exact ⟨clampR_mem h1 _, clampR_mem h2 _⟩

theorem lipschitzWith_clampQ (p : ℚ × ℚ × ℚ × ℚ) : LipschitzWith 2 (clampQ p) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h := Complex.norm_le_abs_re_add_abs_im (clampQ p w - clampQ p w')
  simp only [clampQ, Complex.sub_re, Complex.sub_im] at h
  have h1 := abs_clampR_sub_le p.1 p.2.1 w.re w'.re
  have h2 := abs_clampR_sub_le p.2.2.1 p.2.2.2 w.im w'.im
  have h3 : |w.re - w'.re| ≤ ‖w - w'‖ := by
    simpa using Complex.abs_re_le_norm (w - w')
  have h4 : |w.im - w'.im| ≤ ‖w - w'‖ := by
    simpa using Complex.abs_im_le_norm (w - w')
  have : ‖clampQ p w - clampQ p w'‖ ≤ 2 * ‖w - w'‖ := by
    unfold clampQ; linarith
  simpa using this

/-- **Rational rectangles are relative neighbourhoods.** Every point of `O ∩ Hbar` (`O` open) has
a rational rectangle inside `O ∩ Hbar` (nondegenerate corners, bottom `≥ 0`) that is a
neighbourhood of it within `Hbar`. -/
theorem exists_rectQ_nhdsWithin {O : Set ℂ} (hO : IsOpen O) {z : ℂ} (hz : z ∈ O ∩ Hbar) :
    ∃ p : ℚ × ℚ × ℚ × ℚ, (p.1 : ℝ) ≤ p.2.1 ∧ (p.2.2.1 : ℝ) ≤ p.2.2.2 ∧ (0 : ℝ) ≤ p.2.2.1 ∧
      rectQ p ⊆ O ∧ rectQ p ∈ 𝓝[Hbar] z := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO z hz.1
  have hz0 : 0 ≤ z.im := hz.2
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨a1, ha1, ha1'⟩ := exists_rat_btwn (show z.re - ε / 4 < z.re by linarith)
  obtain ⟨a2, ha2, ha2'⟩ := exists_rat_btwn (show z.re < z.re + ε / 4 by linarith)
  obtain ⟨b2, hb2, hb2'⟩ := exists_rat_btwn (show z.im < z.im + ε / 4 by linarith)
  -- the bottom edge: `0` if `z` is on the real line, otherwise a rational just below `z.im`
  obtain ⟨b1, hb1a, hb1b, hb1c, U, hUo, hzU, hUsub⟩ : ∃ b1 : ℚ, (0 : ℝ) ≤ b1 ∧ (b1 : ℝ) ≤ z.im ∧
      z.im - ε / 4 < b1 ∧ ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
        ∀ w ∈ U ∩ Hbar, (b1 : ℝ) ≤ w.im := by
    rcases hz0.eq_or_lt with h0 | h0
    · refine ⟨0, by simp, by simp [← h0], by simp [← h0]; linarith, univ, isOpen_univ,
        mem_univ _, fun w hw => ?_⟩
      have h0' : 0 ≤ w.im := hw.2
      simpa using h0'
    · obtain ⟨b1, hb1, hb1'⟩ := exists_rat_btwn (show max 0 (z.im - ε / 4) < z.im from
        max_lt h0 (by linarith))
      refine ⟨b1, (le_max_left _ _).trans hb1.le, hb1'.le, (le_max_right _ _).trans_lt hb1,
        {w | (b1 : ℝ) < w.im}, isOpen_lt continuous_const Complex.continuous_im, hb1',
        fun w hw => le_of_lt hw.1⟩
  refine ⟨(a1, a2, b1, b2), by push_cast; linarith, by push_cast; linarith, hb1a, ?_, ?_⟩
  · intro w hw
    rw [mem_rectQ] at hw
    obtain ⟨⟨hw1, hw2⟩, hw3, hw4⟩ := hw
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (w - z)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have e1 : |w.re - z.re| ≤ ε / 4 := abs_le.2 ⟨by push_cast at hw1; linarith,
      by push_cast at hw2; linarith⟩
    have e2 : |w.im - z.im| ≤ ε / 4 := abs_le.2 ⟨by push_cast at hw3; linarith,
      by push_cast at hw4; linarith⟩
    linarith
  · refine mem_nhdsWithin.2 ⟨U ∩ {w | (a1 : ℝ) < w.re ∧ w.re < a2 ∧ w.im < b2}, ?_, ?_, ?_⟩
    · refine hUo.inter ((isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
    · exact ⟨hzU, ha1', ha2, hb2⟩
    · rintro w ⟨⟨hwU, h1, h2, h3⟩, hwH⟩
      rw [mem_rectQ]
      exact ⟨⟨h1.le, h2.le⟩, hUsub w ⟨hwU, hwH⟩, h3.le⟩

/-- A real number in `[a, b]` (rational ends) is a limit of rationals in `[a, b]`. -/
theorem exists_seq_rat_Icc {a b : ℚ} {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) :
    ∃ r : ℕ → ℚ, (∀ n, (r n : ℝ) ∈ Icc (a : ℝ) b) ∧ Tendsto (fun n => (r n : ℝ)) atTop (𝓝 x) := by
  have hab : (a : ℝ) ≤ b := hx.1.trans hx.2
  have hcl : x ∈ closure (range ((↑) : ℚ → ℝ)) := by
    rw [Rat.denseRange_cast.closure_range]; exact mem_univ _
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  choose q hq using hu
  refine ⟨fun n => max a (min b (q n)), fun n => ?_, ?_⟩
  · have := clampR_mem hab (q n)
    simpa [clampR, Rat.cast_max, Rat.cast_min] using this
  · have h := ((continuous_clampR a b).tendsto x).comp hlim
    rw [Function.comp_def, clampR_eq hx.1 hx.2] at h
    refine h.congr fun n => ?_
    simp [clampR, hq n, Rat.cast_max, Rat.cast_min]

/-- **Agreement on a rectangle intersection from agreement at its rational points.** -/
theorem eq_on_inter_of_rat {p p' : ℚ × ℚ × ℚ × ℚ} {f g : ℂ → ℝ} (hf : Continuous f)
    (hg : Continuous g)
    (h : ∀ r : ℚ × ℚ, (⟨r.1, r.2⟩ : ℂ) ∈ rectQ p ∩ rectQ p' →
      f ⟨r.1, r.2⟩ = g ⟨r.1, r.2⟩) {w : ℂ} (hw : w ∈ rectQ p ∩ rectQ p') : f w = g w := by
  obtain ⟨hw1, hw2⟩ := hw
  rw [mem_rectQ] at hw1 hw2
  have hre : w.re ∈ Icc ((max p.1 p'.1 : ℚ) : ℝ) (min p.2.1 p'.2.1 : ℚ) := by
    push_cast; exact ⟨max_le hw1.1.1 hw2.1.1, le_min hw1.1.2 hw2.1.2⟩
  have him : w.im ∈ Icc ((max p.2.2.1 p'.2.2.1 : ℚ) : ℝ) (min p.2.2.2 p'.2.2.2 : ℚ) := by
    push_cast; exact ⟨max_le hw1.2.1 hw2.2.1, le_min hw1.2.2 hw2.2.2⟩
  obtain ⟨r1, hr1, hl1⟩ := exists_seq_rat_Icc hre
  obtain ⟨r2, hr2, hl2⟩ := exists_seq_rat_Icc him
  have hlim : Tendsto (fun n => (⟨r1 n, r2 n⟩ : ℂ)) atTop (𝓝 w) := by
    have := (Complex.equivRealProdCLM.symm.continuous.tendsto (w.re, w.im)).comp
      (hl1.prodMk_nhds hl2)
    refine (this.congr fun n => ?_).trans (le_of_eq (by congr 1))
    apply Complex.ext <;> simp
  have hmem : ∀ n, (⟨r1 n, r2 n⟩ : ℂ) ∈ rectQ p ∩ rectQ p' := by
    intro n
    have h1 := hr1 n
    have h2 := hr2 n
    push_cast at h1 h2
    simp only [mem_Icc, max_le_iff, le_min_iff] at h1 h2
    refine ⟨mem_rectQ.2 ⟨⟨?_, ?_⟩, ?_, ?_⟩, mem_rectQ.2 ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩ <;>
      simp only <;> linarith
  exact tendsto_nhds_unique ((hf.tendsto w).comp hlim)
    (((hg.tendsto w).comp hlim).congr fun n => (h (r1 n, r2 n) (hmem n)).symm)

end Prop16Asm

end QuantumZipper
