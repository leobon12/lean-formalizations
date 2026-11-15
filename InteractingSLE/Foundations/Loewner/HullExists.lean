import InteractingSLE.Foundations.Loewner.HullBasic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Existence of the mapping-out function of a compact `ℍ`-hull

Design `planning/INFRA-GEO.md` §3–§4, packet GEO-HCAP-A (second part of
`InteractingSLE.Foundations.Loewner.Hull`).

## Main result

* `IsHPHull.exists_isMapOut_tendsto`: a compact `ℍ`-hull `A` has a mapping-out function `g`, and
  `z (g z − z)` converges at `∞` to a real number (G. F. Lawler, *Conformally invariant processes
  in the plane*, AMS 2005 ([Law05]), §3.4).

## Proof

Write `A ⊆ B(0, R)`, `p = 2R`, `K = A ∪ conj A ∪ [-p, p]`. The doubled domain
`Ω = {0} ∪ {w ≠ 0 | p − 1/w ∉ K}` (the image of `ℂ̂ \ K` under `z ↦ 1/(p − z)`, `∞ ↦ 0`) is open,
connected, simply connected (every complementary component is unbounded), and symmetric under
`conj`. Its normalized Riemann map `F` (`F 0 = 0`, `F'(0) > 0`) commutes with `conj` by uniqueness,
so it maps `Ω ∩ ℍ = ι(ℍ \ A)` onto the upper half-disc; the Joukowski map `u ↦ −(u + 1/u)/2` maps
the upper half-disc onto `ℍ`. After an affine normalization the composite has the expansion
`g(z) = z + r(1/(p − z))` with `r` holomorphic at `0`, `r(0) = 0`, real on the real axis, and
`z (g z − z) → −r'(0)`. No boundary regularity of conformal maps and no reflection principle is
needed: the symmetry comes from the uniqueness of the normalized Riemann map.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

/-! ### Existence: the doubled domain -/

section Doubling

variable {A : Set ℂ} {R : ℝ}

/-- The real segment `[-2R, 2R]` of the doubled hull. -/
def dblSeg (R : ℝ) : Set ℂ := {z | z.im = 0 ∧ |z.re| ≤ 2 * R}

/-- The doubled hull `K = A ∪ conj A ∪ [-2R, 2R]`. -/
def dblK (A : Set ℂ) (R : ℝ) : Set ℂ := A ∪ {z | conj z ∈ A} ∪ dblSeg R

/-- The doubled domain `Ω = {0} ∪ {w ≠ 0 | 2R − 1/w ∉ K}`: the image of `ℂ̂ \ K` under
`z ↦ 1/(2R − z)` (with `∞ ↦ 0`). -/
def dblΩ (A : Set ℂ) (R : ℝ) : Set ℂ := {w | w = 0 ∨ ((2 * R : ℝ) : ℂ) - w⁻¹ ∉ dblK A R}

/-- The inversion `ι z = 1/(2R − z)`. -/
def dblι (R : ℝ) (z : ℂ) : ℂ := (((2 * R : ℝ) : ℂ) - z)⁻¹

theorem isClosed_dblSeg (R : ℝ) : IsClosed (dblSeg R) :=
  (isClosed_eq continuous_im continuous_const).inter
    (isClosed_le (continuous_abs.comp continuous_re) continuous_const)

theorem closure_subset_union_dblSeg (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    closure A ⊆ A ∪ dblSeg R := by
  intro z hz
  have hzR : ‖z‖ ≤ R := mem_closedBall_zero_iff.1
    (closure_minimal (hAR.trans ball_subset_closedBall) isClosed_closedBall hz)
  have hAH : A ⊆ Hbar := hA.1.trans fun w (hw : 0 < w.im) => show 0 ≤ w.im from hw.le
  have hzH : 0 ≤ z.im := closure_minimal hAH QuantumZipper.isClosed_Hbar hz
  rcases hzH.lt_or_eq with h | h
  · by_contra hzA
    have hzA' : z ∉ A := fun h' => hzA (Or.inl h')
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hz (H \ A) hA.isOpen ⟨h, hzA'⟩
    exact hw1.2 hw2
  · refine Or.inr ⟨h.symm, ?_⟩
    linarith [Complex.abs_re_le_norm z]

theorem isClosed_dblK (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    IsClosed (dblK A R) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  rw [dblK, closure_union, closure_union, (isClosed_dblSeg R).closure_eq] at hz
  rcases hz with (hz | hz) | hz
  · rcases closure_subset_union_dblSeg hA hR hAR hz with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · have hc : conj z ∈ closure A := map_mem_closure continuous_conj hz fun w hw => hw
    rcases closure_subset_union_dblSeg hA hR hAR hc with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨by simpa using h.1, by simpa using h.2⟩
  · exact Or.inr hz

theorem dblK_subset_closedBall (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    dblK A R ⊆ closedBall 0 (2 * R) := by
  rintro z ((hz | hz) | hz) <;> rw [mem_closedBall_zero_iff]
  · linarith [mem_ball_zero_iff.1 (hAR hz)]
  · have := mem_ball_zero_iff.1 (hAR hz); rw [Complex.norm_conj] at this; linarith
  · obtain ⟨h1, h2⟩ := hz
    have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h1])
    rw [this, Complex.norm_real, Real.norm_eq_abs]; exact h2

theorem conj_mem_dblK_iff {z : ℂ} : conj z ∈ dblK A R ↔ z ∈ dblK A R := by
  simp only [dblK, dblSeg, mem_union, mem_ofPred_eq, conj_conj, conj_im, conj_re, neg_eq_zero]
  tauto

theorem dblK_disjoint_H (hA : IsHPHull A) {z : ℂ} (hz : z ∈ H) (hzA : z ∉ A) : z ∉ dblK A R := by
  have hz' : 0 < z.im := hz
  rintro ((h | h) | h)
  · exact hzA h
  · have : 0 < (conj z).im := hA.1 h
    simp at this; linarith
  · exact absurd h.1 hz'.ne'

theorem zero_mem_dblK (hR : 0 < R) : (0 : ℂ) ∈ dblK A R :=
  Or.inr ⟨by simp, by simp; linarith⟩

theorem ball_subset_dblΩ (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    ball (0 : ℂ) (1 / (4 * R)) ⊆ dblΩ A R := by
  intro w hw
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  refine Or.inr fun hK => ?_
  have h1 := mem_closedBall_zero_iff.1 (dblK_subset_closedBall hR hAR hK)
  have h2 : ‖w‖ < 1 / (4 * R) := mem_ball_zero_iff.1 hw
  have h3 : 4 * R < ‖w⁻¹‖ := by
    rw [norm_inv]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    rw [lt_inv_comm₀ (by positivity) hwpos]
    simpa using h2
  have h4 : ‖w⁻¹‖ ≤ ‖((2 * R : ℝ) : ℂ) - w⁻¹‖ + ‖((2 * R : ℝ) : ℂ)‖ := by
    calc ‖w⁻¹‖ = ‖-(((2 * R : ℝ) : ℂ) - w⁻¹) + ((2 * R : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ ‖-(((2 * R : ℝ) : ℂ) - w⁻¹)‖ + ‖((2 * R : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h4
  linarith

theorem isOpen_dblΩ (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    IsOpen (dblΩ A R) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  rcases hw with hw0 | hwK
  · subst hw0
    exact Filter.mem_of_superset (ball_mem_nhds 0 (by positivity)) (ball_subset_dblΩ hR hAR)
  · by_cases hw0 : w = 0
    · subst hw0
      exact Filter.mem_of_superset (ball_mem_nhds 0 (by positivity)) (ball_subset_dblΩ hR hAR)
    have hc : ContinuousAt (fun v : ℂ => ((2 * R : ℝ) : ℂ) - v⁻¹) w :=
      continuousAt_const.sub (continuousAt_inv₀ hw0)
    exact Filter.mem_of_superset
      (hc.preimage_mem_nhds ((isClosed_dblK hA hR hAR).isOpen_compl.mem_nhds hwK))
      fun v hv => Or.inr hv

theorem conj_mem_dblΩ_iff {w : ℂ} : conj w ∈ dblΩ A R ↔ w ∈ dblΩ A R := by
  have h1 : ((2 * R : ℝ) : ℂ) - (conj w)⁻¹ = conj (((2 * R : ℝ) : ℂ) - w⁻¹) := by
    rw [map_sub, map_inv₀, conj_ofReal]
  simp only [dblΩ, mem_ofPred_eq, map_eq_zero, h1, conj_mem_dblK_iff]

theorem dblΩ_ne_univ (hR : 0 < R) : dblΩ A R ≠ univ := by
  intro h
  have hmem : (((2 * R : ℝ) : ℂ))⁻¹ ∈ dblΩ A R := h ▸ mem_univ _
  have hp : ((2 * R : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  rcases hmem with h0 | hK
  · exact inv_ne_zero hp h0
  · apply hK
    rw [inv_inv, sub_self]
    exact zero_mem_dblK hR

theorem dblι_ne_zero {z : ℂ} (hz : z ∈ H) : dblι R z ≠ 0 := by
  refine inv_ne_zero fun h => ?_
  have := congrArg Complex.im h
  have hz' : 0 < z.im := hz
  simp at this; linarith

theorem im_dblι (R : ℝ) (z : ℂ) : (dblι R z).im = z.im / normSq (((2 * R : ℝ) : ℂ) - z) := by
  simp [dblι, inv_im]

theorem dblι_mem_H {z : ℂ} (hz : z ∈ H) : dblι R z ∈ H := by
  show 0 < (dblι R z).im
  rw [im_dblι]
  refine div_pos hz (normSq_pos.2 fun h => ?_)
  have := congrArg Complex.im h
  have hz' : 0 < z.im := hz
  simp at this; linarith

theorem sub_inv_dblι {z : ℂ} : ((2 * R : ℝ) : ℂ) - (dblι R z)⁻¹ = z := by
  simp [dblι]

/-- `ι` maps `ℍ \ A` bijectively onto `Ω ∩ ℍ`. -/
theorem bijOn_dblι (hA : IsHPHull A) : BijOn (dblι R) (H \ A) (dblΩ A R ∩ H) := by
  refine ⟨fun z hz => ⟨Or.inr ?_, dblι_mem_H hz.1⟩, fun z _ z' _ h => ?_, fun w hw => ?_⟩
  · rw [sub_inv_dblι]; exact dblK_disjoint_H hA hz.1 hz.2
  · have := congrArg (fun v => ((2 * R : ℝ) : ℂ) - v⁻¹) h
    simpa only [sub_inv_dblι] using this
  · obtain ⟨hwΩ, hwH⟩ := hw
    have hw' : 0 < w.im := hwH
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw'
    have hK : ((2 * R : ℝ) : ℂ) - w⁻¹ ∉ dblK A R := hwΩ.resolve_left hw0
    have hzH : ((2 * R : ℝ) : ℂ) - w⁻¹ ∈ H := by
      show 0 < (((2 * R : ℝ) : ℂ) - w⁻¹).im
      simp only [sub_im, ofReal_im, inv_im, zero_sub, neg_div, neg_neg]
      exact div_pos hw' (normSq_pos.2 hw0)
    refine ⟨((2 * R : ℝ) : ℂ) - w⁻¹, ⟨hzH, fun h => hK (Or.inl (Or.inl h))⟩, ?_⟩
    simp [dblι]

theorem continuousOn_dblι {T : Set ℂ} (hT : ((2 * R : ℝ) : ℂ) ∉ T) :
    ContinuousOn (dblι R) T := by
  intro z hz
  refine ((continuousAt_const (y := ((2 * R : ℝ) : ℂ))).sub continuousAt_id).inv₀ ?_
    |>.continuousWithinAt
  intro h
  have h' : ((2 * R : ℝ) : ℂ) = z := sub_eq_zero.1 h
  exact hT (h' ▸ hz)

theorem dblι_continuousOn_H : ContinuousOn (dblι R) H :=
  continuousOn_dblι fun h => by simpa using (show (0 : ℝ) < _ from h)

/-- A point of `ℍ \ A` far up is mapped into the disc `B(0, 1/(4R))`. -/
theorem exists_dblι_mem_ball (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    ∃ z ∈ H \ A, dblι R z ∈ ball (0 : ℂ) (1 / (4 * R)) := by
  set z : ℂ := ((4 * R + 1 : ℝ) : ℂ) * I with hzdef
  have hzim : z.im = 4 * R + 1 := by simp [z]
  have hznorm : ‖z‖ = 4 * R + 1 := by
    simp only [z, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)
  have hzH : z ∈ H := show 0 < z.im by rw [hzim]; linarith
  refine ⟨z, ⟨hzH, fun h => ?_⟩, ?_⟩
  · have := mem_ball_zero_iff.1 (hAR h); linarith
  · rw [mem_ball_zero_iff, dblι, norm_inv]
    have h1 : 4 * R + 1 ≤ ‖((2 * R : ℝ) : ℂ) - z‖ := by
      have := Complex.abs_im_le_norm (((2 * R : ℝ) : ℂ) - z)
      simp only [sub_im, ofReal_im, zero_sub, abs_neg, hzim] at this
      rw [abs_of_pos (by linarith)] at this; exact this
    rw [inv_lt_comm₀ (by linarith) (by positivity)]
    rw [one_div, inv_inv]; linarith

theorem isConnected_dblΩ (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    IsConnected (dblΩ A R) := by
  set δ : ℝ := 1 / (4 * R) with hδ
  have hδpos : 0 < δ := by positivity
  set B : Set ℂ := ball 0 δ
  set S₁ : Set ℂ := dblι R '' (H \ A)
  set S₂ : Set ℂ := conj '' S₁
  set S₃ : Set ℂ := ofReal '' Iio δ
  have hB : IsConnected B := (convex_ball (0 : ℂ) δ).isConnected (nonempty_ball.2 hδpos)
  have hS₁ : IsConnected S₁ := hA.isConnected.image _ (dblι_continuousOn_H.mono sdiff_subset)
  have hS₂ : IsConnected S₂ := hS₁.image _ continuous_conj.continuousOn
  have hS₃ : IsConnected S₃ := isConnected_Iio.image _ continuous_ofReal.continuousOn
  obtain ⟨z₀, hz₀, hz₀B⟩ := exists_dblι_mem_ball hR hAR
  have h1 : IsConnected (B ∪ S₁) := IsConnected.union ⟨_, hz₀B, z₀, hz₀, rfl⟩ hB hS₁
  have hcB : conj (dblι R z₀) ∈ B := by
    show conj (dblι R z₀) ∈ ball (0 : ℂ) δ
    rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hz₀B
  have h2 : IsConnected (B ∪ S₁ ∪ S₂) :=
    IsConnected.union ⟨_, Or.inl hcB, _, ⟨z₀, hz₀, rfl⟩, rfl⟩ h1 hS₂
  have h3 : IsConnected (B ∪ S₁ ∪ S₂ ∪ S₃) :=
    IsConnected.union ⟨0, Or.inl (Or.inl (mem_ball_self hδpos)), 0, hδpos, by simp⟩ h2 hS₃
  have hBΩ : B ⊆ dblΩ A R := ball_subset_dblΩ hR hAR
  convert h3 using 1
  ext w
  constructor
  · intro hw
    rcases lt_trichotomy w.im 0 with h | h | h
    · have hc : conj w ∈ dblΩ A R ∩ H :=
        ⟨conj_mem_dblΩ_iff.2 hw, show 0 < (conj w).im by simp; linarith⟩
      obtain ⟨z, hz, hzw⟩ := (bijOn_dblι hA).surjOn hc
      exact Or.inl (Or.inr ⟨dblι R z, ⟨z, hz, rfl⟩, by rw [hzw, conj_conj]⟩)
    · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h])
      by_cases hre : w.re < δ
      · exact Or.inr ⟨w.re, hre, hw'.symm⟩
      · exfalso
        rw [not_lt] at hre
        have hre0 : 0 < w.re := lt_of_lt_of_le hδpos hre
        have hw0 : w ≠ 0 := by intro h0; rw [h0] at hre0; simp at hre0
        apply hw.resolve_left hw0
        refine Or.inr ⟨?_, ?_⟩
        · rw [hw']; simp
        · rw [hw', ← ofReal_inv, ← ofReal_sub, ofReal_re]
          have hinv : (w.re)⁻¹ ≤ 4 * R := by
            rw [inv_le_comm₀ hre0 (by positivity)]
            simpa [hδ] using hre
          have hinv0 : 0 < (w.re)⁻¹ := inv_pos.2 hre0
          rw [abs_le]; constructor <;> linarith
    · exact Or.inl (Or.inl (Or.inr ((bijOn_dblι hA).surjOn ⟨hw, h⟩)))
  · rintro (((hw | hw) | hw) | hw)
    · exact hBΩ hw
    · obtain ⟨z, hz, rfl⟩ := hw; exact ((bijOn_dblι hA).mapsTo hz).1
    · obtain ⟨v, ⟨z, hz, rfl⟩, rfl⟩ := hw
      exact conj_mem_dblΩ_iff.2 ((bijOn_dblι hA).mapsTo hz).1
    · obtain ⟨t, ht, rfl⟩ := hw
      rcases lt_or_ge t 0 with htn | htn
      · refine Or.inr fun hK => ?_
        have hK' := dblK_subset_closedBall hR hAR hK
        rw [mem_closedBall_zero_iff, ← ofReal_inv, ← ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs] at hK'
        have : (t)⁻¹ < 0 := inv_lt_zero.2 htn
        rw [abs_le] at hK'
        linarith [hK'.2]
      · refine hBΩ ?_
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg htn]
        exact ht

/-- The half-open real segment `[-2R, 2R)`. -/
def dblSegIco (R : ℝ) : Set ℂ := ofReal '' Ico (-(2 * R)) (2 * R)

theorem dblSegIco_subset_dblK : dblSegIco R ⊆ dblK A R := by
  rintro _ ⟨t, ht, rfl⟩
  exact Or.inr ⟨by simp, by simp only [ofReal_re]; exact abs_le.2 ⟨ht.1, ht.2.le⟩⟩

theorem not_mem_dblSegIco : ((2 * R : ℝ) : ℂ) ∉ dblSegIco R := by
  rintro ⟨t, ht, h⟩
  have := ofReal_injective h
  exact absurd ht.2 (by rw [this]; exact lt_irrefl _)

theorem isPreconnected_dblSegIco : IsPreconnected (dblSegIco R) :=
  isPreconnected_Ico.image _ continuous_ofReal.continuousOn

/-- Every point `k ≠ 2R` of the doubled hull lies in a preconnected subset of `K \ {2R}`
containing `[-2R, 2R)`. -/
theorem exists_isPreconnected_dblK (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) {k : ℂ}
    (hk : k ∈ dblK A R) (hkp : k ≠ ((2 * R : ℝ) : ℂ)) :
    ∃ T : Set ℂ, IsPreconnected T ∧ k ∈ T ∧ T ⊆ dblK A R ∧ ((2 * R : ℝ) : ℂ) ∉ T ∧
      dblSegIco R ⊆ T := by
  -- the case `k ∈ A`
  have hcaseA : ∀ k ∈ A, ∃ T : Set ℂ, IsPreconnected T ∧ k ∈ T ∧ T ⊆ dblK A R ∧
      ((2 * R : ℝ) : ℂ) ∉ T ∧ dblSegIco R ⊆ T := by
    intro k hk
    have hk' : k ∉ H \ A := fun h => h.2 hk
    set E := connectedComponentIn (H \ A)ᶜ k with hEdef
    have hEu : ¬ Bornology.IsBounded E :=
      not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hA.isOpen hA.2.2.2 hk'
    have hEsub : E ⊆ A ∪ {z : ℂ | z.im ≤ 0} := by
      rw [← compl_H_diff]; exact connectedComponentIn_subset _ _
    set ρ : ℂ → ℂ := fun z => ((max (-R) (min R z.re) : ℝ) : ℂ) + ((max z.im 0 : ℝ) : ℂ) * I
      with hρdef
    have hρc : Continuous ρ := by
      simp only [hρdef]
      fun_prop
    have hρA : ∀ z ∈ A, ρ z = z := by
      intro z hz
      have h1 : |z.re| < R := lt_of_le_of_lt (Complex.abs_re_le_norm z)
        (mem_ball_zero_iff.1 (hAR hz))
      have h2 : 0 < z.im := hA.1 hz
      rw [abs_lt] at h1
      have h3 : max (-R) (min R z.re) = z.re := by
        rw [min_eq_right h1.2.le, max_eq_right h1.1.le]
      apply Complex.ext <;> simp [hρdef, h3, max_eq_left h2.le]
    have hρL : ∀ z : ℂ, z.im ≤ 0 → ρ z ∈ dblSegIco R ∧ (ρ z).re ≤ R := by
      intro z hz
      have hre : (ρ z).re = max (-R) (min R z.re) := by simp [hρdef]
      have him : ρ z = ((max (-R) (min R z.re) : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [hρdef]
        · simp [hρdef, max_eq_right hz]
      refine ⟨⟨max (-R) (min R z.re), ⟨?_, ?_⟩, him.symm⟩, ?_⟩
      · linarith [le_max_left (-R) (min R z.re)]
      · have : max (-R) (min R z.re) ≤ R := max_le (by linarith) (min_le_left _ _)
        linarith
      · rw [hre]; exact max_le (by linarith) (min_le_left _ _)
    have hρre : ∀ z ∈ E, (ρ z).re ≤ R := by
      intro z hz
      rcases hEsub hz with h | h
      · rw [hρA z h]
        exact (le_abs_self _).trans ((Complex.abs_re_le_norm z).trans
          (mem_ball_zero_iff.1 (hAR h)).le)
      · exact (hρL z h).2
    obtain ⟨e, heE, heA⟩ := not_subset.1 fun hsub : E ⊆ A => hEu (hA.2.1.subset hsub)
    have heL : e.im ≤ 0 := (hEsub heE).resolve_left heA
    refine ⟨ρ '' E ∪ dblSegIco R, ?_, Or.inl ⟨k, mem_connectedComponentIn hk', hρA k hk⟩, ?_, ?_,
      subset_union_right⟩
    · exact (isPreconnected_connectedComponentIn.image ρ hρc.continuousOn).union (ρ e)
        ⟨e, heE, rfl⟩ (hρL e heL).1 isPreconnected_dblSegIco
    · rintro _ (⟨z, hz, rfl⟩ | hz)
      · rcases hEsub hz with h | h
        · rw [hρA z h]; exact Or.inl (Or.inl h)
        · exact dblSegIco_subset_dblK (hρL z h).1
      · exact dblSegIco_subset_dblK hz
    · rintro (⟨z, hz, hzp⟩ | hz)
      · have h1 := hρre z hz
        rw [hzp, ofReal_re] at h1
        linarith
      · exact not_mem_dblSegIco hz
  rcases hk with (hk | hk) | hk
  · exact hcaseA k hk
  · obtain ⟨T, hT, hkT, hTK, hpT, hST⟩ := hcaseA (conj k) hk
    refine ⟨conj '' T, hT.image _ continuous_conj.continuousOn, ⟨conj k, hkT, conj_conj k⟩, ?_, ?_,
      ?_⟩
    · rintro _ ⟨t, ht, rfl⟩; exact conj_mem_dblK_iff.2 (hTK ht)
    · rintro ⟨t, ht, htp⟩
      apply hpT
      have : t = ((2 * R : ℝ) : ℂ) := by rw [← conj_conj t, htp, conj_ofReal]
      rw [← this]; exact ht
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, hST ⟨t, ht, rfl⟩, conj_ofReal t⟩
  · refine ⟨dblSegIco R, isPreconnected_dblSegIco, ?_, dblSegIco_subset_dblK,
      not_mem_dblSegIco, subset_rfl⟩
    obtain ⟨h1, h2⟩ := hk
    have hkre : k = (k.re : ℂ) := Complex.ext (by simp) (by simp [h1])
    refine ⟨k.re, ⟨(abs_le.1 h2).1, lt_of_le_of_ne (abs_le.1 h2).2 fun h => hkp ?_⟩, hkre.symm⟩
    rw [hkre, h]

/-- **The doubled domain is simply connected**: every component of its complement is unbounded
(it contains the image under `ι` of a connected subset of `K` accumulating at `2R`). -/
theorem isSimplyConnected_dblΩ (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    IsSimplyConnected (dblΩ A R) := by
  refine isSimplyConnected_of_forall_not_isBounded (isOpen_dblΩ hA hR hAR)
    (isConnected_dblΩ hA hR hAR) fun a ha => ?_
  have ha0 : a ≠ 0 := fun h => ha (Or.inl h)
  have hk : ((2 * R : ℝ) : ℂ) - a⁻¹ ∈ dblK A R := by
    by_contra h; exact ha (Or.inr h)
  have hkp : ((2 * R : ℝ) : ℂ) - a⁻¹ ≠ ((2 * R : ℝ) : ℂ) := by
    intro h; apply inv_ne_zero ha0; linear_combination -h
  obtain ⟨T, hT, hkT, hTK, hpT, hST⟩ := exists_isPreconnected_dblK hA hR hAR hk hkp
  have hιT : dblι R '' T ⊆ (dblΩ A R)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩ (h | h)
    · refine inv_ne_zero (sub_ne_zero.2 ?_) h
      intro hpt; exact hpT (hpt ▸ ht)
    · exact h (by rw [sub_inv_dblι]; exact hTK ht)
  have haT : a ∈ dblι R '' T := ⟨_, hkT, by simp [dblι]⟩
  have hsub := (hT.image _ (continuousOn_dblι hpT)).subset_connectedComponentIn haT hιT
  intro hb
  obtain ⟨M, hM⟩ := (hb.subset hsub).subset_closedBall 0
  set η : ℝ := min (1 / (|M| + 1)) (4 * R) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hηM : η ≤ 1 / (|M| + 1) := min_le_left _ _
  have hηR : η ≤ 4 * R := min_le_right _ _
  have htS : ((2 * R - η : ℝ) : ℂ) ∈ dblSegIco R := ⟨2 * R - η, ⟨by linarith, by linarith⟩, rfl⟩
  have h1 := mem_closedBall_zero_iff.1 (hM ⟨_, hST htS, rfl⟩)
  have h2 : ‖dblι R ((2 * R - η : ℝ) : ℂ)‖ = 1 / η := by
    rw [dblι, ← ofReal_sub, ← ofReal_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [show 2 * R - (2 * R - η) = η by ring, abs_of_pos (inv_pos.2 hη0), one_div]
  rw [h2] at h1
  have h3 : |M| + 1 ≤ 1 / η := by
    rw [le_div_iff₀ hη0]
    calc (|M| + 1) * η ≤ (|M| + 1) * (1 / (|M| + 1)) :=
          mul_le_mul_of_nonneg_left hηM (by positivity)
      _ = 1 := by field_simp
  linarith [le_abs_self M]

end Doubling

/-! ### Existence: the symmetric Riemann map and the Joukowski map -/

section RiemannDouble

variable {A : Set ℂ} {R : ℝ}

/-- The normalized Riemann map of the doubled domain commutes with `conj` (uniqueness of the
normalized Riemann map, applied to `conj ∘ F ∘ conj`). -/
theorem exists_dblRiemann (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) :
    ∃ F : ℂ → ℂ, IsConformalBijection F (dblΩ A R) (ball 0 1) ∧ F 0 = 0 ∧
      0 < (deriv F 0).re ∧ (deriv F 0).im = 0 ∧
      ∀ w ∈ dblΩ A R, F (conj w) = conj (F w) := by
  have hΩo := isOpen_dblΩ hA hR hAR
  have h0 : (0 : ℂ) ∈ dblΩ A R := Or.inl rfl
  obtain ⟨F, hF, hF0, hFre, hFim⟩ := exists_isConformalBijection_ball hΩo
    (isConnected_dblΩ hA hR hAR) (isSimplyConnected_dblΩ hA hR hAR) (dblΩ_ne_univ hR) h0
  set G : ℂ → ℂ := conj ∘ F ∘ conj with hGdef
  have hG : IsConformalBijection G (dblΩ A R) (ball 0 1) := by
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun w hw w' hw' h => ?_, fun u hu => ?_⟩
    · have hcw : conj w ∈ dblΩ A R := conj_mem_dblΩ_iff.2 hw
      have hd : DifferentiableAt ℂ F (conj w) := hF.1.differentiableAt (hΩo.mem_nhds hcw)
      exact (differentiableAt_conj_conj_iff.2 hd).differentiableWithinAt
    · have := hF.2.mapsTo (conj_mem_dblΩ_iff.2 hw)
      simp only [hGdef, Function.comp_apply, mem_ball_zero_iff, Complex.norm_conj] at this ⊢
      exact this
    · simp only [hGdef, Function.comp_apply] at h
      have := hF.2.injOn (conj_mem_dblΩ_iff.2 hw) (conj_mem_dblΩ_iff.2 hw')
        (by simpa using congrArg conj h)
      simpa using congrArg conj this
    · have hcu : conj u ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, Complex.norm_conj]; exact mem_ball_zero_iff.1 hu
      obtain ⟨v, hv, hvu⟩ := hF.2.surjOn hcu
      refine ⟨conj v, conj_mem_dblΩ_iff.2 (by simpa using hv), ?_⟩
      simp [hGdef, hvu]
  have hG0 : G 0 = 0 := by simp [hGdef, hF0]
  have hdG : deriv G 0 = conj (deriv F 0) := by
    rw [hGdef, deriv_conj_conj]; simp
  have hEq := isConformalBijection_unique_of_deriv_pos hΩo h0 hF hG hF0 hG0 hFre hFim
    (by rw [hdG, conj_re]; exact hFre) (by rw [hdG, conj_im, hFim, neg_zero])
  refine ⟨F, hF, hF0, hFre, hFim, fun w hw => ?_⟩
  have := hEq (conj_mem_dblΩ_iff.2 hw)
  simp only [hGdef, Function.comp_apply, conj_conj] at this
  exact this

/-- The symmetric Riemann map sends `Ω ∩ ℍ` onto the upper half-disc. -/
theorem bijOn_dblRiemann_upper (hA : IsHPHull A) (hR : 0 < R) (hAR : A ⊆ ball 0 R) {F : ℂ → ℂ}
    (hF : IsConformalBijection F (dblΩ A R) (ball 0 1)) (hF0 : F 0 = 0)
    (hFre : 0 < (deriv F 0).re) (hsym : ∀ w ∈ dblΩ A R, F (conj w) = conj (F w)) :
    BijOn F (dblΩ A R ∩ H) (ball 0 1 ∩ H) := by
  have hΩo := isOpen_dblΩ hA hR hAR
  have hreal : ∀ w ∈ dblΩ A R, (F w).im = 0 → w.im = 0 := by
    intro w hw h
    have h1 : conj (F w) = F w := Complex.conj_eq_iff_im.2 h
    have h2 := hF.2.injOn (conj_mem_dblΩ_iff.2 hw) hw (by rw [hsym w hw, h1])
    exact Complex.conj_eq_iff_im.1 h2
  have hconn : IsPreconnected (dblΩ A R ∩ H) := by
    rw [← (bijOn_dblι hA).image_eq]
    exact hA.isConnected.isPreconnected.image _ (dblι_continuousOn_H.mono sdiff_subset)
  -- one point of `Ω ∩ ℍ` is sent into `ℍ`
  obtain ⟨ε, hεpos, hεΩ, hεF⟩ : ∃ ε : ℝ, 0 < ε ∧ (ε : ℂ) * I ∈ dblΩ A R ∧
      0 < (F ((ε : ℂ) * I)).im := by
    have hd : HasDerivAt F (deriv F 0) 0 :=
      (hF.1.differentiableAt (hΩo.mem_nhds (Or.inl rfl))).hasDerivAt
    have h1 := hd.tendsto_slope_zero
    have h2 : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
          (continuous_ofReal.mul continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_ne_zero (ofReal_ne_zero.2 (ne_of_gt hε)) I_ne_zero
    have h3 := (Complex.continuous_re.tendsto _).comp (h1.comp h2)
    have h4 := h3.eventually (lt_mem_nhds hFre)
    have h5 : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) * I ∈ dblΩ A R := by
      have : Tendsto (fun ε : ℝ => (ε : ℂ) * I) (𝓝[>] 0) (𝓝 0) := h2.mono_right nhdsWithin_le_nhds
      exact this.eventually (hΩo.mem_nhds (Or.inl rfl))
    obtain ⟨ε, ⟨hε4, hε5⟩, hεpos⟩ := (h4.and h5).and self_mem_nhdsWithin |>.exists
    refine ⟨ε, hεpos, hε5, ?_⟩
    simp only [Function.comp_apply, zero_add, hF0, sub_zero, smul_eq_mul] at hε4
    have : ((ε : ℂ) * I)⁻¹ * F ((ε : ℂ) * I) = F ((ε : ℂ) * I) * (-I) * ((ε⁻¹ : ℝ) : ℂ) := by
      rw [mul_inv, Complex.inv_I, ofReal_inv]; ring
    rw [this] at hε4
    simp only [mul_re, mul_im, neg_re, neg_im, I_re, I_im, ofReal_re, ofReal_im] at hε4
    have : 0 < (F ((ε : ℂ) * I)).im * ε⁻¹ := by linarith
    exact (mul_pos_iff_of_pos_right (inv_pos.2 hεpos)).1 this
  have hεH : (ε : ℂ) * I ∈ H := show 0 < ((ε : ℂ) * I).im by simpa using hεpos
  have himg : F '' (dblΩ A R ∩ H) ⊆ H := by
    have hsub : F '' (dblΩ A R ∩ H) ⊆ {u : ℂ | 0 < u.im} ∪ {u : ℂ | u.im < 0} := by
      rintro _ ⟨w, ⟨hwΩ, hwH⟩, rfl⟩
      rcases lt_trichotomy (F w).im 0 with h | h | h
      · exact Or.inr h
      · exact absurd (hreal w hwΩ h) (ne_of_gt (show 0 < w.im from hwH))
      · exact Or.inl h
    have hdisj : Disjoint {u : ℂ | 0 < u.im} {u : ℂ | u.im < 0} := by
      rw [Set.disjoint_left]; intro u h1 h2; exact lt_asymm (show 0 < u.im from h1) h2
    rcases (hconn.image F (hF.1.continuousOn.mono inter_subset_left)).subset_or_subset
        (isOpen_lt continuous_const continuous_im) (isOpen_lt continuous_im continuous_const)
        hdisj hsub with h | h
    · exact h
    · exact absurd (show (F ((ε : ℂ) * I)).im < 0 from h ⟨_, ⟨hεΩ, hεH⟩, rfl⟩) (not_lt.2 hεF.le)
  refine ⟨fun w hw => ⟨hF.2.mapsTo hw.1, himg ⟨w, hw, rfl⟩⟩,
    hF.2.injOn.mono inter_subset_left, fun u hu => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hF.2.surjOn hu.1
  have hu' : 0 < (F w).im := hu.2
  rcases lt_trichotomy w.im 0 with h | h | h
  · exfalso
    have hcw : conj w ∈ dblΩ A R ∩ H :=
      ⟨conj_mem_dblΩ_iff.2 hw, show 0 < (conj w).im by simp; linarith⟩
    have := himg ⟨_, hcw, rfl⟩
    rw [hsym w hw] at this
    have : 0 < (conj (F w)).im := this
    simp at this; linarith
  · exfalso
    have h1 : conj w = w := Complex.conj_eq_iff_im.2 h
    have h2 := hsym w hw
    rw [h1] at h2
    have := Complex.conj_eq_iff_im.1 h2.symm
    linarith
  · exact ⟨w, ⟨hw, h⟩, rfl⟩

/-- The **Joukowski map** `u ↦ −(u + 1/u)/2`. -/
def joukowski (u : ℂ) : ℂ := -(u + u⁻¹) / 2

theorem im_joukowski (u : ℂ) : (joukowski u).im = u.im * (1 / normSq u - 1) / 2 := by
  simp only [joukowski, neg_div, neg_im, div_ofNat_im, add_im, inv_im]
  ring

theorem differentiableOn_joukowski : DifferentiableOn ℂ joukowski (ball 0 1 ∩ H) := by
  intro u hu
  have hu0 : u ≠ 0 := by
    rintro rfl; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hu.2) (by simp)
  exact ((differentiableAt_id.add (differentiableAt_inv hu0)).neg.div_const 2)
    |>.differentiableWithinAt

/-- The Joukowski map sends the upper half-disc bijectively onto `ℍ`. -/
theorem bijOn_joukowski : BijOn joukowski (ball 0 1 ∩ H) H := by
  have hpos : ∀ u : ℂ, u ≠ 0 → normSq u < 1 → 0 < 1 / normSq u - 1 := by
    intro u hu h
    have := normSq_pos.2 hu
    rw [sub_pos, lt_div_iff₀ this]; linarith
  have hnsq : ∀ u ∈ ball (0 : ℂ) 1, normSq u < 1 := by
    intro u hu
    rw [normSq_eq_norm_sq]
    have := mem_ball_zero_iff.1 hu
    nlinarith [norm_nonneg u]
  refine ⟨fun u hu => ?_, fun u hu v hv h => ?_, fun w hw => ?_⟩
  · have hu0 : u ≠ 0 := by
      rintro rfl; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hu.2) (by simp)
    show 0 < (joukowski u).im
    rw [im_joukowski]
    exact div_pos (mul_pos hu.2 (hpos u hu0 (hnsq u hu.1))) two_pos
  · have hu0 : u ≠ 0 := by
      rintro rfl; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hu.2) (by simp)
    have hv0 : v ≠ 0 := by
      rintro rfl; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hv.2) (by simp)
    have h1 : (u - v) * (u * v - 1) = 0 := by
      simp only [joukowski] at h
      field_simp at h
      linear_combination (-1 : ℂ) * h
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact sub_eq_zero.1 h2
    · exfalso
      have h3 : ‖u * v‖ = 1 := by rw [sub_eq_zero.1 h2, norm_one]
      rw [norm_mul] at h3
      have := mem_ball_zero_iff.1 hu.1
      have := mem_ball_zero_iff.1 hv.1
      nlinarith [norm_nonneg u, norm_nonneg v]
  · have hw' : 0 < w.im := hw
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (w ^ 2 - 1)
    -- the two roots of `u² + 2 w u + 1`
    have hroot : ∀ u : ℂ, u = -w + s ∨ u = -w - s → u ≠ 0 ∧ joukowski u = w := by
      intro u hu
      have hq : u ^ 2 + 2 * w * u + 1 = 0 := by
        rcases hu with rfl | rfl <;> linear_combination (-1 : ℂ) * hs
      have hu0 : u ≠ 0 := by rintro rfl; simp at hq
      refine ⟨hu0, ?_⟩
      simp only [joukowski]
      field_simp
      linear_combination (-1 : ℂ) * hq
    have hprod : (-w + s) * (-w - s) = 1 := by linear_combination hs
    have hnorm1 : ∀ u : ℂ, u ≠ 0 → joukowski u = w → ‖u‖ ≠ 1 := by
      intro u hu0 hJ h1
      have hnsq1 : normSq u = 1 := by rw [normSq_eq_norm_sq, h1]; norm_num
      have := congrArg Complex.im hJ
      rw [im_joukowski, hnsq1] at this
      simp at this; linarith
    have hmem : ∀ u : ℂ, u ≠ 0 → joukowski u = w → ‖u‖ < 1 → u ∈ ball (0 : ℂ) 1 ∩ H := by
      intro u hu0 hJ hlt
      refine ⟨mem_ball_zero_iff.2 hlt, ?_⟩
      have hp := hpos u hu0 (by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg u])
      have := congrArg Complex.im hJ
      rw [im_joukowski] at this
      show 0 < u.im
      by_contra hneg
      rw [not_lt] at hneg
      have : u.im * (1 / normSq u - 1) / 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hp.le) two_pos.le
      linarith
    obtain ⟨h₁0, hJ₁⟩ := hroot _ (Or.inl rfl)
    obtain ⟨h₂0, hJ₂⟩ := hroot _ (Or.inr rfl)
    rcases lt_or_gt_of_ne (hnorm1 _ h₁0 hJ₁) with h | h
    · exact ⟨_, hmem _ h₁0 hJ₁ h, hJ₁⟩
    · refine ⟨_, hmem _ h₂0 hJ₂ ?_, hJ₂⟩
      have h3 : ‖-w + s‖ * ‖-w - s‖ = 1 := by rw [← norm_mul, hprod, norm_one]
      nlinarith [norm_nonneg (-w - s)]

end RiemannDouble

/-! ### Existence: the expansion at `∞` -/

/-- A function holomorphic at `0` and real on a real interval around `0` has a real derivative
at `0`. -/
theorem im_deriv_eq_zero_of_im_eq_zero {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableAt ℂ f 0) (hre : ∀ t : ℝ, |t| < δ → (f t).im = 0) :
    (deriv f 0).im = 0 := by
  have h1 : HasDerivAt (fun w => -I * f w) (-I * deriv f 0) ((0 : ℝ) : ℂ) := by
    rw [ofReal_zero]; exact hf.hasDerivAt.const_mul (-I)
  have h2 : HasDerivAt (fun t : ℝ => (f t).im) (deriv f 0).im 0 := by
    have := h1.real_of_complex
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => (f t).im) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds (show -δ < 0 by linarith) hδ] with t ht
    exact hre t (abs_lt.2 ht)
  exact h2.unique h3

namespace MapOutConstruction

/-- `κ = (F w − F 0)/w`, extended by `F'(0)` at `0`. -/
def kappa (F : ℂ → ℂ) : ℂ → ℂ := dslope F 0

/-- `κ₂ = (κ w − κ 0)/w`, extended by `κ'(0)` at `0`. -/
def kappa2 (F : ℂ → ℂ) : ℂ → ℂ := dslope (kappa F) 0

/-- `P = κ₂/κ`. -/
def quot (F : ℂ → ℂ) (w : ℂ) : ℂ := kappa2 F w / kappa F w

/-- The remainder `r(w) = P(w) − P(0) − F'(0) F(w)`: `g(z) = z + r(1/(2R − z))`. -/
def remainder (F : ℂ → ℂ) (w : ℂ) : ℂ := quot F w - quot F 0 - deriv F 0 * F w

/-- The mapping-out function built from the symmetric Riemann map `F` of the doubled domain:
`g = 2F'(0) · J ∘ F ∘ ι − (P(0) − 2R)`. -/
def mapOut (R : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * deriv F 0 * joukowski (F (dblι R z)) - (quot F 0 - ((2 * R : ℝ) : ℂ))

variable {F : ℂ → ℂ} {δ : ℝ}

theorem eq_mul_kappa (hF0 : F 0 = 0) (w : ℂ) : F w = w * kappa F w := by
  have := sub_smul_dslope F 0 w
  rw [sub_zero, hF0, sub_zero, smul_eq_mul] at this
  exact this.symm

theorem kappa_zero : kappa F 0 = deriv F 0 := dslope_same F 0

theorem kappa_eq (w : ℂ) : kappa F w = deriv F 0 + w * kappa2 F w := by
  have := sub_smul_dslope (kappa F) 0 w
  rw [sub_zero, smul_eq_mul, kappa_zero] at this
  rw [kappa2, this]; ring

theorem differentiableOn_kappa (hδ : 0 < δ) (hFd : DifferentiableOn ℂ F (ball 0 δ)) :
    DifferentiableOn ℂ (kappa F) (ball 0 δ) :=
  (Complex.differentiableOn_dslope (ball_mem_nhds 0 hδ)).2 hFd

theorem differentiableOn_kappa2 (hδ : 0 < δ) (hFd : DifferentiableOn ℂ F (ball 0 δ)) :
    DifferentiableOn ℂ (kappa2 F) (ball 0 δ) :=
  (Complex.differentiableOn_dslope (ball_mem_nhds 0 hδ)).2 (differentiableOn_kappa hδ hFd)

theorem kappa_ne_zero (hF0 : F 0 = 0) (hc : deriv F 0 ≠ 0) (hinj : InjOn F (ball 0 δ))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) δ) : kappa F w ≠ 0 := by
  by_cases hw0 : w = 0
  · rw [hw0, kappa_zero]; exact hc
  · intro h
    have h1 := eq_mul_kappa hF0 w
    rw [h, mul_zero, ← hF0] at h1
    exact hw0 (hinj hw (mem_ball_self (pos_of_mem_ball hw)) h1)

theorem differentiableOn_remainder (hδ : 0 < δ) (hFd : DifferentiableOn ℂ F (ball 0 δ))
    (hF0 : F 0 = 0) (hc : deriv F 0 ≠ 0) (hinj : InjOn F (ball 0 δ)) :
    DifferentiableOn ℂ (remainder F) (ball 0 δ) := by
  have hq : DifferentiableOn ℂ (quot F) (ball 0 δ) :=
    (differentiableOn_kappa2 hδ hFd).div (differentiableOn_kappa hδ hFd)
      fun w hw => kappa_ne_zero hF0 hc hinj hw
  exact (hq.sub_const _).sub (hFd.const_mul _)

theorem remainder_zero (hF0 : F 0 = 0) : remainder F 0 = 0 := by
  simp [remainder, hF0]

/-- The algebraic identity behind the expansion: for `ζ ≠ 0` near `0` and `z = 2R − 1/ζ`,
`g(z) = z + r(ζ)`. -/
theorem mapOut_eq (R : ℝ) (hF0 : F 0 = 0) (hc : deriv F 0 ≠ 0) (hinj : InjOn F (ball 0 δ))
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) δ) (hζ0 : ζ ≠ 0) :
    2 * deriv F 0 * joukowski (F ζ) - (quot F 0 - ((2 * R : ℝ) : ℂ)) =
      (((2 * R : ℝ) : ℂ) - ζ⁻¹) + remainder F ζ := by
  have hk := kappa_ne_zero hF0 hc hinj hζ
  have hFe := eq_mul_kappa hF0 ζ
  have hke := kappa_eq (F := F) ζ
  simp only [remainder, quot, joukowski, hFe]
  have hc' : deriv F 0 = kappa F ζ - ζ * kappa2 F ζ := by rw [hke]; ring
  rw [hc']
  field_simp
  ring

theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- Realness of `P = κ₂/κ` on the real axis. -/
theorem im_quot_eq_zero (hδ : 0 < δ) (hFd : DifferentiableOn ℂ F (ball 0 δ))
    (hF0 : F 0 = 0) (hcim : (deriv F 0).im = 0)
    (hre : ∀ t : ℝ, |t| < δ → (F t).im = 0) :
    ∀ t : ℝ, |t| < δ → (quot F t).im = 0 := by
  -- `κ` is real on the real interval
  have hk : ∀ t : ℝ, |t| < δ → (kappa F t).im = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, ofReal_zero, kappa_zero]; exact hcim
    · rw [kappa, dslope_of_ne _ (ofReal_ne_zero.2 ht0), slope_def_field, hF0, sub_zero,
        sub_zero, eq_ofReal_re_of_im_eq_zero (hre t ht), ← ofReal_div]
      simp
  have hk0 : DifferentiableAt ℂ (kappa F) 0 :=
    (differentiableOn_kappa hδ hFd).differentiableAt (ball_mem_nhds 0 hδ)
  have hk2 : ∀ t : ℝ, |t| < δ → (kappa2 F t).im = 0 := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, ofReal_zero, kappa2, dslope_same]
      exact im_deriv_eq_zero_of_im_eq_zero hδ hk0 hk
    · rw [kappa2, dslope_of_ne _ (ofReal_ne_zero.2 ht0), slope_def_field, sub_zero,
        eq_ofReal_re_of_im_eq_zero (hk t ht),
        eq_ofReal_re_of_im_eq_zero (show (kappa F 0).im = 0 by rw [kappa_zero]; exact hcim),
        ← ofReal_sub, ← ofReal_div]
      simp
  intro t ht
  rw [quot, eq_ofReal_re_of_im_eq_zero (hk2 t ht), eq_ofReal_re_of_im_eq_zero (hk t ht),
    ← ofReal_div]
  simp

/-- Realness of the remainder on the real axis. -/
theorem im_remainder_eq_zero (hδ : 0 < δ) (hFd : DifferentiableOn ℂ F (ball 0 δ))
    (hF0 : F 0 = 0) (hcim : (deriv F 0).im = 0)
    (hre : ∀ t : ℝ, |t| < δ → (F t).im = 0) :
    ∀ t : ℝ, |t| < δ → (remainder F t).im = 0 := by
  have hq := im_quot_eq_zero hδ hFd hF0 hcim hre
  intro t ht
  have h0 : |(0 : ℝ)| < δ := by simpa using hδ
  have hq0 := hq 0 h0
  rw [ofReal_zero] at hq0
  rw [remainder, eq_ofReal_re_of_im_eq_zero (hq t ht), eq_ofReal_re_of_im_eq_zero hq0,
    eq_ofReal_re_of_im_eq_zero hcim, eq_ofReal_re_of_im_eq_zero (hre t ht)]
  simp only [← ofReal_sub, ← ofReal_mul]
  simp

end MapOutConstruction

/-- **Existence of the mapping-out function, with its hydrodynamic expansion** ([Law05] §3.4):
a compact `ℍ`-hull has a mapping-out function `g`, and `z (g z − z)` converges at `∞` to a real
number. -/
theorem IsHPHull.exists_isMapOut_tendsto {A : Set ℂ} (hA : IsHPHull A) :
    ∃ g : ℂ → ℂ, ∃ a : ℝ, IsMapOut A g ∧
      Tendsto (fun z => z * (g z - z)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) (𝓝 (a : ℂ)) := by
  obtain ⟨R, hR, hAR⟩ := hA.exists_subset_ball
  obtain ⟨F, hF, hF0, hFre, hFim, hsym⟩ := exists_dblRiemann hA hR hAR
  have hup := bijOn_dblRiemann_upper hA hR hAR hF hF0 hFre hsym
  set δ : ℝ := 1 / (4 * R) with hδ
  have hδpos : 0 < δ := by positivity
  have hBΩ : ball (0 : ℂ) δ ⊆ dblΩ A R := ball_subset_dblΩ hR hAR
  have hFd : DifferentiableOn ℂ F (ball 0 δ) := hF.1.mono hBΩ
  have hinj : InjOn F (ball 0 δ) := hF.2.injOn.mono hBΩ
  have hc0 : deriv F 0 ≠ 0 := fun h => by rw [h] at hFre; simp at hFre
  have hre : ∀ t : ℝ, |t| < δ → (F t).im = 0 := by
    intro t ht
    have htΩ : (t : ℂ) ∈ dblΩ A R := hBΩ (by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ht)
    have := hsym _ htΩ
    rw [conj_ofReal] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  set r := MapOutConstruction.remainder F with hrdef
  have hrd := MapOutConstruction.differentiableOn_remainder hδpos hFd hF0 hc0 hinj
  have hr0 : r 0 = 0 := MapOutConstruction.remainder_zero hF0
  have hrre := MapOutConstruction.im_remainder_eq_zero hδpos hFd hF0 hFim hre
  have hrD : HasDerivAt r (deriv r 0) 0 :=
    (hrd.differentiableAt (ball_mem_nhds 0 hδpos)).hasDerivAt
  have hrim : (deriv r 0).im = 0 := im_deriv_eq_zero_of_im_eq_zero hδpos hrD.differentiableAt hrre
  have hq0 : (MapOutConstruction.quot F 0).im = 0 := by
    have := MapOutConstruction.im_quot_eq_zero hδpos hFd hF0 hFim hre 0 (by simpa using hδpos)
    rwa [ofReal_zero] at this
  set p : ℂ := ((2 * R : ℝ) : ℂ) with hp
  set g := MapOutConstruction.mapOut R F with hgdef
  set S := H \ A with hSdef
  -- conformal bijection
  have hιd : DifferentiableOn ℂ (dblι R) S := by
    intro z hz
    have hz0 : p - z ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      have hz' : 0 < z.im := hz.1
      simp [hp] at this; linarith
    exact ((differentiableAt_const _).sub differentiableAt_id).inv hz0 |>.differentiableWithinAt
  have hmapsι : MapsTo (dblι R) S (dblΩ A R ∩ H) := (bijOn_dblι hA).mapsTo
  have hgd : DifferentiableOn ℂ g S := by
    have h1 : DifferentiableOn ℂ (fun z => F (dblι R z)) S :=
      (hF.1.mono inter_subset_left).comp hιd hmapsι
    have h2 : DifferentiableOn ℂ (fun z => joukowski (F (dblι R z))) S :=
      differentiableOn_joukowski.comp h1 fun z hz => hup.mapsTo (hmapsι hz)
    exact (h2.const_mul _).sub_const _
  have hgb : BijOn g S H := by
    have hb := (QuantumZipper.CA.bijOn_affine_H (a := 2 * (deriv F 0).re)
      (b := -(MapOutConstruction.quot F 0 - p).re) (by linarith)).comp
      (bijOn_joukowski.comp (hup.comp (bijOn_dblι hA)))
    refine hb.congr fun z _ => ?_
    simp only [Function.comp_apply, hgdef, MapOutConstruction.mapOut]
    rw [MapOutConstruction.eq_ofReal_re_of_im_eq_zero hFim]
    have hβ : (MapOutConstruction.quot F 0 - p) =
        (((MapOutConstruction.quot F 0 - p).re : ℝ) : ℂ) :=
      MapOutConstruction.eq_ofReal_re_of_im_eq_zero (by simp [hp, hq0])
    conv_rhs => rw [hβ]
    simp only [ofReal_re]
    push_cast
    ring
  -- the expansion
  have hpz : Tendsto (fun z => p - z) (Bornology.cobounded ℂ ⊓ 𝓟 S) (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono (fun z => ?_)
      (tendsto_atTop_add_const_right _ (-‖p‖)
        (tendsto_norm_cobounded_atTop.mono_left inf_le_left)))
    have := norm_sub_norm_le z p
    rw [norm_sub_rev] at this
    linarith
  have hι : Tendsto (dblι R) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝[≠] 0) :=
    tendsto_inv₀_cobounded'.comp hpz
  have hι' : Tendsto (dblι R) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) :=
    hι.mono_right nhdsWithin_le_nhds
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 S, g z - z = r (dblι R z) := by
    filter_upwards [hι'.eventually (ball_mem_nhds 0 hδpos), mem_inf_of_right (mem_principal_self S)]
      with z hzB hzS
    have h1 := MapOutConstruction.mapOut_eq R hF0 hc0 hinj hzB (dblι_ne_zero hzS.1)
    rw [sub_inv_dblι] at h1
    simp only [hgdef, MapOutConstruction.mapOut]
    rw [h1]; ring
  have hlim0 : Tendsto (fun z => r (dblι R z)) (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 0) := by
    have := hrD.continuousAt.tendsto.comp hι'
    rwa [hr0] at this
  have hslope : Tendsto (fun ζ => ζ⁻¹ * r ζ) (𝓝[≠] 0) (𝓝 (deriv r 0)) := by
    have := hrD.tendsto_slope_zero
    simpa [hr0] using this
  refine ⟨g, -(deriv r 0).re, ⟨⟨hgd, hgb⟩, (hlim0.congr' (hev.mono fun z h => h.symm))⟩, ?_⟩
  have hT : Tendsto (fun z => p * r (dblι R z) - (dblι R z)⁻¹ * r (dblι R z))
      (Bornology.cobounded ℂ ⊓ 𝓟 S) (𝓝 (p * 0 - deriv r 0)) :=
    (hlim0.const_mul p).sub (hslope.comp hι)
  have hval : p * 0 - deriv r 0 = ((-(deriv r 0).re : ℝ) : ℂ) := by
    rw [mul_zero, zero_sub, ofReal_neg, ← MapOutConstruction.eq_ofReal_re_of_im_eq_zero hrim]
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [hev] with z hz
  rw [hz]
  have hz' : p - (dblι R z)⁻¹ = z := sub_inv_dblι
  calc p * r (dblι R z) - (dblι R z)⁻¹ * r (dblι R z)
      = (p - (dblι R z)⁻¹) * r (dblι R z) := by ring
    _ = z * r (dblι R z) := by rw [hz']

theorem IsHPHull.exists_isMapOut {A : Set ℂ} (hA : IsHPHull A) : ∃ g, IsMapOut A g := by
  obtain ⟨g, -, hg, -⟩ := hA.exists_isMapOut_tendsto
  exact ⟨g, hg⟩

end InteractingSLE
