import QuantumZipper.Proofs.Complex.KernelChordStatement
import QuantumZipper.Proofs.Complex.UniformizerTopo

/-!
# The doubled left domain of a chord (EXT-CA KT2, inputs R and K: topology)

For a simple chord `η`, `leftDoubled η = D₁ ∪ conj D₁ ∪ (−∞,0)` is open
(`isOpen_leftDoubled`), connected (`isConnected_leftDoubled`), contains `−1`, is not `ℂ`, and
contains a disk around every negative real point (`exists_ball_subset_leftDoubled`). These are
the non-degeneracy clauses of kernel convergence (Pommerenke, *Boundary Behaviour of Conformal
Maps* (1992), p. 13) and the openness clause of input R. Own elementary proofs from the U1
topology of `UniformizerTopo.lean`.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA.Uniformizer
open scoped ComplexConjugate

namespace QuantumZipper.CA.Kernel

variable {η : ℝ → ℂ}

theorem conj_image_eq_preimage (S : Set ℂ) : (starRingEnd ℂ) '' S = (starRingEnd ℂ) ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa using hw
  · intro h; exact ⟨conj z, h, conj_conj z⟩

theorem mem_leftComponent_of_near_neg (hη : IsSimpleChord η) {x : ℝ} (hx : x < 0) :
    ∃ δ > 0, ∀ w ∈ H, dist w (x : ℂ) < δ → w ∈ leftComponent η := by
  obtain ⟨δ, hδ, h⟩ := exists_nhd_mem_cc hη hx
  exact ⟨δ, hδ, fun w hw hd => (leftComponent_eq hη).symm ▸ h w hw hd⟩

/-- A disk around each negative real point lies in the doubled domain. -/
theorem exists_ball_subset_leftDoubled (hη : IsSimpleChord η) {x : ℝ} (hx : x < 0) :
    ∃ δ > 0, ball (x : ℂ) δ ⊆ leftDoubled η := by
  obtain ⟨δ, hδ, h⟩ := mem_leftComponent_of_near_neg hη hx
  refine ⟨min δ (-x), lt_min hδ (by linarith), fun w hw => ?_⟩
  have hw1 : dist w (x : ℂ) < δ := lt_of_lt_of_le hw (min_le_left _ _)
  have hw2 : dist w (x : ℂ) < -x := lt_of_lt_of_le hw (min_le_right _ _)
  rcases lt_trichotomy w.im 0 with him | him | him
  · refine Or.inl (Or.inr ⟨conj w, h _ ?_ ?_, conj_conj w⟩)
    · show 0 < (conj w).im; rw [conj_im]; linarith
    · rw [← conj_ofReal, dist_conj_conj]; exact hw1
  · refine Or.inr ⟨him, ?_⟩
    have : |w.re - x| < -x := by
      have := abs_re_le_norm (w - x)
      rw [dist_eq_norm] at hw2
      simp only [sub_re, ofReal_re] at this
      linarith
    have := (abs_lt.1 this).2
    linarith
  · exact Or.inl (Or.inl (h w him hw1))

theorem isOpen_leftDoubled (hη : IsSimpleChord η) : IsOpen (leftDoubled η) := by
  have hL := isOpen_leftComponent hη
  have hC : IsOpen ((starRingEnd ℂ) '' leftComponent η) := by
    rw [conj_image_eq_preimage]; exact hL.preimage continuous_conj
  rw [isOpen_iff_mem_nhds]
  rintro z ((hz | hz) | ⟨h0, hneg⟩)
  · exact mem_of_superset (hL.mem_nhds hz) fun _ h => Or.inl (Or.inl h)
  · exact mem_of_superset (hC.mem_nhds hz) fun _ h => Or.inl (Or.inr h)
  · obtain ⟨δ, hδ, hsub⟩ := exists_ball_subset_leftDoubled hη hneg
    have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hz]
    exact mem_of_superset (ball_mem_nhds _ hδ) hsub

theorem leftDoubled_ne_univ : leftDoubled η ≠ univ := by
  intro h
  have h0 : (0 : ℂ) ∈ leftDoubled η := h ▸ mem_univ _
  rcases h0 with (h0 | ⟨w, hw, hw0⟩) | ⟨-, h0⟩
  · have : (0 : ℂ).im > 0 := leftComponent_subset_H η h0
    simp at this
  · have : 0 < w.im := leftComponent_subset_H η hw
    have h' : w = 0 := by simpa using hw0
    rw [h'] at this; simp at this
  · simp at h0

theorem isConnected_leftDoubled (hη : IsSimpleChord η) : IsConnected (leftDoubled η) := by
  obtain ⟨δ, hδ, hsub⟩ := exists_ball_subset_leftDoubled hη (x := -1) (by norm_num)
  obtain ⟨δ', hδ', hnear⟩ := mem_leftComponent_of_near_neg hη (x := -1) (by norm_num)
  set r := min δ δ' / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrδ : r < δ := by rw [hr]; linarith [min_le_left δ δ']
  have hrδ' : r < δ' := by rw [hr]; linarith [min_le_right δ δ']
  set p : ℂ := -1 + (r : ℂ) * I with hp
  have hpd : dist p ((-1 : ℝ) : ℂ) = r := by
    rw [hp, dist_eq_norm]; push_cast
    rw [show -1 + (r : ℂ) * I - -1 = (r : ℂ) * I by ring, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hpH : p ∈ H := by show 0 < p.im; simp [hp, hr0]
  have hpL : p ∈ leftComponent η := hnear p hpH (by rw [hpd]; exact hrδ')
  have hpB : p ∈ ball ((-1 : ℝ) : ℂ) δ := by rw [mem_ball, hpd]; exact hrδ
  have hcpB : conj p ∈ ball ((-1 : ℝ) : ℂ) δ := by
    rw [mem_ball, ← conj_ofReal, dist_conj_conj, hpd]; exact hrδ
  have hm1B : ((-1 : ℝ) : ℂ) ∈ ball ((-1 : ℝ) : ℂ) δ := mem_ball_self hδ
  have hL := isPreconnected_leftComponent hη
  have hC : IsPreconnected ((starRingEnd ℂ) '' leftComponent η) :=
    hL.image _ continuous_conj.continuousOn
  have hA : IsPreconnected {z : ℂ | z.im = 0 ∧ z.re < 0} := by
    have : {z : ℂ | z.im = 0 ∧ z.re < 0} = ((↑) : ℝ → ℂ) '' Iio 0 := by
      ext z; constructor
      · rintro ⟨h0, h1⟩; exact ⟨z.re, h1, Complex.ext (by simp) (by simp [h0])⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨by simp, by simpa using hx⟩
    rw [this]
    exact isPreconnected_Iio.image _ continuous_ofReal.continuousOn
  have hB := (convex_ball ((-1 : ℝ) : ℂ) δ).isPreconnected
  have h1 := hB.union p hpB hpL hL
  have h2 := h1.union (conj p) (Or.inl hcpB)
    (show conj p ∈ (starRingEnd ℂ) '' leftComponent η from ⟨p, hpL, rfl⟩) hC
  have h3 := h2.union ((-1 : ℝ) : ℂ) (Or.inl (Or.inl hm1B))
    (show ((-1 : ℝ) : ℂ) ∈ {z : ℂ | z.im = 0 ∧ z.re < 0} from ⟨by simp, by simp⟩) hA
  have heq : ball ((-1 : ℝ) : ℂ) δ ∪ leftComponent η ∪ (starRingEnd ℂ) '' leftComponent η ∪
      {z : ℂ | z.im = 0 ∧ z.re < 0} = leftDoubled η := by
    apply Subset.antisymm
    · rintro z (((hz | hz) | hz) | hz)
      · exact hsub hz
      · exact Or.inl (Or.inl hz)
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
    · rintro z ((hz | hz) | hz)
      · exact Or.inl (Or.inl (Or.inr hz))
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
  rw [heq] at h3
  exact ⟨⟨-1, neg_one_mem_leftDoubled η⟩, h3⟩

end QuantumZipper.CA.Kernel
