import HigherDimLQGMetric.Collapse.UniformSeparation

/-! # Connecting a weighted path to the collapse set -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

theorem weylDistOn_le_from_tube_contact {X : Type*} [MetricSpace X]
    {Y K : Set X} (hKY : K ⊆ Y)
    {δ : ℝ} (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ →
      ∃ A : ℝ → X, ContinuousOn A (Icc 0 1) ∧ A 0 = p ∧ A 1 = q ∧
        MapsTo A (Icc 0 1) Y ∧ curveLength A 0 1 = edist p q)
    {w : X → ℝ} (hw1 : ∀ p, w p ≤ 1)
    {lam eta T s t : ℝ} (hlam : 0 < lam)
    (hwK : ∀ p ∈ K, w p = lam)
    {P : ℝ → X} (hPc : ContinuousOn P (Icc 0 T))
    (hPY : MapsTo P (Icc 0 T) Y)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hcost : weightedLength w P s t ≤ ENNReal.ofReal (lam * (t - s)))
    {q z : X} (hq : q ∈ K) (_hz : z ∈ K)
    (hclose : dist (P s) q ≤ eta) (hetaδ : eta < δ) :
    weylDistOn w Y (P t) z ≤
      ENNReal.ofReal (lam * (t - s)) + ENNReal.ofReal eta +
        ENNReal.ofReal lam * internalEDist K q z := by
  have hsub : Icc s t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc hs ht
  have hfirst : weylDistOn w Y (P t) (P s) ≤ ENNReal.ofReal (lam * (t - s)) := by
    rw [weylDistOn_comm]
    exact (weylDistOn_le_of_curve hst (hPc.mono hsub)
      (hPY.mono_left hsub)).trans hcost
  have hsecond : weylDistOn w Y (P s) q ≤ ENNReal.ofReal eta := by
    have hreal' := hreal (P s) (hPY ⟨hs, hst.trans ht⟩) q hq
      (hclose.trans_lt hetaδ)
    calc
      weylDistOn w Y (P s) q ≤ edist (P s) q :=
        weylDistOn_le_edist_of_realization hreal' hw1
      _ ≤ ENNReal.ofReal eta := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal hclose
  have hthird := weylDistOn_le_mul_internalEDist hKY hlam hwK q z
  have htri1 := weylDistOn_triangle (w := w) (S := Y) (P t) (P s) z
  have htri2 := weylDistOn_triangle (w := w) (S := Y) (P s) q z
  calc
    weylDistOn w Y (P t) z
        ≤ weylDistOn w Y (P t) (P s) + weylDistOn w Y (P s) z := htri1
    _ ≤ weylDistOn w Y (P t) (P s) +
        (weylDistOn w Y (P s) q + weylDistOn w Y q z) :=
      add_le_add_right htri2 _
    _ = weylDistOn w Y (P t) (P s) + weylDistOn w Y (P s) q +
        weylDistOn w Y q z := by rw [add_assoc]
    _ ≤ ENNReal.ofReal (lam * (t - s)) + ENNReal.ofReal eta +
        ENNReal.ofReal lam * internalEDist K q z :=
      add_le_add (add_le_add hfirst hsecond) hthird

/-- Real form of the contact connection estimate after dividing by `λ`. -/
theorem normalized_contact_real_le {lam eta D : ℝ} {d W : ℝ≥0∞}
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hD : 0 ≤ D) (hd : d ≠ ⊤)
    (hW : W ≤ ENNReal.ofReal (lam * D) + ENNReal.ofReal eta +
      ENNReal.ofReal lam * d) :
    ((ENNReal.ofReal lam)⁻¹ * W).toReal ≤ D + eta / lam + d.toReal := by
  have hterm : ENNReal.ofReal lam * d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd
  have hsum1 : ENNReal.ofReal (lam * D) + ENNReal.ofReal eta ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hsum : ENNReal.ofReal (lam * D) + ENNReal.ofReal eta +
      ENNReal.ofReal lam * d ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsum1, hterm⟩
  have hnorm : (ENNReal.ofReal lam)⁻¹ *
      (ENNReal.ofReal (lam * D) + ENNReal.ofReal eta +
        ENNReal.ofReal lam * d) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr hlam))) hsum
  have hle := ENNReal.toReal_mono hnorm (mul_le_mul_right hW _)
  have hle' : ((ENNReal.ofReal lam)⁻¹ * W).toReal ≤
      lam⁻¹ * (lam * D + eta + lam * d.toReal) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_add hsum1 hterm,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hlam.le,
      ENNReal.toReal_ofReal (mul_nonneg hlam.le hD),
      ENNReal.toReal_ofReal heta] using hle
  calc
    ((ENNReal.ofReal lam)⁻¹ * W).toReal
        ≤ lam⁻¹ * (lam * D + eta + lam * d.toReal) := hle'
    _ = D + eta / lam + d.toReal := by field_simp

end HigherDimLQGMetric
