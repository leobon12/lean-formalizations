import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.InternalShortcut




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings


 

def OrderedCrossings (g : ℝ → ℝ) (r : ℕ → ℝ) (b : ℝ) :
    ℕ → ℕ → ℝ → Prop
  | 0, _, a => a ≤ b
  | n + 1, k, a =>
      ∃ s t : ℝ, a ≤ s ∧ s ≤ t ∧ t ≤ b ∧
        g s = 2 * r k ∧ g t = r k ∧
        (∀ u ∈ Icc s t, g u ∈ Icc (r k) (2 * r k)) ∧
        OrderedCrossings g r b n (k + 1) t

 

theorem ordered_crossings_of_nested
    (g : ℝ → ℝ) (r : ℕ → ℝ) (b : ℝ)
    (hrpos : ∀ k, 0 < r k)
    (hsep : ∀ k, 2 * r (k + 1) ≤ r k)
    (hmono : ∀ i j, i ≤ j → r j ≤ r i)
    (n k : ℕ) (a : ℝ) (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (ha : 2 * r k ≤ g a)
    (hb : g b ≤ r (k + n - 1)) :
    OrderedCrossings g r b n k a := by
  induction n generalizing k a with
  | zero =>
      exact hab
  | succ n ih =>
      have hlast : r (k + n) ≤ r k :=
        hmono k (k + n) (Nat.le_add_right ..)
      have hgb : g b ≤ r k := by
        have hb' : g b ≤ r (k + n) := by
          simpa only [show k + (n + 1) - 1 = k + n by omega] using hb
        exact hb'.trans hlast
      obtain ⟨s, t, has, hst, htb, hs, ht, hstrip⟩ :=
        LQGMetric.RectCross.exists_sub_crossing'
          hab hg (by linarith [hrpos k]) ha hgb
      have htbcont : ContinuousOn g (Icc t b) :=
        hg.mono (Icc_subset_Icc (has.trans hst) le_rfl)
      have htailstart : 2 * r (k + 1) ≤ g t := by
        rw [ht]
        exact hsep k
      have htailend : g b ≤ r ((k + 1) + n - 1) := by
        simpa only [show (k + 1) + n - 1 = k + (n + 1) - 1 by omega] using hb
      exact ⟨s, t, has, hst, htb, hs, ht, hstrip,
        ih (k + 1) t htb htbcont htailstart htailend⟩

 


theorem sum_cost_le_time_of_ordered
    (g : ℝ → ℝ) (r : ℕ → ℝ) (b : ℝ)
    (lo hi : ℝ) (cost : ℕ → ℝ≥0∞)
    (hcost : ∀ (k : ℕ) (s t : ℝ), lo ≤ s → s ≤ t → t ≤ hi →
      g s = 2 * r k → g t = r k →
      cost k ≤ ENNReal.ofReal (t - s))
    (n k : ℕ) (a : ℝ)
    (hloa : lo ≤ a) (hbhi : b ≤ hi)
    (h : OrderedCrossings g r b n k a) :
    (∑ j ∈ Finset.Ico k (k + n), cost j) ≤
      ENNReal.ofReal (b - a) := by
  induction n generalizing k a with
  | zero =>
      simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty]
      exact bot_le
  | succ n ih =>
      obtain ⟨s, t, has, hst, htb, hs, ht, _, htail⟩ := h
      have hfirst := hcost k s t (hloa.trans has) hst (htb.trans hbhi) hs ht
      have hrest := ih (k + 1) t (hloa.trans (has.trans hst)) htail
      have hsum : (∑ j ∈ Finset.Ico k (k + (n + 1)), cost j) =
          cost k + ∑ j ∈ Finset.Ico (k + 1) ((k + 1) + n), cost j := by
        rw [show k + (n + 1) = (k + 1) + n by omega]
        exact Finset.sum_eq_sum_Ico_succ_bot (by omega) cost
      rw [hsum]
      calc
        cost k + (∑ j ∈ Finset.Ico (k + 1) ((k + 1) + n), cost j)
            ≤ ENNReal.ofReal (t - s) + ENNReal.ofReal (b - t) :=
              add_le_add hfirst hrest
        _ = ENNReal.ofReal (b - s) := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
        _ ≤ ENNReal.ofReal (b - a) :=
          ENNReal.ofReal_le_ofReal (by linarith)

 
def radialAnnulus (z : ℂ) (r : ℕ → ℝ) (hrpos : ∀ k, 0 < r k)
    (k : ℕ) : EuclideanAnnulus :=
  ⟨(z, r k, 2 * r k), hrpos k, by linarith [hrpos k]⟩

 

theorem sum_acrossDist_le_internal_geodesic_time
    (D : LSCMetric) (K : Set ℂ) (hK : IsCompact K)
    (z : ℂ) (r : ℕ → ℝ)
    (hrpos : ∀ k, 0 < r k)
    (hsep : ∀ k, 2 * r (k + 1) ≤ r k)
    (hmono : ∀ i j, i ≤ j → r j ≤ r i)
    {P : ℝ → ℂ} {T a b : ℝ} (n k : ℕ)
    (h0a : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hP : D.IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist (D.pt '' K) (D.pt (P u)) (D.pt (P v)) =
        ENNReal.ofReal (v - u))
    (ha : 2 * r k ≤ dist (P a) z)
    (hb : dist (P b) z ≤ r (k + n - 1)) :
    (∑ j ∈ Finset.Ico k (k + n),
      acrossDist D (radialAnnulus z r hrpos j)) ≤
      ENNReal.ofReal (b - a) := by
  let g : ℝ → ℝ := fun t => dist (P t) z
  have hPcont : ContinuousOn P (Icc a b) :=
    (hP.continuousOn_of_mapsTo hK hPK).mono
      (Icc_subset_Icc h0a hbT)
  have hg : ContinuousOn g (Icc a b) :=
    continuous_dist.comp_continuousOn (hPcont.prodMk continuousOn_const)
  have hcross : OrderedCrossings g r b n k a :=
    ordered_crossings_of_nested g r b hrpos hsep hmono n k a hab hg ha hb
  apply sum_cost_le_time_of_ordered g r b 0 T
    (fun j => acrossDist D (radialAnnulus z r hrpos j))
    _ n k a h0a hbT hcross
  intro j s t h0s hst htT hs ht
  exact TwoScale.Mesh.acrossDist_le_internal_geodesic_time D K hK
    (radialAnnulus z r hrpos j) h0s hst htT hP hPK hgeo
    (by simpa only [g, radialAnnulus, EuclideanAnnulus.outerRadius,
      EuclideanAnnulus.center] using hs.ge)
    (by simpa only [g, radialAnnulus, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.center] using ht.le)


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.OrderedCrossings
