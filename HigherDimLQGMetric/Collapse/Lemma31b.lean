import HigherDimLQGMetric.Collapse.UniformEstimate

/-! # Geodesic part of weighted collapse -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- A weighted curve has zero cost on an interval where it is constant. -/
theorem weightedLength_eq_zero_of_const {w : X → ℝ} {P : ℝ → X}
    {a b : ℝ} {z : X} (hconst : ∀ t ∈ Icc a b, P t = z) :
    weightedLength w P a b = 0 := by
  have hlen : curveLength P a b = 0 := by
    rw [curveLength_congr (Q := fun _ => z) hconst]
    exact eVariationOn.constant_on (by
      rintro _ ⟨t, -, rfl⟩ _ ⟨t', -, rfl⟩
      rfl)
  apply le_antisymm _ bot_le
  calc
    weightedLength w P a b ≤ ENNReal.ofReal (w z) * curveLength P a b :=
      weightedLength_le_ofReal_mul_curveLength (fun t ht => by
        rw [hconst t ht])
    _ = 0 := by rw [hlen, mul_zero]

/-- Lemma 3.1′(b), geodesic extraction. `P n` is a weighted unit-speed geodesic
extended constantly from time `L n`, where `L n` is its normalized weighted distance. -/
theorem lemma31_geodesic_subseq
    (Y K : Set X) (hY : IsCompact Y) (hK : IsCompact K) (hKY : K ⊆ Y)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    (δ : ℝ) (hδ : 0 < δ)
    (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ → ∃ A : ℝ → X,
      ContinuousOn A (Icc 0 1) ∧ A 0 = p ∧ A 1 = q ∧
      MapsTo A (Icc 0 1) Y ∧ curveLength A 0 1 = edist p q)
    (lam eta : ℕ → ℝ) (hlam0 : ∀ n, 0 < lam n) (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n) (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (a₀ : ℝ) (ha₀ : 0 < a₀) (w : ℕ → X → ℝ) (hw : ∀ n, Continuous (w n))
    (hw1 : ∀ n p, lam n ≤ w n p ∧ w n p ≤ 1)
    (hwK : ∀ n, ∀ p ∈ K, w n p = lam n)
    (hwoff : ∀ n p, eta n ≤ Metric.infDist p K → a₀ ≤ w n p)
    (x y u v : ℕ → X) (uLim vLim : X)
    (hx : ∀ n, x n ∈ Y) (hy : ∀ n, y n ∈ Y)
    (hu : ∀ n, u n ∈ K) (hv : ∀ n, v n ∈ K)
    (hxu : ∀ n, dist (x n) (u n) ≤ eta n)
    (hyv : ∀ n, dist (y n) (v n) ≤ eta n)
    (huLim : Tendsto u atTop (𝓝 uLim)) (hvLim : Tendsto v atTop (𝓝 vLim))
    (T : ℝ) (hT : 0 ≤ T)
    (P : ℕ → ℝ → X)
    (hPc : ∀ n, ContinuousOn (P n) (Icc 0 T))
    (hPY : ∀ n, MapsTo (P n) (Icc 0 T) Y)
    (hP0 : ∀ n, P n 0 = x n)
    (hPL : ∀ n, P n
      ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal = y n)
    (hLT : ∀ n,
      ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal ≤ T)
    (hparam : ∀ n s t, 0 ≤ s → s ≤ t →
      t ≤ ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal →
      weightedLength (w n) (P n) s t = ENNReal.ofReal (lam n * (t - s)))
    (hconst : ∀ n t,
      ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal ≤ t →
      t ≤ T → P n t = P n
        ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal) :
    ∃ Q : Icc (0 : ℝ) T →ᵇ X, (∀ t, Q t ∈ K) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => P (φ n) t) Q atTop ∧
        (Set.IccExtend hT Q) 0 = uLim ∧
        (∃ hℓ : (internalEDist K uLim vLim).toReal ∈ Icc (0 : ℝ) T,
          Q ⟨(internalEDist K uLim vLim).toReal, hℓ⟩ = vLim ∧
          (∀ s ∈ Icc (0 : ℝ) (internalEDist K uLim vLim).toReal,
            ∀ t ∈ Icc (0 : ℝ) (internalEDist K uLim vLim).toReal, s ≤ t →
              internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
                ENNReal.ofReal (t - s)) ∧
          (∀ t : Icc (0 : ℝ) T,
            (internalEDist K uLim vLim).toReal ≤ t → Q t = vLim) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
            ∀ t : Icc (0 : ℝ) T,
              (ENNReal.ofReal (lam (φ n)))⁻¹ *
                weylDistOn (w (φ n)) Y (P (φ n) t) (Q t) < ENNReal.ofReal ε) := by
  have hKne : K.Nonempty := ⟨u 0, hu 0⟩
  have huK : uLim ∈ K := hK.isClosed.mem_of_tendsto huLim (Eventually.of_forall hu)
  have hvK : vLim ∈ K := hK.isClosed.mem_of_tendsto hvLim (Eventually.of_forall hv)
  have hdfin : internalEDist K uLim vLim ≠ ⊤ := hKfin uLim huK vLim hvK
  let L : ℕ → ℝ := fun n =>
    ((ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n)).toReal
  have hcollapse := lemma31_collapse Y K hY hK hKY hKfin hKcont δ hδ hreal
    lam eta hlam0 hlam heta0 heta a₀ ha₀ w hw hw1 hwK hwoff
    x y u v uLim vLim hx hy hu hv hxu hyv huLim hvLim
  have hL : Tendsto L atTop (𝓝 (internalEDist K uLim vLim).toReal) :=
    (ENNReal.tendsto_toReal hdfin).comp hcollapse
  have hetaLim : Tendsto eta atTop (𝓝 0) := by
    have hp : Tendsto (fun n => eta n / lam n * lam n) atTop (𝓝 0) := by
      simpa using heta.mul hlam
    have heq : (fun n => eta n / lam n * lam n) = eta := by
      funext n
      exact div_mul_cancel₀ _ (ne_of_gt (hlam0 n))
    simpa only [heq] using hp
  have hxLim : Tendsto x atTop (𝓝 uLim) := by
    have hd : Tendsto (fun n => dist (u n) (x n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [dist_comm] using hxu n)
      exact hetaLim
    exact huLim.congr_dist hd
  have hyLim : Tendsto y atTop (𝓝 vLim) := by
    have hd : Tendsto (fun n => dist (v n) (y n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => dist_nonneg) (fun n => by simpa [dist_comm] using hyv n)
      exact hetaLim
    exact hvLim.congr_dist hd
  have hL0 : ∀ n, 0 ≤ L n := fun n => ENNReal.toReal_nonneg
  have htotal : ∀ n, weightedLength (w n) (P n) 0 T ≤
      ENNReal.ofReal (lam n * L n) := by
    intro n
    have htailzero : weightedLength (w n) (P n) (L n) T = 0 :=
      weightedLength_eq_zero_of_const (fun t ht => hconst n t ht.1 ht.2)
    have hsum := weightedLength_add (w := w n) (P := P n) (hL0 n) (hLT n)
    rw [htailzero, add_zero] at hsum
    rw [← hsum]
    simpa only [sub_zero] using (hparam n 0 (L n) le_rfl (hL0 n) le_rfl).le
  have hspeed : ∀ n, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      dist (P n s) (P n t) ≤ dist s t := by
    intro n
    exact normalized_path_lipschitz (hlam0 n) (fun z => (hw1 n z).1)
      (hparam n) (hconst n)
  have hcostlim : Tendsto (fun n => eta n + lam n * L n / a₀) atTop (𝓝 0) := by
    have hprod : Tendsto (fun n => lam n * L n) atTop (𝓝 0) := by
      simpa using hlam.mul hL
    convert hetaLim.add (hprod.div_const a₀) using 1
    simp
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (0 : ℝ) T, Metric.infDist (P n t) K < ε := by
    intro ε hε
    filter_upwards [hcostlim.eventually (eventually_lt_nhds hε)] with n hn t ht
    have hstart : Metric.infDist (P n 0) K ≤ eta n := by
      rw [hP0]
      exact (Metric.infDist_le_dist_of_mem (hu n)).trans (hxu n)
    have hb := infDist_le_eta_add_cost_div_on hT (hPc n) ha₀
      (mul_nonneg (hlam0 n).le (hL0 n)) hstart (hwoff n) (htotal n) t ht
    exact hb.trans_lt hn
  have hend : internalEDist K uLim vLim =
      ENNReal.ofReal (internalEDist K uLim vLim).toReal :=
    (ENNReal.ofReal_toReal hdfin).symm
  obtain ⟨Q, hQK, φ, hφ, hlim, hQ0, hℓ, hQℓ, hgeo, htail⟩ :=
    collapse_geodesic_subseq hY hK hKne hT hL0 hLT hL hPc hPY
      hspeed hnear hP0 hPL hconst hxLim hyLim hend
  have hest := lemma31_uniform_estimate hK hKne hKY hKfin hKcont hδ hreal
    (lam := lam ∘ φ) (eta := eta ∘ φ)
    (fun n => hlam0 (φ n)) (hlam.comp hφ.tendsto_atTop)
    (fun n => heta0 (φ n)) (heta.comp hφ.tendsto_atTop)
    (hetaLim.comp hφ.tendsto_atTop) ha₀
    (w := w ∘ φ)
    (fun n z => hw1 (φ n) z) (fun n z hz => hwK (φ n) z hz)
    (fun n z hz => hwoff (φ n) z hz)
    hT hℓ.1 hℓ.2 Q hQK hgeo
    (fun t ht => (htail t ht).trans hQℓ.symm)
    (P := P ∘ φ) (L := L ∘ φ)
    (fun n => hPc (φ n)) (fun n => hPY (φ n))
    (fun n => by
      change Metric.infDist (P (φ n) 0) K ≤ eta (φ n)
      rw [hP0]
      exact (Metric.infDist_le_dist_of_mem (hu (φ n))).trans (hxu (φ n)))
    (fun n => hL0 (φ n)) (fun n => hLT (φ n)) (hL.comp hφ.tendsto_atTop)
    hlim (fun n s t hs hst htL => hparam (φ n) s t hs hst htL)
    (fun n t hnt htT => hconst (φ n) t hnt htT)
  exact ⟨Q, hQK, φ, hφ, hlim, hQ0,
    ⟨hℓ, hQℓ, hgeo, htail, fun ε hε => hest ε hε⟩⟩

end HigherDimLQGMetric
