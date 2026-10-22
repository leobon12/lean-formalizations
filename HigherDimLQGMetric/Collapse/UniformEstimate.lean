import HigherDimLQGMetric.Collapse.Connection

/-! # Uniform normalized distance to the limiting graph geodesic -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Lemma 3.1′(b), estimate (3), for a sequence already selected by Arzelà–Ascoli.
The premise `hparam` is precisely weighted arc-length parametrization and `hconst`
is its constant extension. -/
theorem lemma31_uniform_estimate {X : Type*} [MetricSpace X]
    {Y K : Set X} (hK : IsCompact K) (hKne : K.Nonempty) (hKY : K ⊆ Y)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K))
    {δ : ℝ} (hδ : 0 < δ) (hreal : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ →
      ∃ A : ℝ → X, ContinuousOn A (Icc 0 1) ∧ A 0 = p ∧ A 1 = q ∧
        MapsTo A (Icc 0 1) Y ∧ curveLength A 0 1 = edist p q)
    {lam eta : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n)
    (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (hetaLim : Tendsto eta atTop (𝓝 0))
    {a₀ : ℝ} (ha₀ : 0 < a₀) {w : ℕ → X → ℝ}
    (hw1 : ∀ n p, lam n ≤ w n p ∧ w n p ≤ 1)
    (hwK : ∀ n, ∀ p ∈ K, w n p = lam n)
    (hwoff : ∀ n p, eta n ≤ Metric.infDist p K → a₀ ≤ w n p)
    {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T)
    (Q : Icc (0 : ℝ) T →ᵇ X) (hQK : ∀ t, Q t ∈ K)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
        ENNReal.ofReal (t - s))
    (htail : ∀ t : Icc (0 : ℝ) T, ℓ ≤ t → Q t = Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩)
    {P : ℕ → ℝ → X} {L : ℕ → ℝ}
    (hPc : ∀ n, ContinuousOn (P n) (Icc 0 T))
    (hPY : ∀ n, MapsTo (P n) (Icc 0 T) Y)
    (hstart : ∀ n, Metric.infDist (P n 0) K ≤ eta n)
    (hL0 : ∀ n, 0 ≤ L n) (hLT : ∀ n, L n ≤ T)
    (hL : Tendsto L atTop (𝓝 ℓ))
    (hlim : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => P n t) Q atTop)
    (hparam : ∀ n s t, 0 ≤ s → s ≤ t → t ≤ L n →
      weightedLength (w n) (P n) s t = ENNReal.ofReal (lam n * (t - s)))
    (hconst : ∀ n t, L n ≤ t → t ≤ T → P n t = P n (L n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t : Icc (0 : ℝ) T,
        (ENNReal.ofReal (lam n))⁻¹ *
          weylDistOn (w n) Y (P n t) (Q t) < ENNReal.ofReal ε := by
  have hclamped : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t →
      (internalEDist K ((Set.IccExtend hT Q) s)
        ((Set.IccExtend hT Q) t)).toReal = min t ℓ - min s ℓ :=
    fun s hs t ht hst => intrinsic_distance_eq_clamped_time hT hℓ0 hℓT Q hQK
      hgeo htail hs ht hst
  have he : Tendsto (fun n => lam n * T / a₀) atTop (𝓝 0) := by
    simpa using (hlam.mul_const T).div_const a₀
  have hshort : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ L n →
        dist (P n s) (P n t) ≤ lam n * T / a₀ → t - s < ε :=
    uniform_time_separation hK hKfin hKcont hT Q hQK hclamped hlim hL he hLT
  intro ε hε
  obtain ⟨δK, hδK, hmod⟩ := intrinsic_uniform_small hK hKfin hKcont
    (ε / 4) (by positivity)
  let ρ := min (ε / 4) (δK / 3)
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρeps : ρ ≤ ε / 4 := min_le_left _ _
  have hρδ : ρ ≤ δK / 3 := min_le_right _ _
  have hclose := (Metric.tendstoUniformly_iff.mp hlim) (δK / 3) (by positivity)
  have hηsmall := hetaLim.eventually (eventually_lt_nhds (by positivity : 0 < δK / 3))
  have hηδ := hetaLim.eventually (eventually_lt_nhds hδ)
  have hratio := heta.eventually (eventually_lt_nhds (by positivity : 0 < ε / 4))
  filter_upwards [hshort ρ hρ, hclose, hηsmall, hηδ, hratio] with n hnshort hnclose hnη hnδ hnratio t
  let τ := min (t : ℝ) (L n)
  have hτ0 : 0 ≤ τ := le_min t.2.1 (hL0 n)
  have hτL : τ ≤ L n := min_le_right _ _
  have hτT : τ ≤ T := hτL.trans (hLT n)
  have hPt : P n t = P n τ := by
    by_cases htL : (t : ℝ) ≤ L n
    · simp [τ, min_eq_left htL]
    · have hLt : L n ≤ (t : ℝ) := le_of_not_ge htL
      rw [hconst n t hLt t.2.2]
      simp [τ, min_eq_right hLt]
  have hcontact : ∃ s : ℝ, 0 ≤ s ∧ s ≤ τ ∧
      Metric.infDist (P n s) K ≤ eta n ∧ τ - s < ρ := by
    by_cases hnear : Metric.infDist (P n τ) K ≤ eta n
    · exact ⟨τ, hτ0, le_rfl, hnear, by simpa using hρ⟩
    have hfar : eta n < Metric.infDist (P n τ) K := lt_of_not_ge hnear
    let Qn : ℝ → X := Set.IccExtend hT
      (fun r : Icc (0 : ℝ) T => P n r)
    have hQnc : Continuous Qn := continuous_IccExtend_iff.mpr (hPc n).domRestrict
    have hQneq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) : Qn r = P n r :=
      Set.IccExtend_of_mem hT _ hr
    have hf : Continuous (fun r => Metric.infDist (Qn r) K) :=
      (Metric.continuous_infDist_pt K).comp hQnc
    have hf0 : Metric.infDist (Qn 0) K ≤ eta n := by
      simpa only [hQneq ⟨le_rfl, hT⟩] using hstart n
    have hfτ : eta n < Metric.infDist (Qn τ) K := by
      simpa only [hQneq ⟨hτ0, hτT⟩] using hfar
    obtain ⟨s, hs, hlevel, hoff⟩ := exists_last_level hf hτ0 hf0 hfτ
    have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hτT⟩
    have hcontact' : Metric.infDist (P n s) K ≤ eta n := by
      simpa only [hQneq hsT] using hlevel.le
    have hw : ∀ r ∈ Icc s τ, a₀ ≤ w n (P n r) := by
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hs.1.trans hr.1, hr.2.trans hτT⟩
      exact hwoff n (P n r) (by simpa only [hQneq hrT] using hoff r hr)
    have hcost : weightedLength (w n) (P n) s τ ≤
        ENNReal.ofReal (lam n * (τ - s)) := (hparam n s τ hs.1 hs.2 hτL).le
    have hdist0 := dist_le_cost_div_of_weight_lower ha₀
      (mul_nonneg (hlam0 n).le (sub_nonneg.mpr hs.2)) hs.2 hw hcost
    have hdist : dist (P n s) (P n τ) ≤ lam n * T / a₀ := by
      have hτs : τ - s ≤ T := by linarith [hs.1, hτT]
      have hmul : lam n * (τ - s) / a₀ ≤ lam n * T / a₀ := by
        apply div_le_div_of_nonneg_right _ ha₀.le
        exact mul_le_mul_of_nonneg_left hτs (hlam0 n).le
      exact hdist0.trans hmul
    exact ⟨s, hs.1, hs.2, hcontact', hnshort s τ hs.1 hs.2 hτL hdist⟩
  obtain ⟨s, hs0, hsτ, hsclose, hgap⟩ := hcontact
  obtain ⟨q, hqK, hqdist⟩ := hK.exists_infDist_eq_dist hKne (P n s)
  have hqclose : dist (P n s) q ≤ eta n := by
    rw [← hqdist]
    exact hsclose
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs0, hsτ.trans hτT⟩
  have hqQclose : dist q (Q t) < δK := by
    have hspeed := dist_le_time_of_weighted_cost (hlam0 n) hsτ
      (fun z => (hw1 n z).1) ((hparam n s τ hs0 hsτ hτL).le)
    have htri : dist q (Q t) ≤
        dist q (P n s) + dist (P n s) (P n τ) + dist (P n t) (Q t) := by
      calc
        dist q (Q t) ≤ dist q (P n s) + dist (P n s) (Q t) := dist_triangle _ _ _
        _ ≤ dist q (P n s) + (dist (P n s) (P n τ) + dist (P n τ) (Q t)) :=
          add_le_add_right (dist_triangle _ _ _) _
        _ = _ := by rw [← hPt]; ring
    have hPtQ := hnclose t
    rw [dist_comm] at hPtQ
    rw [dist_comm] at hqclose
    linarith [hρδ]
  have hqKQ : (internalEDist K q (Q t)).toReal < ε / 4 :=
    hmod q hqK (Q t) (hQK t) hqQclose
  have hqKfin : internalEDist K q (Q t) ≠ ⊤ := hKfin q hqK (Q t) (hQK t)
  have hconn : weylDistOn (w n) Y (P n t) (Q t) ≤
      ENNReal.ofReal (lam n * (τ - s)) + ENNReal.ofReal (eta n) +
        ENNReal.ofReal (lam n) * internalEDist K q (Q t) := by
    rw [hPt]
    exact weylDistOn_le_from_tube_contact hKY hreal
      (fun z => (hw1 n z).2) (hlam0 n) (hwK n) (hPc n) (hPY n)
      hs0 hsτ hτT (hparam n s τ hs0 hsτ hτL).le
      hqK (hQK t) hqclose hnδ
  have hrealbound := normalized_contact_real_le (hlam0 n) (heta0 n).le
    (sub_nonneg.mpr hsτ) hqKfin hconn
  have hconnfin : (ENNReal.ofReal (lam n))⁻¹ *
      weylDistOn (w n) Y (P n t) (Q t) ≠ ⊤ := by
    have hterm : ENNReal.ofReal (lam n) * internalEDist K q (Q t) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqKfin
    have hsum : ENNReal.ofReal (lam n * (τ - s)) + ENNReal.ofReal (eta n) +
        ENNReal.ofReal (lam n) * internalEDist K q (Q t) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩, hterm⟩
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (hlam0 n))))
      (ne_top_of_le_ne_top hsum hconn)
  apply (ENNReal.lt_ofReal_iff_toReal_lt hconnfin).2
  linarith [hρeps]

end HigherDimLQGMetric
