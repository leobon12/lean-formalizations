import HigherDimLQGMetric.Config.Relations

/-! The deterministic collar estimate behind configuration upper moduli. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology LQGMetric.MetricGeometry
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem config_internalC_eq_ambient_of_collar
    (D : ContMetric d) (hD : D.IsLength)
    {U O K : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hO : IsOpen O) (hKO : K ⊆ O) (hOU : O ⊆ U)
    {a : ℝ} (ha : 0 < a)
    (hsep : ∀ u ∈ K, ∀ v ∈ frontier O, a ≤ D.1 (u, v))
    (u v : U) (hu : u.1 ∈ K) (_hv : v.1 ∈ K)
    (hnear : D.1 (u.1, v.1) < a) :
    internalC D hD hU hUc (u, v) = D.1 (u.1, v.1) := by
  have hcost : ENNReal.ofReal a ≤
      Metric.infEDist (D.pt u.1) (D.pt '' frontier O) := by
    apply Metric.le_infEDist.mpr
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [D.edist_pt]
    exact ENNReal.ofReal_le_ofReal (hsep u.1 hu z hz)
  have hshort : edist (D.pt u.1) (D.pt v.1) <
      Metric.infEDist (D.pt u.1) (D.pt '' frontier O) := by
    rw [D.edist_pt]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).2 hnear |>.trans_le hcost
  have hOeq := (ContMetric.internal_eq_of_lt_infEDist_frontier hD hO
    (hKO hu) hshort).2
  have hUeq : D.internal U u.1 v.1 = ENNReal.ofReal (D.1 (u.1, v.1)) := by
    apply le_antisymm
    · exact (D.internal_anti hOU u.1 v.1).trans (by simpa [D.edist_pt] using hOeq.le)
    · exact D.ofReal_le_internal U u.1 v.1
  change (D.internal U u.1 v.1).toReal = _
  rw [hUeq, ENNReal.toReal_ofReal (D.nonneg u.1 v.1)]

theorem config_internalC_upper_modulus_of_collar
    (D : ContMetric d) (hD : D.IsLength)
    {U O K : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hO : IsOpen O) (hKO : K ⊆ O) (hOU : O ⊆ U)
    {a θ η : ℝ} (ha : 0 < a) (hθa : θ < a)
    (hsep : ∀ u ∈ K, ∀ v ∈ frontier O, a ≤ D.1 (u, v))
    (hsmall : ∀ u ∈ K, ∀ v ∈ K, dist u v ≤ η → D.1 (u, v) ≤ θ)
    (p q : U × U) (hp₁ : p.1.1 ∈ K) (hp₂ : p.2.1 ∈ K)
    (hq₁ : q.1.1 ∈ K) (hq₂ : q.2.1 ∈ K)
    (hnear : dist p.1.1 q.1.1 ≤ η ∧ dist p.2.1 q.2.1 ≤ η) :
    dist (internalC D hD hU hUc p) (internalC D hD hU hUc q) ≤ 2 * θ := by
  let ρ := internalC D hD hU hUc
  have hρ : IsMetricFun ρ := config_internalC_isMetricFun D hD hU hUc
  have hD₁ := hsmall p.1.1 hp₁ q.1.1 hq₁ hnear.1
  have hD₂ := hsmall p.2.1 hp₂ q.2.1 hq₂ hnear.2
  have hρ₁ : ρ (p.1, q.1) ≤ θ := by
    rw [config_internalC_eq_ambient_of_collar D hD hU hUc hO hKO hOU ha
      hsep p.1 q.1 hp₁ hq₁ (hD₁.trans_lt hθa)]
    exact hD₁
  have hρ₂ : ρ (p.2, q.2) ≤ θ := by
    rw [config_internalC_eq_ambient_of_collar D hD hU hUc hO hKO hOU ha
      hsep p.2 q.2 hp₂ hq₂ (hD₂.trans_lt hθa)]
    exact hD₂
  have htri₁ : ρ p ≤ ρ (p.1, q.1) + ρ q + ρ (p.2, q.2) := by
    have h₁ := hρ.triangle p.1 q.1 p.2
    have h₂ := hρ.triangle q.1 q.2 p.2
    rw [hρ.symm q.2 p.2] at h₂
    linarith
  have htri₂ : ρ q ≤ ρ (p.1, q.1) + ρ p + ρ (p.2, q.2) := by
    have h₁ := hρ.triangle q.1 p.1 q.2
    have h₂ := hρ.triangle p.1 p.2 q.2
    rw [hρ.symm q.1 p.1] at h₁
    linarith
  rw [Real.dist_eq]
  apply abs_le.mpr
  constructor <;> linarith

end HigherDimLQGMetric
