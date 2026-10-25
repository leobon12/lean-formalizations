import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.ScaleF3
import SupercriticalLQGUniqueness.Uniqueness.Objects.ShieldLocality.ShieldScale




set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

theorem block_geodesic_iff_of_scale (E E' : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hscale : ∀ x y : ℂ, E' (x,y) = ENNReal.ofReal k * E (x,y))
    (K : Set ℂ) (u v : ℂ) :
    (∃ (P : ℝ → ℂ) (a b : ℝ), E'.IsCurve P a b ∧ P a = u ∧ P b = v ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧ E'.len P a b = E' (u,v)) ↔
    (∃ (P : ℝ → ℂ) (a b : ℝ), E.IsCurve P a b ∧ P a = u ∧ P b = v ∧
      (∀ s ∈ Icc a b, P s ∈ K) ∧ E.len P a b = E (u,v)) := by
  have hc0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
  have hcTop : ENNReal.ofReal k ≠ ∞ := ENNReal.ofReal_ne_top
  constructor
  · rintro ⟨P,a,b,hP,ha,hb,htrace,hlen⟩
    refine ⟨P,a,b,(Positivity.Witnesses.isCurve_iff_of_dist_scale E E' _ hc0 hcTop hscale P a b).mp hP,
      ha,hb,htrace,?_⟩
    rw [Positivity.Witnesses.len_eq_mul_of_dist_scale E E' _ hscale P a b, hscale u v] at hlen
    exact (ENNReal.mul_right_inj hc0 hcTop).mp hlen
  · rintro ⟨P,a,b,hP,ha,hb,htrace,hlen⟩
    refine ⟨P,a,b,(Positivity.Witnesses.isCurve_iff_of_dist_scale E E' _ hc0 hcTop hscale P a b).mpr hP,
      ha,hb,htrace,?_⟩
    rw [Positivity.Witnesses.len_eq_mul_of_dist_scale E E' _ hscale P a b, hscale u v, hlen]

 

theorem blockRaw_iff_of_common_scale (C : Objects.CorrectedEvent.Constants)
    (T : Objects.CorrectedEvent.TubeData) (Ksh : ℕ) (Cmid0 : ℝ)
    (D E D' E' : LSCMetric) (k : ℝ) (hk : 0 < k)
    (hD : ∀ x y : ℂ, D' (x,y) = ENNReal.ofReal k * D (x,y))
    (hE : ∀ x y : ℂ, E' (x,y) = ENNReal.ofReal k * E (x,y))
    (g : LQGMetric.DistC) :
    Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D') (fun _ => E') g ↔
      Objects.Excursions.blockRaw C T Ksh Cmid0 (fun _ => D) (fun _ => E) g := by
  have hc0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
  have hcTop : ENNReal.ofReal k ≠ ∞ := ENNReal.ofReal_ne_top
  have hshield := Objects.ShieldLocality.shield_iff_of_dist_scale C T Ksh D D'
    (ENNReal.ofReal k) hc0 hcTop hD
  have hratio (u v : ℂ) :
      E' (u,v) ≤ ENNReal.ofReal Cmid0 * D' (u,v) ↔
      E (u,v) ≤ ENNReal.ofReal Cmid0 * D (u,v) := by
    rw [hE u v, hD u v, mul_left_comm]
    exact ENNReal.mul_le_mul_iff_right hc0 hcTop
  have hfin (u v : ℂ) : E' (u,v) < ⊤ ↔ E (u,v) < ⊤ := by
    rw [hE u v]
    constructor
    · intro h
      exact ENNReal.lt_top_of_mul_ne_top_right h.ne hc0
    · intro h
      exact ENNReal.mul_lt_top hcTop.lt_top h
  constructor
  · rintro ⟨⟨u,v,h1,h2,h3,h4,h5,h6,h7,⟨hu,h8⟩,⟨hv,h9⟩⟩,hs⟩
    refine ⟨⟨u,v,h1,h2,h3,h4,(hratio u v).mp h5,(hfin u v).mp h6,
      (block_geodesic_iff_of_scale E E' k hk hE _ u v).mp h7,
      ⟨hu,?_⟩,⟨hv,?_⟩⟩,hshield.mp hs⟩
    · rw [← goodSet_eq_of_common_scale D E D' E' k C.lamConst hk hD hE
        (Objects.Excursions.cU T) u u v T.blockRadius hu]
      exact h8
    · rw [← goodSet_eq_of_common_scale D E D' E' k C.lamConst hk hD hE
        (Objects.Excursions.cV T) v u v T.blockRadius hv]
      exact h9
  · rintro ⟨⟨u,v,h1,h2,h3,h4,h5,h6,h7,⟨hu,h8⟩,⟨hv,h9⟩⟩,hs⟩
    refine ⟨⟨u,v,h1,h2,h3,h4,(hratio u v).mpr h5,(hfin u v).mpr h6,
      (block_geodesic_iff_of_scale E E' k hk hE _ u v).mpr h7,
      ⟨hu,?_⟩,⟨hv,?_⟩⟩,hshield.mpr hs⟩
    · rw [goodSet_eq_of_common_scale D E D' E' k C.lamConst hk hD hE
        (Objects.Excursions.cU T) u u v T.blockRadius hu]
      exact h8
    · rw [goodSet_eq_of_common_scale D E D' E' k C.lamConst hk hD hE
        (Objects.Excursions.cV T) v u v T.blockRadius hv]
      exact h9

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
