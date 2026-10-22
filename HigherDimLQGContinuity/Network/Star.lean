import HigherDimLQGContinuity.Network.StarGeometry
import HigherDimLQGContinuity.SiteCert.Metric

/-! # Connected node sets without opposite gates -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

/-- Blueprint `b:lem-star`, with the fixed network constant chosen before the
tolerance parameter. -/
theorem labelNet_star {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    ∃ vsite : ℝ, 0 < vsite ∧ ∀ v : ℝ,
      0 < v → v ≤ vsite →
      ∀ {Kc Kl : ℕ}
        (ℓ : SiteLabel S Kc Kl (siteConsts S (siteNetCnet S) v).N
          (siteConsts S (siteNetCnet S) v).μ
          (siteConsts S (siteNetCnet S) v).ν
          (siteConsts S (siteNetCnet S) v).r (Routing.gpC1 4))
        (T : Set (NetworkNode S)),
      ((labelNet S (siteConsts S (siteNetCnet S) v) ℓ).adj.induce T).Connected →
      (∀ e : S.Edge,
        ¬ (Sum.inr (e, (0 : Fin 3)) ∈ T ∧
          Sum.inr (e, (2 : Fin 3)) ∈ T)) →
      ∃ z : Rd d,
        closedBall z (4 * S.mesh.δm) ⊆ siteA d ∧
        (⋃ n ∈ T, cthickening (siteConsts S (siteNetCnet S) v).ς
          ((labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Node n)) ⊆
          closedBall z S.mesh.δm ∧
        ∀ D : ContMetric d,
          DUpper D (siteA d) S.Hup S.s →
          diamIn D (siteA d) (closedBall z S.mesh.δm) ≤
            ENNReal.ofReal (siteEps0 S.mc S.Hlo) := by
  have hCnet : 0 < siteNetCnet S :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (siteNetCnet_ge_one S hd)
  obtain ⟨vsite, c, Cmax, K, hvsite, hvsite1, hc, hCmax, hK,
    _, _, _, _, hspec⟩ := siteConsts_spec S hd (siteNetCnet S) hCnet
  refine ⟨vsite, hvsite, ?_⟩
  intro v hv hvsite' Kc Kl ℓ T hconn hNo
  have hv1 : v ≤ 1 := (hvsite'.trans hvsite1).trans (by norm_num)
  obtain ⟨hA, _, hC, _⟩ := hspec v hv hvsite'
  obtain ⟨z, hzA, hzT⟩ := q4_labelNet_star_of_order S hd
    (siteNetCnet S) v hCnet hv hv1 hA hC ℓ T hconn hNo
  refine ⟨z, hzA, hzT, ?_⟩
  intro D hDup
  have hδ := S.mesh.δm_pos
  refine (q7b_diamIn_closedBall_le hDup hδ hzA).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hH : 0 ≤ S.Hup := by linarith [S.Hup_ge]
  calc
    S.Hup * (2 * S.mesh.δm) ^ S.s ≤
        S.Hup * (10 * Real.sqrt d * S.mesh.δm) ^ S.s := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply Real.rpow_le_rpow (by positivity) _ S.s_pos.le
      nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hδ.le]
    _ ≤ siteEps0 S.mc S.Hlo := S.mesh.access_cost

end HigherDimLQGContinuity
