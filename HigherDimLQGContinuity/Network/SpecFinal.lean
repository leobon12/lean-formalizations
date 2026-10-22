import HigherDimLQGContinuity.Network.SeparationFinal
import HigherDimLQGContinuity.Network.CataloguePower
import HigherDimLQGContinuity.SiteCert.Certificate

/-! # The complete finite plateau network specification -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

/-- The radius-power sum has the half-factor in `b:lem-net`(b). -/
theorem labelNet_radius_sum_half {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : ℝ) (hv : 0 < v)
    (ℓ : q7bLabel S (siteNetCnet S) v) :
    let C := siteConsts S (siteNetCnet S) v
    ∑ p ∈ labelBallSpecs ℓ C.g C.ω, p.2 ^ S.s ≤
      siteNetCnet S * C.ν ^ (-(8 * d : ℝ)) / 2 := by
  let C := siteConsts S (siteNetCnet S) v
  have hsum := labelBallSpecs_radius_sum_power S hd (siteNetCnet S) v hv ℓ
  have hν : 0 < C.ν := siteConsts_ν_pos S hd (siteNetCnet S) v
  have hpow : 0 ≤ C.ν ^ (-(8 * d : ℝ)) := Real.rpow_nonneg hν.le _
  have hcount : 0 ≤ siteNetCountCoeff S := siteNetCountCoeff_nonneg S hd
  have ha : 0 ≤ (1 / 2 : ℝ) ^ S.s := Real.rpow_nonneg (by norm_num) _
  have halt : (1 / 2 : ℝ) ^ S.s < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) S.s_pos
  have hden : 0 < 1 - (1 / 2 : ℝ) ^ S.s := by linarith
  have hfac : 2 ≤ 4 / (1 - (1 / 2 : ℝ) ^ S.s) := by
    apply (le_div_iff₀ hden).2
    linarith
  have hcoef : siteNetCountCoeff S ≤ siteNetCnet S / 2 := by
    unfold siteNetCnet
    nlinarith [mul_nonneg (sub_nonneg.mpr hfac) hcount]
  have hmul := mul_le_mul_of_nonneg_right hcoef hpow
  change (∑ p ∈ labelBallSpecs ℓ C.g C.ω, p.2 ^ S.s) ≤
    siteNetCnet S * C.ν ^ (-(8 * d : ℝ)) / 2
  nlinarith

/-- Each member ball of the finite network lies in the collector interior. -/
theorem labelNet_closedBall_subset_interior {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S (siteNetCnet S) v))
    (hC : SiteConstsC S (siteConsts S (siteNetCnet S) v) v)
    (ℓ : q7bLabel S (siteNetCnet S) v)
    (p : Rd d × ℝ)
    (hp : p ∈ labelBallSpecs ℓ
      (siteConsts S (siteNetCnet S) v).g
      (siteConsts S (siteNetCnet S) v).ω) :
    closedBall p.1 p.2 ⊆ interior (siteC d) := by
  let C := siteConsts S (siteNetCnet S) v
  have hCnet : 0 < siteNetCnet S :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (siteNetCnet_ge_one S hd)
  have hcollar := labelNet_cthickening_subset_interior S hd
    (siteNetCnet S) v hCnet hv hv1 hA hC ℓ
  intro x hx
  have hxU : x ∈ (labelNet S C ℓ).U := by
    change x ∈ closedBallSpecs (labelBallSpecs ℓ C.g C.ω)
    exact mem_iUnion₂.mpr ⟨p, hp, hx⟩
  exact hcollar (self_subset_cthickening _ hxU)

theorem labelNet_edgeOpen_subset {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    openBallSpecs (edgeBallSpecs ℓ e C.g C.ω) ⊆
      (labelNet S C ℓ).Uo := by
  rw [labelNet_Uo_eq_edgeUnion]
  intro x hx
  exact mem_iUnion.mpr ⟨e, hx⟩

theorem labelNet_gateOpen_subset {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) (i : Fin 2) :
    ballUnionOpen C.μ (S.edgeCenter e)
      (labelCellIndices (if i = 0 then (ℓ e).1.gate0 else (ℓ e).1.gate1)) C.g ⊆
      (labelNet S C ℓ).Uo := by
  have h := labelNet_edgeOpen_subset S C ℓ e
  rw [edgeBallSpecs_open_eq] at h
  fin_cases i
  · intro x hx
    apply h
    simp only [mem_union]
    have hx' : x ∈ edgeGateOpen ℓ e 0 C.g := hx
    tauto
  · intro x hx
    apply h
    simp only [mem_union]
    have hx' : x ∈ edgeGateOpen ℓ e 1 C.g := hx
    tauto

theorem labelNet_chamberOpen_subset {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    ballUnionOpen C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) C.ω ⊆
      (labelNet S C ℓ).Uo := by
  have h := labelNet_edgeOpen_subset S C ℓ e
  rw [edgeBallSpecs_open_eq] at h
  intro x hx
  apply h
  simp only [mem_union]
  have hx' : x ∈ edgeChamberOpen ℓ e C.ω := hx
  tauto

/-- The literal ball network supplies every field read by the site
certificate, under the proven scalar clauses (a) and (c). -/
theorem labelNet_spec_of_order {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S (siteNetCnet S) v))
    (hC : SiteConstsC S (siteConsts S (siteNetCnet S) v) v)
    (ℓ : q7bLabel S (siteNetCnet S) v)
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S (siteNetCnet S) v).t₀) :
    Nonempty (Q7bNet S (siteConsts S (siteNetCnet S) v) ℓ) := by
  classical
  let C := siteConsts S (siteNetCnet S) v
  let W := labelNet S C ℓ
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  letI : Fintype (NetworkNode S) := inferInstance
  have hCnet : 0 < siteNetCnet S :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (siteNetCnet_ge_one S hd)
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd (siteNetCnet S) v) _)
  refine ⟨{
    U := W.U
    Uo := W.Uo
    Node := NetworkNode S
    nodeFin := inferInstance
    N := W.Node
    adj := W.adj
    gate0 := fun e => Sum.inr (e, (0 : Fin 3))
    gate1 := fun e => Sum.inr (e, (2 : Fin 3))
    isClosed_U := labelNet_isClosed S C ℓ
    isOpen_Uo := labelNet_isOpen S C ℓ
    Uo_subset_U := labelNet_Uo_subset_U S C ℓ
    thick_subset := labelNet_cthickening_subset_interior S hd
      (siteNetCnet S) v hCnet hv hv1 hA hC ℓ
    isClosed_N := labelNet_node_isClosed S C ℓ
    cover := labelNet_nodes_cover S C ℓ
    sep := labelNet_sep_of_order S hd (siteNetCnet S) v hv hv1 hA ℓ hreal
    star := ?_
    net := ?_
    attach := ?_
    vertex := ?_
    gate0_eq := ?_
    gate1_eq := ?_
    gate0_open := ?_
    gate1_open := ?_
    chamber_open := ?_ }⟩
  · intro T hconn hno
    exact q4_labelNet_star_of_order S hd (siteNetCnet S) v
      hCnet hv hv1 hA hC ℓ T hconn hno
  · intro D hD hDup x hx y hy
    exact labelNet_internal_bound S hd v hv hv1 hA hC ℓ hreal
      D hD hDup x y hx hy
  · intro x hx
    exact labelNet_near_Uo S hd (siteNetCnet S) v hCnet hv hv1 ℓ hx
  · intro u
    exact labelNet_vertex_mem_Uo S hd C ℓ hω u
  · intro e
    rfl
  · intro e
    rfl
  · intro e
    exact labelNet_gateOpen_subset S C ℓ e 0
  · intro e
    exact labelNet_gateOpen_subset S C ℓ e 1
  · intro e
    exact labelNet_chamberOpen_subset S C ℓ e

/-- Blueprint `b:lem-net`: one fixed network constant and threshold work for
every realizable finite label. This includes (4.7), exact incidence, and the
properties consumed by the forcing certificate. -/
theorem labelNet_spec {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    ∃ vsite : ℝ, 0 < vsite ∧ ∀ v : ℝ,
      0 < v → v ≤ vsite →
      ∀ ℓ : q7bLabel S (siteNetCnet S) v,
        IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
          (siteConsts S (siteNetCnet S) v).t₀ →
        Nonempty (Q7bNet S (siteConsts S (siteNetCnet S) v) ℓ) := by
  have hCnet : 0 < siteNetCnet S :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (siteNetCnet_ge_one S hd)
  obtain ⟨vsite, c, Cmax, K, hvsite, hvsite1, hc, hCmax, hK,
    _, _, _, _, hspec⟩ := siteConsts_spec S hd (siteNetCnet S) hCnet
  refine ⟨vsite, hvsite, ?_⟩
  intro v hv hvs ℓ hreal
  have hv1 : v ≤ 1 := (hvs.trans hvsite1).trans (by norm_num)
  obtain ⟨hA, _, hC, _⟩ := hspec v hv hvs
  exact labelNet_spec_of_order S hd v hv hv1 hA hC ℓ hreal

/-- Exact network input for `q7b_siteCert_of_net`. -/
theorem q4_hnet {d : ℕ} (hd : 2 ≤ d) :
    ∀ S : SiteData d, ∃ Cnet : ℝ, 1 ≤ Cnet ∧
      ∀ v : ℝ, Q7bConstOK S (siteConsts S Cnet v) v →
      ∀ ℓ : q7bLabel S Cnet v,
        IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
          (siteConsts S Cnet v).t₀ →
        Nonempty (Q7bNet S (siteConsts S Cnet v) ℓ) := by
  intro S
  refine ⟨siteNetCnet S, siteNetCnet_ge_one S hd, ?_⟩
  intro v hok ℓ hreal
  exact labelNet_spec_of_order S hd v hok.v_pos
    (hok.v_le.trans (by norm_num)) hok.hA hok.hC ℓ hreal

end HigherDimLQGContinuity
