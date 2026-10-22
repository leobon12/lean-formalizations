import HigherDimLQGContinuity.SiteCert.Arc
import HigherDimLQGContinuity.SiteCert.Bump

/-!
# The forcing certificate of a valid label (packet Q7b; Part B `b:thm-sitecert`(iv))

Source: blueprint Part B, proof of `b:thm-sitecert`(iv), items (C1)–(C10), for a **length** primary metric (IA1
MAJOR-2, ruling N20, erratum EB22). The plateau network of the label enters through `Q7bNet`, which records the
properties of Part B's network that the certificate reads: `b:def-net` (the gate nodes are the closed gate unions;
the open gate and chamber cores lie in the open core), `b:lem-net`(a)–(c) (closedness, `U^{+ς} ⊆ int C`, the node
cover, the network bound `D(x, y; U°) ≤ A_net` for a length metric with the primary doubled-ball reference, the
attachments within `2ς`, every tree vertex in `U°`), `b:lem-sep` and `b:lem-star` (connected node sets without
opposite gates lie in one ball `B̄_{δ_m}(z)` with `B̄_{4δ_m}(z) ⊆ A`). It is instantiated with the label network of
packet Q4 in the final assembly.

`q7b_forcingCert`: for a label `ℓ` with a network `net`, the profile `ψ_ℓ = plateauBump U_ℓ ς` (`b:def-bump`),
`ξ > 0`, a length metric `D` and `SiteSource_ℓ(D, E)` (Q5's `labelSource`), the frozen `ForcingCert` holds with
`f = M_ξ ψ_ℓ`, `M_ξ = ξ⁻¹ log θ⁻¹`, the scales of `siteConsts`, `ε₀ = siteEps0`, `aout = siteAout`, `H = H_lo` and
`d₀` of (F6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-- **The plateau network of one label** with the properties that the certificate reads (Part B `b:def-net`,
`b:lem-net`(a)–(c), `b:lem-sep`, `b:lem-star`), for the cell sets of the label `ℓ` at the constants `C`. -/
structure Q7bNet (S : SiteData d) (C : SiteConsts) {Kc Kl N : ℕ} {r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N C.μ C.ν r c₁) where
  /-- the closed plateau `U_ℓ` -/
  U : Set (Rd d)
  /-- the open core `U°_ℓ` -/
  Uo : Set (Rd d)
  /-- the nodes -/
  Node : Type
  nodeFin : Fintype Node
  N : Node → Set (Rd d)
  adj : SimpleGraph Node
  /-- the two gates of each tree edge -/
  gate0 : S.Edge → Node
  gate1 : S.Edge → Node
  isClosed_U : IsClosed U
  isOpen_Uo : IsOpen Uo
  Uo_subset_U : Uo ⊆ U
  thick_subset : cthickening C.ς U ⊆ interior (siteC d)
  isClosed_N : ∀ n, IsClosed (N n)
  cover : U ⊆ ⋃ n, N n
  sep : ∀ n n', n ≠ n' → ¬ adj.Adj n n' → ∀ x ∈ N n, ∀ y ∈ N n', C.δsep ≤ dist x y
  star : ∀ T : Set Node, (adj.induce T).Connected → (∀ e, ¬ (gate0 e ∈ T ∧ gate1 e ∈ T)) →
    ∃ z : Rd d, closedBall z (4 * S.mesh.δm) ⊆ siteA d ∧
      (⋃ n ∈ T, cthickening C.ς (N n)) ⊆ closedBall z S.mesh.δm
  net : ∀ D : ContMetric d, D.IsLength → DUpper D (siteA d) S.Hup S.s →
    ∀ x ∈ Uo, ∀ y ∈ Uo, D.internal Uo x y ≤ ENNReal.ofReal C.Anet
  attach : ∀ x ∈ cthickening C.ς U, ∃ y ∈ Uo, dist x y ≤ 2 * C.ς
  vertex : ∀ v : S.Vertex, S.vertexPoint v ∈ Uo
  gate0_eq : ∀ e, N (gate0 e) = ballUnion C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate0) C.g
  gate1_eq : ∀ e, N (gate1 e) = ballUnion C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate1) C.g
  gate0_open : ∀ e, ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate0) C.g ⊆ Uo
  gate1_open : ∀ e, ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate1) C.g ⊆ Uo
  chamber_open : ∀ e, ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.chamber) C.ω ⊆ Uo

/-- `ballUnionOpen` is open. -/
theorem q7b_isOpen_ballUnionOpen (μ : ℝ) (o : Rd d) (Q : Finset (Fin d → ℤ)) (t : ℝ) :
    IsOpen (ballUnionOpen μ o Q t) :=
  isOpen_biUnion fun _ _ => isOpen_ball

/-- `(C3)` access: a collector point is within `4√d δ_m` of a tree vertex, which lies in the open core; the
doubled-ball reference and (F3) bound the `A`-internal distance by `ε₀`. -/
theorem q7b_access {S : SiteData d} (hd : 2 ≤ d) {D : ContMetric d}
    (hDup : DUpper D (siteA d) S.Hup S.s) {Uo : Set (Rd d)} (hvert : ∀ v : S.Vertex, S.vertexPoint v ∈ Uo) :
    ∀ x ∈ siteC d, ∃ y ∈ Uo, D.internal (siteA d) x y ≤ ENNReal.ofReal (siteEps0 S.mc S.Hlo) := by
  intro x hx
  obtain ⟨v, hv⟩ := (siteMesh_geometry S hd).collector_cover x hx
  refine ⟨S.vertexPoint v, hvert v, ?_⟩
  have hδ := S.mesh.δm_pos
  have hsq : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ d by omega))
  have hsmall := S.mesh.δm_small
  set ρ : ℝ := 5 * Real.sqrt d * S.mesh.δm with hρ
  have hρ0 : 0 < ρ := by positivity
  have hball : closedBall x (2 * ρ) ⊆ siteA d := q7b_closedBall_subset_siteA hx (by rw [hρ]; nlinarith)
  have hy : S.vertexPoint v ∈ ball x ρ := by
    rw [mem_ball, dist_comm]
    calc dist x (S.vertexPoint v) ≤ 4 * Real.sqrt d * S.mesh.δm := hv
      _ < ρ := by rw [hρ]; nlinarith
  refine (q4_internal_le_of_doubled_ball D hDup hρ0 hball (ball_subset_closedBall.trans hball)
    (mem_ball_self hρ0) hy).trans (ENNReal.ofReal_le_ofReal ?_)
  have hH : 0 ≤ S.Hup := by linarith [S.Hup_ge]
  calc S.Hup * ρ ^ S.s ≤ S.Hup * (10 * Real.sqrt d * S.mesh.δm) ^ S.s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hρ0.le (by rw [hρ]; nlinarith) S.s_pos.le) hH
    _ ≤ siteEps0 S.mc S.Hlo := S.mesh.access_cost

/-- **The forcing certificate of a valid label** (Part B `b:thm-sitecert`(iv), (C1)–(C10)). -/
theorem q7b_forcingCert {S : SiteData d} (hd : 2 ≤ d) {C : SiteConsts} {v : ℝ} (hok : Q7bConstOK S C v)
    {Kc Kl N : ℕ} {r c₁ : ℝ} {ℓ : SiteLabel S Kc Kl N C.μ C.ν r c₁} (net : Q7bNet S C ℓ)
    (prof : C(Rd d, ℝ)) (hprof : ∀ x, prof x = plateauBump net.U C.ς hok.ς_pos x)
    {ξ : ℝ} (hξ : 0 < ξ) {D E : ContMetric d} (hD : D.IsLength) (hsrc : labelSource S C.t₀ v ℓ D E) :
    Nonempty (ForcingCert D E ((ξ⁻¹ * Real.log C.θ⁻¹) • prof) ξ (ξ⁻¹ * Real.log C.θ⁻¹) C.θ C.ς C.δsep
      (siteEps0 S.mc S.Hlo) C.enet C.eatt (siteAout S.mc S.Hlo) S.Hlo S.b v S.seed.d₀) := by
  obtain ⟨hRefs, hedge⟩ := hsrc
  obtain ⟨hDup, hlow, hcol1, hcol2, -⟩ := hRefs
  have := q7b_finite_edge S
  set M : ℝ := ξ⁻¹ * Real.log C.θ⁻¹ with hM
  have hθ := hok.θ_pos
  have hθ1 := hok.θ_lt
  have hlog : 0 ≤ Real.log C.θ⁻¹ := Real.log_nonneg (one_le_inv₀ hθ |>.2 hθ1.le)
  have hM0 : 0 ≤ M := mul_nonneg (inv_pos.2 hξ).le hlog
  have hf : ∀ x, ((M • prof : C(Rd d, ℝ)) : Rd d → ℝ) x = M * plateauBump net.U C.ς hok.ς_pos x := by
    intro x
    rw [ContinuousMap.smul_apply, smul_eq_mul, hprof]
  have hς := hok.ς_pos
  have hς8 : 8 * C.ς < 1 := by
    have h1 := hok.hB.1
    have h2 := min_le_right C.eD (1 / 8)
    have h3 := hok.g_pos
    have h4 := hok.ω_pos
    have h5 : 0 ≤ S.seed.A * (2 * C.t₀) ^ S.seed.α :=
      mul_nonneg (by linarith [S.seed.A_ge]) (Real.rpow_nonneg (by linarith [hok.t₀_pos]) _)
    linarith
  refine ⟨{
    U := net.U
    Uo := net.Uo
    hU := net.isClosed_U
    hUo := net.isOpen_Uo
    hUoU := net.Uo_subset_U
    h_pos := hς
    hV := net.thick_subset
    f_eq := ?_
    f_bd := ?_
    f_supp := ?_
    θ_eq := ?_
    access := q7b_access hd hDup net.vertex
    net := ?_
    attach := ?_
    collar := ?_
    lower := hlow
    Node := net.Node
    node_fin := net.nodeFin
    N := net.N
    N_closed := net.isClosed_N
    adj := net.adj
    Ch := S.Edge
    ch_fin := Fintype.ofFinite S.Edge
    gate0 := net.gate0
    gate1 := net.gate1
    cover := net.cover
    sep := net.sep
    star := ?_
    arc := ?_ }⟩
  · -- (C2) the plateau value
    intro x hx
    rw [hf, plateauBump_eq_one net.U C.ς hς hx, mul_one]
  · -- (C2) the bounds
    intro x
    rw [hf]
    obtain ⟨h0, h1⟩ := plateauBump_mem_Icc net.U C.ς hς x
    exact ⟨mul_nonneg hM0 h0, by nlinarith⟩
  · -- (C2) the support
    have he : ((M • prof : C(Rd d, ℝ)) : Rd d → ℝ) = fun x => (fun _ : Rd d => M) x • prof x := by
      funext x
      rfl
    have hp : (prof : Rd d → ℝ) = plateauBump net.U C.ς hς := funext hprof
    rw [he]
    refine (tsupport_smul_subset_right (fun _ : Rd d => M) prof).trans ?_
    rw [hp]
    exact plateauBump_tsupport_subset net.U C.ς hς
  · -- (C2) `θ = e^{-ξ M}`
    rw [hM, ← mul_assoc, mul_inv_cancel₀ hξ.ne', one_mul, Real.log_inv, neg_neg, Real.exp_log hθ]
  · -- (C4) the discounted network
    intro x hx y hy
    have h := net.net D hD hDup x hx y hy
    calc ENNReal.ofReal C.θ * D.internal net.Uo x y ≤ ENNReal.ofReal C.θ * ENNReal.ofReal C.Anet := by
          gcongr
      _ = ENNReal.ofReal C.enet := by rw [← ENNReal.ofReal_mul hθ.le, hok.enet_eq]
  · -- (C5) attachments
    intro x hx
    obtain ⟨y, hy, hxy⟩ := net.attach x hx
    refine ⟨y, hy, ?_⟩
    have hxC : x ∈ siteC d := interior_subset (net.thick_subset hx)
    have h4 : (0 : ℝ) < 4 * C.ς := by positivity
    have hball : closedBall x (2 * (4 * C.ς)) ⊆ siteA d :=
      q7b_closedBall_subset_siteA hxC (by linarith)
    have hyb : y ∈ ball x (4 * C.ς) := by
      rw [mem_ball, dist_comm]
      rw [dist_comm] at hxy
      linarith [dist_comm x y]
    refine (q4_internal_le_of_doubled_ball D hDup h4 hball (ball_subset_closedBall.trans hball)
      (mem_ball_self h4) hyb).trans (le_of_eq ?_)
    rw [hok.eatt_eq]
  · -- (C6) collars
    intro P hP hends
    have haout : siteAout S.mc S.Hlo ≤ S.mc := by
      unfold siteAout
      have := min_le_left S.mc S.Hlo⁻¹
      linarith [S.mc_pos]
    rcases hends with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact (ENNReal.ofReal_le_ofReal haout).trans (hcol1.trans (q7b_collar_inner D hP h0 h1))
    · exact (ENNReal.ofReal_le_ofReal haout).trans (hcol2.trans (q7b_collar_outer D hP h0 h1))
  · -- (C9) stars
    intro T hT hgate
    obtain ⟨z, hz, hsub⟩ := net.star T hT hgate
    refine ⟨closedBall z S.mesh.δm, hsub, ?_⟩
    have hδ := S.mesh.δm_pos
    refine (q7b_diamIn_closedBall_le hDup hδ hz).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsq : (1 : ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.2 (by exact_mod_cast (show 1 ≤ d by omega))
    have hH : 0 ≤ S.Hup := by linarith [S.Hup_ge]
    calc S.Hup * (2 * S.mesh.δm) ^ S.s ≤ S.Hup * (10 * Real.sqrt d * S.mesh.δm) ^ S.s :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by nlinarith) S.s_pos.le) hH
      _ ≤ siteEps0 S.mc S.Hlo := S.mesh.access_cost
  · -- (C10) the chambers
    intro e
    obtain ⟨u, w, hu, hw, hu', hw', hd₀, hdiam0, hdiam1, hatt0, hatt1, hcon0, hcon1, hch⟩ :=
      q7b_arc hd hok hD hDup e (ℓ e) (hedge e)
    refine ⟨u, w, ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate0) C.g,
      ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.gate1) C.g,
      ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.chamber) C.ω,
      q7b_isOpen_ballUnionOpen _ _ _ _, q7b_isOpen_ballUnionOpen _ _ _ _, q7b_isOpen_ballUnionOpen _ _ _ _,
      net.gate0_open e, net.gate1_open e, net.chamber_open e, ?_, ?_, hu', hw', hd₀, ?_, ?_, ?_, ?_,
      hcon0, hcon1, hch⟩
    · rw [net.gate0_eq e]; exact hu
    · rw [net.gate1_eq e]; exact hw
    · rw [net.gate0_eq e]; exact hdiam0
    · rw [net.gate1_eq e]; exact hdiam1
    · rw [net.gate0_eq e]; exact hatt0
    · rw [net.gate1_eq e]; exact hatt1

end HigherDimLQGContinuity
