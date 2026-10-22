import HigherDimLQGContinuity.SiteCert.Metric
import HigherDimLQGContinuity.SiteCert.Constants

/-!
# The chambers of the certificate (C10) from the source arcs (packet Q7b)

Source: blueprint Part B, proof of `b:thm-sitecert`(iv), item (C10), with `b:lem-sandwich` (Q3's `gate_sandwich`),
`b:lem-gateconn` and `b:lem-unionballs` (one ball, for any continuous metric: `q7b_internal_ball_le`), the remark after
`b:def-source` (Q5's `EdgeSource.exists_arc_spec`), and `b:lem-order`(a)–(c) (Q3's `SiteConstsA/B/C`).

For an edge `e` with a valid edge label (its source arc `γ`, own length `λ ∈ [ℓ₀, ℓ₁]`), put `u = γ(0)`, `w = γ(1)`,
`G_i = ⋃_{k ∈ Q^i} B_g(c_k)` (open gate cores), `Ch_e = ⋃_{k ∈ Q_*} B_ω(c_k)`:
(a) `d₀ ≤ D(u, w)`; (b) `diamIn D A (G_{e,i}^{+ς}) ≤ v d₀/1000` (`q7b_gate_diam`); (c) every point of `G_{e,i}^{+ς}` is
`E`-joined inside `B` to `G_i` at cost `≤ v θ d₀/1000` (`q7b_gate_attach`); (d) `E(y, u; G_0) ≤ v d₀/1000`
(`q7b_gate_connector`, no length property of `E`); (e) `E(u, w; Ch_e) ≤ (1 + 4v) D(u, w)` (`q7b_chamber_internal`).
The assembly is `q7b_arc`.
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

/-! ## Covered sets and seed buffers -/

/-- A covered set lies in the open ball union once `c_d μ < t`. -/
theorem q7b_covered_subset_open {μ t : ℝ} {o : Rd d} {Q : Finset (Fin d → ℤ)} {T : Set (Rd d)}
    (hμ : 0 ≤ μ) (hQ : CoveredHit μ o Q T) (ht : Real.sqrt d / 2 * μ < t) :
    T ⊆ ballUnionOpen μ o Q t := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (hQ.1 hx)
  exact mem_iUnion₂.2 ⟨k, hk,
    mem_ball.2 ((mem_closedBall.1 (cell_subset_closedBall hμ o k hxk)).trans_lt ht)⟩

/-- A hit point of a selected cell is within `c_d μ` of its centre. -/
theorem q7b_hit_near_center {μ : ℝ} {o : Rd d} {Q : Finset (Fin d → ℤ)} {T : Set (Rd d)}
    (hμ : 0 ≤ μ) (hQ : CoveredHit μ o Q T) {k : Fin d → ℤ} (hk : k ∈ Q) :
    ∃ y ∈ T, dist y (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ := by
  obtain ⟨y, hyT, hyc⟩ := hQ.2 k hk
  exact ⟨y, hyT, mem_closedBall.1 (cell_subset_closedBall hμ o k hyc)⟩

/-- Points within `r/4` of the seed shell lie in the seed inspection. -/
theorem q7b_mem_srcSeedA_of_near {c k y : Rd d} {r : ℝ} (hr : 0 < r) (hk : k ∈ srcSeedK c r)
    (hy : dist y k < r / 4) : y ∈ srcSeedA c r := by
  rw [srcSeedK_eq c hr] at hk
  rw [srcSeedA_eq c hr]
  obtain ⟨hk1, hk2⟩ := hk
  rw [dist_eq_norm] at hy
  have h1 : ‖y - c‖ ≤ ‖y - k‖ + ‖k - c‖ := by
    calc ‖y - c‖ = ‖(y - k) + (k - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - k‖ + ‖k - c‖ := norm_add_le _ _
  have h2 : ‖k - c‖ ≤ ‖y - c‖ + ‖y - k‖ := by
    calc ‖k - c‖ = ‖(y - c) - (y - k)‖ := by congr 1; abel
      _ ≤ ‖y - c‖ + ‖y - k‖ := norm_sub_le _ _
  constructor <;> linarith

/-! ## The four chamber estimates -/

/-- **(C10)(b), gate diameter.** If the gate cells cover and hit `T ⊆ B̄_{R₀}(u)` with `u ∈ C`, then the `ς`-thickened
gate has `A`-internal `D`-diameter `≤ H_up (2ρ)^s`, `ρ = R₀ + g + c_d μ + ς ≤ 1/8`. -/
theorem q7b_gate_diam {D : ContMetric d} {Hup s μ g ς R₀ ε : ℝ} {o u : Rd d} {Q : Finset (Fin d → ℤ)}
    {T : Set (Rd d)} (hDup : DUpper D (siteA d) Hup s) (hT : IsCompact T) (hQ : CoveredHit μ o Q T)
    (hTu : T ⊆ closedBall u R₀) (hu : u ∈ siteC d) (hμ : 0 ≤ μ) (hμg : Real.sqrt d / 2 * μ < g)
    (hς : 0 ≤ ς) (hR₀ : 0 ≤ R₀) (hρ : R₀ + g + Real.sqrt d / 2 * μ + ς ≤ 1 / 8)
    (hcost : Hup * (2 * (R₀ + g + Real.sqrt d / 2 * μ + ς)) ^ s ≤ ε) :
    diamIn D (siteA d) (cthickening ς (ballUnion μ o Q g)) ≤ ENNReal.ofReal ε := by
  set c := Real.sqrt d / 2 * μ with hc
  have hc0 : 0 ≤ c := by positivity
  have hg : 0 < g := lt_of_le_of_lt hc0 hμg
  set ρ := R₀ + g + c + ς with hρdef
  have hρ0 : 0 < ρ := by linarith
  have hsub : cthickening ς (ballUnion μ o Q g) ⊆ closedBall u ρ := by
    have h1 := (gate_sandwich hμ o Q T hT hQ hμg).2.1
    calc cthickening ς (ballUnion μ o Q g) ⊆ cthickening ς (cthickening (g + c) T) :=
          cthickening_subset_of_subset ς h1
      _ ⊆ cthickening (ς + (g + c)) T := cthickening_cthickening_subset hς (by linarith) _
      _ ⊆ cthickening (ς + (g + c)) (closedBall u R₀) := cthickening_subset_of_subset _ hTu
      _ = closedBall u (ς + (g + c) + R₀) := cthickening_closedBall (by linarith) hR₀ u
      _ = closedBall u ρ := by rw [hρdef]; congr 1; ring
  have hball : closedBall u (4 * ρ) ⊆ siteA d := q7b_closedBall_subset_siteA hu (by linarith)
  calc diamIn D (siteA d) (cthickening ς (ballUnion μ o Q g)) ≤ diamIn D (siteA d) (closedBall u ρ) :=
        q7b_diamIn_mono D _ hsub
    _ ≤ ENNReal.ofReal (Hup * (2 * ρ) ^ s) := q7b_diamIn_closedBall_le hDup hρ0 hball
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hcost

/-- **(C10)(c), secondary attachment.** Every point of the `ς`-thickened gate is `E`-joined inside `B` to a point of
the open gate core at cost `≤ H_E (4ς)^{s_E}`, if the closed `8ς`-balls about points near the covered set lie in a
region `W ⊆ B` with `DUp(E, W, H_E, s_E)`. -/
theorem q7b_gate_attach {E : ContMetric d} {W : Set (Rd d)} {HE sE μ g ς ε : ℝ} {o : Rd d}
    {Q : Finset (Fin d → ℤ)} {T : Set (Rd d)} (hE : DUpper E W HE sE) (hWB : W ⊆ siteB d)
    (hQ : CoveredHit μ o Q T) (hμ : 0 ≤ μ) (hς : 0 < ς) (hςg : ς < g)
    (hbuf : ∀ x k, k ∈ T → dist x k ≤ g + ς + Real.sqrt d / 2 * μ → closedBall x (8 * ς) ⊆ W)
    (hcost : HE * (4 * ς) ^ sE ≤ ε) :
    ∀ x ∈ cthickening ς (ballUnion μ o Q g), ∃ y ∈ ballUnionOpen μ o Q g,
      E.internal (siteB d) x y ≤ ENNReal.ofReal ε := by
  intro x hx
  have hclosed : IsClosed (ballUnion μ o Q g) :=
    isClosed_biUnion_finset fun k _ => isClosed_closedBall
  rw [cthickening_eq_biUnion_closedBall _ hς.le, hclosed.closure_eq] at hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 hx
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 hy
  have hxk : x ∈ closedBall (cellCenter μ o k) (g + ς) := by
    rw [mem_closedBall] at hxy hyk ⊢
    calc dist x (cellCenter μ o k) ≤ dist x y + dist y (cellCenter μ o k) := dist_triangle _ _ _
      _ ≤ ς + g := add_le_add hxy hyk
      _ = g + ς := add_comm _ _
  obtain ⟨z, hz, hxz⟩ := q7b_exists_mem_ball_near hς hςg hxk
  refine ⟨z, mem_iUnion₂.2 ⟨k, hk, hz⟩, ?_⟩
  obtain ⟨t, htT, htc⟩ := q7b_hit_near_center hμ hQ hk
  have hxt : dist x t ≤ g + ς + Real.sqrt d / 2 * μ := by
    calc dist x t ≤ dist x (cellCenter μ o k) + dist (cellCenter μ o k) t := dist_triangle _ _ _
      _ ≤ (g + ς) + Real.sqrt d / 2 * μ :=
          add_le_add (mem_closedBall.1 hxk) (by rw [dist_comm]; exact htc)
  have hW := hbuf x t htT hxt
  have h4 : (0 : ℝ) < 4 * ς := by positivity
  have hW' : closedBall x (2 * (4 * ς)) ⊆ W := by
    rw [show 2 * (4 * ς) = 8 * ς by ring]
    exact hW
  have hU : ball x (2 * (4 * ς)) ⊆ siteB d := ball_subset_closedBall.trans (hW'.trans hWB)
  have hzb : z ∈ ball x (4 * ς) := by
    rw [mem_ball, dist_comm]
    linarith
  exact (q4_internal_le_of_doubled_ball E hE h4 hW' hU (mem_ball_self h4) hzb).trans
    (ENNReal.ofReal_le_ofReal hcost)

/-- **(C10)(d), gate connector** (`b:lem-gateconn`, for any continuous metric `E`): every point of the open gate core
is `E`-joined inside it to `γ(c)` at cost `≤ 2 C_{s_E} H_E g^{s_E} + len_E(γ|[a,b])`. -/
theorem q7b_gate_connector {E : ContMetric d} {W : Set (Rd d)} {HE sE μ g : ℝ} {o : Rd d}
    {Q : Finset (Fin d → ℤ)} {γ : ℝ → Rd d} {a b c : ℝ} (hE : DUpper E W HE sE) (hHE : 0 ≤ HE)
    (hsE : 0 < sE) (hγ : ContinuousOn γ (Icc a b)) (hQ : CoveredHit μ o Q (γ '' Icc a b)) (hμ : 0 ≤ μ)
    (hμg : Real.sqrt d / 2 * μ < g) (hW : ∀ k ∈ Q, closedBall (cellCenter μ o k) g ⊆ W)
    (hc : c ∈ Icc a b) :
    ∀ y ∈ ballUnionOpen μ o Q g, E.internal (ballUnionOpen μ o Q g) y (γ c) ≤
      ENNReal.ofReal (2 * siteCS sE * HE * g ^ sE) + E.len γ a b := by
  intro y hy
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.1 hy
  obtain ⟨z, ⟨t, ht, rfl⟩, hzc⟩ := hQ.2 k hk
  have hzk : γ t ∈ ball (cellCenter μ o k) g :=
    mem_ball.2 ((mem_closedBall.1 (cell_subset_closedBall hμ o k hzc)).trans_lt hμg)
  have hsub : ball (cellCenter μ o k) g ⊆ ballUnionOpen μ o Q g := fun x hx =>
    mem_iUnion₂.2 ⟨k, hk, hx⟩
  have h1 : E.internal (ballUnionOpen μ o Q g) y (γ t) ≤ ENNReal.ofReal (2 * siteCS sE * HE * g ^ sE) :=
    (E.internal_anti hsub y (γ t)).trans (q7b_internal_ball_le hE hHE hsE (hW k hk) hyk hzk)
  have hmaps : MapsTo γ (Icc a b) (ballUnionOpen μ o Q g) := fun s hs =>
    q7b_covered_subset_open hμ hQ hμg (mem_image_of_mem γ hs)
  have h2 : E.internal (ballUnionOpen μ o Q g) (γ t) (γ c) ≤ E.len γ a b := by
    rcases le_total t c with htc | hct
    · calc E.internal (ballUnionOpen μ o Q g) (γ t) (γ c) ≤ E.len γ t c :=
            E.internal_le_len htc (hγ.mono (Icc_subset_Icc ht.1 hc.2))
              (hmaps.mono_left (Icc_subset_Icc ht.1 hc.2))
        _ ≤ E.len γ a b := E.len_mono γ ht.1 hc.2
    · rw [E.internal_comm]
      calc E.internal (ballUnionOpen μ o Q g) (γ c) (γ t) ≤ E.len γ c t :=
            E.internal_le_len hct (hγ.mono (Icc_subset_Icc hc.1 ht.2))
              (hmaps.mono_left (Icc_subset_Icc hc.1 ht.2))
        _ ≤ E.len γ a b := E.len_mono γ hc.1 ht.2
  calc E.internal (ballUnionOpen μ o Q g) y (γ c)
      ≤ E.internal (ballUnionOpen μ o Q g) y (γ t) + E.internal (ballUnionOpen μ o Q g) (γ t) (γ c) :=
        E.internal_triangle _ _ _ _
    _ ≤ ENNReal.ofReal (2 * siteCS sE * HE * g ^ sE) + E.len γ a b := add_le_add h1 h2

/-- **(C10)(e), chamber.** The arc lies in the open chamber core, so `E(γ(0), γ(1); Ch_e) ≤ len_E(γ)`. -/
theorem q7b_chamber_internal {E : ContMetric d} {μ ω : ℝ} {o : Rd d} {Q : Finset (Fin d → ℤ)}
    {γ : ℝ → Rd d} (hγ : ContinuousOn γ (Icc 0 1)) (hQ : CoveredHit μ o Q (γ '' Icc 0 1)) (hμ : 0 ≤ μ)
    (hμω : Real.sqrt d / 2 * μ < ω) :
    E.internal (ballUnionOpen μ o Q ω) (γ 0) (γ 1) ≤ E.len γ 0 1 :=
  E.internal_le_len zero_le_one hγ fun _ hs => q7b_covered_subset_open hμ hQ hμω (mem_image_of_mem γ hs)

/-! ## The chamber of one edge -/

/-- Points of the initial and final pieces of an arc with moduli `(A, α, β)` lie within `A (2t₀)^α` of its
endpoints. -/
theorem q7b_arc_ends_near {γ : ℝ → Rd d} {A α β t₀ : ℝ} (hmod : Topology.ArcModuli γ A α β)
    (hA : 0 ≤ A) (hα : 0 < α) (ht₀' : 2 * t₀ ≤ 1) :
    γ '' Icc 0 (2 * t₀) ⊆ closedBall (γ 0) (A * (2 * t₀) ^ α) ∧
      γ '' Icc (1 - 2 * t₀) 1 ⊆ closedBall (γ 1) (A * (2 * t₀) ^ α) := by
  constructor
  · rintro x ⟨t, ht, rfl⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀'⟩
    have h := (hmod t ht1 0 ⟨le_rfl, zero_le_one⟩).1
    rw [sub_zero, abs_of_nonneg ht.1] at h
    rw [mem_closedBall, dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 hα.le) hA)
  · rintro x ⟨t, ht, rfl⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have h := (hmod t ht1 1 ⟨zero_le_one, le_rfl⟩).1
    rw [abs_sub_comm, abs_of_nonneg (by linarith [ht.2])] at h
    rw [mem_closedBall, dist_eq_norm]
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [ht.2]) (by linarith [ht.1]) hα.le) hA)

/-- **The chamber of one edge** ((C10) of `b:thm-sitecert`(iv)): from a valid edge label (the edge source with a
length primary metric `D` and the primary doubled-ball reference), the arc endpoints `u = γ(0)`, `w = γ(1)`, the open
gate cores and the open chamber core of the label satisfy (a)–(e). -/
theorem q7b_arc {S : SiteData d} (hd : 2 ≤ d) {C : SiteConsts} {v : ℝ} (hok : Q7bConstOK S C v)
    {D E : ContMetric d} (hD : D.IsLength) (hDup : DUpper D (siteA d) S.Hup S.s) (e : S.Edge)
    {Kc Kl N : ℕ} {r c₁ : ℝ} (E' : EdgeLabel S e Kc Kl N C.μ C.ν r c₁)
    (hsrc : EdgeSource S.seed.HE S.seed.sE S.seed.A S.seed.α S.seed.β S.seed.ℓ₀ S.seed.ℓ₁ S.seed.d₀ v
      (S.edgeCenter e) (S.seedRadius E'.1.trial) (fun γ => labelGeo S e E' C.t₀ γ) D E) :
    ∃ u w : Rd d,
      u ∈ ballUnion C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g ∧
      w ∈ ballUnion C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g ∧
      u ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g ∧
      w ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g ∧
      S.seed.d₀ ≤ D.1 (u, w) ∧
      diamIn D (siteA d) (cthickening C.ς (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices E'.1.gate0) C.g)) ≤ ENNReal.ofReal (v * S.seed.d₀ / 1000) ∧
      diamIn D (siteA d) (cthickening C.ς (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices E'.1.gate1) C.g)) ≤ ENNReal.ofReal (v * S.seed.d₀ / 1000) ∧
      (∀ x ∈ cthickening C.ς (ballUnion C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g),
        ∃ y ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g,
          E.internal (siteB d) x y ≤ ENNReal.ofReal (v * C.θ * S.seed.d₀ / 1000)) ∧
      (∀ x ∈ cthickening C.ς (ballUnion C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g),
        ∃ y ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g,
          E.internal (siteB d) x y ≤ ENNReal.ofReal (v * C.θ * S.seed.d₀ / 1000)) ∧
      (∀ y ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g,
        E.internal (ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate0) C.g) y u ≤
          ENNReal.ofReal (v * S.seed.d₀ / 1000)) ∧
      (∀ y ∈ ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g,
        E.internal (ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.gate1) C.g) y w ≤
          ENNReal.ofReal (v * S.seed.d₀ / 1000)) ∧
      E.internal (ballUnionOpen C.μ (S.edgeCenter e) (labelCellIndices E'.1.chamber) C.ω) u w ≤
        ENNReal.ofReal ((1 + 4 * v) * D.1 (u, w)) := by
  -- the arc of the edge
  have hr : 0 < S.seedRadius E'.1.trial := q5_seedRadius_pos S hd _
  obtain ⟨hup, γ₀, hγ₀, lam, hlam, -, hlen, -, hd₀, hratio, hgeo⟩ :=
    hsrc.exists_arc_spec hD hr hok.v_pos.le
  obtain ⟨hch, hg0, hg1, -, -, -, -⟩ := hgeo
  set γ : ℝ → Rd d := witExt γ₀ with hγdef
  set m := S.edgeCenter e with hm
  set rr := S.seedRadius E'.1.trial with hrr
  set c := Real.sqrt d / 2 * C.μ with hc
  have hγc : Continuous γ := continuous_witExt γ₀
  have hmod : Topology.ArcModuli γ S.seed.A S.seed.α S.seed.β := (mem_arcSpace_iff_arcModuli.1 hγ₀).2
  have hK : ∀ t, γ t ∈ srcSeedK m rr := witExt_mem hγ₀.1
  have hγ0 : γ 0 = γ₀ 0 := witExt_zero γ₀
  have hγ1 : γ 1 = γ₀ 1 := witExt_one γ₀
  -- the constants
  obtain ⟨hA, hB, hC⟩ := And.intro hok.hA (And.intro hok.hB hok.hC)
  have hμ0 : 0 ≤ C.μ := hok.μ_pos.le
  have hcω : c ≤ C.ω / 4 := hA.2.2.2.2.1
  have hseed : 2 * C.g + 8 * C.ς < S.seedMin / 4 := hA.2.2.2.2.2.2
  have hrmin : S.seedMin ≤ rr := q5_seedMin_le_seedRadius S _ hd
  have hςω : C.ς ≤ C.ω / 4 := hC.2.2.1
  have hω := hok.ω_pos
  have hωg := hok.ω_le_g
  have hς := hok.ς_pos
  have hc0 : 0 ≤ c := by positivity
  have hcg : c < C.g := by linarith
  have hcω' : c < C.ω := by linarith
  have hςg : C.ς < C.g := by linarith
  have ht₀ := hok.t₀_pos
  have ht₀' := hok.t₀_le
  have h2t₀ : 2 * C.t₀ ≤ 1 := by linarith
  have hAge := S.seed.A_ge
  have hR₀ : 0 ≤ S.seed.A * (2 * C.t₀) ^ S.seed.α :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  obtain ⟨hnear0, hnear1⟩ := q7b_arc_ends_near hmod (by linarith) S.seed.α_pos h2t₀
  -- the endpoints are collector points
  have hmemC : ∀ t, γ t ∈ siteC d := by
    intro t
    have hk := hK t
    rw [srcSeedK_eq m hr] at hk
    have hball : γ t ∈ closedBall m S.boxHalfSide := by
      rw [mem_closedBall, dist_eq_norm]
      have := q5_seedRadius_le S hd E'.1.trial
      have hL := S.boxHalfSide_pos hd
      linarith [hk.2]
    exact interior_subset (S.center_ball_interior_C hd e hball)
  -- the seed buffer
  have hbuf : ∀ x k, k ∈ γ '' Icc 0 1 → dist x k ≤ C.g + C.ς + c →
      closedBall x (8 * C.ς) ⊆ srcSeedA m rr := by
    rintro x k ⟨t, -, rfl⟩ hxk y hy
    refine q7b_mem_srcSeedA_of_near hr (hK t) ?_
    rw [mem_closedBall] at hy
    calc dist y (γ t) ≤ dist y x + dist x (γ t) := dist_triangle _ _ _
      _ ≤ 8 * C.ς + (C.g + C.ς + c) := add_le_add hy hxk
      _ < rr / 4 := by linarith
  have hbuf0 : ∀ x k, k ∈ γ '' Icc 0 (2 * C.t₀) → dist x k ≤ C.g + C.ς + c →
      closedBall x (8 * C.ς) ⊆ srcSeedA m rr := fun x k hk =>
    hbuf x k (image_mono (Icc_subset_Icc le_rfl h2t₀) hk)
  have hbuf1 : ∀ x k, k ∈ γ '' Icc (1 - 2 * C.t₀) 1 → dist x k ≤ C.g + C.ς + c →
      closedBall x (8 * C.ς) ⊆ srcSeedA m rr := fun x k hk =>
    hbuf x k (image_mono (Icc_subset_Icc (by linarith) le_rfl) hk)
  have hcellW : ∀ (a b : ℝ) (Q : Finset (Fin d → ℤ)), Icc a b ⊆ Icc 0 1 →
      CoveredHit C.μ m Q (γ '' Icc a b) → ∀ k ∈ Q, closedBall (cellCenter C.μ m k) C.g ⊆ srcSeedA m rr := by
    intro a b Q hab hQ k hk y hy
    obtain ⟨z, ⟨t, ht, rfl⟩, hzc⟩ := q7b_hit_near_center hμ0 hQ hk
    refine q7b_mem_srcSeedA_of_near hr (hK t) ?_
    rw [mem_closedBall] at hy
    calc dist y (γ t) ≤ dist y (cellCenter C.μ m k) + dist (cellCenter C.μ m k) (γ t) := dist_triangle _ _ _
      _ ≤ C.g + c := add_le_add hy (by rw [dist_comm]; exact hzc)
      _ < rr / 4 := by linarith
  have hWB : srcSeedA m rr ⊆ siteB d := q5_srcSeedA_subset_siteB S hd e _
  have hHE : 0 ≤ S.seed.HE := by linarith [S.seed.HE_ge]
  have hsE := S.seed.sE_pos
  -- the gate diameter cost
  have hgate_cost : S.Hup * (2 * (S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + c + C.ς)) ^ S.s ≤
      v * S.seed.d₀ / 1000 := by
    have hle : S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + c + C.ς ≤ C.eD := by
      have := hB.1
      have := min_le_left C.eD (1 / 8)
      linarith
    rw [← hok.eD_cost]
    have hH : 0 ≤ S.Hup := by linarith [S.Hup_ge]
    have hg0 := hok.g_pos
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) S.s_pos.le) hH
  have hgate_rad : S.seed.A * (2 * C.t₀) ^ S.seed.α + C.g + c + C.ς ≤ 1 / 8 := by
    have := hB.1
    have := min_le_right C.eD (1 / 8)
    linarith
  -- the connector cost
  have hlen0 : E.len γ 0 (2 * C.t₀) = ENNReal.ofReal (lam * (2 * C.t₀ - 0)) :=
    hlen 0 (2 * C.t₀) le_rfl (by linarith) h2t₀
  have hlen1 : E.len γ (1 - 2 * C.t₀) 1 = ENNReal.ofReal (lam * (1 - (1 - 2 * C.t₀))) :=
    hlen (1 - 2 * C.t₀) 1 (by linarith) (by linarith) le_rfl
  have hlenall : E.len γ 0 1 = ENNReal.ofReal (lam * (1 - 0)) := hlen 0 1 le_rfl zero_le_one le_rfl
  have hlam0 : 0 ≤ lam := le_trans S.seed.ℓ₀_pos.le hlam.1
  have hconn_cost : ∀ L : ℝ, L = lam * (2 * C.t₀) →
      ENNReal.ofReal (2 * siteCS S.seed.sE * S.seed.HE * C.g ^ S.seed.sE) + ENNReal.ofReal L ≤
        ENNReal.ofReal (v * S.seed.d₀ / 1000) := by
    intro L hL
    have h1 : 0 ≤ 2 * siteCS S.seed.sE * S.seed.HE * C.g ^ S.seed.sE :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (siteCS_pos hsE).le) hHE)
        (Real.rpow_nonneg hok.g_pos.le _)
    have h2 : 0 ≤ L := by rw [hL]; exact mul_nonneg hlam0 (by linarith)
    rw [← ENNReal.ofReal_add h1 h2]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hB.2
    have hlam1 : lam * (2 * C.t₀) ≤ 2 * C.t₀ * S.seed.ℓ₁ := by nlinarith [hlam.2]
    linarith
  have hu0 : γ 0 ∈ ballUnionOpen C.μ m (labelCellIndices E'.1.gate0) C.g :=
    q7b_covered_subset_open hμ0 hg0 hcg (mem_image_of_mem γ ⟨le_rfl, by linarith⟩)
  have hw1 : γ 1 ∈ ballUnionOpen C.μ m (labelCellIndices E'.1.gate1) C.g :=
    q7b_covered_subset_open hμ0 hg1 hcg (mem_image_of_mem γ ⟨by linarith, le_rfl⟩)
  have hopen_sub : ∀ (Q : Finset (Fin d → ℤ)) (t : ℝ), ballUnionOpen C.μ m Q t ⊆ ballUnion C.μ m Q t :=
    fun Q t x hx => by
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
      exact mem_iUnion₂.2 ⟨k, hk, ball_subset_closedBall hxk⟩
  refine ⟨γ₀ 0, γ₀ 1, ?_, ?_, ?_, ?_, hd₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hγ0]; exact hopen_sub _ _ hu0
  · rw [← hγ1]; exact hopen_sub _ _ hw1
  · rw [← hγ0]; exact hu0
  · rw [← hγ1]; exact hw1
  · exact q7b_gate_diam hDup ((isCompact_Icc).image hγc) hg0 hnear0 (hmemC 0) hμ0 hcg hς.le hR₀
      hgate_rad hgate_cost
  · exact q7b_gate_diam hDup ((isCompact_Icc).image hγc) hg1 hnear1 (hmemC 1) hμ0 hcg hς.le hR₀
      hgate_rad hgate_cost
  · exact q7b_gate_attach hup hWB hg0 hμ0 hς hςg hbuf0 hC.2.2.2.2
  · exact q7b_gate_attach hup hWB hg1 hμ0 hς hςg hbuf1 hC.2.2.2.2
  · intro y hy
    rw [← hγ0]
    refine (q7b_gate_connector hup hHE hsE hγc.continuousOn hg0 hμ0 hcg
      (hcellW 0 (2 * C.t₀) _ (Icc_subset_Icc le_rfl h2t₀) hg0) ⟨le_rfl, by linarith⟩ y hy).trans ?_
    rw [hlen0]
    exact hconn_cost _ (by ring)
  · intro y hy
    rw [← hγ1]
    refine (q7b_gate_connector hup hHE hsE hγc.continuousOn hg1 hμ0 hcg
      (hcellW (1 - 2 * C.t₀) 1 _ (Icc_subset_Icc (by linarith) le_rfl) hg1) ⟨by linarith, le_rfl⟩
      y hy).trans ?_
    rw [hlen1]
    exact hconn_cost _ (by ring)
  · rw [← hγ0, ← hγ1]
    refine (q7b_chamber_internal hγc.continuousOn hch hμ0 hcω').trans ?_
    rw [hlenall, hγ0, hγ1]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hratio
    linarith

end HigherDimLQGContinuity
