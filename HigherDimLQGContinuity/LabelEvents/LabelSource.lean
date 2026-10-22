import HigherDimLQGContinuity.LabelEvents.SourceBorel
import HigherDimLQGContinuity.LabelEvents.SourceArc
import HigherDimLQGContinuity.Labels.Realizable
import HigherDimLQGContinuity.Labels.OrderSpecA
import HigherDimLQGContinuity.Routing.Leads

/-!
# Source validity of the concrete site labels (packet Q5; Part B `b:def-label`, `b:def-source`, `b:lem-src-meas`)

Source: blueprint Part B `b:def-label` (the geometric predicate and realizability), `b:def-source`, `b:lem-src-meas`
(a)–(b), `b:def-sitedata` (F4)–(F5) (ports with denominator dividing `q₀ = 2^{k_m+7} d`, concentric seed radii);
planning audit NA2, items 8, 12–13, R8; rulings N13, N20, N30. Inputs: packet Q3's `SiteData`, `cell`, `CoveredHit`,
`EdgeLabel`, `SiteLabel`, `EdgeLabel.IsRealizable`, `IsRealizable` (`Labels/`), packet Q2's `exists_leads`
(`Routing/Leads.lean`), and this packet's generic `SiteSource` (`LabelEvents/Source.lean`, `SourceBorel.lean`).

* Cells met by a set: `q5FloorIndex`, `mem_cell_q5FloorIndex`, `q5MetCells`, `coveredHit_q5MetCells`,
  `q5_cell_subset_box`; closedness `q5_isClosed_cell`, `q5_isClosed_coveredHit`.
* `labelGeo S e E t₀ γ`: the geometric predicate of the edge label `E` on arcs `γ : C([0, 1], ℝ^d)` (covered-and-hit
  cell sets of `γ([0, 1])`, `γ([0, 2t₀])`, `γ([1 - 2t₀, 1])`, lead clearances, lead tips), `isClosed_labelGeo`,
  `isRealizable_of_labelGeo` (Q3's `EdgeLabel.IsRealizable`).
* `labelSource S t₀ v ℓ D E`: Part B's `SiteSource_ℓ(D, E)` for the site label `ℓ` (the generic `SiteSource` with
  the site data's constants, the seed of each edge's trial and `labelGeo`); `labelSource_borel` (`b:lem-src-meas`(a)),
  `labelSource_local` (`b:lem-src-meas`(b)), `siteRefs_of_labelSource`, `isRealizable_of_labelSource` (every label
  accepted by a source event is realizable, `b:thm-sitecert`(iv)).
* Seeds and ports: `q5_seedRadius_pos`, `q5_seedRadius_le` (`s_{e,j} ≤ L/32`), `q5_seedMin_le_seedRadius`,
  `q5_seedRadius_eq` (the radius of the frozen exhaustion clause), `q5_srcSeedA_subset_siteB`, `q5_port_zero`,
  `q5_port_one` (the ports as `m_e ∓ L u_e`; their grid membership is Q3's `siteConsts_port_onGrid`).
* `q5_exists_leads_of_arc`: Q2's `exists_leads` for the arc of a seed of an edge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## Cells met by a set -/

/-- The floor index of a point. -/
def q5FloorIndex (μ : ℝ) (o x : Rd d) : Fin d → ℤ := fun i => ⌊(x i - o i) / μ⌋

theorem mem_cell_q5FloorIndex {μ : ℝ} (hμ : 0 < μ) (o x : Rd d) : x ∈ cell μ o (q5FloorIndex μ o x) := by
  intro i
  have h1 := Int.floor_le ((x i - o i) / μ)
  have h2 := Int.lt_floor_add_one ((x i - o i) / μ)
  have e1 : μ * (⌊(x i - o i) / μ⌋ : ℝ) ≤ x i - o i := by
    rw [le_div_iff₀ hμ] at h1
    linarith
  have e2 : x i - o i ≤ μ * ((⌊(x i - o i) / μ⌋ : ℝ) + 1) := by
    rw [div_lt_iff₀ hμ] at h2
    linarith
  exact ⟨by simp only [q5FloorIndex]; linarith, by simp only [q5FloorIndex]; linarith⟩

open Classical in
/-- The cells (side `μ`, origin `o`) of the index box `[-K, K]^d` met by a set. -/
def q5MetCells (μ : ℝ) (o : Rd d) (K : ℕ) (T : Set (Rd d)) : Finset (Fin d → ℤ) :=
  (labelIndexFinset d K).filter fun k => (T ∩ cell μ o k).Nonempty

theorem coveredHit_q5MetCells {μ : ℝ} (hμ : 0 < μ) (o : Rd d) (K : ℕ) {T : Set (Rd d)}
    (hT : ∀ x ∈ T, q5FloorIndex μ o x ∈ labelIndexFinset d K) :
    CoveredHit μ o (q5MetCells μ o K T) T := by
  classical
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · refine mem_iUnion₂.2 ⟨q5FloorIndex μ o x, ?_, mem_cell_q5FloorIndex hμ o x⟩
    rw [q5MetCells, Finset.mem_filter]
    exact ⟨hT x hx, x, hx, mem_cell_q5FloorIndex hμ o x⟩
  · rw [q5MetCells, Finset.mem_filter] at hk
    exact hk.2

/-- A cell meeting the closed `ρ`-ball about the box centre lies in the box when `ρ + μ ≤ L`. -/
theorem q5_cell_subset_box {μ ρ L : ℝ} {m : Rd d} {k : Fin d → ℤ}
    (hk : (closedBall m ρ ∩ cell μ m k).Nonempty) (hρL : ρ + μ ≤ L) :
    cell μ m k ⊆ {x : Rd d | ∀ i, |x i - m i| ≤ L} := by
  obtain ⟨x, hxB, hxc⟩ := hk
  intro y hy i
  have hxm : |x i - m i| ≤ ρ := by
    have := PiLp.norm_apply_le (x - m) i
    rw [mem_closedBall, dist_eq_norm] at hxB
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using this.trans hxB
  have hxy : |y i - x i| ≤ μ := by
    obtain ⟨hx1, hx2⟩ := hxc i
    obtain ⟨hy1, hy2⟩ := hy i
    rw [abs_le]
    constructor <;> nlinarith
  calc |y i - m i| = |(y i - x i) + (x i - m i)| := by ring_nf
    _ ≤ |y i - x i| + |x i - m i| := abs_add_le _ _
    _ ≤ L := by linarith

theorem q5_isClosed_cell (μ : ℝ) (o : Rd d) (k : Fin d → ℤ) : IsClosed (cell μ o k) := by
  have hc : ∀ i : Fin d, Continuous fun x : Rd d => x i := fun i => (EuclideanSpace.proj i).continuous
  have e : cell μ o k = ⋂ i, ({x : Rd d | o i + μ * (k i : ℝ) ≤ x i} ∩ {x | x i ≤ o i + μ * ((k i : ℝ) + 1)}) := by
    ext x
    simp only [cell, mem_ofPred_eq, mem_iInter, mem_inter_iff]
  rw [e]
  exact isClosed_iInter fun i => (isClosed_le continuous_const (hc i)).inter (isClosed_le (hc i) continuous_const)

/-- The covered-and-hit condition on the image of `[a, b]` is closed in the arc. -/
theorem q5_isClosed_coveredHit (μ : ℝ) (o : Rd d) (Q : Finset (Fin d → ℤ)) (a b : ℝ) :
    IsClosed {γ : C(unitInterval, Rd d) | CoveredHit μ o Q (witExt γ '' Icc a b)} := by
  have h1 : IsClosed {γ : C(unitInterval, Rd d) | witExt γ '' Icc a b ⊆ ⋃ k ∈ Q, cell μ o k} :=
    isClosed_setOf_witExt_image_subset a b (isClosed_biUnion_finset fun k _ => q5_isClosed_cell μ o k)
  have h2 : IsClosed {γ : C(unitInterval, Rd d) | ∀ k ∈ Q, (witExt γ '' Icc a b ∩ cell μ o k).Nonempty} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_setOf_witExt_image_inter_nonempty a b (q5_isClosed_cell μ o k)
  have e : {γ : C(unitInterval, Rd d) | CoveredHit μ o Q (witExt γ '' Icc a b)} =
      {γ | witExt γ '' Icc a b ⊆ ⋃ k ∈ Q, cell μ o k} ∩
        {γ | ∀ k ∈ Q, (witExt γ '' Icc a b ∩ cell μ o k).Nonempty} := by
    ext γ
    rfl
  rw [e]
  exact h1.inter h2

/-! ## The geometric predicate of a label -/

/-- **The geometric predicate of an edge label** on arcs (Part B `b:def-label`): the covered-and-hit cell sets, the
lead clearances and the lead tips, for the real-parameter extension `witExt γ` (the moduli and the seed shell are
carried by the arc space). -/
def labelGeo (S : SiteData d) (e : S.Edge) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (E : EdgeLabel S e Kc Kl N μ ν r c₁) (t₀ : ℝ) (γ : C(unitInterval, Rd d)) : Prop :=
  CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.chamber) (witExt γ '' Icc 0 1) ∧
  CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.gate0) (witExt γ '' Icc 0 (2 * t₀)) ∧
  CoveredHit μ (S.edgeCenter e) (labelCellIndices E.1.gate1) (witExt γ '' Icc (1 - 2 * t₀) 1) ∧
  (∀ x ∈ E.1.lead0.trace ν, ∀ t ∈ Icc t₀ 1, r ≤ dist x (witExt γ t)) ∧
  (∀ x ∈ E.1.lead1.trace ν, ∀ t ∈ Icc 0 (1 - t₀), r ≤ dist x (witExt γ t)) ∧
  dist (E.1.lead0.point ν E.1.lead0.last) (γ 0) ≤ d * ν ∧
  dist (E.1.lead1.point ν E.1.lead1.last) (γ 1) ≤ d * ν

/-- The geometric predicate of a label is a closed condition on arcs. -/
theorem isClosed_labelGeo (S : SiteData d) (e : S.Edge) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (E : EdgeLabel S e Kc Kl N μ ν r c₁) (t₀ : ℝ) : IsClosed {γ | labelGeo S e E t₀ γ} := by
  simp only [labelGeo, ofPred_and]
  exact (q5_isClosed_coveredHit _ _ _ _ _).inter ((q5_isClosed_coveredHit _ _ _ _ _).inter
    ((q5_isClosed_coveredHit _ _ _ _ _).inter ((isClosed_setOf_forall_le_dist_witExt _ _ _ _).inter
      ((isClosed_setOf_forall_le_dist_witExt _ _ _ _).inter ((isClosed_setOf_dist_apply_le _ _ _).inter
        (isClosed_setOf_dist_apply_le _ _ _))))))

/-- An arc of the arc space of the label's seed shell satisfying its geometric predicate realizes the label
(Q3's `EdgeLabel.IsRealizable`). -/
theorem isRealizable_of_labelGeo (S : SiteData d) (e : S.Edge) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ}
    (E : EdgeLabel S e Kc Kl N μ ν r c₁) {A α β t₀ : ℝ} {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace (srcSeedK (S.edgeCenter e) (S.seedRadius E.1.trial)) A α β)
    (hgeo : labelGeo S e E t₀ γ) : EdgeLabel.IsRealizable S e E A α β t₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hgeo
  refine ⟨witExt γ, (mem_arcSpace_iff_arcModuli.1 hγ).2, fun t _ => witExt_mem hγ.1 t, h1, h2, h3, h4, h5,
    ?_, ?_⟩
  · rwa [witExt_zero]
  · rwa [witExt_one]

/-! ## Seed radii -/

theorem q5_seedRadius_pos (S : SiteData d) (hd : 2 ≤ d) (j : Fin S.Ntr) : 0 < S.seedRadius j := by
  unfold SiteData.seedRadius
  exact mul_pos (div_pos (S.boxHalfSide_pos hd) (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)

theorem q5_seedRadius_le (S : SiteData d) (hd : 2 ≤ d) (j : Fin S.Ntr) :
    S.seedRadius j ≤ S.boxHalfSide / 32 := by
  unfold SiteData.seedRadius
  have hL := S.boxHalfSide_pos hd
  have h8 : (8 : ℝ) ^ (-((j : ℕ) + 1 : ℝ)) ≤ 8⁻¹ := by
    have : (8 : ℝ) ^ (-((j : ℕ) + 1 : ℝ)) ≤ (8 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
        linarith)
    simpa [Real.rpow_neg_one] using this
  calc S.boxHalfSide / 4 * (8 : ℝ) ^ (-((j : ℕ) + 1 : ℝ)) ≤ S.boxHalfSide / 4 * 8⁻¹ :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
    _ = S.boxHalfSide / 32 := by ring

theorem q5_seedMin_le_seedRadius (S : SiteData d) (j : Fin S.Ntr) (hd : 2 ≤ d) :
    S.seedMin ≤ S.seedRadius j := by
  unfold SiteData.seedMin SiteData.seedRadius
  have hL := S.boxHalfSide_pos hd
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity)
  have : (j : ℕ) + 1 ≤ S.Ntr := j.isLt
  have : ((j : ℕ) : ℝ) + 1 ≤ (S.Ntr : ℝ) := by exact_mod_cast this
  linarith

theorem q5_srcSeedA_subset_siteB (S : SiteData d) (hd : 2 ≤ d) (e : S.Edge) (j : Fin S.Ntr) :
    srcSeedA (S.edgeCenter e) (S.seedRadius j) ⊆ siteB d := by
  have hr := q5_seedRadius_pos S hd j
  have hrL := q5_seedRadius_le S hd j
  have hL := S.boxHalfSide_pos hd
  refine (srcSeedA_subset_closedBall _ hr).trans ?_
  refine (closedBall_subset_closedBall (show 7 * S.seedRadius j / 2 ≤ S.boxHalfSide by linarith)).trans ?_
  refine (S.center_ball_interior_C hd e).trans (interior_subset.trans ?_)
  intro x hx
  rw [siteB, mem_ball, dist_zero_right]
  have := hx.2
  rw [sub_zero] at this
  linarith

/-! ## The source predicate of the concrete labels -/

/-- **Source validity of a site label** (Part B `b:def-source` for Q3's labels): `SiteSource` with the site data's
references (F1), the seed constants (F6), the seed of each edge's trial and the geometric predicate `labelGeo`. -/
def labelSource (S : SiteData d) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ} (t₀ v : ℝ) (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (D E : ContMetric d) : Prop :=
  SiteSource S.Hup S.s S.Hlo S.b S.mc S.A0 S.seed.HE S.seed.sE S.seed.A S.seed.α S.seed.β S.seed.ℓ₀ S.seed.ℓ₁
    S.seed.d₀ v (fun e => S.edgeCenter e) (fun e => S.seedRadius (ℓ e).1.trial)
    (fun e γ => labelGeo S e (ℓ e) t₀ γ) D E

theorem labelSource_borel (S : SiteData d) (hd : 2 ≤ d) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ} (t₀ v : ℝ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) :
    ∃ T : Set (ContMetric d × ContMetric d), MeasurableSet T ∧
      ∀ D E : ContMetric d, D.IsLength → E.IsLength → ((D, E) ∈ T ↔ labelSource S t₀ v ℓ D E) := by
  have : Finite S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).to_subtype
  exact siteSource_borel (by linarith [S.Hup_ge]) S.s_pos.le (by linarith [S.seed.HE_ge]) S.seed.sE_pos.le
    S.seed.α_pos S.seed.β_pos _ _ (fun e => q5_seedRadius_pos S hd _) _
    (fun e => isClosed_labelGeo S e (ℓ e) t₀)

theorem labelSource_local (S : SiteData d) (hd : 2 ≤ d) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ} (t₀ v : ℝ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) {D E D₂ E₂ : ContMetric d}
    (hD : ∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y)
    (hE : ∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) :
    labelSource S t₀ v ℓ D E ↔ labelSource S t₀ v ℓ D₂ E₂ :=
  siteSource_local (fun e => q5_srcSeedA_subset_siteB S hd e _) hD hE

theorem siteRefs_of_labelSource (S : SiteData d) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ} {t₀ v : ℝ}
    {ℓ : SiteLabel S Kc Kl N μ ν r c₁} {D E : ContMetric d} (h : labelSource S t₀ v ℓ D E) :
    SiteRefs S.Hup S.s S.Hlo S.b S.mc S.A0 D :=
  h.1

theorem isRealizable_of_labelSource (S : SiteData d) {Kc Kl N : ℕ} {μ ν r c₁ : ℝ} {t₀ v : ℝ}
    {ℓ : SiteLabel S Kc Kl N μ ν r c₁} {D E : ContMetric d} (h : labelSource S t₀ v ℓ D E) :
    IsRealizable S ℓ S.seed.A S.seed.α S.seed.β t₀ := by
  intro e
  obtain ⟨-, γ, hγ, -, -, -, -, -, -, hgeo⟩ := h.2 e
  exact isRealizable_of_labelGeo S e (ℓ e) hγ hgeo

/-! ## The two leads of an arc -/

theorem q5_port_zero (S : SiteData d) (e : S.Edge) :
    S.port e 0 = S.edgeCenter e - S.boxHalfSide • S.edgeUnit e := by
  simp [SiteData.port]

theorem q5_port_one (S : SiteData d) (e : S.Edge) :
    S.port e 1 = S.edgeCenter e + S.boxHalfSide • S.edgeUnit e := by
  simp [SiteData.port]

theorem q5_resBox_subset (S : SiteData d) (hd : 2 ≤ d) (e : S.Edge) :
    Routing.resBox (S.edgeCenter e) S.boxHalfSide ⊆ closedBall 0 4 := by
  intro x hx
  have hC : x ∈ siteC d := interior_subset (S.box_subset_interior_C hd e hx)
  rw [mem_closedBall, dist_zero_right]
  have := hC.2
  rw [sub_zero] at this
  linarith

/-- The arc of a seed of the edge `e` lies in the closed `L/32`-ball about the box centre. -/
theorem q5_witExt_mem_closedBall (S : SiteData d) (hd : 2 ≤ d) (e : S.Edge) (j : Fin S.Ntr)
    {A α β : ℝ} {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace (srcSeedK (S.edgeCenter e) (S.seedRadius j)) A α β) (t : ℝ) :
    witExt γ t ∈ closedBall (S.edgeCenter e) (S.boxHalfSide / 32) := by
  have hr := q5_seedRadius_pos S hd j
  have hmem : witExt γ t ∈ srcSeedK (S.edgeCenter e) (S.seedRadius j) := witExt_mem hγ.1 t
  rw [srcSeedK_eq _ hr] at hmem
  rw [mem_closedBall, dist_eq_norm]
  exact hmem.2.trans (q5_seedRadius_le S hd j)

/-- **The two leads of a seed arc** (Q2's `exists_leads`, `b:lem-leads`, for the arc of a favorable seed of the edge
`e` and the constants `(t₀, ν)` satisfying its hypotheses). -/
theorem q5_exists_leads_of_arc (S : SiteData d) (hd : 3 ≤ d) (e : S.Edge) (j : Fin S.Ntr)
    {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace (srcSeedK (S.edgeCenter e) (S.seedRadius j)) S.seed.A S.seed.α S.seed.β)
    {t₀ ν : ℝ} (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 6) (hν : 0 < ν)
    (hp₀ : Routing.OnGrid ν 0 (S.port e 0)) (hp₁ : Routing.OnGrid ν 0 (S.port e 1))
    (hνN : ν ≤ Routing.gpC0 d * (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀ / (4 * √(d : ℝ))) /
      (2 * (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) : ℝ) + 5) ^ 3)
    (hνr : √(d : ℝ) * ν ≤ Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) :
    ∃ (n₀ n₁ : ℕ) (y₀ y₁ : ℕ → Rd d),
      Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 0) (witExt γ 0) (Icc t₀ 1) (witExt γ)
        (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) ν 0
        (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)) n₀ y₀ ∧
      Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 1) (witExt γ 1) (Icc 0 (1 - t₀)) (witExt γ)
        (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) ν 0
        (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)) n₁ y₁ ∧
      (∀ j ≤ n₀, ∀ j' ≤ n₁, y₀ j ≠ y₁ j') ∧
      (∀ j < n₀, ∀ j' < n₁, ∀ x ∈ segment ℝ (y₀ j) (y₀ (j + 1)),
        ∀ x' ∈ segment ℝ (y₁ j') (y₁ (j' + 1)), Routing.gpC1 4 * ν ^ 3 ≤ dist x x') := by
  have hd2 : 2 ≤ d := by omega
  rw [q5_port_zero] at hp₀ ⊢
  rw [q5_port_one] at hp₁ ⊢
  exact Routing.exists_leads hd S.seed.A_ge S.seed.α_pos S.seed.α_le S.seed.β_pos S.seed.β_le
    (S.boxHalfSide_pos hd2) (S.boxHalfSide_le_one hd2) (q5_resBox_subset S hd2 e) (S.edgeUnit_norm e) hν hp₀ hp₁
    (mem_arcSpace_iff_arcModuli.1 hγ).2 (fun t _ => q5_witExt_mem_closedBall S hd2 e j hγ t) ht₀ ht₀' hνN hνr

/-- Q3's seed radius in the form of the frozen `SiteCertOfLabel` (exhaustion clause). -/
theorem q5_seedRadius_eq (S : SiteData d) (j : Fin S.Ntr) :
    S.seedRadius j = S.boxHalfSide / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1) := by
  unfold SiteData.seedRadius
  congr 1
  rw [Real.rpow_neg (by norm_num), inv_pow]
  congr 1
  exact_mod_cast Real.rpow_natCast (8 : ℝ) ((j : ℕ) + 1)

end HigherDimLQGContinuity
