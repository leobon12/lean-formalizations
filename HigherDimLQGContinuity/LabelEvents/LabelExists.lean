import HigherDimLQGContinuity.LabelEvents.LabelSource
import HigherDimLQGContinuity.LabelEvents.SeedArc
import HigherDimLQGContinuity.Labels.LabelSources
import HigherDimLQGContinuity.Labels.OrderSpec
import HigherDimLQGContinuity.Labels.PortGrid

/-!
# Every favorable seed gives a valid label (packet Q5; Part B `b:lem-label-exists`)

Source: blueprint Part B `b:lem-label-exists` (statement, constants (F6), proof: *Arc* and *Label*), `b:lem-order`(a)
(the hypotheses of the leads), `b:def-order` (O1)–(O4); [C] l. 709, 1067–1079; planning audit NA2, items 13, 25–27,
R3, R8, R14 ("every favorable arc has a label"); rulings N24, N25, N29, N30. Inputs: this packet's
`exists_seedArc_of_seedFav` (arc part), packet Q2's `exists_leads`, packet Q3's label codes (`leadCodeOfIsLead`,
`encodeLabelIndices`, `cell_index_mem_labelCutoff`) and constants `siteConsts`.

* `exists_edgeLabel_of_arc` (**every favorable arc has a label**, NA2 R8): an arc of the arc space of a seed shell of
  the edge `e` (site constants `(A, α, β)`) has an edge label of the catalogue with the seed's trial whose geometric
  predicate it satisfies: the chamber and gate cell sets are the cells met by `γ([0, 1])`, `γ([0, 2t₀])`,
  `γ([1 - 2t₀, 1])`, the leads are those of `exists_leads`.
* `exists_labelSource_of_seedFav`: `b:lem-label-exists` for any constants `(t₀, μ, ν)` with the hypotheses of the
  leads and `L/32 + μ ≤ L`, and the (F6) seed constants.
* `exists_label_of_seedFav`: `b:lem-label-exists` with the explicit constants `siteConsts S Cnet v`, `0 < v ≤ 1/2`
  (part (iii) of `SiteCertOfLabel`); the constant facts come from Q3's `siteConsts_t₀_le_sixth`,
  `siteConsts_lead_grid_constraint`, `siteConsts_lead_short`, `siteConsts_port_onGrid`, and `q5_siteConsts_μ_le`
  (`L/32 + μ ≤ L`).
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

/-! ## Constants of the order (O1)–(O4) -/

/-- The cell side `μ = ω²/(2√d)` is positive. -/
theorem q5_siteConsts_μ_pos (S : SiteData d) (hd : 2 ≤ d) (Cnet v : ℝ) : 0 < (siteConsts S Cnet v).μ := by
  have hν0 := siteConsts_ν_pos S hd Cnet v
  have hcω0 := siteOmegaCoeff_pos d (by omega)
  have hsq : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  change 0 < (siteOmegaCoeff d * (siteConsts S Cnet v).ν ^ 4) ^ 2 / (2 * √(d : ℝ))
  positivity

/-- The cell side is small: `L/32 + μ ≤ L` (so the cells met by a seed arc lie in the reserved box). -/
theorem q5_siteConsts_μ_le (S : SiteData d) (hd : 2 ≤ d) (Cnet : ℝ) {v : ℝ} (hv : 0 < v) :
    S.boxHalfSide / 32 + (siteConsts S Cnet v).μ ≤ S.boxHalfSide := by
  set C := siteConsts S Cnet v with hC
  have hL := S.boxHalfSide_pos hd
  have hr1 := siteConsts_r_le_one S hd Cnet v hv
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hr0 := siteConsts_r_pos S hd Cnet v hv
  have hνr := siteConsts_ν_le_r_div S hd Cnet v hv hr1
  have hων := siteConsts_omega_le_nu S hd Cnet v
  have hμω := siteConsts_cell_radius_bound S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsq : 1 ≤ √(d : ℝ) := Real.one_le_sqrt.mpr hdR
  have hμ0 : 0 ≤ C.μ := (q5_siteConsts_μ_pos S hd Cnet v).le
  have hμω' : C.μ ≤ C.ω / 2 := by nlinarith [mul_le_mul_of_nonneg_right hsq hμ0]
  have hνr' : C.ν ≤ C.r := by
    refine hνr.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-! ## Labels of arcs -/



/-- Points of the trace of an encoded lead lie on its segments. -/
theorem q5_mem_trace_leadCode (S : SiteData d) (hd : 2 ≤ d) {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (p g : Rd d)
    (I : Set ℝ) (γ : ℝ → Rd d) (N n : ℕ) (y : ℕ → Rd d)
    (h : Routing.IsLead (S.edgeCenter e) S.boxHalfSide p g I γ r ν 0 N n y) {x : Rd d}
    (hx : x ∈ (leadCodeOfIsLead S hd hν e p g I γ N n y h).trace ν) :
    ∃ j < n, x ∈ segment ℝ (y j) (y (j + 1)) := by
  set P := leadCodeOfIsLead S hd hν e p g I γ N n y h with hP
  have hlast : P.last.val = n := rfl
  simp only [LeadCode.trace, mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  by_cases hjl : (j : ℕ) < P.last
  · simp only [hjl, ↓reduceIte] at hj
    have hjn : (j : ℕ) < n := by rw [← hlast]; exact_mod_cast hjl
    rw [leadCodeOfIsLead_point S hd hν e p g I γ N n y h j.castSucc (by simp; omega),
      leadCodeOfIsLead_point S hd hν e p g I γ N n y h j.succ (by simp; omega)] at hj
    exact ⟨j, hjn, by simpa using hj⟩
  · simp only [hjl, ↓reduceIte] at hj
    exact absurd hj (notMem_empty x)

/-- **Every favorable arc has a label** (NA2 R8; `b:lem-label-exists`, label part): for an arc of the arc space of
a seed shell of the edge `e` (constants of the site data), the cells met by the arc (chamber and the two gate
pieces) and the two leads of `exists_leads` form an edge label of the catalogue whose trial is the seed's and whose
geometric predicate the arc satisfies. -/
theorem exists_edgeLabel_of_arc (S : SiteData d) (hd : 3 ≤ d) (e : S.Edge) (j : Fin S.Ntr)
    {γ : C(unitInterval, Rd d)}
    (hγ : γ ∈ ArcSpace (srcSeedK (S.edgeCenter e) (S.seedRadius j)) S.seed.A S.seed.α S.seed.β)
    {t₀ μ ν : ℝ} (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 6) (hμ : 0 < μ)
    (hμL : S.boxHalfSide / 32 + μ ≤ S.boxHalfSide) (hν : 0 < ν)
    (hp₀ : Routing.OnGrid ν 0 (S.port e 0)) (hp₁ : Routing.OnGrid ν 0 (S.port e 1))
    (hνN : ν ≤ Routing.gpC0 d * (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀ / (4 * √(d : ℝ))) /
      (2 * (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) : ℝ) + 5) ^ 3)
    (hνr : √(d : ℝ) * ν ≤ Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) :
    ∃ E : EdgeLabel S e (labelCellCutoff S μ) (labelLeadCutoff ν)
        (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)) μ ν
        (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) (Routing.gpC1 4),
      E.1.trial = j ∧ labelGeo S e E t₀ γ := by
  classical
  have hd2 : 2 ≤ d := by omega
  set rL := Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀ with hrL
  set NL := Routing.leadN d rL with hNL
  set m := S.edgeCenter e with hm
  set L := S.boxHalfSide with hLdef
  set Kc := labelCellCutoff S μ with hKc
  have hL : 0 < L := S.boxHalfSide_pos hd2
  have hrL0 : 0 < rL := Routing.leadR_pos S.seed.A_ge ht₀ hL
  -- the arc stays in the closed `L/32`-ball about the box centre
  have hball : ∀ t, witExt γ t ∈ closedBall m (L / 32) := fun t => q5_witExt_mem_closedBall S hd2 e j hγ t
  -- cells met by the arc lie in the box; their indices fit the cutoff
  have hcellbox : ∀ (T : Set (Rd d)), T ⊆ closedBall m (L / 32) → ∀ k : Fin d → ℤ,
      (T ∩ cell μ m k).Nonempty → cell μ m k ⊆ S.box e := by
    intro T hT k hk
    obtain ⟨x, hxT, hxc⟩ := hk
    exact q5_cell_subset_box ⟨x, hT hxT, hxc⟩ hμL
  have hfloor : ∀ (T : Set (Rd d)), T ⊆ closedBall m (L / 32) →
      ∀ x ∈ T, q5FloorIndex μ m x ∈ labelIndexFinset d Kc := by
    intro T hT x hx
    exact cell_index_mem_labelCutoff S hμ e _
      (hcellbox T hT _ ⟨x, hx, mem_cell_q5FloorIndex hμ m x⟩)
  have himg : ∀ a b : ℝ, witExt γ '' Icc a b ⊆ closedBall m (L / 32) := by
    rintro a b _ ⟨t, _, rfl⟩
    exact hball t
  set Qch := q5MetCells μ m Kc (witExt γ '' Icc 0 1) with hQch
  set Q0 := q5MetCells μ m Kc (witExt γ '' Icc 0 (2 * t₀)) with hQ0
  set Q1 := q5MetCells μ m Kc (witExt γ '' Icc (1 - 2 * t₀) 1) with hQ1
  have hmet : ∀ (T : Set (Rd d)), T ⊆ closedBall m (L / 32) → ∀ k ∈ q5MetCells μ m Kc T,
      cell μ m k ⊆ S.box e := by
    intro T hT k hk
    rw [q5MetCells, Finset.mem_filter] at hk
    exact hcellbox T hT k hk.2
  -- the two leads
  obtain ⟨n₀, n₁, y₀, y₁, h0, h1, -, hcross⟩ :=
    q5_exists_leads_of_arc S hd e j hγ ht₀ ht₀' hν hp₀ hp₁ hνN hνr
  -- the label
  let P0 := leadCodeOfIsLead S hd2 hν e (S.port e 0) (witExt γ 0) (Icc t₀ 1) (witExt γ) NL n₀ y₀ h0
  let P1 := leadCodeOfIsLead S hd2 hν e (S.port e 1) (witExt γ 1) (Icc 0 (1 - t₀)) (witExt γ) NL n₁ y₁ h1
  have hchK : ∀ k ∈ Qch, k ∈ labelIndexFinset d Kc := fun k hk =>
    cell_index_mem_labelCutoff S hμ e k (hmet _ (himg 0 1) k hk)
  have h0K : ∀ k ∈ Q0, k ∈ labelIndexFinset d Kc := fun k hk =>
    cell_index_mem_labelCutoff S hμ e k (hmet _ (himg 0 (2 * t₀)) k hk)
  have h1K : ∀ k ∈ Q1, k ∈ labelIndexFinset d Kc := fun k hk =>
    cell_index_mem_labelCutoff S hμ e k (hmet _ (himg (1 - 2 * t₀) 1) k hk)
  let C : EdgeLabelCode S Kc (labelLeadCutoff ν) NL :=
    ⟨j, encodeLabelIndices Qch hchK, encodeLabelIndices Q0 h0K, encodeLabelIndices Q1 h1K, P0, P1⟩
  have hgeom : C.Geometry S e μ ν rL (Routing.gpC1 4) := by
    refine ⟨?_, ?_, ?_, leadCodeOfIsLead_geometry S hd2 hν e _ _ _ _ NL n₀ y₀ h0,
      leadCodeOfIsLead_geometry S hd2 hν e _ _ _ _ NL n₁ y₁ h1, ?_⟩
    · intro k hk
      rw [labelCellIndices_encode] at hk
      exact hmet _ (himg 0 1) k hk
    · intro k hk
      rw [labelCellIndices_encode] at hk
      exact hmet _ (himg 0 (2 * t₀)) k hk
    · intro k hk
      rw [labelCellIndices_encode] at hk
      exact hmet _ (himg (1 - 2 * t₀) 1) k hk
    · intro a a' ha ha' x hx x' hx'
      have ha0 : (a : ℕ) < n₀ := ha
      have ha1 : (a' : ℕ) < n₁ := ha'
      rw [leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₀ y₀ h0 a.castSucc (by simp; omega),
        leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₀ y₀ h0 a.succ (by simp; omega)] at hx
      rw [leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₁ y₁ h1 a'.castSucc (by simp; omega),
        leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₁ y₁ h1 a'.succ (by simp; omega)] at hx'
      exact hcross a ha0 a' ha1 x (by simpa using hx) x' (by simpa using hx')
  refine ⟨⟨C, hgeom⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change CoveredHit μ m (labelCellIndices (encodeLabelIndices Qch hchK)) (witExt γ '' Icc 0 1)
    rw [labelCellIndices_encode]
    exact coveredHit_q5MetCells hμ m Kc (hfloor _ (himg 0 1))
  · change CoveredHit μ m (labelCellIndices (encodeLabelIndices Q0 h0K)) (witExt γ '' Icc 0 (2 * t₀))
    rw [labelCellIndices_encode]
    exact coveredHit_q5MetCells hμ m Kc (hfloor _ (himg 0 (2 * t₀)))
  · change CoveredHit μ m (labelCellIndices (encodeLabelIndices Q1 h1K)) (witExt γ '' Icc (1 - 2 * t₀) 1)
    rw [labelCellIndices_encode]
    exact coveredHit_q5MetCells hμ m Kc (hfloor _ (himg (1 - 2 * t₀) 1))
  · intro x hx t ht
    obtain ⟨a, ha, hxa⟩ := q5_mem_trace_leadCode S hd2 hν e _ _ _ _ NL n₀ y₀ h0 hx
    have := h0.clear a ha x hxa t ht
    linarith
  · intro x hx t ht
    obtain ⟨a, ha, hxa⟩ := q5_mem_trace_leadCode S hd2 hν e _ _ _ _ NL n₁ y₁ h1 hx
    have := h1.clear a ha x hxa t ht
    linarith
  · change dist (P0.point ν P0.last) (γ 0) ≤ d * ν
    rw [leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₀ y₀ h0 P0.last le_rfl, dist_eq_norm, ← witExt_zero]
    refine h0.attach.trans ?_
    have hsq : √(d : ℝ) ≤ d := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      nlinarith
    nlinarith
  · change dist (P1.point ν P1.last) (γ 1) ≤ d * ν
    rw [leadCodeOfIsLead_point S hd2 hν e _ _ _ _ NL n₁ y₁ h1 P1.last le_rfl, dist_eq_norm, ← witExt_one]
    refine h1.attach.trans ?_
    have hsq : √(d : ℝ) ≤ d := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      nlinarith
    nlinarith

/-- **Every favorable seed gives a valid label** (Part B `b:lem-label-exists`; part (iii) of `SiteCertOfLabel`), for
the (F6) seed constants and constants `(t₀, μ, ν)` satisfying the hypotheses of the leads (`b:lem-order`(a)) and the
cell size: if `D, E` are continuous length metrics with `SiteRefs(D)` and a favorable seed on every edge, then some
label of the catalogue is source-valid. -/
theorem exists_labelSource_of_seedFav (S : SiteData d) (hd : 3 ≤ d)
    (hHE : S.seed.HE = seedConstHE S.seed.Hsd S.seed.σsd S.seed.Λ S.seedMin) (hsE : S.seed.sE = S.seed.σsd)
    (hA : S.seed.A = seedConstA S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seedMin)
    (hα : S.seed.α = 1 / S.seed.β₀) (hβ : S.seed.β = S.seed.σ₀)
    (hℓ₀ : S.seed.ℓ₀ = seedConstEll0 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seed.Λ)
    (hℓ₁ : S.seed.ℓ₁ = seedConstEll1 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.M S.seed.Λ)
    (hd₀ : S.seed.d₀ = seedConstD0 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seed.Λ)
    {t₀ μ ν v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1 / 2) (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 6) (hμ : 0 < μ)
    (hμL : S.boxHalfSide / 32 + μ ≤ S.boxHalfSide) (hν : 0 < ν)
    (hgrid : ∀ e i, Routing.OnGrid ν 0 (S.port e i))
    (hνN : ν ≤ Routing.gpC0 d * (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀ / (4 * √(d : ℝ))) /
      (2 * (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) : ℝ) + 5) ^ 3)
    (hνr : √(d : ℝ) * ν ≤ Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)
    {D E : ContMetric d} (hD : D.IsLength) (hE : E.IsLength) (hR : SiteRefs S.Hup S.s S.Hlo S.b S.mc S.A0 D)
    (hfav : ∀ e : S.Edge, ∃ j : Fin S.Ntr, SeedFav S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M
      S.seed.Hsd S.seed.σsd S.seed.Λ v D E (S.edgeCenter e) (S.seedRadius j)) :
    ∃ ℓ : SiteLabel S (labelCellCutoff S μ) (labelLeadCutoff ν)
        (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)) μ ν
        (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) (Routing.gpC1 4),
      labelSource S t₀ v ℓ D E := by
  have hd2 : 2 ≤ d := by omega
  have hsmin : 0 < S.seedMin := by
    unfold SiteData.seedMin
    exact mul_pos (div_pos (S.boxHalfSide_pos hd2) (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)
  have key : ∀ e : S.Edge, ∃ Ee : EdgeLabel S e (labelCellCutoff S μ) (labelLeadCutoff ν)
      (Routing.leadN d (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀)) μ ν
      (Routing.leadR S.seed.A S.seed.α S.seed.β S.boxHalfSide t₀) (Routing.gpC1 4),
      EdgeSource S.seed.HE S.seed.sE S.seed.A S.seed.α S.seed.β S.seed.ℓ₀ S.seed.ℓ₁ S.seed.d₀ v
        (S.edgeCenter e) (S.seedRadius Ee.1.trial) (fun γ => labelGeo S e Ee t₀ γ) D E := by
    intro e
    obtain ⟨j, hj⟩ := hfav e
    have hsr : S.seedMin ≤ S.seedRadius j := q5_seedMin_le_seedRadius S j hd2
    have hr1 : S.seedRadius j ≤ 1 :=
      (q5_seedRadius_le S hd2 j).trans (by linarith [S.boxHalfSide_le_one hd2])
    obtain ⟨hup, γ, hγ, lam, hlam, ha, hb, hc, hfe⟩ :=
      exists_seedArc_of_seedFav hD hE (by linarith [S.seed.H₀_ge]) S.seed.σ₀_pos
        (by linarith [S.seed.β₀_gt]) S.seed.m_pos (by linarith [S.seed.Hsd_ge]) S.seed.σsd_pos.le hv hv1
        hsmin hsr hr1 hj
    rw [← hA, ← hα, ← hβ] at hγ
    obtain ⟨Ee, hEj, hgeo⟩ :=
      exists_edgeLabel_of_arc S hd e j hγ ht₀ ht₀' hμ hμL hν (hgrid e 0) (hgrid e 1) hνN hνr
    refine ⟨Ee, ?_⟩
    rw [hEj]
    refine ⟨by rwa [hHE, hsE], γ, hγ, lam, by rwa [hℓ₀, hℓ₁], ha, by rwa [hd₀], hc, hfe, hgeo⟩
  choose ℓ hℓ using key
  exact ⟨ℓ, hR, hℓ⟩

/-- **Every favorable seed gives a valid label** (Part B `b:lem-label-exists`; part (iii) of `SiteCertOfLabel`) with
the explicit constants (O1)–(O10) of `siteConsts` at a tolerance `v ∈ (0, 1/2]` and the (F6) seed constants: if
`D, E` are continuous length metrics with `SiteRefs(D)` and a favorable seed on every edge, some label of the
catalogue is source-valid. -/
theorem exists_label_of_seedFav (S : SiteData d) (hd : 3 ≤ d)
    (hHE : S.seed.HE = seedConstHE S.seed.Hsd S.seed.σsd S.seed.Λ S.seedMin) (hsE : S.seed.sE = S.seed.σsd)
    (hA : S.seed.A = seedConstA S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seedMin)
    (hα : S.seed.α = 1 / S.seed.β₀) (hβ : S.seed.β = S.seed.σ₀)
    (hℓ₀ : S.seed.ℓ₀ = seedConstEll0 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seed.Λ)
    (hℓ₁ : S.seed.ℓ₁ = seedConstEll1 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.M S.seed.Λ)
    (hd₀ : S.seed.d₀ = seedConstD0 S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M S.seed.Λ)
    (Cnet : ℝ) {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 2)
    {D E : ContMetric d} (hD : D.IsLength) (hE : E.IsLength) (hR : SiteRefs S.Hup S.s S.Hlo S.b S.mc S.A0 D)
    (hfav : ∀ e : S.Edge, ∃ j : Fin S.Ntr, SeedFav S.seed.H₀ S.seed.σ₀ S.seed.β₀ S.seed.m S.seed.M
      S.seed.Hsd S.seed.σsd S.seed.Λ v D E (S.edgeCenter e) (S.seedRadius j)) :
    ∃ ℓ : SiteLabel S (labelCellCutoff S (siteConsts S Cnet v).μ) (labelLeadCutoff (siteConsts S Cnet v).ν)
        (siteConsts S Cnet v).N (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν (siteConsts S Cnet v).r
        (Routing.gpC1 4),
      labelSource S (siteConsts S Cnet v).t₀ v ℓ D E := by
  have hd2 : 2 ≤ d := by omega
  have hr1 := siteConsts_r_le_one S hd2 Cnet v hv
  exact exists_labelSource_of_seedFav S hd hHE hsE hA hα hβ hℓ₀ hℓ₁ hd₀ hv.le hv1
    (siteConsts_t₀_pos S Cnet v hv) (siteConsts_t₀_le_sixth S Cnet v hv (by linarith))
    (q5_siteConsts_μ_pos S hd2 Cnet v) (q5_siteConsts_μ_le S hd2 Cnet hv)
    (siteConsts_ν_pos S hd2 Cnet v) (fun e i => siteConsts_port_onGrid S hd2 Cnet v e i)
    (siteConsts_lead_grid_constraint S hd2 Cnet v hv hr1) (siteConsts_lead_short S hd2 Cnet v hv hr1).1
    hD hE hR hfav

end HigherDimLQGContinuity
