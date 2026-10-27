import Mathlib
import MatedCRTHarmonic.MesoModel.TransferScaling
import MatedCRTHarmonic.CellScaling.Model

/-!
# Joint scaling: the mesh-`2^{-k}` event and the unit-scale event at radius `R_{2^k}` have the same probability

In the joint-scaling identity, dilation by `R_b` identifies the `1/b`-cell configuration
for `(h_b, η^b)` with the unit-cell configuration for `(h, η)`. The cell identity is **deterministic**:
`H^{1/b}_x(h_b, η^b) = R_b⁻¹ H^1_x(h, η)` (ℤ-indexing), and `x ↦ x` is a multigraph identity
`G^{1/b}(b^{-1/2} bm(b ·)) = G^1(bm)` (Brownian scaling of Definition 1.12; `MesoModel.graphCast_eq_unitRescalePath`).
The law identity (the joint-scaling identity as printed, plus the boundary-length covariance) then transfers probabilities.

Main results:
* `rawScaledGridControl_smul_iff`: dilation covariance of the scaled-grid estimate event (deterministic);
* `rawScaledGridControl_unit_iff_meshGridGood`: the unit-mesh event of `(bm, η)` at radius `c` is the mesh-`2^{-k}`
  event of `(b^{-1/2} bm(b ·), c⁻¹ η(b ·))`, `b = 2^k` (deterministic);
* `configScalingLaw`: `(b^{-1/2} bm(b ·), η^b) =d (bm, η)` from `Prop23JointScaling` and `BoundaryLengthCovariance`;
* `matedCRTProposition23GridScalingInput_of_cone`: `MesoModel.MatedCRTProposition23GridScalingInput`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Pointwise

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-! ### Dilations of sets in `ℂ` by positive reals -/

section Dilation

variable {c : ℝ}

theorem smul_ball_pos (hc : 0 < c) (z : ℂ) (r : ℝ) : c • ball z r = ball (c • z) (c * r) := by
  rw [_root_.smul_ball (ne_of_gt hc), Real.norm_of_nonneg (le_of_lt hc)]

theorem smul_sphere_pos (hc : 0 < c) (z : ℂ) (r : ℝ) : c • sphere z r = sphere (c • z) (c * r) := by
  rw [smul_sphere' (ne_of_gt hc), Real.norm_of_nonneg (le_of_lt hc)]

theorem smul_annulus_pos (hc : 0 < c) (z : ℂ) (r s : ℝ) :
    c • annulus z r s = annulus (c • z) (c * r) (c * s) := by
  unfold annulus
  rw [Set.smul_set_sdiff₀ (ne_of_gt hc), smul_ball_pos hc, smul_ball_pos hc]

theorem inter_smul_nonempty_iff (hc : 0 < c) (A S : Set ℂ) :
    (c⁻¹ • A ∩ S).Nonempty ↔ (A ∩ c • S).Nonempty := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h : c⁻¹ • A ∩ S = c⁻¹ • (A ∩ c • S) := by
    rw [Set.smul_set_inter₀ (inv_ne_zero hc0), inv_smul_smul₀ hc0]
  rw [h, Set.smul_set_nonempty]

theorem verticesMeeting_smul (hc : 0 < c) (J : ℤ → Set ℂ) (S : Set ℂ) :
    verticesMeeting (fun x => c⁻¹ • J x) S = verticesMeeting J (c • S) := by
  ext x
  exact inter_smul_nonempty_iff hc (J x) S

theorem smul_subset_iff_pos (hc : 0 < c) (A S : Set ℂ) : c⁻¹ • A ⊆ S ↔ A ⊆ c • S := by
  rw [Set.smul_set_subset_iff₀ (inv_ne_zero (ne_of_gt hc)), inv_inv]

theorem diam_inv_smul (hc : 0 < c) (A : Set ℂ) : diam (c⁻¹ • A) = c⁻¹ * diam A := by
  rw [diam_smul₀, Real.norm_of_nonneg (le_of_lt (inv_pos.2 hc))]

end Dilation

/-! ### Dilation covariance of the annular event and of the scaled-grid estimate event -/

theorem annularEvent_smul_iff {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ} (hc : 0 < c)
    (z : ℂ) (r : ℝ) (X : ℕ → ℤ) :
    G.AnnularEvent (fun x => c⁻¹ • J x) z r X ↔ G.AnnularEvent J (c • z) (c * r) X := by
  unfold LFMultigraph.AnnularEvent
  simp only [verticesMeeting_smul hc, smul_annulus_pos hc, smul_sphere_pos hc, smul_subset_iff_pos hc]
  have e1 : c * (r / 2) = c * r / 2 := by ring
  have e2 : c * (3 * r / 2) = 3 * (c * r) / 2 := by ring
  have e3 : c * (3 * r / 4) = 3 * (c * r) / 4 := by ring
  have e4 : c * (5 * r / 4) = 5 * (c * r) / 4 := by ring
  have e5 : c * (r / 3) = c * r / 3 := by ring
  have e6 : c * (5 * r / 3) = 5 * (c * r) / 3 := by ring
  rw [e1, e2, e3, e4, e5, e6]

theorem rawScaledGridControl_of_smul {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ}
    (hc : 0 < c) {R ε χ β q ρ p : ℝ} (h : RawScaledGridControl G (fun x => c⁻¹ • J x) R ε χ β q ρ p) :
    RawScaledGridControl G J (c * R) ε χ β q ρ p := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, fun m n k hz hβ hρ hball x hx => ?_⟩
  · have hx' : (c⁻¹ • J x ∩ ball 0 (ρ * R)).Nonempty := by
      rw [inter_smul_nonempty_iff hc, smul_ball_pos hc, smul_zero]
      convert hx using 3
      ring
    have hd := h1 x hx'
    rw [diam_inv_smul hc] at hd
    have := (inv_mul_le_iff₀ hc).1 hd
    calc diam (J x) ≤ c * (R * ε ^ q) := this
      _ = c * R * ε ^ q := by ring
  · set w : ℂ := (m : ℂ) + (n : ℂ) * Complex.I
    set z' : ℂ := ((R * ε ^ χ : ℝ) : ℂ) * w with hz'
    have hzc : ((c * R * ε ^ χ : ℝ) : ℂ) * w = c • z' := by
      rw [hz', Complex.real_smul]; push_cast; ring
    have hrc : c * R * ε ^ χ * k = c * (R * ε ^ χ * k) := by ring
    rw [hzc] at hz hball hx ⊢
    rw [hrc] at hball hx ⊢
    have hz' : z' ∈ ball (0 : ℂ) (ρ * R) := by
      rw [mem_ball_zero_iff] at hz ⊢
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)] at hz
      nlinarith
    have hβ' : R * ε ^ β ≤ R * ε ^ χ * k := by nlinarith
    have hρ' : R * ε ^ χ * k ≤ ρ * R := by nlinarith
    have hball' : ball z' (2 * (R * ε ^ χ * k)) ⊆ ball (0 : ℂ) (ρ * R) := by
      rw [← Set.smul_set_subset_smul_set_iff₀ (ne_of_gt hc), smul_ball_pos hc, smul_ball_pos hc,
        smul_zero]
      convert hball using 2 <;> ring
    have hx' : x ∈ verticesMeeting (fun x => c⁻¹ • J x) (sphere z' (R * ε ^ χ * k)) := by
      rw [verticesMeeting_smul hc, smul_sphere_pos hc]
      exact hx
    have hmain := h2 m n k hz' hβ' hρ' hball' x hx'
    have hset : {ω | G.AnnularEvent (fun x => c⁻¹ • J x) z' (R * ε ^ χ * k) (G.vertexPath ω)} =
        {ω | G.AnnularEvent J (c • z') (c * (R * ε ^ χ * k)) (G.vertexPath ω)} := by
      ext ω
      exact annularEvent_smul_iff G J hc z' _ _
    rw [hset] at hmain
    exact hmain

/-- **Dilation covariance of the scaled-grid estimate event** (deterministic): shrinking all cells by `c > 0` and the
scale by `c` gives the same event. -/
theorem rawScaledGridControl_smul_iff {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) {c : ℝ}
    (hc : 0 < c) (R ε χ β q ρ p : ℝ) :
    RawScaledGridControl G (fun x => c⁻¹ • J x) R ε χ β q ρ p ↔
      RawScaledGridControl G J (c * R) ε χ β q ρ p := by
  refine ⟨rawScaledGridControl_of_smul G J hc, fun h => ?_⟩
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  have hJ : (fun x => c⁻¹⁻¹ • (fun x => c⁻¹ • J x) x) = J := by
    funext x
    simp only [inv_inv, smul_inv_smul₀ (ne_of_gt hc)]
  have h' : RawScaledGridControl G (fun x => c⁻¹⁻¹ • (fun x => c⁻¹ • J x) x) (c * R) ε χ β q ρ p := by
    rw [hJ]; exact h
  have := rawScaledGridControl_of_smul G (fun x => c⁻¹ • J x) hc' h'
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul] at this

/-! ### Transport along the edge-type identification -/

theorem rawScaledGridControl_cast_iff {E F : Type} (hEF : E = F) {G : LFMultigraph ℤ E}
    {G' : LFMultigraph ℤ F} (hG : cast (congrArg (LFMultigraph ℤ) hEF) G = G') (J : ℤ → Set ℂ)
    (R ε χ β q ρ p : ℝ) :
    RawScaledGridControl G J R ε χ β q ρ p ↔ RawScaledGridControl G' J R ε χ β q ρ p := by
  cases hEF
  change G = G' at hG
  subst G'
  rfl

theorem rawScaledGridControl_graph_congr {ε : ℝ} {Z₁ Z₂ : MatedCRT.Path2} (e : Z₁ = Z₂)
    (h₁ : MatedCRT.IsLocallyFinite ε Z₁) (h₂ : MatedCRT.IsLocallyFinite ε Z₂) (J : ℤ → Set ℂ)
    (R ε' χ β q ρ p : ℝ) :
    RawScaledGridControl (MatedCRT.graph ε Z₁ h₁) J R ε' χ β q ρ p ↔
      RawScaledGridControl (MatedCRT.graph ε Z₂ h₂) J R ε' χ β q ρ p := by
  subst e
  rfl

/-! ### The deterministic cell and graph identities of the joint-scaling identity -/

theorem mesh_mul_two_pow (k : ℕ) : CellFamily.mesh k * (2 : ℝ) ^ k = 1 := by
  unfold CellFamily.mesh
  rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]

theorem mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := by
  unfold CellFamily.mesh; positivity

/-- `unitRescalePath (2^{-k}) (b^{-1/2} Z(b ·)) = Z` for `b = 2^k`. -/
theorem unitRescalePath_brownRescale (k : ℕ) (Z : MatedCRT.Path2) :
    MesoModel.unitRescalePath (CellFamily.mesh k) (brownRescale ((2 : ℝ) ^ k) Z) = Z := by
  ext t
  · simp only [MesoModel.unitRescalePath, brownRescale, ContinuousMap.coe_mk, Prod.smul_fst, smul_eq_mul]
    have hmul : (2 : ℝ) ^ k * (CellFamily.mesh k * t) = t := by
      rw [← mul_assoc, mul_comm ((2 : ℝ) ^ k), mesh_mul_two_pow, one_mul]
    rw [hmul, ← mul_assoc]
    have hsq : (Real.sqrt (CellFamily.mesh k))⁻¹ * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = 1 := by
      have hm : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
        unfold CellFamily.mesh; rw [zpow_neg, zpow_natCast]
      rw [hm, Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
      norm_num
    rw [hsq, one_mul]
  · simp only [MesoModel.unitRescalePath, brownRescale, ContinuousMap.coe_mk, Prod.smul_snd, smul_eq_mul]
    have hmul : (2 : ℝ) ^ k * (CellFamily.mesh k * t) = t := by
      rw [← mul_assoc, mul_comm ((2 : ℝ) ^ k), mesh_mul_two_pow, one_mul]
    rw [hmul, ← mul_assoc]
    have hsq : (Real.sqrt (CellFamily.mesh k))⁻¹ * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)) = 1 := by
      have hm : CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
        unfold CellFamily.mesh; rw [zpow_neg, zpow_natCast]
      rw [hm, Real.sqrt_inv, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
      norm_num
    rw [hsq, one_mul]

/-- The mesh-`2^{-k}` cells of `η^b = c⁻¹ η(b ·)`, `b = 2^k`, are the unit cells of `η` shrunk by `c`
(the scaling argument step 5). -/
theorem meshCells_coneRescaleCurve (k : ℕ) (c : ℝ) (η : C(ℝ, ℂ)) :
    meshCells (CellFamily.mesh k) (coneRescaleCurve c ((2 : ℝ) ^ k) η) =
      fun x : ℤ => c⁻¹ • (η '' Icc ((x : ℝ) - 1) x) := by
  funext x
  have hb : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have himg : (fun t : ℝ => (2 : ℝ) ^ k * t) '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) =
      Icc ((x : ℝ) - 1) x := by
    rw [Set.image_mul_left_Icc' hb, ← mul_assoc, ← mul_assoc, mul_comm ((2 : ℝ) ^ k),
      mesh_mul_two_pow, one_mul, one_mul]
  ext w
  simp only [meshCells, coneRescaleCurve, ContinuousMap.coe_mk, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨η ((2 : ℝ) ^ k * t), ⟨(2 : ℝ) ^ k * t, ?_, rfl⟩, ?_⟩
    · rw [← himg]; exact ⟨t, ht, rfl⟩
    · rw [Complex.real_smul]
  · rintro ⟨y, ⟨s, hs, rfl⟩, rfl⟩
    rw [← himg] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, ht, by rw [Complex.real_smul]⟩

/-- **Cell-configuration identity, event form** (deterministic): the unit-mesh scaled-grid event of `(Z, η)` at scale
`c` is the mesh-`2^{-k}` event at scale `1` of the rescaled data `(2^{-k/2} Z(2^k ·), c⁻¹ η(2^k ·))`. -/
theorem rawScaledGridControl_unit_iff_meshGridGood (k : ℕ) (Z : MatedCRT.Path2)
    (hlf : MatedCRT.IsLocallyFinite 1 Z) (η : C(ℝ, ℂ)) {c : ℝ} (hc : 0 < c) (χ β q ρ p : ℝ) :
    RawScaledGridControl (MatedCRT.graph 1 Z hlf) (fun x => η '' Icc ((x : ℝ) - 1) x) c
        (CellFamily.mesh k) χ β q ρ p ↔
      (brownRescale ((2 : ℝ) ^ k) Z, coneRescaleCurve c ((2 : ℝ) ^ k) η) ∈ meshGridGood k χ β q ρ p := by
  set Zb := brownRescale ((2 : ℝ) ^ k) Z with hZb
  have hpath : MesoModel.unitRescalePath (CellFamily.mesh k) Zb = Z := unitRescalePath_brownRescale k Z
  have hlfb : MatedCRT.IsLocallyFinite (CellFamily.mesh k) Zb := by
    rw [MesoModel.isLocallyFinite_unitRescalePath_iff (mesh_pos k), hpath]
    exact hlf
  have hlf1 : MatedCRT.IsLocallyFinite 1 (MesoModel.unitRescalePath (CellFamily.mesh k) Zb) := by
    rw [hpath]; exact hlf
  have hgraph := MesoModel.graphCast_eq_unitRescalePath (mesh_pos k) Zb hlfb hlf1
  have hcells := meshCells_coneRescaleCurve k c η
  constructor
  · intro h
    refine ⟨hlfb, ?_⟩
    rw [hcells, rawScaledGridControl_cast_iff (MesoModel.edgeTypeEq_unitRescalePath (mesh_pos k) Zb) hgraph,
      rawScaledGridControl_graph_congr hpath hlf1 hlf, rawScaledGridControl_smul_iff _ _ hc, mul_one]
    exact h
  · rintro ⟨hlfb', h⟩
    rw [hcells, rawScaledGridControl_cast_iff (MesoModel.edgeTypeEq_unitRescalePath (mesh_pos k) Zb)
      (MesoModel.graphCast_eq_unitRescalePath (mesh_pos k) Zb hlfb' hlf1),
      rawScaledGridControl_graph_congr hpath hlf1 hlf, rawScaledGridControl_smul_iff _ _ hc, mul_one] at h
    exact h

/-! ### The law of the rescaled configuration -/

/-- **`(b^{-1/2} bm(b ·), η^b) =d (bm, η)`** for every `b > 0` (from the joint-scaling identity as printed and the
boundary-length covariance): equality of probabilities of every measurable set of `(path, curve)` pairs. -/
theorem configScalingLaw {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)
    (h23 : Prop23JointScaling D) (hBL : BoundaryLengthCovariance D) {b : ℝ} (hb : 0 < b)
    {S : Set (MatedCRT.Path2 × C(ℝ, ℂ))} (hS : MeasurableSet S) :
    M.coupled.family.P {ω | (brownRescale b (M.coupled.bm ω),
        coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =
      M.coupled.family.P {ω | (M.coupled.bm ω, D.curve ω) ∈ S} := by
  obtain ⟨BL, hBLm, hbm, hcov⟩ := hBL
  set G : LQGMetric.DistC × C(ℝ, ℂ) → MatedCRT.Path2 × C(ℝ, ℂ) := fun d => (BL d, d.2) with hG
  have hGm : Measurable G := hBLm.prodMk measurable_snd
  have hS' : MeasurableSet (G ⁻¹' S) := hGm hS
  have h1 : {ω | (brownRescale b (M.coupled.bm ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈ S} =ᵐ[M.coupled.family.P]
      {ω | (coneRescaleField γ (D.scale b ω) b (D.field ω), coneRescaleCurve (D.scale b ω) b (D.curve ω)) ∈
        G ⁻¹' S} := by
    filter_upwards [hcov b hb] with ω hω
    simp only [mem_preimage, hG, hω]
  have h2 : {ω | (M.coupled.bm ω, D.curve ω) ∈ S} =ᵐ[M.coupled.family.P]
      {ω | (D.field ω, D.curve ω) ∈ G ⁻¹' S} := by
    filter_upwards [hbm] with ω hω
    simp only [mem_preimage, hG, hω]
  rw [measure_congr h1, measure_congr h2]
  exact h23 b hb _ hS'

/-! ### Joint scaling in the form used in the mesoscopic construction -/

/-- **the joint-scaling identity, §6 event-transfer form** : the mesoscopic construction's
`MesoModel.MatedCRTProposition23GridScalingInput`, for the SLE/LQG cone realization, from the joint-scaling identity as printed
(`Prop23JointScaling`), the boundary-length covariance and the measurability of the mesh event. -/
theorem matedCRTProposition23GridScalingInput_of_cone {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) (h23 : Prop23JointScaling D) (hBL : BoundaryLengthCovariance D)
    (hmeas : MeshGridEventMeasurable) :
    MesoModel.MatedCRTProposition23GridScalingInput M := by
  intro k χ β p
  set S := meshGridGood k χ β M.q M.ρ p with hS
  have hb : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hconf := configScalingLaw D h23 hBL hb (hmeas k χ β M.q M.ρ p).compl
  have hunit : {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k) χ β M.q M.ρ p}
      =ᵐ[M.coupled.family.P] {ω | (brownRescale ((2 : ℝ) ^ k) (M.coupled.bm ω),
        coneRescaleCurve (D.scale ((2 : ℝ) ^ k) ω) ((2 : ℝ) ^ k) (D.curve ω)) ∈ Sᶜ} := by
    filter_upwards [D.radius_eq, D.cell_eq] with ω hrad hcell
    have hcellfun : (M.unitEmbedding ω).cell = fun x : ℤ => D.curve ω '' Icc ((x : ℝ) - 1) x := by
      funext x
      rw [M.unitEmbedding_cell ω]
      exact hcell x
    have hR : M.radius ω k = D.scale ((2 : ℝ) ^ k) ω := hrad k
    have hc : 0 < D.scale ((2 : ℝ) ^ k) ω := Real.exp_pos _
    apply propext
    change (¬ RawScaledGridControl _ (M.unitEmbedding ω).cell (M.radius ω k) (CellFamily.mesh k) χ β M.q M.ρ p) ↔ _
    rw [hcellfun, hR, rawScaledGridControl_unit_iff_meshGridGood k _ (M.unitLocallyFinite ω) _ hc]
    rfl
  have hfam : {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β M.q M.ρ p}
      =ᵐ[M.coupled.family.P] {ω | (M.coupled.bm ω, D.curve ω) ∈ Sᶜ} := by
    filter_upwards [D.meshCell_eq k, M.coupled.meshGraph_eq k] with ω hcell hgraph
    obtain ⟨hE, hlf, hG⟩ := hgraph
    have hcellfun : (M.coupled.family.H k ω).cell = meshCells (CellFamily.mesh k) (D.curve ω) := by
      funext x
      exact hcell x
    apply propext
    change (¬ RawScaledGridControl _ (M.coupled.family.H k ω).cell 1 (CellFamily.mesh k) χ β M.q M.ρ p) ↔ _
    rw [hcellfun, rawScaledGridControl_cast_iff hE hG]
    simp only [mem_compl_iff, hS, meshGridGood, mem_ofPred_eq]
    constructor
    · intro h ⟨hlf', h'⟩
      exact h h'
    · intro h h'
      exact h ⟨hlf, h'⟩
  rw [measure_congr hunit, measure_congr hfam]
  exact hconf

end MatedCRTHarmonic.CellScaling
