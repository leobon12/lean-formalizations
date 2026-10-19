import HigherDimLFPP.Lower.AtomCoupling
import HigherDimLFPP.Field.GraphMeasure

/-!
# Normalized arclength of equal-edge polygons (lower comparison, source §5.1–§5.2)

Packet P-L3 (ruling H6; audit HA4, "Details for later use" D4 (K3)–(K5), D5 steps 1 and 6,
D6 Step 1).  For a polygon `V 0, …, V K` all of whose edges have length `q`, normalized
arclength is `polyM K V = K⁻¹ Σ_i ν_{[V i, V (i+1)]}` (P-U1's `Upper.segSum`).

* `polyM_eq_map_rampPath`, `rampPath_eq_polyPath`: it is the push-forward of Lebesgue measure
  on `[0, 1]` under the uniform-speed parametrization (P-L1's `polyPath`).
* `polyM_eq_sum_map`: the equal-edge identity `ν_{j, ν₀} = ν_j`, i.e.
  `polyM K V = K⁻¹ Σ_i (T_i)_* ν₀` for the edge similarities `T_i` (source after (5.11)).
* `growthBound_polyM`: forward polygons with small edge angles have the linear growth bound
  (3.4) with constant `4` at scale `1` (HA4 (K4)).
* `coupledWithin_polyM_graph`: the equal-parameter coupling of the Lemma 5.1 polygon with the
  graph measure `μ_{δ g_{j,δ}}` within `δ² E₀` (HA4 D5, step 1).
* `coupledWithin_riemann_polyM`, `coupledWithin_riemann_ref`: the left Riemann measures
  `ν_j^N`, `ν₀^N` are coupled with `ν_j`, `ν₀` within `q/N`, `1/N` (HA4 D5, step 6).
* `coupledWithin_repl_polyM`: for `μ ∈ C_δ`-type data the replaced measure
  `ν_{j,μ} = K⁻¹ Σ_i (T_i)_* μ` is coupled with `ν_j` within `q (r + m)` (source (5.17),
  HA4 D6 Step 1).

2D source: none.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-- Normalized arclength of a polygon `V 0, …, V K` with `K` edges of equal length:
`K⁻¹ Σ_{i < K} ν_{[V i, V (i+1)]}`. -/
def polyM (K : ℕ) (V : ℕ → Rd d) : Measure (Rd d) := Upper.segSum K (fun _ => 1 / (K : ℝ)) V

theorem isProbabilityMeasure_polyM {K : ℕ} (hK : 0 < K) (V : ℕ → Rd d) :
    IsProbabilityMeasure (polyM K V) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨?_⟩
  rw [polyM, Upper.segSum_univ V fun i _ => by positivity, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one_div_cancel hK'.ne', ENNReal.ofReal_one]

/-- The uniform-speed ramp path with breakpoints `i/K` agrees with P-L1's `polyPath` on
`[0, 1]`. -/
theorem rampPath_eq_polyPath {K : ℕ} (hK : 0 < K) (V : ℕ → Rd d) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : rampPath K (fun i => (i : ℝ) / K) V s = polyPath V K s := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hT : ∀ i < K, (i : ℝ) / K < ((i + 1 : ℕ) : ℝ) / K := fun i _ => by
    push_cast
    exact div_lt_div_of_pos_right (by linarith) hK'
  set i := idx K s with hi
  have hiK : i < K := idx_lt K hK s
  have hsi := mem_Icc_idx K hK s hs.1 hs.2
  have hsi' : s ∈ Icc ((i : ℝ) / K) (((i + 1 : ℕ) : ℝ) / K) := by
    push_cast
    exact hsi
  rw [rampPath_eq V hT hiK hsi', polyPath_eq_edgeAff V K hK i hiK s hsi, edgeAff]
  congr 1
  congr 1
  push_cast
  field_simp
  ring

/-- `polyM` is the push-forward of Lebesgue measure on `[0,1]` under the ramp path. -/
theorem polyM_eq_map_rampPath {K : ℕ} (hK : 0 < K) (V : ℕ → Rd d) :
    polyM K V = (volume.restrict (Icc (0 : ℝ) 1)).map (rampPath K (fun i => (i : ℝ) / K) V) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hT : ∀ i < K, (fun i : ℕ => (i : ℝ) / K) i < (fun i : ℕ => (i : ℝ) / K) (i + 1) :=
    fun i _ => by
      simp only
      push_cast
      exact div_lt_div_of_pos_right (by linarith) hK'
  rw [map_rampPath V hT (by simp) (by simp [div_self hK'.ne']), polyM]
  congr 1
  funext i
  push_cast
  field_simp
  ring

/-- The image of `ν₀ = 𝓛` under an edge similarity is the uniform measure on the edge. -/
theorem segMeasure_map_edgeSim (hd : 0 < d) {q : ℝ} (hq : 0 < q) {V : ℕ → Rd d} {i : ℕ}
    (hlen : ‖V (i + 1) - V i‖ = q) :
    (Upper.segMeasure 0 (e₁ d)).map (edgeSim q V i).app = Upper.segMeasure (V i) (V (i + 1)) := by
  have hS : Measurable (edgeSim q V i).app := (edgeSim q V i).continuous_app.measurable
  rw [Upper.segMeasure_eq, Upper.segMeasure_eq, Measure.map_map hS (Upper.measurable_lin _ _)]
  congr 1
  funext s
  simp only [Function.comp_apply, Upper.lin, zero_add, sub_zero]
  rw [edgeSim_app_smul_e₁ hd hq hlen]

/-- **The equal-edge identity** `ν_{j, ν₀} = ν_j`: `polyM K V = K⁻¹ Σ_i (T_i)_* ν₀`. -/
theorem polyM_eq_sum_map (hd : 0 < d) {K : ℕ} {q : ℝ} (hq : 0 < q) {V : ℕ → Rd d}
    (hlen : ∀ i < K, ‖V (i + 1) - V i‖ = q) :
    polyM K V = ∑ i ∈ Finset.range K,
      ENNReal.ofReal (1 / (K : ℝ)) • (Upper.segMeasure 0 (e₁ d)).map (edgeSim q V i).app := by
  rw [polyM, Upper.segSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [segMeasure_map_edgeSim hd hq (hlen i (Finset.mem_range.1 hi))]

/-- **Linear growth of the equal-edge polygon** (HA4 (K4)): if every edge advances
horizontally by at least `q/2` and `K q ≥ 1`, then `ν(B̄(z, t)) ≤ min(1, 4t)`. -/
theorem growthBound_polyM (hd : 0 < d) {K : ℕ} (hK : 0 < K) {q : ℝ} (hq : 1 / (K : ℝ) ≤ q)
    {V : ℕ → Rd d} (hfwd : ∀ i < K, q / 2 ≤ horiz (V (i + 1)) - horiz (V i)) :
    GrowthBound (polyM K V) 4 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have := isProbabilityMeasure_polyM hK V
  have he : e₁ d ≠ 0 := by
    intro h
    have := norm_e₁ hd
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hproj : ∀ p : Rd d, Upper.proj 0 (e₁ d) p = horiz p := fun p => by
    rw [Upper.proj, sub_zero, norm_e₁ hd, div_one, real_inner_comm, horiz]
  intro z t ht
  have hb := Upper.forward_growth (m := K) (W := fun _ => 1 / (K : ℝ)) (V := V) 0 he
    (κ := 2) (by norm_num) (fun _ _ => by positivity) (fun i hi => by
      rw [hproj, hproj]
      have := hfwd i hi
      have : 0 < q := lt_of_lt_of_le (by positivity) hq
      linarith) (fun i hi => by
      rw [hproj, hproj]
      have := hfwd i hi
      linarith) z t
  rw [div_one]
  have h4 : polyM K V (Metric.closedBall z t) ≤ ENNReal.ofReal (4 * t) := by
    rw [polyM]
    calc Upper.segSum K (fun _ => 1 / (K : ℝ)) V (Metric.closedBall z t)
        ≤ ENNReal.ofReal (2 * 2 * t) := hb
      _ = ENNReal.ofReal (4 * t) := by ring_nf
  have := Upper.real_le_min_of_le (by positivity) h4
  calc (polyM K V).real (Metric.closedBall z t) ≤ min 1 (4 * t) := this
    _ ≤ 4 * min 1 t := by
        rcases le_total t 1 with h | h
        · rw [min_eq_right h]
          exact min_le_right _ _
        · rw [min_eq_left h]
          linarith [min_le_left 1 (4 * t)]

/-- Edges of an equal-edge polygon with angle `≤ cδ ≤ 1/2` advance horizontally by `≥ q/2`. -/
theorem half_le_horiz_edge (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {V : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c V) (hq : 0 < q) (hcδ : c * δ ≤ 1 / 2) {i : ℕ}
    (hi : i < K) : q / 2 ≤ horiz (V (i + 1)) - horiz (V i) := by
  have hang := hE.angle i hi
  have h1 : |horiz (q⁻¹ • (V (i + 1) - V i) - e₁ d)| ≤ c * δ :=
    (abs_horiz_le _ hd).trans hang
  rw [horiz_sub, horiz_e₁ hd, horiz_smul, horiz_sub] at h1
  have h2 := (abs_le.1 h1).1
  have h3 : 1 / 2 ≤ q⁻¹ * (horiz (V (i + 1)) - horiz (V i)) := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hq.le
  rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h4
  linarith

/-- **Equal-parameter coupling with the graph** (HA4 D5, step 1): the Lemma 5.1 polygon's
normalized arclength is coupled with `μ_{δ g}`, `g = f + a ψ_K v`, within `δ² E₀`. -/
theorem coupledWithin_polyM_graph (hd : 0 < d) {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → Rd (d - 1)}
    (hf : f ∈ Vg (Rd (d - 1)) n) (v : Rd (d - 1)) {a δ q E₀ M₀ c : ℝ}
    (hE : EqualEdgeData (2 ^ (n + g)) δ q E₀ M₀ c (eqVert (2 ^ (n + g)) q δ f v a)) :
    CoupledWithin (polyM (2 ^ (n + g)) (eqVert (2 ^ (n + g)) q δ f v a))
      (graphMeasure d δ (padProf (2 ^ (n + g)) f v a)) (δ ^ 2 * E₀) := by
  have hK : 0 < 2 ^ (n + g) := by positivity
  have hpad : padProf (2 ^ (n + g)) f v a ∈ Vg (Rd (d - 1)) (n + g) := padProf_mem_Vg hg hf v a
  rw [polyM_eq_map_rampPath hK, graphMeasure]
  refine coupledWithin_map (continuous_rampPath _ _ _).measurable
    (measurable_graphPt (Var.Vg_continuous hpad).measurable) fun s hs => ?_
  rw [rampPath_eq_polyPath hK _ hs, graphPt, embedT_smul]
  exact eqVert_polyPath_coupling hd hg hf v hE hs

/-- `atomM` only depends on the weights and points on the index set. -/
theorem atomM_congr {α : Type*} (A : Finset α) {c c' : α → ℝ} {p p' : α → Rd d}
    (hc : ∀ x ∈ A, c x = c' x) (hp : ∀ x ∈ A, p x = p' x) : atomM A c p = atomM A c' p' := by
  rw [atomM, atomM]
  exact Finset.sum_congr rfl fun x hx => by rw [hc x hx, hp x hx]

/-- **The left Riemann measure of an equal-edge polygon** (HA4 D5, step 6):
`ν^N = (KN)⁻¹ Σ_{i,l} δ_{T_i(l/N e₁)}` is coupled with `polyM K V` within `q/N`. -/
theorem coupledWithin_riemann_polyM (hd : 0 < d) {K N : ℕ} (hN : 0 < N) {q : ℝ} (hq : 0 < q)
    {V : ℕ → Rd d} (hlen : ∀ i < K, ‖V (i + 1) - V i‖ = q) :
    CoupledWithin (atomM (Finset.range K ×ˢ Finset.range N) (fun _ => 1 / ((K : ℝ) * N))
        (fun x => (edgeSim q V x.1).app (refPt N x.2))) (polyM K V) (q / N) := by
  have e1 : atomM (Finset.range K ×ˢ Finset.range N) (fun _ => 1 / ((K : ℝ) * N))
      (fun x => (edgeSim q V x.1).app (refPt N x.2)) =
      ∑ i ∈ Finset.range K, ENNReal.ofReal (1 / (K : ℝ)) •
        atomM (Finset.range N) (fun _ => 1 / (N : ℝ))
          (fun l => Upper.lin (V i) (V (i + 1)) ((l : ℝ) / N)) := by
    rw [sum_smul_atomM _ (by positivity)]
    refine atomM_congr _ (fun x _ => by rw [one_div_mul_one_div]) fun x hx => ?_
    rw [Finset.mem_product, Finset.mem_range] at hx
    rw [refPt, edgeSim_app_smul_e₁ hd hq (hlen x.1 hx.1)]
    rfl
  rw [e1, polyM, Upper.segSum]
  refine coupledWithin_finsetSum _ _ _ fun i hi => coupledWithin_smul _ ?_
  have h := coupledWithin_riemann_segMeasure (V i) (V (i + 1)) hN
  rwa [hlen i (Finset.mem_range.1 hi)] at h

/-- **The left Riemann reference measure** `ν₀^N = N⁻¹ Σ_{l<N} δ_{(l/N) e₁}` is coupled with
`ν₀ = 𝓛` within `1/N`. -/
theorem coupledWithin_riemann_ref (hd : 0 < d) {N : ℕ} (hN : 0 < N) :
    CoupledWithin (atomM (Finset.range N) (fun _ => 1 / (N : ℝ)) (refPt (d := d) N))
      (Upper.segMeasure 0 (e₁ d)) (1 / N) := by
  have h := coupledWithin_riemann_segMeasure (0 : Rd d) (e₁ d) hN
  rw [sub_zero, norm_e₁ hd] at h
  have e : (fun l : ℕ => Upper.lin (0 : Rd d) (e₁ d) ((l : ℝ) / N)) = refPt N := by
    funext l
    rw [lin_zero_e₁, refPt]
  rwa [e] at h

/-- **The replaced measure** (source (5.11), (5.17); HA4 D6 Step 1): if `μ = Σ w δ_z` is a
probability measure with `μ_x ∈ W(r)` whose atoms have transverse parts `≤ m`, then
`ν_{j,μ} = K⁻¹ Σ_i (T_i)_* μ` is coupled with `ν_j = polyM K V` within `q (r + m)`. -/
theorem coupledWithin_repl_polyM (hd : 0 < d) {K : ℕ} {q : ℝ} (hq : 0 < q) {V : ℕ → Rd d}
    (hlen : ∀ i < K, ‖V (i + 1) - V i‖ = q) {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hμ : IsFinProb S w) {r m : ℝ} (hW : HorizW S w r)
    (htr : ∀ z ∈ S, w z ≠ 0 → ‖transv z‖ ≤ m) :
    CoupledWithin (atomM (Finset.range K ×ˢ S) (fun x => 1 / (K : ℝ) * w x.2)
        (fun x => (edgeSim q V x.1).app x.2)) (polyM K V) (q * (r + m)) := by
  have e : atomM (Finset.range K ×ˢ S) (fun x => 1 / (K : ℝ) * w x.2)
      (fun x => (edgeSim q V x.1).app x.2) =
      ∑ i ∈ Finset.range K, ENNReal.ofReal (1 / (K : ℝ)) • atomM S w (edgeSim q V i).app :=
    (sum_smul_atomM (Finset.range K) (show (0 : ℝ) ≤ 1 / K by positivity) S w
      fun i z => (edgeSim q V i).app z).symm
  rw [e, polyM_eq_sum_map hd hq hlen]
  refine coupledWithin_finsetSum _ _ _ fun i _ => coupledWithin_smul _ ?_
  have h := coupledWithin_map_sim (edgeSim q V i) (coupledWithin_quantile hd hμ hW htr)
  rw [map_atomM _ _ _ (edgeSim q V i).continuous_app.measurable, edgeSim_r,
    abs_of_pos hq] at h
  exact h

end HigherDimLFPP.Lower
