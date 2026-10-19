import HigherDimLFPP.Lower.ClassC
import HigherDimLFPP.Lower.Polygon

/-!
# The equal-edge polygon as a path; the equal-parameter coupling; constants of Lemma 5.3

Packet P-L1, supplements to targets T1, T3 and T4 (audit HA4, "Details for later use" D1, D5
step 1, D6 "Constants"). All statements are deterministic.

* `EqualEdgeData.mem_cube`, `EqualEdgeData.isAdmissiblePath`: the polygon of Lemma 5.1 lies in
  `U` and its uniform-speed parametrization `polyPath v K` is an admissible path once
  `M₀ δ < 2`.
* `norm_polyPath_sub_graph_le`: **the equal-parameter coupling** (HA4 D5, step 1). If the
  vertices are `v_j = x_j e₁ + δ (0, G(j/K))` with `G` affine on the mesh `1/K` and
  `|x_j - j/K| ≤ ρ`, then at every parameter `s ∈ [0,1]` the polygon point and the graph point
  `s e₁ + δ (0, G(s))` differ by a horizontal vector of norm `≤ ρ`. For the Lemma 5.1 polygon
  (`G = f + a ψ_K v`, `ρ = δ²E₀`) this is `eqVert_polyPath_coupling`.
* `energy_padProf_aLim`: `E(f + a_f ψ_K v) = E₀` (source: `E(g_j) = E₀`).
* `constM_spec`, `constB_spec`: the choices `M = (M₀ + q₀ + 1)/(1 - q₀)` and
  `B = (E₀ + q₀ c M + X + 1)/(1 - q₀)` of HA4 D6 satisfy the containment conditions of
  `edgeSim_mapsTo_Vdelta` and the budget (5.22) of `inCDelta_of_hCDF_close`.

2D source: none for the coupling and the constants; the admissibility statement uses the port
of `LQGDimension/LFPP/PolygonRiemann.lean` in `HigherDimLFPP/Lower/Polygon.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## The equal-edge polygon is an admissible path -/

/-- The vertices of an equal-edge polygon lie in `U` when `M₀ δ < 2`. -/
theorem EqualEdgeData.mem_cube (hd : 0 < d) {K : ℕ} {δ q E₀ M₀ c : ℝ} {v : ℕ → Rd d}
    (hE : EqualEdgeData K δ q E₀ M₀ c v) (hM : M₀ * δ < 2) {i : ℕ} (hi : i ≤ K) :
    v i ∈ cube d := by
  intro j
  by_cases hj : (j : ℕ) = 0
  · have hj' : j = ⟨0, hd⟩ := Fin.ext hj
    rw [hj', ← horiz_apply hd, abs_lt]
    have := horiz_mem_Icc_of_EqualEdgeData hd hE hi
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · exact lt_of_le_of_lt ((abs_ofLp_le_norm_transv (v i) hj).trans (hE.transverse i hi)) hM

/-- **The Lemma 5.1 polygon is an admissible path** (finding HA4-13). -/
theorem EqualEdgeData.isAdmissiblePath (hd : 0 < d) {K : ℕ} (hK : 0 < K) {δ q E₀ M₀ c : ℝ}
    {v : ℕ → Rd d} (hE : EqualEdgeData K δ q E₀ M₀ c v) (hM : M₀ * δ < 2) :
    IsAdmissiblePath d (polyPath v K) :=
  isAdmissiblePath_polyPath v K hK hE.start hE.finish fun _ hi => hE.mem_cube hd hM hi

/-! ## The equal-parameter coupling with the graph -/

/-- **Equal-parameter coupling** (HA4 D5, step 1). Let `v j = x j • e₁ + δ • (0, G(j/K))` for
`j ≤ K`, where `G ∈ V_m(ℝ^{d-1})`, `K = 2^m`, and `|x j - j/K| ≤ ρ`. Then for `s ∈ [0,1]` the
point of `polyPath v K` at parameter `s` and the graph point `s e₁ + δ (0, G(s))` satisfy
`‖polyPath v K s - (s e₁ + δ (0, G(s)))‖ ≤ ρ`. -/
theorem norm_polyPath_sub_graph_le (hd : 0 < d) {m K : ℕ} (hK : K = 2 ^ m)
    {G : ℝ → Rd (d - 1)} (hG : G ∈ Vg (Rd (d - 1)) m) {δ ρ : ℝ} {x : ℕ → ℝ} {v : ℕ → Rd d}
    (hv : ∀ j ≤ K, v j = x j • e₁ d + δ • embedT (G ((j : ℝ) / K)))
    (hx : ∀ j ≤ K, |x j - (j : ℝ) / K| ≤ ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖polyPath v K s - (s • e₁ d + δ • embedT (G s))‖ ≤ ρ := by
  have hKpos : 0 < K := by rw [hK]; positivity
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  set i := idx K s with hi_def
  have hiK : i < K := idx_lt K hKpos s
  have hsi : s ∈ Icc ((i : ℝ) / K) (((i : ℝ) + 1) / K) := mem_Icc_idx K hKpos s hs.1 hs.2
  set lam := s * K - i with hlam
  have hlam0 : 0 ≤ lam := by
    have := hsi.1; rw [div_le_iff₀ hK'] at this; rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by
    have := hsi.2; rw [le_div_iff₀ hK'] at this; rw [hlam]; linarith
  -- the polygon point
  have hpoly : polyPath v K s = v i + lam • (v (i + 1) - v i) :=
    polyPath_eq_edgeAff v K hKpos i hiK s hsi
  -- the profile is affine on the mesh interval
  have hGs : G s = G ((i : ℝ) / K) + lam • (G (((i : ℝ) + 1) / K) - G ((i : ℝ) / K)) := by
    have hcast : ((K : ℕ) : ℝ) = (2 : ℝ) ^ m := by rw [hK]; push_cast; ring
    have hiK' : i < 2 ^ m := hK ▸ hiK
    have hsi' : s ∈ Icc ((i : ℝ) / 2 ^ m) (((i : ℝ) + 1) / 2 ^ m) := by rwa [← hcast]
    have := Var.Vg_piece hG hiK' hsi'
    rw [this, ← hcast, hlam, mul_comm s]
  have hv0 := hv i hiK.le
  have hv1 := hv (i + 1) hiK
  push_cast at hv1
  have hdiff : polyPath v K s - (s • e₁ d + δ • embedT (G s)) =
      ((1 - lam) * (x i - (i : ℝ) / K) + lam * (x (i + 1) - ((i : ℝ) + 1) / K)) • e₁ d := by
    rw [hpoly, hv0, hv1, hGs, embedT_add, embedT_smul, embedT_sub]
    have hs' : s = (1 - lam) * ((i : ℝ) / K) + lam * (((i : ℝ) + 1) / K) := by
      rw [hlam]; field_simp; ring
    rw [hs']
    module
  rw [hdiff, norm_smul, norm_e₁ hd, mul_one, Real.norm_eq_abs]
  have h1 := hx i hiK.le
  have h2 := hx (i + 1) hiK
  push_cast at h2
  calc |(1 - lam) * (x i - (i : ℝ) / K) + lam * (x (i + 1) - ((i : ℝ) + 1) / K)|
      ≤ |(1 - lam) * (x i - (i : ℝ) / K)| + |lam * (x (i + 1) - ((i : ℝ) + 1) / K)| :=
        abs_add_le _ _
    _ = (1 - lam) * |x i - (i : ℝ) / K| + lam * |x (i + 1) - ((i : ℝ) + 1) / K| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * ρ + lam * ρ :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith))
          (mul_le_mul_of_nonneg_left h2 hlam0)
    _ = ρ := by ring

/-- The equal-parameter coupling for the Lemma 5.1 polygon: at every parameter `s ∈ [0,1]`,
`‖polyPath (eqVert …) K s - (s e₁ + δ (0, (f + a ψ_K v)(s)))‖ ≤ δ² E₀`. -/
theorem eqVert_polyPath_coupling (hd : 0 < d) {n g : ℕ} (hg : 1 ≤ g) {f : ℝ → Rd (d - 1)}
    (hf : f ∈ Vg (Rd (d - 1)) n) (v : Rd (d - 1)) {a δ q E₀ M₀ c : ℝ}
    (hE : EqualEdgeData (2 ^ (n + g)) δ q E₀ M₀ c (eqVert (2 ^ (n + g)) q δ f v a))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖polyPath (eqVert (2 ^ (n + g)) q δ f v a) (2 ^ (n + g)) s -
        (s • e₁ d + δ • embedT (padProf (2 ^ (n + g)) f v a s))‖ ≤ δ ^ 2 * E₀ := by
  refine norm_polyPath_sub_graph_le hd rfl (padProf_mem_Vg hg hf v a)
    (x := knot (2 ^ (n + g)) q δ f v a) (fun j _ => rfl) (fun j hj => ?_) hs
  have := hE.knots j hj
  rwa [horiz_eqVert hd] at this

/-! ## The padded profile at the limit amplitude -/

/-- `E(f + a_f ψ_K v) = E₀ = e + 1` (source §5.2, `E(g_j) = E₀`). -/
theorem energy_padProf_aLim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n g : ℕ} (hg : 1 ≤ g) {e : ℝ} {f : ℝ → E} (hf : f ∈ Vg E n) (hfe : energy f ≤ e) {v : E}
    (hv : ‖v‖ = 1) : energy (padProf (2 ^ (n + g)) f v (aLim e f)) = e + 1 := by
  rw [energy_padProf hg hf hv, aLim_sq hfe]
  ring

/-! ## The constants `M` and `B` of Lemma 5.3 -/

/-- `M = (M₀ + q₀ + 1)/(1 - q₀)` satisfies `M₀ + q(Bδ + M) ≤ M` for `0 ≤ q ≤ q₀ < 1`,
`Bδ ≤ 1`, `M₀ ≥ 0` (condition `h2` of `edgeSim_mapsTo_Vdelta`; source (5.16)). -/
theorem constM_spec {M₀ q₀ q B δ : ℝ} (hM₀ : 0 ≤ M₀) (hq₀ : q₀ < 1) (hq : 0 ≤ q)
    (hqq₀ : q ≤ q₀) (hBδ : B * δ ≤ 1) :
    M₀ + q * (B * δ + (M₀ + q₀ + 1) / (1 - q₀)) ≤ (M₀ + q₀ + 1) / (1 - q₀) := by
  have h1q : 0 < 1 - q₀ := by linarith
  set M := (M₀ + q₀ + 1) / (1 - q₀) with hM
  have hM0 : 0 ≤ M := div_nonneg (by linarith) h1q.le
  have hMeq : M * (1 - q₀) = M₀ + q₀ + 1 := by rw [hM]; field_simp
  have h1 : q * (B * δ + M) ≤ q₀ * (1 + M) := by
    have : B * δ + M ≤ 1 + M := by linarith
    calc q * (B * δ + M) ≤ q * (1 + M) := mul_le_mul_of_nonneg_left this hq
      _ ≤ q₀ * (1 + M) := mul_le_mul_of_nonneg_right hqq₀ (by linarith)
  nlinarith

/-- `B = (E₀ + q₀ c M + X + 1)/(1 - q₀)` satisfies `q(B + cM) ≤ B` (condition `h1` of
`edgeSim_mapsTo_Vdelta`) and the budget `E₀ + q(B + cM) + X + 1 ≤ B` of (5.22), for
`0 ≤ q ≤ q₀ < 1`, `c, M ≥ 0`, `E₀ + X + 1 ≥ 0` (HA4 D6 with `X = 3C'`). -/
theorem constB_spec {E₀ X c M q₀ q : ℝ} (hEX : 0 ≤ E₀ + X + 1) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hq₀ : q₀ < 1) (hq : 0 ≤ q) (hqq₀ : q ≤ q₀) :
    q * ((E₀ + q₀ * c * M + X + 1) / (1 - q₀) + c * M) ≤ (E₀ + q₀ * c * M + X + 1) / (1 - q₀) ∧
      E₀ + q * ((E₀ + q₀ * c * M + X + 1) / (1 - q₀) + c * M) + X + 1 ≤
        (E₀ + q₀ * c * M + X + 1) / (1 - q₀) := by
  have h1q : 0 < 1 - q₀ := by linarith
  have hq₀0 : 0 ≤ q₀ := hq.trans hqq₀
  set B := (E₀ + q₀ * c * M + X + 1) / (1 - q₀) with hB
  have hcM : 0 ≤ c * M := mul_nonneg hc hM
  have hBeq : B * (1 - q₀) = E₀ + q₀ * c * M + X + 1 := by rw [hB]; field_simp
  have hB0 : 0 ≤ B := div_nonneg (by nlinarith) h1q.le
  have hqB : q * (B + c * M) ≤ q₀ * (B + c * M) :=
    mul_le_mul_of_nonneg_right hqq₀ (by linarith)
  constructor
  · nlinarith
  · nlinarith

end HigherDimLFPP.Lower
