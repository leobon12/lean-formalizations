import HigherDimLQGContinuity.Events.Profile
import HigherDimLQGContinuity.Norm.ScalingSets
import HigherDimLQGContinuity.Witness.Refs
import HigherDimLQGMetric.Shell.Across

/-!
# Lemma `a:lem-connector`: physical connectors from good recentred fields (packet P5b)

Packet P5b, target `connector_of_good`. Source: blueprint Part A, Lemma `a:lem-connector` (NA1's "scaled-connector
lemma" of packet P5; NA1 §3.3 P5, R9; BWA); consumers: Lemmas 3.2 and Proposition 3.3 (packet P7), with Lemma 3.1
(`lemma31a`, `lemma31b`, packet P6), whose crossing, diameter and connector hypotheses are written exactly in the
forms of the conclusions below.

**Statement.** For `D`, `E` strong at `ξ, η > 0`, pins `s`, `s₀ > 0`, a ball `B_r(z)` and `b ≥ 0`: for `𝐏_{s₀}`-a.e.
`g`, with `g' = recentre s r z g`, `S_D = scaleS d ξ s r z g`, `S_E = scaleS d η s r z g`, if `g' ∈ PairRefs(D, E; 𝓡)`:
* (a) `setDistIn ρ^D_g ℝ^d (∂B_{3r/4}(z)) (∂B_r(z)) ≥ m S_D` and `diamIn ρ^D_g (ann z (r/2) (7r/2)) (∂B_r(z)) ≤ M S_D`,
  and the same for `E` with `S_E`;
* (b) if moreover `g' ∉ H↑(D, E; b)`: for every `ρ^D_g`-geodesic `P : [u, v] → ℝ^d` parametrized by `ρ^D_g`-length
  (`ρ^D_g(P a, P a') = |a - a'|`) with `P([u, v]) ⊆ annCl z (3r/4) r` and endpoints on the two boundary spheres (in
  either order): `ρ^E_g(P u, P v) ≤ b (S_E/S_D) (v - u)`;
* (c) if moreover `g' ∉ H↑(E, D; b)`: the same with `D` and `E` exchanged (factor `S_D/S_E`).

**Proof.** The exact scaling (2.6) (`rho_scaling_of`, `rho_scaling_sets` of packet P2) at `(r, z)` for `D` and `E`
(two null sets), and a.s. length of `ρ^D_g`, `ρ^E_g`. (a) Set distances and internal diameters scale by `S`; for a
length metric the global crossing equals the crossing inside any open neighbourhood of the closed annulus
(`acrossDist_eq_setDistIn`), in particular inside `ann z (r/2) (7r/2) = z + r A`. (b) The block, rescaled to
`γ(τ) = r⁻¹ (P(u + τ(v - u)) - z)` (reversed if `P u ∈ ∂B_r(z)`), is a global `ρ^D_{g'}`-geodesic in `K` at constant
speed `(v - u)/S_D`, hence a witness for `ρ^D_{g'}` with `ρ^D_{g'}(γ 0, γ 1; A) = (v - u)/S_D` (`isWitness_of_apply_eq`
of packet P5a); `g' ∉ H↑(D, E; b)` gives `ρ^E_{g'}(γ 0, γ 1) ≤ ρ^E_{g'}(γ 0, γ 1; A) ≤ b (v - u)/S_D`, and scaling back
multiplies by `S_E`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Images of the unit objects under `w ↦ r w + z` -/

theorem p5b_image_annA {r : ℝ} (hr : 0 < r) (z : Rd d) :
    (fun w => r • w + z) '' annA d = ann z (r / 2) (7 * r / 2) := by
  rw [annA, p2_image_affine_ann hr, smul_zero, zero_add]
  congr 1 <;> ring

theorem p5b_image_sphere {r : ℝ} (hr : 0 < r) (z : Rd d) (a : ℝ) :
    (fun w => r • w + z) '' sphere (0 : Rd d) a = sphere z (r * a) := by
  rw [p2_image_affine_sphere hr, smul_zero, zero_add]

theorem p5b_annCl_subset_ann {r : ℝ} (hr : 0 < r) (z : Rd d) :
    annCl z (3 * r / 4) r ⊆ ann z (r / 2) (7 * r / 2) := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ## A path parametrized by length is continuous -/

/-- A map of an interval into `ℝ^d` that is an isometry for a continuous metric `G` is continuous. -/
theorem p5b_continuousOn_of_isometry {G : ContMetric d} {P : ℝ → Rd d} {u v : ℝ}
    (hP : ∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, G.1 (P a, P a') = |a - a'|) : ContinuousOn P (Icc u v) := by
  rw [← G.continuousOn_pt_comp_iff]
  refine (LipschitzOnWith.of_dist_le_mul fun a ha a' ha' => ?_).continuousOn (K := 1)
  rw [Function.comp_apply, Function.comp_apply, ContMetric.dist_pt, hP a ha a' ha', Real.dist_eq,
    NNReal.coe_one, one_mul]

/-! ## The connector step for one ordered pair -/

/-- **The deterministic connector step.** Let `ρ, ρ'` (primary, secondary) and their unit-scale versions `G, G'` be
related by the exact scaling at `(r, z)` with constants `S, S' > 0`. If `γ` runs in `K` from `∂B_{3/4}` to `∂B₁` as a
global `G`-geodesic at constant speed `L/S`, and the `A`-ratio of the witness `γ` is at most `b`, then the physical
endpoints satisfy `ρ'(r γ 0 + z, r γ 1 + z) ≤ b (S'/S) L`. -/
theorem p5b_connector_core {ρ' G G' : ContMetric d} {r S S' L b : ℝ} {z : Rd d} (hS : 0 < S) (hS' : 0 < S')
    (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hscale' : ∀ x y : Rd d, ρ'.1 (r • x + z, r • y + z) = S' * G'.1 (x, y))
    {γ : C(unitInterval, Rd d)} (h0 : ‖γ 0‖ = 3 / 4) (h1 : ‖γ 1‖ = 1) (hK : ∀ t, γ t ∈ annK d)
    (hgeo : ∀ s t : unitInterval, G.1 (γ s, γ t) = L / S * |(s : ℝ) - t|)
    (hnot : ¬ ENNReal.ofReal b * G.internal (annA d) (γ 0) (γ 1) < G'.internal (annA d) (γ 0) (γ 1)) :
    ρ'.1 (r • γ 0 + z, r • γ 1 + z) ≤ b * (S' / S) * L := by
  obtain ⟨-, hint⟩ := isWitness_of_apply_eq h0 h1 hK hgeo
  push Not at hnot
  rw [hint, ← ENNReal.ofReal_mul hb] at hnot
  have hG' : G'.1 (γ 0, γ 1) ≤ b * (L / S) := by
    have := (G'.ofReal_le_internal (annA d) (γ 0) (γ 1)).trans hnot
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
  rw [hscale']
  calc S' * G'.1 (γ 0, γ 1) ≤ S' * (b * (L / S)) := mul_le_mul_of_nonneg_left hG' hS'.le
    _ = b * (S' / S) * L := by field_simp

/-- The rescaled block of a length-parametrized `ρ`-geodesic `P : [u, v] → annCl z (3r/4) r` from `∂B_{3r/4}(z)` to
`∂B_r(z)`: `γ(τ) = r⁻¹ (P(u + τ(v - u)) - z)`. -/
def p5bBlock (P : ℝ → Rd d) (u v r : ℝ) (z : Rd d) (hP : ContinuousOn P (Icc u v)) (huv : u ≤ v) :
    C(unitInterval, Rd d) :=
  ⟨fun τ => r⁻¹ • (P (u + (τ : ℝ) * (v - u)) - z), by
    have hmaps : MapsTo (fun τ : unitInterval => u + (τ : ℝ) * (v - u)) univ (Icc u v) := by
      intro τ _
      have h0 := τ.2.1
      have h1 := τ.2.2
      constructor <;> nlinarith
    have hc : Continuous fun τ : unitInterval => P (u + (τ : ℝ) * (v - u)) := by
      rw [← continuousOn_univ]
      exact hP.comp (by fun_prop) hmaps
    exact (hc.sub continuous_const).const_smul r⁻¹⟩

theorem p5bBlock_apply (P : ℝ → Rd d) (u v r : ℝ) (z : Rd d) (hP : ContinuousOn P (Icc u v)) (huv : u ≤ v)
    (τ : unitInterval) : p5bBlock P u v r z hP huv τ = r⁻¹ • (P (u + (τ : ℝ) * (v - u)) - z) := rfl

/-- The physical point of the rescaled block. -/
theorem p5bBlock_phys (P : ℝ → Rd d) (u v : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) (hP : ContinuousOn P (Icc u v))
    (huv : u ≤ v) (τ : unitInterval) :
    r • p5bBlock P u v r z hP huv τ + z = P (u + (τ : ℝ) * (v - u)) := by
  rw [p5bBlock_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, sub_add_cancel]

theorem p5b_mem_Icc_affine {u v : ℝ} (huv : u ≤ v) (τ : unitInterval) :
    u + (τ : ℝ) * (v - u) ∈ Icc u v := by
  have h0 := τ.2.1
  have h1 := τ.2.2
  constructor <;> nlinarith

theorem p5b_norm_block (P : ℝ → Rd d) (u v : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hP : ContinuousOn P (Icc u v)) (huv : u ≤ v) (τ : unitInterval) :
    ‖p5bBlock P u v r z hP huv τ‖ = r⁻¹ * ‖P (u + (τ : ℝ) * (v - u)) - z‖ := by
  rw [p5bBlock_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]

/-- **The connector bound for one orientation**: from the exact scaling of the primary and the secondary metric at
`(r, z)`, a block `P : [u, v] → annCl z (3r/4) r` of a length-parametrized `ρ`-geodesic from `∂B_{3r/4}(z)` to
`∂B_r(z)`, and the non-occurrence of the unit-scale `H↑`-condition along every rescaled block. -/
theorem p5b_connector_oriented {ρ ρ' G G' : ContMetric d} {r S S' b : ℝ} {z : Rd d} (hr : 0 < r)
    (hS : 0 < S) (hS' : 0 < S') (hb : 0 ≤ b)
    (hscale : ∀ x y : Rd d, ρ.1 (r • x + z, r • y + z) = S * G.1 (x, y))
    (hscale' : ∀ x y : Rd d, ρ'.1 (r • x + z, r • y + z) = S' * G'.1 (x, y))
    (hnot : ∀ γ : C(unitInterval, Rd d), IsWitness G γ →
      ¬ ENNReal.ofReal b * G.internal (annA d) (γ 0) (γ 1) < G'.internal (annA d) (γ 0) (γ 1))
    {P : ℝ → Rd d} {u v : ℝ} (huv : u ≤ v)
    (hgeo : ∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, ρ.1 (P a, P a') = |a - a'|)
    (hsub : P '' Icc u v ⊆ annCl z (3 * r / 4) r)
    (hu : ‖P u - z‖ = 3 * r / 4) (hv : ‖P v - z‖ = r) :
    ρ'.1 (P u, P v) ≤ b * (S' / S) * (v - u) := by
  have hPc : ContinuousOn P (Icc u v) := p5b_continuousOn_of_isometry hgeo
  set γ := p5bBlock P u v r z hPc huv with hγ
  have hphys : ∀ τ : unitInterval, r • γ τ + z = P (u + (τ : ℝ) * (v - u)) :=
    p5bBlock_phys P u v hr z hPc huv
  have hnorm : ∀ τ : unitInterval, ‖γ τ‖ = r⁻¹ * ‖P (u + (τ : ℝ) * (v - u)) - z‖ :=
    p5b_norm_block P u v hr z hPc huv
  have hP0 : u + ((0 : unitInterval) : ℝ) * (v - u) = u := by simp
  have hP1 : u + ((1 : unitInterval) : ℝ) * (v - u) = v := by simp
  have h0 : ‖γ 0‖ = 3 / 4 := by
    rw [hnorm, hP0, hu]
    field_simp
  have h1 : ‖γ 1‖ = 1 := by
    rw [hnorm, hP1, hv, inv_mul_cancel₀ hr.ne']
  have hK : ∀ t, γ t ∈ annK d := by
    intro t
    have hmem := hsub ⟨_, p5b_mem_Icc_affine huv t, rfl⟩
    rw [mem_annK_iff, hnorm]
    have ha : 3 * r / 4 ≤ ‖P (u + (t : ℝ) * (v - u)) - z‖ := hmem.1
    have hb' : ‖P (u + (t : ℝ) * (v - u)) - z‖ ≤ r := hmem.2
    constructor
    · rw [le_inv_mul_iff₀ hr]
      linarith
    · rw [inv_mul_le_iff₀ hr]
      linarith
  have hgeoγ : ∀ s t : unitInterval, G.1 (γ s, γ t) = (v - u) / S * |(s : ℝ) - t| := by
    intro s t
    have h := hscale (γ s) (γ t)
    rw [hphys, hphys, hgeo _ (p5b_mem_Icc_affine huv s) _ (p5b_mem_Icc_affine huv t)] at h
    have hst : u + (s : ℝ) * (v - u) - (u + (t : ℝ) * (v - u)) = ((s : ℝ) - t) * (v - u) := by ring
    rw [hst, abs_mul, abs_of_nonneg (sub_nonneg.2 huv)] at h
    field_simp
    linarith
  have hcore := p5b_connector_core hS hS' hb (sub_nonneg.2 huv) hscale' h0 h1 hK hgeoγ
    (hnot γ (isWitness_of_apply_eq h0 h1 hK hgeoγ).1)
  rwa [hphys, hphys, hP0, hP1] at hcore

/-- **The connector bound, both orientations of the block** (the form of `lemma31b`'s `hconnector`). -/
theorem p5b_connector_bound {ρ ρ' G G' : ContMetric d} {r S S' b : ℝ} {z : Rd d} (hr : 0 < r)
    (hS : 0 < S) (hS' : 0 < S') (hb : 0 ≤ b)
    (hscale : ∀ x y : Rd d, ρ.1 (r • x + z, r • y + z) = S * G.1 (x, y))
    (hscale' : ∀ x y : Rd d, ρ'.1 (r • x + z, r • y + z) = S' * G'.1 (x, y))
    (hnot : ∀ γ : C(unitInterval, Rd d), IsWitness G γ →
      ¬ ENNReal.ofReal b * G.internal (annA d) (γ 0) (γ 1) < G'.internal (annA d) (γ 0) (γ 1))
    (P : ℝ → Rd d) (u v : ℝ) (huv : u ≤ v)
    (hgeo : ∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, ρ.1 (P a, P a') = |a - a'|)
    (hsub : P '' Icc u v ⊆ annCl z (3 * r / 4) r)
    (hends : (‖P u - z‖ = r ∧ ‖P v - z‖ = 3 * r / 4) ∨ (‖P u - z‖ = 3 * r / 4 ∧ ‖P v - z‖ = r)) :
    ρ'.1 (P u, P v) ≤ b * (S' / S) * (v - u) := by
  rcases hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · -- reverse the block: `Q a = P (u + v - a)`
    set Q : ℝ → Rd d := fun a => P (u + v - a) with hQ
    have hmem : ∀ a ∈ Icc u v, u + v - a ∈ Icc u v := fun a ha => ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have hgeoQ : ∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, ρ.1 (Q a, Q a') = |a - a'| := by
      intro a ha a' ha'
      rw [hQ, hgeo _ (hmem a ha) _ (hmem a' ha'), abs_sub_comm]
      congr 1
      ring
    have hsubQ : Q '' Icc u v ⊆ annCl z (3 * r / 4) r := by
      rintro _ ⟨a, ha, rfl⟩
      exact hsub ⟨u + v - a, hmem a ha, rfl⟩
    have hQu : Q u = P v := by simp only [hQ, add_sub_cancel_left]
    have hQv : Q v = P u := by simp only [hQ, add_sub_cancel_right]
    have h := p5b_connector_oriented hr hS hS' hb hscale hscale' hnot huv hgeoQ hsubQ
      (by rw [hQu]; exact hv) (by rw [hQv]; exact hu)
    rwa [hQu, hQv, ρ'.apply_comm] at h
  · exact p5b_connector_oriented hr hS hS' hb hscale hscale' hnot huv hgeo hsub hu hv

/-! ## Crossings and diameters at the physical scale -/

/-- (a) of `a:lem-connector` for one metric, deterministic form. -/
theorem p5b_cross_diam_of_scaling {ρ G : ContMetric d} (hρ : ρ.IsLength) {r S H₀ σ₀ β₀ m M : ℝ} {z : Rd d}
    (hr : 0 < r) (hS : 0 < S)
    (hsd : ∀ V A B : Set (Rd d), setDistIn ρ ((fun w => r • w + z) '' V) ((fun w => r • w + z) '' A)
      ((fun w => r • w + z) '' B) = ENNReal.ofReal S * setDistIn G V A B)
    (hdi : ∀ V A : Set (Rd d), diamIn ρ ((fun w => r • w + z) '' V) ((fun w => r • w + z) '' A) =
      ENNReal.ofReal S * diamIn G V A)
    (hR : LocalRefs G H₀ σ₀ β₀ m M) :
    ENNReal.ofReal (m * S) ≤ setDistIn ρ univ (sphere z (3 * r / 4)) (sphere z r) ∧
      diamIn ρ (ann z (r / 2) (7 * r / 2)) (sphere z r) ≤ ENNReal.ofReal (M * S) := by
  have hS1 : (fun w => r • w + z) '' sphere (0 : Rd d) 1 = sphere z r := by
    rw [p5b_image_sphere hr, mul_one]
  have hS34 : (fun w => r • w + z) '' sphere (0 : Rd d) (3 / 4) = sphere z (3 * r / 4) := by
    rw [p5b_image_sphere hr]
    congr 1
    ring
  constructor
  · have hlt : 3 * r / 4 < r := by linarith
    have h1 := acrossDist_eq_setDistIn ρ hρ (z := z) isOpen_univ hlt (subset_univ _)
    have h2 := acrossDist_eq_setDistIn ρ hρ (isOpen_ann z (r / 2) (7 * r / 2)) hlt
      (p5b_annCl_subset_ann hr z)
    rw [← h1, h2, ← p5b_image_annA hr, ← hS34, ← hS1, hsd, mul_comm m S, ENNReal.ofReal_mul hS.le]
    gcongr
    exact hR.cross
  · rw [← p5b_image_annA hr, ← hS1, hdi, mul_comm M S, ENNReal.ofReal_mul hS.le]
    gcongr
    exact hR.diam

/-! ## Lemma `a:lem-connector` -/

/-- **Lemma `a:lem-connector`** (blueprint Part A; NA1's scaled-connector lemma). Let `D`, `E` be strong at
`ξ, η > 0`, `s₀ > 0`, `r > 0`, `z ∈ ℝ^d`, `b ≥ 0` and reference constants `(H₀, σ₀, β₀, m, M)`. For `𝐏_{s₀}`-a.e.
`g`, with `g' = recentre s r z g`, `S_D = scaleS d ξ s r z g`, `S_E = scaleS d η s r z g`: if `g' ∈ PairRefs(D, E)`,
then (a) the physical crossings and diameters of both metrics in the ball `B_r(z)` are bounded by `m S`, `M S`;
(b) if `g' ∉ H↑(D, E; b)`, every length-parametrized `ρ^D_g`-geodesic block across `annCl z (3r/4) r` (either
orientation) has `ρ^E_g(P u, P v) ≤ b (S_E/S_D)(v - u)`; (c) the same with `D` and `E` exchanged if
`g' ∉ H↑(E, D; b)`. -/
theorem connector_of_good (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E)
    {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) {b : ℝ} (hb : 0 ≤ b) (H₀ σ₀ β₀ m M : ℝ) :
    ∀ᵐ g ∂(pinLaw d s₀), recentre s r z g ∈ PairRefs D E H₀ σ₀ β₀ m M →
      ((ENNReal.ofReal (m * scaleS d ξ s r z g) ≤
            setDistIn (rho D g) univ (sphere z (3 * r / 4)) (sphere z r) ∧
          diamIn (rho D g) (ann z (r / 2) (7 * r / 2)) (sphere z r) ≤
            ENNReal.ofReal (M * scaleS d ξ s r z g)) ∧
        (ENNReal.ofReal (m * scaleS d η s r z g) ≤
            setDistIn (rho E g) univ (sphere z (3 * r / 4)) (sphere z r) ∧
          diamIn (rho E g) (ann z (r / 2) (7 * r / 2)) (sphere z r) ≤
            ENNReal.ofReal (M * scaleS d η s r z g))) ∧
      (recentre s r z g ∉ Hup D E b → ∀ (P : ℝ → Rd d) (u v : ℝ), u ≤ v →
        (∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, (rho D g).1 (P a, P a') = |a - a'|) →
        P '' Icc u v ⊆ annCl z (3 * r / 4) r →
        ((‖P u - z‖ = r ∧ ‖P v - z‖ = 3 * r / 4) ∨ (‖P u - z‖ = 3 * r / 4 ∧ ‖P v - z‖ = r)) →
        (rho E g).1 (P u, P v) ≤ b * (scaleS d η s r z g / scaleS d ξ s r z g) * (v - u)) ∧
      (recentre s r z g ∉ Hup E D b → ∀ (P : ℝ → Rd d) (u v : ℝ), u ≤ v →
        (∀ a ∈ Icc u v, ∀ a' ∈ Icc u v, (rho E g).1 (P a, P a') = |a - a'|) →
        P '' Icc u v ⊆ annCl z (3 * r / 4) r →
        ((‖P u - z‖ = r ∧ ‖P v - z‖ = 3 * r / 4) ∨ (‖P u - z‖ = 3 * r / 4 ∧ ‖P v - z‖ = r)) →
        (rho D g).1 (P u, P v) ≤ b * (scaleS d ξ s r z g / scaleS d η s r z g) * (v - u)) := by
  filter_upwards [rho_scaling_of hd hξ hD (s := s) hs₀ hr z, rho_scaling_of hd hη hE (s := s) hs₀ hr z,
    rho_scaling_sets hd hξ hD (s := s) hs₀ hr z, rho_scaling_sets hd hη hE (s := s) hs₀ hr z,
    p5b_ae_isLength_rho hd hD hs₀, p5b_ae_isLength_rho hd hE hs₀] with g hscD hscE hsetD hsetE hlD hlE
  intro hrefs
  have hSD := scaleS_pos d ξ s hr z g
  have hSE := scaleS_pos d η s hr z g
  refine ⟨⟨p5b_cross_diam_of_scaling hlD hr hSD hsetD.1 hsetD.2 hrefs.1,
    p5b_cross_diam_of_scaling hlE hr hSE hsetE.1 hsetE.2 hrefs.2⟩, ?_, ?_⟩
  · intro hnot P u v huv hgeo hsub hends
    refine p5b_connector_bound hr hSD hSE hb hscD.1 hscE.1 ?_ P u v huv hgeo hsub hends
    intro γ hγ hlt
    exact hnot ⟨γ, hγ, hlt⟩
  · intro hnot P u v huv hgeo hsub hends
    refine p5b_connector_bound hr hSE hSD hb hscE.1 hscD.1 ?_ P u v huv hgeo hsub hends
    intro γ hγ hlt
    exact hnot ⟨γ, hγ, hlt⟩

end HigherDimLQGContinuity
