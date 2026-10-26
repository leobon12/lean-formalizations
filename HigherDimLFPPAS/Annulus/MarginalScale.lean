import HigherDimLFPPAS.Core.Interfaces
import HigherDimLQGMetric.Sec4.Scale
import HigherDimLQGMetric.Sharp.ShellScaling
import HigherDimLQGMetric.Events.AnnulusGeometry

/-!
# Lemma 3.2, marginal part — Step 1: rescaling of `E′` to the unit annulus (packet L32p)

Source: `planning/audits/MA1-sections-1-3.md` Details A9 (Definition 3.1′ = `Core.GoodAnnulus`) and A10.1 (the
normalization of the pair `(D, M_ε)` at `(z, r)`).

For `0 < ε < 1`, `r > 0`, a centre `z` and `g = recentAff r z h`:
* `l32p_Meps_scale` (deterministic): `M_ε(h)(z + r u, z + r v) = c_ε(r) · r^{ξQ} e^{ξ c₀} · 𝔐_{ε,ε/r}(g)(u, v)` with
  `c₀ = sphereAvg (affineComp r z h) 1 0` (the two-parameter field identity `Core.LocFieldScaling`, the constant shift
  of the localized field, and the LFPP change of variables `l9b_lfppDistOn_affine`);
* `l32pUnitGood` is the rescaled event `Ẽ` (`E′` at `(z, r) = (0, 1)` with ratio `c = 1` and connection radius `b`);
* `l32p_goodAnnulus_of_unit` (deterministic): if the internal metrics of `(G, G')` at `z + r ·` are `λ`, `c λ` times
  those of `(H, H')`, then `Ẽ(H, H'; b′)` implies `E′(G, G'; c, b)` at `(z, r)` whenever `b ≤ r b′` (every inequality of
  `E′` is homogeneous of degree one in the pair);
* `l32p_ae_goodAnnulus_of_unit`: the almost-sure implication `Ẽ(D_g, 𝔐(g); b′) ⇒ E′_ε(z, r)` for the field `h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Annulus

open HigherDimLFPPAS.Core HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The localized fields and metrics -/

/-- Constant shifts of the rescaled localized field (as `locField_addConst`). -/
theorem l32p_locFieldR_addConst {κ : Rd d → ℝ} {ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < locRad ε / r) (hZ : locMass κ (ε / r) (locRad ε / r) ≠ 0)
    (g : DistRd d) (c : ℝ) (x : Rd d) :
    locFieldR κ ε r (addConst g c) x = locFieldR κ ε r g x + c := by
  unfold locFieldR
  rw [addConst_apply, integral_locTest hK hs, mul_add]
  field_simp

/-- `locFieldR` is continuous for every distribution (smooth kernel, positive radius). -/
theorem l32p_continuous_locFieldR {κ : Rd d → ℝ} {ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hs : 0 < locRad ε / r) (g : DistRd d) : Continuous (locFieldR κ ε r g) :=
  continuous_const.mul (continuous_apply_locTest hK hs g)

/-- The value of `M_ε` (non-junk branch). -/
theorem l32p_Meps_apply {κ : Rd d → ℝ} {ξ ε : ℝ} {g : DistRd d}
    (hc : Continuous (locField κ ε g)) (ha : 0 < aEps κ ξ ε) (p : Rd d × Rd d) :
    (Meps κ ξ ε g).1 p =
      (aEps κ ξ ε)⁻¹ * HigherDimLFPP.lfppDistOn ξ (locField κ ε g) univ p.1 p.2 := by
  have hC : (⇑(locFieldC κ ε g) : Rd d → ℝ) = locField κ ε g := by
    unfold locFieldC
    rw [dite_eq_left hc]
    rfl
  unfold Meps
  rw [dite_eq_left ha, ContMetric.smul_apply, fieldLfppMetric_apply,
    fieldLfpp_eq_lfppDistOn (locFieldC κ ε g).continuous, hC]

/-- The value of `𝔐_{ε,ε/r}` (non-junk branch). -/
theorem l32p_MepsR_apply {κ : Rd d → ℝ} {ξ ε r : ℝ} {g : DistRd d}
    (hc : Continuous (locFieldR κ ε r g)) (ha : 0 < aEps κ ξ (ε / r)) (p : Rd d × Rd d) :
    (MepsR κ ξ ε r g).1 p =
      (aEps κ ξ (ε / r))⁻¹ * HigherDimLFPP.lfppDistOn ξ (locFieldR κ ε r g) univ p.1 p.2 := by
  have hC : (⇑(locFieldRC κ ε r g) : Rd d → ℝ) = locFieldR κ ε r g := by
    unfold locFieldRC
    rw [dite_eq_left hc]
    rfl
  unfold MepsR
  rw [dite_eq_left ha, ContMetric.smul_apply, fieldLfppMetric_apply,
    fieldLfpp_eq_lfppDistOn (locFieldRC κ ε r g).continuous, hC]

/-- `𝔐_{ε,ε/r}(g)` is a length metric (both branches are). -/
theorem l32p_MepsR_isLength (κ : Rd d → ℝ) (ξ ε r : ℝ) (g : DistRd d) :
    (MepsR κ ξ ε r g).IsLength := by
  unfold MepsR
  split_ifs with ha
  · exact ContMetric.isLength_smul _ (fieldLfppMetric_isLength ξ _)
  · exact fieldLfppMetric_isLength ξ _

/-- `0 < locRad ε` for `0 < ε < 1`. -/
theorem l32p_locRad_pos {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : 0 < locRad ε := by
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hε).2 hε1)
  unfold locRad
  exact mul_pos hε (pow_pos hlog _)

/-- `c_ε(r) > 0`. -/
theorem l32p_cRatio_pos {κ : Rd d → ℝ} {ξ Q ε r : ℝ} (hr : 0 < r) (ha : 0 < aEps κ ξ ε)
    (har : 0 < aEps κ ξ (ε / r)) : 0 < cRatio κ ξ Q ε r := by
  change 0 < r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε)
  exact div_pos (mul_pos hr har) (mul_pos (Real.rpow_pos_of_pos hr _) ha)

/-- **The normalization of `M_ε` at `(z, r)`** (MA1 A10.1, deterministic): with `g = recentAff r z h` and
`c₀ = sphereAvg (affineComp r z h) 1 0`, `M_ε(h)(z + r u, z + r v) = c_ε(r) r^{ξQ} e^{ξ c₀} 𝔐_{ε,ε/r}(g)(u, v)`. -/
theorem l32p_Meps_scale {κ : Rd d → ℝ} {ξ Q ε r : ℝ}
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    (hsc : LocFieldScaling κ) (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r)
    (hZ : locMass κ ε (locRad ε) ≠ 0) (ha : 0 < aEps κ ξ ε) (har : 0 < aEps κ ξ (ε / r))
    (g : DistRd d) (z u v : Rd d) :
    (Meps κ ξ ε g).1 (z + r • u, z + r • v) =
      cRatio κ ξ Q ε r * (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (affineComp r z g) 1 0)) *
        (MepsR κ ξ ε r (recentAff r z g)).1 (u, v) := by
  have hlocRad : 0 < locRad ε := l32p_locRad_pos hε hε1
  have hs : 0 < locRad ε / r := div_pos hlocRad hr
  obtain ⟨hmass, hfield⟩ := hsc ε r hε hε1 hr
  have hZ' : locMass κ (ε / r) (locRad ε / r) ≠ 0 := by rw [hmass]; exact hZ
  have hφψ : ∀ x : Rd d, locField κ ε g (z + r • x) =
      locFieldR κ ε r (recentAff r z g) x + sphereAvg (affineComp r z g) 1 0 := by
    intro x
    have h2 := l32p_locFieldR_addConst hK hs hZ' (recentAff r z g)
      (sphereAvg (affineComp r z g) 1 0) x
    rw [addConst_recentAff] at h2
    rw [hfield z g x, h2]
  have himage : (fun w : Rd d => z + r • w) '' univ = univ := by
    refine image_univ_of_surjective fun y => ⟨r⁻¹ • (y - z), ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have hlfpp := l9b_lfppDistOn_affine (ξ := ξ) hr hφψ univ u v
  rw [himage] at hlfpp
  rw [l32p_Meps_apply (continuous_locField hK hlocRad g) ha,
    l32p_MepsR_apply (l32p_continuous_locFieldR hK hs _) har]
  simp only
  rw [hlfpp]
  change (aEps κ ξ ε)⁻¹ * (r * Real.exp (ξ * sphereAvg (affineComp r z g) 1 0) *
      HigherDimLFPP.lfppDistOn ξ (locFieldR κ ε r (recentAff r z g)) univ u v) =
    r * aEps κ ξ (ε / r) / (r ^ (ξ * Q) * aEps κ ξ ε) *
      (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (affineComp r z g) 1 0)) *
      ((aEps κ ξ (ε / r))⁻¹ *
        HigherDimLFPP.lfppDistOn ξ (locFieldR κ ε r (recentAff r z g)) univ u v)
  have hrq : r ^ (ξ * Q) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  field_simp

/-! ### The rescaled event and the deterministic transfer -/

/-- **The rescaled good event `Ẽ`** (MA1 A10.1): `E′` at `(z, r) = (0, 1)` with ratio `c = 1` and connection radius
`b`, radii simplified: `U = A_{1/4,2}`, `V = A_{1/2,3/2}`, `S_in = S_{3/4}`, `S_out = S_1`, `F = Ā_{3/4,1}`. -/
def l32pUnitGood (G G' : ContMetric d) (A η b : ℝ) : Prop :=
  (∀ x ∈ sphere (0 : Rd d) (3 / 4), ∀ y ∈ sphere (0 : Rd d) 1,
      G'.internal (ann 0 (1 / 4) 2) x y ≤
          ENNReal.ofReal (1 + η) * G.internal (ann 0 (1 / 2) (3 / 2)) x y ∧
        G.internal (ann 0 (1 / 4) 2) x y ≤
          ENNReal.ofReal (1 + η) * G'.internal (ann 0 (1 / 2) (3 / 2)) x y) ∧
  (∀ x ∈ sphere (0 : Rd d) (3 / 4), ∀ y ∈ sphere (0 : Rd d) (3 / 4),
      G.internal (ann 0 (1 / 4) 2) x y ≤
          ENNReal.ofReal A * setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1) ∧
        G'.internal (ann 0 (1 / 4) 2) x y ≤
          ENNReal.ofReal A * setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1)) ∧
  (∀ x ∈ annCl (0 : Rd d) (3 / 4) 1, ∀ w ∈ ball x b,
      G'.internal (ann 0 (1 / 4) 2) x w ≤
          ENNReal.ofReal η * setDistIn G (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1) ∧
        G.internal (ann 0 (1 / 4) 2) x w ≤
          ENNReal.ofReal η * setDistIn G' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1))

theorem l32p_image_ann {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => z + r • x) '' ann 0 a b = ann z (r * a) (r * b) := by
  have hf : (fun x : Rd d => z + r • x) = fun x => r • x + z := funext fun x => add_comm _ _
  rw [hf, image_ann_affine hr z a b]

theorem l32p_image_sphere {r : ℝ} (hr : 0 < r) (z : Rd d) (t : ℝ) :
    (fun x : Rd d => z + r • x) '' sphere 0 t = sphere z (r * t) := by
  have hf : (fun x : Rd d => z + r • x) = fun x => r • x + z := funext fun x => add_comm _ _
  rw [hf, image_sphere_affine hr z t]

theorem l32p_image_annCl {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => z + r • x) '' annCl 0 a b = annCl z (r * a) (r * b) := by
  have hf : (fun x : Rd d => z + r • x) = fun x => r • x + z := funext fun x => add_comm _ _
  rw [hf, image_annCl_affine hr z a b]

/-- Internal set distances under the rescaling (from the internal-metric identity). -/
theorem l32p_setDistIn_scale {G H : ContMetric d} {lam r : ℝ} {z : Rd d} (hlam : 0 < lam)
    (hG : ∀ (V : Set (Rd d)) (u v : Rd d),
      G.internal ((fun x => z + r • x) '' V) (z + r • u) (z + r • v) =
        ENNReal.ofReal lam * H.internal V u v)
    (U S T : Set (Rd d)) :
    setDistIn G ((fun x => z + r • x) '' U) ((fun x => z + r • x) '' S)
        ((fun x => z + r • x) '' T) = ENNReal.ofReal lam * setDistIn H U S T := by
  unfold setDistIn
  simp only [iInf_image, hG]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hlam).ne' ENNReal.ofReal_ne_top]

/-- The algebra of one homogeneous inequality: `X ≤ a Y` implies `k X ≤ m (s Y)` when `m s = a k`. -/
theorem l32p_ofReal_mul_le {X Y : ℝ≥0∞} {k m s a : ℝ} (hk : 0 ≤ k) (hm : 0 ≤ m)
    (hmsak : m * s = a * k) (h : X ≤ ENNReal.ofReal a * Y) :
    ENNReal.ofReal k * X ≤ ENNReal.ofReal m * (ENNReal.ofReal s * Y) := by
  calc ENNReal.ofReal k * X ≤ ENNReal.ofReal k * (ENNReal.ofReal a * Y) := mul_le_mul_right h _
    _ = ENNReal.ofReal (a * k) * Y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hk, mul_comm k a]
    _ = ENNReal.ofReal (m * s) * Y := by rw [hmsak]
    _ = ENNReal.ofReal m * (ENNReal.ofReal s * Y) := by rw [ENNReal.ofReal_mul hm, mul_assoc]

/-- **Deterministic transfer** (MA1 A10.1): if the internal metrics of `G` and `G'` at `z + r ·` are `λ` and `c λ`
times those of `H` and `H'`, then `Ẽ(H, H'; b′)` implies `E′(G, G'; A, η, c, b)` at `(z, r)` whenever `b ≤ r b′`. -/
theorem l32p_goodAnnulus_of_unit {G G' H H' : ContMetric d} {A η c b b' lam r : ℝ} {z : Rd d}
    (hr : 0 < r) (hlam : 0 < lam) (hc : 0 < c) (hη : 0 ≤ η) (hb : b ≤ r * b')
    (hG : ∀ (V : Set (Rd d)) (u v : Rd d),
      G.internal ((fun x => z + r • x) '' V) (z + r • u) (z + r • v) =
        ENNReal.ofReal lam * H.internal V u v)
    (hG' : ∀ (V : Set (Rd d)) (u v : Rd d),
      G'.internal ((fun x => z + r • x) '' V) (z + r • u) (z + r • v) =
        ENNReal.ofReal (c * lam) * H'.internal V u v)
    (hE : l32pUnitGood H H' A η b') :
    GoodAnnulus G G' A η c b z r := by
  have hU : ann z (r / 4) (2 * r) = (fun x : Rd d => z + r • x) '' ann 0 (1 / 4) 2 := by
    rw [l32p_image_ann hr]; congr 1 <;> ring
  have hV : ann z (r / 2) (3 * r / 2) = (fun x : Rd d => z + r • x) '' ann 0 (1 / 2) (3 / 2) := by
    rw [l32p_image_ann hr]; congr 1 <;> ring
  have hSi : sphere z (3 * r / 4) = (fun x : Rd d => z + r • x) '' sphere 0 (3 / 4) := by
    rw [l32p_image_sphere hr]; congr 1; ring
  have hSo : sphere z r = (fun x : Rd d => z + r • x) '' sphere 0 1 := by
    rw [l32p_image_sphere hr, mul_one]
  have hF : annCl z (3 * r / 4) r = (fun x : Rd d => z + r • x) '' annCl 0 (3 / 4) 1 := by
    rw [l32p_image_annCl hr, mul_one]; congr 1; ring
  have hδ := l32p_setDistIn_scale hlam hG (ann 0 (1 / 4) 2) (sphere 0 (3 / 4)) (sphere 0 1)
  have hδ' := l32p_setDistIn_scale (mul_pos hc hlam) hG' (ann 0 (1 / 4) 2) (sphere 0 (3 / 4))
    (sphere 0 1)
  obtain ⟨h1, h2, h3⟩ := hE
  have hcl : 0 ≤ c * lam := (mul_pos hc hlam).le
  unfold GoodAnnulus
  rw [hU, hV, hSi, hSo, hF, hδ, hδ']
  simp only [Set.forall_mem_image]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hG', hG, hG, hG']
    obtain ⟨k1, k2⟩ := h1 x hx y hy
    exact ⟨l32p_ofReal_mul_le hcl (by positivity) (by ring) k1,
      l32p_ofReal_mul_le hlam.le (by positivity) (by field_simp) k2⟩
  · intro x hx y hy
    rw [hG, hG']
    obtain ⟨k1, k2⟩ := h2 x hx y hy
    refine ⟨?_, ?_⟩
    · rw [mul_left_comm]; exact mul_le_mul_right k1 _
    · rw [mul_left_comm]; exact mul_le_mul_right k2 _
  · intro x hx w hw
    obtain ⟨w', rfl⟩ : ∃ w' : Rd d, z + r • w' = w :=
      ⟨r⁻¹ • (w - z), by simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]⟩
    have hw' : w' ∈ ball x b' := by
      rw [mem_ball] at hw ⊢
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, ← dist_eq_norm] at hw
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_left hcon hr.le
      linarith
    rw [hG', hG]
    obtain ⟨k1, k2⟩ := h3 x hx w' hw'
    exact ⟨l32p_ofReal_mul_le hcl (by positivity) (by ring) k1,
      l32p_ofReal_mul_le hlam.le (by positivity) (by field_simp) k2⟩

/-- **Step 1, almost surely** (MA1 A10.1): for `0 < ε < 1` with `Z_ε ≠ 0`, `r > 0` and a centre `z`, almost surely
the rescaled event `Ẽ(D_g, 𝔐_{ε,ε/r}(g); b′)`, `g = recentAff r z h`, implies `E′_ε(z, r)` for `(D_h, M_ε(h))` with ratio
`c_ε(r)` and any connection radius `b ≤ r b′`. Uses `CoordScaling` for `D`, `l32p_Meps_scale` for `M_ε`, the
almost-sure identity `sphereAvg (affineComp r z h) 1 0 = h_r(z)` (`SeedFacts.affine`) and `AffineInternalScaling`. -/
theorem l32p_ae_goodAnnulus_of_unit {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (hsc : LocFieldScaling κ) (hcs : CoordScaling ξ Q D P h)
    (hai : AffineInternalScaling d) {ε r : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hr : 0 < r)
    (hZ : locMass κ ε (locRad ε) ≠ 0) (z : Rd d) {A η b b' : ℝ} (hη : 0 ≤ η)
    (hb : b ≤ r * b') :
    ∀ᵐ ω ∂P, l32pUnitGood (D (recentAff r z (h ω))) (MepsR κ ξ ε r (recentAff r z (h ω))) A η b' →
      GoodAnnulus (D (h ω)) (Meps κ ξ ε (h ω)) A η (cRatio κ ξ Q ε r) b z r := by
  have ha : 0 < aEps κ ξ ε := hS.seed.aEps_pos ξ ε hε
  have har : 0 < aEps κ ξ (ε / r) := hS.seed.aEps_pos ξ (ε / r) (div_pos hε hr)
  have hcR : 0 < cRatio κ ξ Q ε r := l32p_cRatio_pos hr ha har
  filter_upwards [hcs r hr z, hS.seed.affine P h hS.field z r hr] with ω hD haff hE
  have hlam : 0 < r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r z) :=
    mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  have hM : ∀ u v : Rd d, (Meps κ ξ ε (h ω)).1 (z + r • u, z + r • v) =
      (cRatio κ ξ Q ε r * (r ^ (ξ * Q) * Real.exp (ξ * sphereAvg (h ω) r z))) *
        (MepsR κ ξ ε r (recentAff r z (h ω))).1 (u, v) := by
    intro u v
    rw [l32p_Meps_scale hS.seed.kernelSmooth hsc hε hε1 hr hZ ha har (h ω) z u v, haff.2]
  exact l32p_goodAnnulus_of_unit hr hlam hcR hη hb (hai _ _ z r _ hr hlam hD)
    (hai _ _ z r _ hr (mul_pos hcR hlam) hM) hE

end HigherDimLFPPAS.Annulus
