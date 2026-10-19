import HigherDimLFPP.Lower.GaussModel
import HigherDimLFPP.Lower.Frames
import HigherDimLFPP.Field.BandFacts
import QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# Band triples and their Gaussian law (lower comparison, source §5.3)

Packet P-L2a, target T1 (ruling H6; audit HA4, "Details for later use" D2 "Law invariance" and
D7 "Finite model").

A *triple* `t = (a, b, z) : TriD d` stands for the scale band `(a, b]` at the point `z`, i.e.
the band field value `H_{a,b}(z) = W(k_{a,b,z})` of (1.1).  Its covariance kernel is

`kapD κ (a,b,z) (a',b',z') = ∫_{(a,b] ∩ (a',b']} C(s⁻¹ (z - z')) ds / s`,  `C = autoCorr κ`.

* `kapD_eq_inner`: for positive lower endpoints, `kapD` is the `L²(ℝ × ℝ^d)` Gram kernel of the
  band vectors `triVec κ t = k_{a,b,z}` (P-F1's `inner_bandVec`); hence `kapD_psd` (no Fourier
  analysis) and `exists_gram_kapD`.
* `kapD_diag`: `kapD (a,b,z) (a,b,z) = log (b/a)`; `kapD_split`: additivity over adjacent bands;
  `kapD_eq_zero_of_le`: disjoint bands are uncorrelated.
* `kapD_sim`, `kapD_tau`: invariance under `τ_S (a,b,z) = (r a, r b, S z)` for a similarity
  `S` of ratio `r > 0` (any `T` with `‖T z - T w‖ = r ‖z - w‖`; `C` is radial, so the whole
  orthogonal group is allowed, HA4 D2).  `tau_comp`: `τ_S ∘ τ_T = τ_{S ∘ T}` (recursive frames).
* `gLawD κ F`: the centered Gaussian law on `TriD d → ℝ` with covariance `kapD κ` on the finite
  set `F` (the generic `gLawOn` of `GaussModel.lean`), and its consequences:
  `integral_gLawD_eq_of_subset` (law transfer of finite-dimensional functionals between
  ambient sets), `integral_gLawD_tau` (similarity invariance in law),
  `integral_mul_gLawD_of_disjoint` (independence of functionals of disjoint band groups),
  `integral_exp_gLawD` (`E e^{c Y(a,b,z)} = e^{c² log(b/a)/2}`), `ae_gLawD_split`
  (`Y(a,c,z) = Y(a,b,z) + Y(b,c,z)` a.s.).
* `map_restrict_gLawD`, `integral_gLawD_eq_whiteNoise`, `measure_gLawD_eq_whiteNoise`: on a
  finite set of triples, `gLawD κ F` is the joint law of the white-noise band values
  `W(k_{a,b,z})` (both are centered Gaussian vectors with covariance `kapD κ`), for every white
  noise `W` on any probability space.

2D source: `LQGDimension/LFPP/BlockConstructionAux2.lean` (`Tri`, `kap`, `kap_psd`, `kap_band`,
`kap_diag`, `kap_split`, `kap_eq_zero_of_le`, `kap_sim`, `exists_gram_kap`), with the heat
kernel replaced by `C = κ ⋆ κ` and the Fourier representation by the `L²` realization.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ## Triples and the kernel -/

/-- A band triple `(a, b, z)`: the scale band `(a, b]` at the point `z`. -/
abbrev TriD (d : ℕ) : Type := ℝ × ℝ × Rd d

/-- The covariance kernel of band triples:
`kapD κ (a,b,z) (a',b',z') = ∫_{(a,b] ∩ (a',b']} C(s⁻¹ (z - z')) ds / s`. -/
def kapD (κ : Rd d → ℝ) (t t' : TriD d) : ℝ :=
  ∫ s in Ioc (max t.1 t'.1) (min t.2.1 t'.2.1), autoCorr κ (s⁻¹ • (t.2.2 - t'.2.2)) / s

/-- The band vector `k_{a,b,z} ∈ L²(ℝ × ℝ^d)` of a triple. -/
def triVec (κ : Rd d → ℝ) (t : TriD d) : WN d := bandVec κ t.1 t.2.1 t.2.2

theorem triVec_mk (κ : Rd d → ℝ) (a b : ℝ) (z : Rd d) : triVec κ (a, b, z) = bandVec κ a b z :=
  rfl

/-- **Gram realization**: `kapD` is the `L²` Gram kernel of the band vectors. -/
theorem kapD_eq_inner (hκ : IsLFPPKernel κ) {t t' : TriD d} (ht : 0 < t.1) (ht' : 0 < t'.1) :
    kapD κ t t' = ⟪triVec κ t, triVec κ t'⟫ := by
  rw [triVec, triVec, inner_bandVec hκ ht ht', kapD, integral_Ioc_eq_integral_Ioo]

theorem kapD_comm (κ : Rd d → ℝ) (t t' : TriD d) : kapD κ t t' = kapD κ t' t := by
  unfold kapD
  rw [max_comm, min_comm]
  congr 1
  funext s
  rw [← neg_sub, smul_neg, autoCorr_neg]

/-- `kapD` is positive semidefinite on finite sets of triples with positive lower endpoints. -/
theorem kapD_psd (hκ : IsLFPPKernel κ) (F : Finset (TriD d)) (hF : ∀ t ∈ F, 0 < t.1) :
    LQGDimension.PSDOn F (kapD κ) := by
  unfold LQGDimension.PSDOn
  have h : (Matrix.of fun i j : F => kapD κ i j) =
      Matrix.of fun i j : F => ⟪triVec κ i, triVec κ j⟫ := by
    ext i j
    simp only [Matrix.of_apply]
    exact kapD_eq_inner hκ (hF i i.2) (hF j j.2)
  rw [h]
  exact LQGDimension.posSemidef_gramOn F (triVec κ)

/-- Gram realization of `kapD` on a finite set of triples in a Euclidean space. -/
theorem exists_gram_kapD (hκ : IsLFPPKernel κ) (F : Finset (TriD d)) (hF : ∀ t ∈ F, 0 < t.1) :
    ∃ m : ℕ, ∃ β : TriD d → EuclideanSpace ℝ (Fin m),
      ∀ t ∈ F, ∀ t' ∈ F, ⟪β t, β t'⟫ = kapD κ t t' := by
  obtain ⟨v, hv⟩ := LQGDimension.exists_gram_of_psdOn F (kapD κ) (kapD_psd hκ F hF)
  refine ⟨F.card, fun t => LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ F.equivFin (v t), ?_⟩
  intro t ht t' ht'
  rw [LinearIsometryEquiv.inner_map_map]
  exact hv t ht t' ht'

/-- The band covariance: `kapD (a,b,z) (a,b,w) = ∫_{(a,b]} C(s⁻¹ (z - w)) ds / s`. -/
theorem kapD_band (κ : Rd d → ℝ) (a b : ℝ) (z w : Rd d) :
    kapD κ (a, b, z) (a, b, w) = ∫ s in Ioc a b, autoCorr κ (s⁻¹ • (z - w)) / s := by
  simp only [kapD, max_self, min_self]

/-- `Var Y(a,b,z) = log (b/a)`. -/
theorem kapD_diag (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (z : Rd d) :
    kapD κ (a, b, z) (a, b, z) = Real.log (b / a) := by
  rw [kapD_eq_inner hκ ha ha, real_inner_self_eq_norm_sq]
  exact norm_bandVec_sq hκ ha hab z

/-- **Additivity over adjacent bands** (first argument). -/
theorem kapD_split (hκ : IsLFPPKernel κ) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (z : Rd d) {t' : TriD d} (ht' : 0 < t'.1) :
    kapD κ (a, c, z) t' = kapD κ (a, b, z) t' + kapD κ (b, c, z) t' := by
  rw [kapD_eq_inner hκ ha ht', kapD_eq_inner hκ ha ht',
    kapD_eq_inner hκ (lt_of_lt_of_le ha hab) ht']
  simp only [triVec_mk]
  rw [← bandVec_add hκ ha hab hbc z, inner_add_left]

/-- **Additivity over adjacent bands** (second argument). -/
theorem kapD_split_right (hκ : IsLFPPKernel κ) {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbc : b ≤ c) (z : Rd d) {t' : TriD d} (ht' : 0 < t'.1) :
    kapD κ t' (a, c, z) = kapD κ t' (a, b, z) + kapD κ t' (b, c, z) := by
  rw [kapD_comm κ t', kapD_comm κ t', kapD_comm κ t', kapD_split hκ ha hab hbc z ht']

/-- **Disjoint bands are uncorrelated**. -/
theorem kapD_eq_zero_of_le (κ : Rd d → ℝ) {t t' : TriD d} (h : t.2.1 ≤ t'.1) :
    kapD κ t t' = 0 := by
  unfold kapD
  rw [Ioc_eq_empty (not_lt.2 ((min_le_left _ _).trans (h.trans (le_max_right _ _)))),
    Measure.restrict_empty, integral_zero_measure]

theorem kapD_eq_zero_of_le' (κ : Rd d → ℝ) {t t' : TriD d} (h : t'.2.1 ≤ t.1) :
    kapD κ t t' = 0 := by
  rw [kapD_comm]
  exact kapD_eq_zero_of_le κ h

/-- An empty band has zero covariance with everything. -/
theorem kapD_eq_zero_of_empty (κ : Rd d → ℝ) {t : TriD d} (h : t.2.1 ≤ t.1) (t' : TriD d) :
    kapD κ t t' = 0 := by
  unfold kapD
  rw [Ioc_eq_empty (not_lt.2 ((min_le_left _ _).trans (h.trans (le_max_left _ _)))),
    Measure.restrict_empty, integral_zero_measure]

/-- **Similarity invariance** (HA4 D2): for `T` with `‖T z - T w‖ = r ‖z - w‖`, `r > 0`,
`kapD (r a, r b, T z) (r a', r b', T w) = kapD (a, b, z) (a', b', w)`. This uses only that
`C = autoCorr κ` is radial, so every orthogonal frame is allowed. -/
theorem kapD_sim (hκ : IsLFPPKernel κ) {r : ℝ} (hr : 0 < r) (T : Rd d → Rd d)
    (hT : ∀ z w, ‖T z - T w‖ = r * ‖z - w‖) (t t' : TriD d) :
    kapD κ (r * t.1, r * t.2.1, T t.2.2) (r * t'.1, r * t'.2.1, T t'.2.2) = kapD κ t t' := by
  unfold kapD
  rw [← mul_max_of_nonneg _ _ hr.le, ← mul_min_of_nonneg _ _ hr.le]
  obtain ⟨m, hm⟩ : ∃ m, m = max t.1 t'.1 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = min t.2.1 t'.2.1 := ⟨_, rfl⟩
  rw [← hm, ← hM]
  rcases le_or_gt m M with hmM | hmM
  · rw [← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hmM hr.le),
      ← intervalIntegral.integral_of_le hmM]
    have hcv := intervalIntegral.integral_comp_mul_left
      (fun s => autoCorr κ (s⁻¹ • (T t.2.2 - T t'.2.2)) / s) hr.ne' (a := m) (b := M)
    have hpt : ∀ u : ℝ, autoCorr κ ((r * u)⁻¹ • (T t.2.2 - T t'.2.2)) / (r * u) =
        r⁻¹ * (autoCorr κ (u⁻¹ • (t.2.2 - t'.2.2)) / u) := by
      intro u
      rcases eq_or_ne u 0 with hu | hu
      · simp [hu]
      · have hn : ‖(r * u)⁻¹ • (T t.2.2 - T t'.2.2)‖ = ‖u⁻¹ • (t.2.2 - t'.2.2)‖ := by
          rw [norm_smul, norm_smul, hT, norm_inv, norm_inv, norm_mul, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hr]
          field_simp
        rw [autoCorr_eq_of_norm_eq hκ hn]
        field_simp
    simp_rw [hpt] at hcv
    rw [intervalIntegral.integral_const_mul, smul_eq_mul] at hcv
    have hr' : r ≠ 0 := hr.ne'
    have : ∫ x in r * m..r * M, autoCorr κ (x⁻¹ • (T t.2.2 - T t'.2.2)) / x =
        r * (r⁻¹ * ∫ x in m..M, autoCorr κ (x⁻¹ • (t.2.2 - t'.2.2)) / x) := by
      rw [hcv, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    rw [this, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
  · rw [Ioc_eq_empty (not_lt.2 (mul_le_mul_of_nonneg_left hmM.le hr.le)),
      Ioc_eq_empty (not_lt.2 hmM.le), Measure.restrict_empty, integral_zero_measure,
      integral_zero_measure]

/-! ## The action of similarities on triples -/

/-- The action `τ_S (a, b, z) = (r a, r b, S z)` of a similarity of ratio `r` on band triples
(the band `(a,b]` at `z` in the coordinates of `S`). -/
def tau (S : SimD d) (t : TriD d) : TriD d := (S.r * t.1, S.r * t.2.1, S.app t.2.2)

theorem tau_mk (S : SimD d) (a b : ℝ) (z : Rd d) : tau S (a, b, z) = (S.r * a, S.r * b, S.app z) :=
  rfl

theorem tau_fst (S : SimD d) (t : TriD d) : (tau S t).1 = S.r * t.1 := rfl

theorem tau_snd_fst (S : SimD d) (t : TriD d) : (tau S t).2.1 = S.r * t.2.1 := rfl

/-- **Recursive frames**: `τ_S ∘ τ_T = τ_{S ∘ T}`. -/
theorem tau_comp (S T : SimD d) (t : TriD d) : tau S (tau T t) = tau (S.comp T) t := by
  simp only [tau, SimD.app_comp, SimD.comp_r, mul_assoc]

theorem tau_id (t : TriD d) : tau (SimD.id : SimD d) t = t := by
  rw [tau, SimD.app_id]
  simp only [SimD.id, one_mul]

/-- **Similarity invariance of the kernel** under `τ_S`, `S` of ratio `r > 0`. -/
theorem kapD_tau (hκ : IsLFPPKernel κ) (S : SimD d) (hS : 0 < S.r) (t t' : TriD d) :
    kapD κ (tau S t) (tau S t') = kapD κ t t' :=
  kapD_sim hκ hS S.app (fun z w => by rw [S.norm_app_sub, abs_of_pos hS]) t t'

/-! ## The Gaussian law on band triples -/

/-- The centered Gaussian law on `TriD d → ℝ` with covariance `kapD κ` on the finite set `F`
(and `0` off `F`): the law of the band values `Y(a,b,z) = H_{a,b}(z)`, `(a,b,z) ∈ F`. -/
def gLawD (κ : Rd d → ℝ) (F : Finset (TriD d)) : Measure (TriD d → ℝ) := gLawOn (kapD κ) F

instance isProbabilityMeasure_gLawD (κ : Rd d → ℝ) (F : Finset (TriD d)) :
    IsProbabilityMeasure (gLawD κ F) :=
  isProbabilityMeasure_gLawOn _ _

/-- **Law transfer between ambient sets**: the law of an `F`-local functional under `gLawD κ F`
and `gLawD κ G` agree for `F ⊆ G` (positive lower endpoints on `G`). -/
theorem integral_gLawD_eq_of_subset (hκ : IsLFPPKernel κ) {F G : Finset (TriD d)} (hFG : F ⊆ G)
    (hG : ∀ t ∈ G, 0 < t.1) {Φ : (TriD d → ℝ) → ℝ} (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    ∫ Y, Φ Y ∂gLawD κ F = ∫ Y, Φ Y ∂gLawD κ G :=
  integral_gLawOn_eq_of_subset (kapD κ) hFG (kapD_psd hκ G hG) hΦ hloc

theorem integrable_gLawD_iff_of_subset (hκ : IsLFPPKernel κ) {F G : Finset (TriD d)}
    (hFG : F ⊆ G) (hG : ∀ t ∈ G, 0 < t.1) {Φ : (TriD d → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hloc : IsLoc F Φ) : Integrable Φ (gLawD κ F) ↔ Integrable Φ (gLawD κ G) :=
  integrable_gLawOn_iff_of_subset (kapD κ) hFG (kapD_psd hκ G hG) hΦ hloc

theorem measure_gLawD_eq_of_subset (hκ : IsLFPPKernel κ) {F G : Finset (TriD d)} (hFG : F ⊆ G)
    (hG : ∀ t ∈ G, 0 < t.1) {A : Set (TriD d → ℝ)} (hA : MeasurableSet A)
    (hloc : IsLoc F fun Y => Y ∈ A) : gLawD κ F A = gLawD κ G A :=
  measure_gLawOn_eq_of_subset (kapD κ) hFG (kapD_psd hκ G hG) hA hloc

/-- **Similarity invariance in law**: if `τ_S` (ratio `r > 0`) maps `F` into `G`, then the field
`Y ∘ τ_S` under `gLawD κ G` has the law `gLawD κ F` on `F`-local functionals. -/
theorem integral_gLawD_tau (hκ : IsLFPPKernel κ) {F G : Finset (TriD d)} (S : SimD d)
    (hS : 0 < S.r) (hτ : ∀ t ∈ F, tau S t ∈ G) (hG : ∀ t ∈ G, 0 < t.1)
    {Φ : (TriD d → ℝ) → ℝ} (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    ∫ Y, Φ (fun t => Y (tau S t)) ∂gLawD κ G = ∫ Y, Φ Y ∂gLawD κ F :=
  integral_gLawOn_comp (kapD κ) (tau S) hτ (fun t _ t' _ => kapD_tau hκ S hS t t')
    (kapD_psd hκ G hG) hΦ hloc

/-- **Independence of disjoint band groups**: if every band of `A` lies below or above every
band of `B` (no common scale), functionals of the `A`-coordinates and of the `B`-coordinates are
independent. -/
theorem integral_mul_gLawD_of_disjoint (hκ : IsLFPPKernel κ) {F A B : Finset (TriD d)}
    (hA : A ⊆ F) (hB : B ⊆ F) (hF : ∀ t ∈ F, 0 < t.1)
    (hdisj : ∀ t ∈ A, ∀ t' ∈ B, t.2.1 ≤ t'.1 ∨ t'.2.1 ≤ t.1) {Φ Ψ : (TriD d → ℝ) → ℝ}
    (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (hΦl : IsLoc A Φ) (hΨl : IsLoc B Ψ) :
    ∫ Y, Φ Y * Ψ Y ∂gLawD κ F = (∫ Y, Φ Y ∂gLawD κ F) * ∫ Y, Ψ Y ∂gLawD κ F :=
  integral_mul_gLawOn_of_orth (kapD κ) hA hB (kapD_psd hκ F hF)
    (fun t ht t' ht' => (hdisj t ht t' ht').elim (kapD_eq_zero_of_le κ)
      (kapD_eq_zero_of_le' κ)) hΦ hΨ hΦl hΨl

/-- **Exponential moments**: `E e^{c Y(a,b,z)} = e^{c² log(b/a) / 2}`. -/
theorem integral_exp_gLawD (hκ : IsLFPPKernel κ) {F : Finset (TriD d)} (hF : ∀ t ∈ F, 0 < t.1)
    {a b : ℝ} {z : Rd d} (ht : (a, b, z) ∈ F) (hab : a ≤ b) (c : ℝ) :
    ∫ Y, Real.exp (c * Y (a, b, z)) ∂gLawD κ F = Real.exp (c ^ 2 * Real.log (b / a) / 2) := by
  rw [gLawD, integral_exp_gLawOn (kapD κ) (kapD_psd hκ F hF) ht c,
    kapD_diag hκ (hF _ ht) hab z]

theorem integrable_exp_gLawD (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) {t : TriD d} (ht : t ∈ F) (c : ℝ) :
    Integrable (fun Y : TriD d → ℝ => Real.exp (c * Y t)) (gLawD κ F) :=
  integrable_exp_gLawOn (kapD κ) (kapD_psd hκ F hF) ht c

/-- **Band additivity holds almost surely**: `Y(a,c,z) = Y(a,b,z) + Y(b,c,z)`. -/
theorem ae_gLawD_split (hκ : IsLFPPKernel κ) {F : Finset (TriD d)} (hF : ∀ t ∈ F, 0 < t.1)
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {z : Rd d} (hac : (a, c, z) ∈ F)
    (habF : (a, b, z) ∈ F) (hbcF : (b, c, z) ∈ F) :
    ∀ᵐ Y ∂gLawD κ F, Y (a, c, z) = Y (a, b, z) + Y (b, c, z) := by
  have h := ae_gLawOn_eq_sum (kapD κ) (kapD_psd hκ F hF) (Finset.univ : Finset (Fin 2))
    (a, c, z) ![(a, b, z), (b, c, z)] hac (fun k _ => by fin_cases k <;> simpa)
    (fun j hj => by
      rw [Fin.sum_univ_two]
      exact kapD_split_right hκ (hF _ hac) hab hbc z (hF j hj))
  filter_upwards [h] with Y hY
  rw [hY, Fin.sum_univ_two]
  rfl

/-! ## The law of white-noise band values -/

section WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **The joint law of finitely many band values**: for every white noise `W` (on any
probability space) and every finite set `F` of triples with positive lower endpoints, the vector
`(Y t)_{t ∈ F}` under `gLawD κ F` has the law of `(W(k_t))_{t ∈ F}`. -/
theorem map_restrict_gLawD (hκ : IsLFPPKernel κ) (F : Finset (TriD d)) (hF : ∀ t ∈ F, 0 < t.1)
    (hW : IsWhiteNoise P W) :
    (gLawD κ F).map (fun Y (t : F) => Y t) = P.map (fun ω (t : F) => W (triVec κ t) ω) := by
  have := hW.isProbabilityMeasure
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn F (kapD κ) (kapD_psd hκ F hF)
  have hm1 : Measurable (extQ F ∘ LQGDimension.gramMap F β) :=
    (measurable_extQ F).comp (LQGDimension.gramMap F β).continuous.measurable
  have hm2 : Measurable fun (Y : TriD d → ℝ) (t : F) => Y t :=
    Measurable.of_eval fun t => measurable_pi_apply _
  rw [gLawD, gLawOn_eq_map (kapD κ) F β hβ, Measure.map_map hm2 hm1]
  have hfun : (fun (Y : TriD d → ℝ) (t : F) => Y t) ∘ (extQ F ∘ LQGDimension.gramMap F β) =
      fun x (t : F) => ⟪β t, x⟫ := by
    funext x t
    simp only [Function.comp_apply]
    rw [extQ_of_mem F _ t.2, LQGDimension.gramMap_apply]
  rw [hfun]
  have hL : HasGaussianLaw (fun (x : EuclideanSpace ℝ F) (t : F) => ⟪β t, x⟫)
      (stdGaussian (EuclideanSpace ℝ F)) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (EuclideanSpace ℝ F))).map_fun
      (ContinuousLinearMap.pi fun t : F => innerSL ℝ (β t))
  refine QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
    (U := fun (t : F) (x : EuclideanSpace ℝ F) => ⟪β t, x⟫)
    (V := fun (t : F) ω => W (triVec κ t) ω) hL (hW.hasGaussianLaw_fintype fun t : F => triVec κ t)
    (fun t => (continuous_const.inner continuous_id).measurable) (fun t => hW.measurable _)
    (fun t => (hL.eval t).memLp_two) (fun t => hW.memLp _ 2 ENNReal.ofNat_ne_top)
    (fun t => ?_) (fun t => hW.integral_eq_zero _) fun t t' => ?_
  · have h := integral_inner (𝕜 := ℝ) (IsGaussian.integrable_id
      (μ := stdGaussian (EuclideanSpace ℝ F))) (β t)
    simp only [id] at h
    rw [h, integral_id_stdGaussian, inner_zero_right]
  · rw [cov_inner_stdGaussian, hW.cov_eq, hβ t t.2 t' t'.2,
      kapD_eq_inner hκ (hF t t.2) (hF t' t'.2)]

/-- **Expectations of finite-dimensional functionals** under `gLawD κ F` are expectations of the
same functionals of the white-noise band values. -/
theorem integral_gLawD_eq_whiteNoise (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) (hW : IsWhiteNoise P W) {Φ : (TriD d → ℝ) → ℝ}
    (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    ∫ Y, Φ Y ∂gLawD κ F = ∫ ω, Φ (fun t => W (triVec κ t) ω) ∂P := by
  have hm2 : Measurable fun (Y : TriD d → ℝ) (t : F) => Y t :=
    Measurable.of_eval fun t => measurable_pi_apply _
  have hmW : Measurable fun ω (t : F) => W (triVec κ t) ω :=
    Measurable.of_eval fun t => hW.measurable _
  have hG : Measurable (Φ ∘ extF F) := hΦ.comp (measurable_extF F)
  have e1 : ∫ Y, Φ Y ∂gLawD κ F = ∫ Y, (Φ ∘ extF F) (fun t : F => Y t) ∂gLawD κ F :=
    integral_congr_ae (ae_of_all _ fun Y => hloc.eq_extF Y)
  have e2 : ∫ ω, Φ (fun t => W (triVec κ t) ω) ∂P =
      ∫ ω, (Φ ∘ extF F) (fun t : F => W (triVec κ t) ω) ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => hloc.eq_extF _)
  rw [e1, e2, ← integral_map hm2.aemeasurable hG.aestronglyMeasurable,
    ← integral_map hmW.aemeasurable hG.aestronglyMeasurable, map_restrict_gLawD hκ F hF hW]

/-- **Probabilities of finite-dimensional events** under `gLawD κ F` are probabilities of the
same events for the white-noise band values. -/
theorem measure_gLawD_eq_whiteNoise (hκ : IsLFPPKernel κ) {F : Finset (TriD d)}
    (hF : ∀ t ∈ F, 0 < t.1) (hW : IsWhiteNoise P W) {A : Set (TriD d → ℝ)}
    (hA : MeasurableSet A) (hloc : IsLoc F fun Y => Y ∈ A) :
    gLawD κ F A = P {ω | (fun t => W (triVec κ t) ω) ∈ A} := by
  have hm2 : Measurable fun (Y : TriD d → ℝ) (t : F) => Y t :=
    Measurable.of_eval fun t => measurable_pi_apply _
  have hmW : Measurable fun ω (t : F) => W (triVec κ t) ω :=
    Measurable.of_eval fun t => hW.measurable _
  have hA' : MeasurableSet (extF F ⁻¹' A) := measurable_extF F hA
  have e1 : A = (fun (Y : TriD d → ℝ) (t : F) => Y t) ⁻¹' (extF F ⁻¹' A) := by
    ext Y
    simp only [mem_preimage]
    exact iff_of_eq (hloc.eq_extF Y)
  have e2 : {ω | (fun t => W (triVec κ t) ω) ∈ A} =
      (fun ω (t : F) => W (triVec κ t) ω) ⁻¹' (extF F ⁻¹' A) := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    exact iff_of_eq (hloc.eq_extF _)
  rw [e2, ← Measure.map_apply hmW hA', ← map_restrict_gLawD hκ F hF hW,
    Measure.map_apply hm2 hA', ← e1]

end WhiteNoise

end HigherDimLFPP.Lower
