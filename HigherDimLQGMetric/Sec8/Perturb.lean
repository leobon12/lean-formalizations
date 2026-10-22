import HigherDimLQGMetric.Sec6.Geometry
import HigherDimLQGMetric.Sphere.Conv
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# Section 8: finite perturbations

The finite sum of the smooth traps and its exact local support properties.
The almost-sure sphere-average statements are kept separate from these
deterministic identities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open MeasureTheory Set Metric Filter Topology

variable {d : ℕ}

/-- The deterministic perturbation associated to a finite labeled set. -/
def F_Z (f : ℕ → C(Rd d, ℝ)) (r : ℝ) (Z : Finset (Rd d × ℕ)) : C(Rd d, ℝ) :=
  ∑ q ∈ Z, bumpAt (f q.2) r q.1

/-- A finite sum of nonnegative bounded bumps has the expected global bound. -/
theorem F_Z_nonneg_le {f : ℕ → C(Rd d, ℝ)} {J : ℕ} {Mf : ℝ}
    (hf : ∀ j < J, (∀ x, 0 ≤ f j x) ∧ (∀ x, f j x ≤ Mf))
    (r : ℝ) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < J) (x : Rd d) :
    0 ≤ F_Z f r Z x ∧ F_Z f r Z x ≤ Z.card * Mf := by
  rw [F_Z, ContinuousMap.sum_apply]
  constructor
  · exact Finset.sum_nonneg fun q hq => (hf q.2 (hJ q hq)).1 _
  · calc
      ∑ q ∈ Z, bumpAt (f q.2) r q.1 x ≤ ∑ _q ∈ Z, Mf := by
        apply Finset.sum_le_sum
        intro q hq
        exact (hf q.2 (hJ q hq)).2 _
      _ = Z.card * Mf := by simp

/-- Inside a selected trap ball only that trap's bump is present. -/
theorem F_Z_eq_bumpAt {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {x : Rd d} (hx : x ∈ ball z (4 * r)) :
    F_Z f r Z x = bumpAt (f j) r z x :=
  S6a.sum_bumpAt_eq hsupp hr hzZ hJ hdisj hx

/-- A color class has centers at least `10r` apart. Consequently all other
bumps vanish throughout `B_{7r}(z)`, which contains both configuration shells. -/
theorem F_Z_eq_bumpAt_separated {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖)
    {x : Rd d} (hx : x ∈ ball z (7 * r)) :
    F_Z f r Z x = bumpAt (f j) r z x := by
  rw [F_Z, ContinuousMap.sum_apply]
  refine Finset.sum_eq_single (z, j) (fun q hq hne => ?_) (fun h => absurd hzZ h)
  have hfar : 3 * r ≤ ‖x - q.1‖ := by
    have htri := dist_triangle q.1 x z
    have hx' : ‖x - z‖ < 7 * r := by
      simpa only [mem_ball, dist_eq_norm] using hx
    have hs := hsep q hq hne
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev q.1 x] at htri
    linarith
  rw [bumpAt_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hAnn := hsupp q.2 (hJ q hq) hmem
  have h3 := hAnn.2
  rw [sub_zero, S6a.norm_pull hr, div_lt_iff₀ hr] at h3
  linarith

/-- Every trap bump vanishes on its own radius-`r` sphere. -/
theorem F_Z_eq_zero_on_site_sphere {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖)
    {x : Rd d} (hx : x ∈ sphere z r) : F_Z f r Z x = 0 := by
  have hnorm : ‖x - z‖ = r := by
    simpa only [mem_sphere, dist_eq_norm] using hx
  have hball : x ∈ ball z (7 * r) := by
    simp only [mem_ball, dist_eq_norm, hnorm]
    linarith
  rw [F_Z_eq_bumpAt_separated hsupp hr hzZ hJ hsep hball, bumpAt_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hAnn := hsupp j (hJ (z, j) hzZ) hmem
  have h1 := hAnn.1
  rw [sub_zero, S6a.norm_pull hr, hnorm, div_self hr.ne'] at h1
  exact (lt_irrefl (1 : ℝ)) h1

/-- Local Weyl scaling identifies the metric of a finite perturbation with
that of its one surviving bump, on every open subset of the trap ball. -/
theorem lemma82_internal {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P) {ξ Q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖) :
    ∀ᵐ ω ∂P, ∀ W : Set (Rd d), IsOpen W → W ⊆ ball z (7 * r) →
      ∀ u v : Rd d,
        (D (addFun (h ω) (F_Z f r Z))).internal W u v =
          (D (addFun (h ω) (bumpAt (f j) r z))).internal W u v ∧
        (Dt (addFun (h ω) (F_Z f r Z))).internal W u v =
          (Dt (addFun (h ω) (bumpAt (f j) r z))).internal W u v := by
  filter_upwards [hD.ae_internal_eq_weylScaleOn hh.isLGFPlusCont,
    hDt.ae_internal_eq_weylScaleOn hh.isLGFPlusCont] with ω hDw hDtw
  intro W hW hWball u v
  have hweight : ∀ x ∈ W, ξ * (F_Z f r Z) x = ξ * bumpAt (f j) r z x := by
    intro x hx
    rw [F_Z_eq_bumpAt_separated hsupp hr hzZ hJ hsep (hWball hx)]
  constructor
  · calc
      (D (addFun (h ω) (F_Z f r Z))).internal W u v =
          weylScaleOn ξ (F_Z f r Z) (D (h ω)) W u v := hDw _ W hW u v
      _ = weylScaleOn ξ (bumpAt (f j) r z) (D (h ω)) W u v :=
          weylScaleOn_congr hweight
      _ = (D (addFun (h ω) (bumpAt (f j) r z))).internal W u v :=
          (hDw _ W hW u v).symm
  · calc
      (Dt (addFun (h ω) (F_Z f r Z))).internal W u v =
          weylScaleOn ξ (F_Z f r Z) (Dt (h ω)) W u v := hDtw _ W hW u v
      _ = weylScaleOn ξ (bumpAt (f j) r z) (Dt (h ω)) W u v :=
          weylScaleOn_congr hweight
      _ = (Dt (addFun (h ω) (bumpAt (f j) r z))).internal W u v :=
          (hDtw _ W hW u v).symm

/-- The same local identity holds when all bumps are subtracted. -/
theorem lemma82_internal_neg {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P) {ξ Q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖) :
    ∀ᵐ ω ∂P, ∀ W : Set (Rd d), IsOpen W → W ⊆ ball z (7 * r) →
      ∀ u v : Rd d,
        (D (addFun (h ω) (-F_Z f r Z))).internal W u v =
          (D (addFun (h ω) (-bumpAt (f j) r z))).internal W u v ∧
        (Dt (addFun (h ω) (-F_Z f r Z))).internal W u v =
          (Dt (addFun (h ω) (-bumpAt (f j) r z))).internal W u v := by
  filter_upwards [hD.ae_internal_eq_weylScaleOn hh.isLGFPlusCont,
    hDt.ae_internal_eq_weylScaleOn hh.isLGFPlusCont] with ω hDw hDtw
  intro W hW hWball u v
  have hweight : ∀ x ∈ W, ξ * (-F_Z f r Z) x = ξ * (-bumpAt (f j) r z) x := by
    intro x hx
    rw [ContinuousMap.neg_apply, ContinuousMap.neg_apply,
      F_Z_eq_bumpAt_separated hsupp hr hzZ hJ hsep (hWball hx)]
  constructor
  · calc
      (D (addFun (h ω) (-F_Z f r Z))).internal W u v =
          weylScaleOn ξ (-F_Z f r Z) (D (h ω)) W u v := hDw _ W hW u v
      _ = weylScaleOn ξ (-bumpAt (f j) r z) (D (h ω)) W u v :=
          weylScaleOn_congr hweight
      _ = (D (addFun (h ω) (-bumpAt (f j) r z))).internal W u v :=
          (hDw _ W hW u v).symm
  · calc
      (Dt (addFun (h ω) (-F_Z f r Z))).internal W u v =
          weylScaleOn ξ (-F_Z f r Z) (Dt (h ω)) W u v := hDtw _ W hW u v
      _ = weylScaleOn ξ (-bumpAt (f j) r z) (Dt (h ω)) W u v :=
          weylScaleOn_congr hweight
      _ = (Dt (addFun (h ω) (-bumpAt (f j) r z))).internal W u v :=
          (hDtw _ W hW u v).symm

/-- The radius-`r` sphere average at a selected center is unchanged by the
entire separated perturbation, wherever the original defining limit exists. -/
theorem lemma82_sphereAvg_site (g : DistRd d)
    {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖)
    {a : ℝ} (hlim : Tendsto (sphereAvgSeq g r z) atTop (𝓝 a)) :
    sphereAvg (addFun g (F_Z f r Z)) r z = sphereAvg g r z := by
  rw [sphereAvg_addFun_of_tendsto hlim]
  have hzero : ∀ᵐ u ∂(unitSphereProb d), (F_Z f r Z) (z + r • u) = 0 := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    apply F_Z_eq_zero_on_site_sphere hsupp hr hzZ hJ hsep
    simp only [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  rw [integral_eq_zero_of_ae hzero]
  exact add_zero _

/-- The single bump also leaves its own radius-`r` sphere average fixed. -/
theorem lemma82_sphereAvg_single (g : DistRd d)
    {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    (hj : j < J) {r : ℝ} (hr : 0 < r) (z : Rd d)
    {a : ℝ} (hlim : Tendsto (sphereAvgSeq g r z) atTop (𝓝 a)) :
    sphereAvg (addFun g (bumpAt (f j) r z)) r z = sphereAvg g r z := by
  have hJ : ∀ q ∈ ({(z, j)} : Finset (Rd d × ℕ)), q.2 < J := by
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact hj
  have hsep : ∀ q ∈ ({(z, j)} : Finset (Rd d × ℕ)), q ≠ (z, j) →
      10 * r ≤ ‖q.1 - z‖ := by
    intro q hq hne
    exact False.elim (hne (Finset.mem_singleton.mp hq))
  have h := lemma82_sphereAvg_site g hsupp hr
    (Z := {(z, j)}) (by simp) hJ hsep hlim
  simpa only [F_Z, Finset.sum_singleton] using h

/-- All selected bumps are supported well inside the macroscopic sphere. -/
theorem F_Z_eq_zero_on_macro_sphere {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r R : ℝ} (hr : 0 < r) (hrR : 3 * r ≤ R)
    {Z : Finset (Rd d × ℕ)} (hJ : ∀ q ∈ Z, q.2 < J)
    (hcenter : ∀ q ∈ Z, ‖q.1‖ < 5 * R)
    {x : Rd d} (hx : x ∈ sphere (0 : Rd d) (8 * R)) :
    F_Z f r Z x = 0 := by
  rw [F_Z, ContinuousMap.sum_apply]
  apply Finset.sum_eq_zero
  intro q hq
  rw [bumpAt_apply]
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hAnn := hsupp q.2 (hJ q hq) hmem
  have h3 := hAnn.2
  rw [sub_zero, S6a.norm_pull hr, div_lt_iff₀ hr] at h3
  have htri := norm_add_le (x - q.1) q.1
  have hxnorm : ‖x‖ = 8 * R := by
    simpa only [mem_sphere, dist_eq_norm, sub_zero] using hx
  have heq : (x - q.1) + q.1 = x := sub_add_cancel x q.1
  rw [heq, hxnorm] at htri
  linarith [hcenter q hq]

/-- The macroscopic sphere average in (24) is unchanged by the finite sum. -/
theorem lemma82_sphereAvg_macro (g : DistRd d)
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r R : ℝ} (hr : 0 < r) (hrR : 3 * r ≤ R)
    {Z : Finset (Rd d × ℕ)} (hJ : ∀ q ∈ Z, q.2 < J)
    (hcenter : ∀ q ∈ Z, ‖q.1‖ < 5 * R)
    {a : ℝ} (hlim : Tendsto (sphereAvgSeq g (8 * R) 0) atTop (𝓝 a)) :
    sphereAvg (addFun g (F_Z f r Z)) (8 * R) 0 = sphereAvg g (8 * R) 0 := by
  rw [sphereAvg_addFun_of_tendsto hlim]
  have hzero : ∀ᵐ u ∂(unitSphereProb d), (F_Z f r Z) ((8 * R) • u) = 0 := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    apply F_Z_eq_zero_on_macro_sphere hsupp hr hrR hJ hcenter
    have hR : 0 ≤ R := by linarith
    simp only [mem_sphere, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 8 * R), hu, mul_one]
  have hzero' : ∀ᵐ u ∂(unitSphereProb d), (F_Z f r Z) (0 + (8 * R) • u) = 0 := by
    simpa only [zero_add] using hzero
  rw [integral_eq_zero_of_ae hzero']
  exact add_zero _

/-- Equality of the two annular internal metrics for each assignment and of
the normalizer gives equality of all four configuration coordinates. -/
theorem lemma82_config_of_internal (D₁ Dt₁ D₂ Dt₂ : ContMetric d)
    {s₁ s₂ r : ℝ} {z : Rd d} (hs : s₁ = s₂)
    (houtD : ∀ u v, D₁.internal (ann z (r / 2) (5 * r)) u v =
      D₂.internal (ann z (r / 2) (5 * r)) u v)
    (houtDt : ∀ u v, Dt₁.internal (ann z (r / 2) (5 * r)) u v =
      Dt₂.internal (ann z (r / 2) (5 * r)) u v)
    (hinD : ∀ u v, D₁.internal (ann z (3 * r / 4) (7 * r / 2)) u v =
      D₂.internal (ann z (3 * r / 4) (7 * r / 2)) u v)
    (hinDt : ∀ u v, Dt₁.internal (ann z (3 * r / 4) (7 * r / 2)) u v =
      Dt₂.internal (ann z (3 * r / 4) (7 * r / 2)) u v) :
    config D₁ Dt₁ s₁ r z = config D₂ Dt₂ s₂ r z := by
  unfold config
  subst s₂
  apply Prod.ext
  · funext u v
    dsimp only
    rw [houtD (r • u + z) (r • v + z)]
  apply Prod.ext
  · funext u v
    dsimp only
    rw [houtDt (r • u + z) (r • v + z)]
  apply Prod.ext
  · funext u v
    dsimp only
    rw [hinD (r • u + z) (r • v + z)]
  · funext u v
    dsimp only
    rw [hinDt (r • u + z) (r • v + z)]

/-- At a separated trap, adding the full finite perturbation gives exactly
the same four-component configuration as adding its one local bump. -/
theorem lemma82_config {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {ξ Q : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {f : ℕ → C(Rd d, ℝ)} {J j : ℕ}
    (hsupp : ∀ i < J, tsupport (f i) ⊆ ann (0 : Rd d) 1 3)
    {r : ℝ} (hr : 0 < r) {z : Rd d} {Z : Finset (Rd d × ℕ)}
    (hzZ : (z, j) ∈ Z) (hJ : ∀ q ∈ Z, q.2 < J)
    (hsep : ∀ q ∈ Z, q ≠ (z, j) → 10 * r ≤ ‖q.1 - z‖) :
    ∀ᵐ ω ∂P,
      config (D (addFun (h ω) (F_Z f r Z)))
        (Dt (addFun (h ω) (F_Z f r Z)))
        (sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r z) r z =
      config (D (addFun (h ω) (bumpAt (f j) r z)))
        (Dt (addFun (h ω) (bumpAt (f j) r z)))
        (sNorm ξ Q (addFun (h ω) (bumpAt (f j) r z)) r z) r z := by
  have houter : ann z (r / 2) (5 * r) ⊆ ball z (7 * r) := by
    intro x hx
    change ‖x - z‖ < 7 * r
    exact hx.2.trans (by linarith)
  have hinner : ann z (3 * r / 4) (7 * r / 2) ⊆ ball z (7 * r) := by
    intro x hx
    change ‖x - z‖ < 7 * r
    exact hx.2.trans (by linarith)
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z,
    lemma82_internal P h hh hD hDt hsupp hr hzZ hJ hsep] with ω hlim hw
  obtain ⟨a, ha⟩ := hlim
  have hs : sNorm ξ Q (addFun (h ω) (F_Z f r Z)) r z =
      sNorm ξ Q (addFun (h ω) (bumpAt (f j) r z)) r z := by
    simp only [sNorm, lemma82_sphereAvg_site (h ω) hsupp hr hzZ hJ hsep ha,
      lemma82_sphereAvg_single (h ω) hsupp (hJ (z, j) hzZ) hr z ha]
  have ho := hw (ann z (r / 2) (5 * r)) (isOpen_ann z _ _) houter
  have hi := hw (ann z (3 * r / 4) (7 * r / 2)) (isOpen_ann z _ _) hinner
  exact lemma82_config_of_internal _ _ _ _ hs
    (fun u v => (ho u v).1) (fun u v => (ho u v).2)
    (fun u v => (hi u v).1) (fun u v => (hi u v).2)

/-- Removing a finite perturbation after adding it gives the original distribution. -/
theorem addFun_F_Z_sub (g : DistRd d) (f : ℕ → C(Rd d, ℝ))
    (r : ℝ) (Z : Finset (Rd d × ℕ)) :
    addFun (addFun g (F_Z f r Z)) (-F_Z f r Z) = g := by
  rw [addFun_addFun]
  simp

/-- Conversely, adding a finite perturbation after removing it gives the original distribution. -/
theorem addFun_neg_F_Z_add (g : DistRd d) (f : ℕ → C(Rd d, ℝ))
    (r : ℝ) (Z : Finset (Rd d × ℕ)) :
    addFun (addFun g (-F_Z f r Z)) (F_Z f r Z) = g := by
  rw [addFun_addFun]
  simp

end HigherDimLQGMetric
