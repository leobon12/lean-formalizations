import HigherDimLQGContinuity.ForcingCount.Defs
import HigherDimLQGContinuity.Norm.ScalingSets
import HigherDimLQGMetric.Sharp.ScaledMetric
import HigherDimLQGMetric.Amplify.LengthScale

/-!
# Transport through site normalization

Packet Q9 (deterministic). For `0 < s`, `0 < S` the site-normalized metric `q9SiteNorm G z s S = G(z + s·, z + s·)/S`
transports distances, internal distances, curve lengths, the length property, geodesic segments, Weyl relations and the
trigger between physical and site coordinates (Part B `b:lem-site-normal`(b), deterministic part).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- The site affine map `w ↦ s w + z`. -/
def q9Aff (z : Rd d) (s : ℝ) : Rd d → Rd d := fun w => s • w + z

theorem q9SiteNorm_eq {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S) :
    q9SiteNorm G z s S = (G.affine s hs.ne' z).smul S⁻¹ (inv_pos.2 hS) := by
  unfold q9SiteNorm
  split_ifs with h
  · rfl
  · exact absurd ⟨hs, hS⟩ h

theorem q9SiteNorm_apply {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    (u v : Rd d) : (q9SiteNorm G z s S).1 (u, v) = S⁻¹ * G.1 (s • u + z, s • v + z) := by
  rw [q9SiteNorm_eq hs hS, ContMetric.smul_apply, ContMetric.affine_apply]

theorem q9SiteNorm_internal {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    (U : Set (Rd d)) (u v : Rd d) :
    (q9SiteNorm G z s S).internal U u v =
      ENNReal.ofReal S⁻¹ * G.internal (q9Aff z s '' U) (q9Aff z s u) (q9Aff z s v) := by
  rw [q9SiteNorm_eq hs hS, ContMetric.internal_smul, ContMetric.internal_affine]
  rfl

theorem q9SiteNorm_len {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    (P : ℝ → Rd d) (a b : ℝ) :
    (q9SiteNorm G z s S).len P a b = ENNReal.ofReal S⁻¹ * G.len (fun t => s • P t + z) a b := by
  rw [q9SiteNorm_eq hs hS, amplify_len_smul, amplify_len_affine]

theorem q9Aff_sitePath {P : ℝ → Rd d} {z : Rd d} {s : ℝ} (hs : 0 < s) (t : ℝ) :
    s • q9SitePath P z s t + z = P t := by
  simp only [q9SitePath, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, sub_add_cancel]

theorem q9Aff_apply_sitePath {P : ℝ → Rd d} {z : Rd d} {s : ℝ} (hs : 0 < s) (t : ℝ) :
    q9Aff z s (q9SitePath P z s t) = P t :=
  q9Aff_sitePath hs t

theorem q9SiteNorm_len_sitePath {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    (P : ℝ → Rd d) (a b : ℝ) :
    (q9SiteNorm G z s S).len (q9SitePath P z s) a b = ENNReal.ofReal S⁻¹ * G.len P a b := by
  rw [q9SiteNorm_len hs hS]
  congr 1
  exact G.len_congr fun t _ => q9Aff_sitePath hs t

theorem q9SiteNorm_apply_sitePath {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    (P : ℝ → Rd d) (a b : ℝ) :
    (q9SiteNorm G z s S).1 (q9SitePath P z s a, q9SitePath P z s b) = S⁻¹ * G.1 (P a, P b) := by
  rw [q9SiteNorm_apply hs hS, q9Aff_sitePath hs, q9Aff_sitePath hs]

theorem q9SiteNorm_isLength {G : ContMetric d} (hG : G.IsLength) (z : Rd d) (s S : ℝ) :
    (q9SiteNorm G z s S).IsLength := by
  unfold q9SiteNorm
  split_ifs with h
  · exact ContMetric.isLength_smul _ (ContMetric.isLength_affine _ _ hG)
  · exact hG

theorem continuousOn_q9SitePath {P : ℝ → Rd d} {z : Rd d} {s : ℝ} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) : ContinuousOn (q9SitePath P z s) (Icc a b) :=
  (hP.sub continuousOn_const).const_smul s⁻¹

/-- Site normalization of a geodesic segment is a geodesic segment. -/
theorem isGeodSeg_q9SiteNorm {G : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S)
    {P : ℝ → Rd d} {a b : ℝ} (hP : IsGeodSeg G P a b) :
    IsGeodSeg (q9SiteNorm G z s S) (q9SitePath P z s) a b := by
  refine ⟨hP.1, continuousOn_q9SitePath hP.2.1, ?_⟩
  rw [q9SiteNorm_len_sitePath hs hS, hP.2.2, q9SiteNorm_apply_sitePath hs hS,
    ENNReal.ofReal_mul (inv_nonneg.2 hS.le)]

theorem q9Aff_image_open {z : Rd d} {s : ℝ} (hs : 0 < s) {U : Set (Rd d)} (hU : IsOpen U) :
    IsOpen (q9Aff z s '' U) := by
  have h := (affineHomeomorph s hs.ne' z).isOpenMap U hU
  have he : ⇑(affineHomeomorph s hs.ne' z) = q9Aff z s := by
    funext x
    simp [q9Aff]
  rwa [he] at h

theorem q9Aff_preimage_image {z : Rd d} {s : ℝ} (hs : 0 < s) (U : Set (Rd d)) :
    ContMetric.affineMap s z ⁻¹' (q9Aff z s '' U) = U := by
  ext w
  simp only [mem_preimage, mem_image, ContMetric.affineMap_apply, q9Aff]
  constructor
  · rintro ⟨u, hu, huw⟩
    have : u = w := by
      have h2 := congrArg (fun p => s⁻¹ • (p - z)) huw
      simpa [smul_smul, inv_mul_cancel₀ hs.ne'] using h2
    rwa [← this]
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- **Weyl relations pass to site-normalized metrics** (same unit on both sides). -/
theorem isWeylInternal_q9SiteNorm {G G' : ContMetric d} {ζ : ℝ} {F : C(Rd d, ℝ)}
    (hW : ∀ U : Set (Rd d), IsOpen U → ∀ u v : Rd d, G'.internal U u v = weylScaleOn ζ F G U u v)
    {z : Rd d} {s S : ℝ} (hs : 0 < s) (hS : 0 < S) :
    IsWeylInternal ζ (F.comp (ContMetric.affineMap s z)) (q9SiteNorm G z s S) (q9SiteNorm G' z s S) := by
  intro U hU u v
  have h := weylScaleOn_affine (ξ := ζ) (f := F) hs.ne' z G (q9Aff z s '' U) u v
  rw [q9Aff_preimage_image hs] at h
  calc (q9SiteNorm G' z s S).internal U u v
      = ENNReal.ofReal S⁻¹ * G'.internal (q9Aff z s '' U) (q9Aff z s u) (q9Aff z s v) :=
        q9SiteNorm_internal hs hS U u v
    _ = ENNReal.ofReal S⁻¹ * weylScaleOn ζ F G (q9Aff z s '' U) (q9Aff z s u) (q9Aff z s v) := by
        rw [hW _ (q9Aff_image_open hs hU)]
    _ = ENNReal.ofReal S⁻¹ *
          weylScaleOn ζ (F.comp (ContMetric.affineMap s z)) (G.affine s hs.ne' z) U u v := by
        rw [h]
        rfl
    _ = weylScaleOn ζ (F.comp (ContMetric.affineMap s z))
          ((G.affine s hs.ne' z).smul S⁻¹ (inv_pos.2 hS)) U u v :=
        (weylScaleOn_smul _ _ _).symm
    _ = weylScaleOn ζ (F.comp (ContMetric.affineMap s z)) (q9SiteNorm G z s S) U u v := by
        rw [q9SiteNorm_eq hs hS]

/-- The trigger depends on the source metric only through its internal metric in `B`. -/
theorem q9_passesTrigger_congr {D D₂ : ContMetric d}
    (h : ∀ u v, D.internal (siteB d) u v = D₂.internal (siteB d) u v) (P : ℝ → Rd d) (a b bt : ℝ) :
    PassesTrigger D P a b bt ↔ PassesTrigger D₂ P a b bt := by
  unfold PassesTrigger
  rw [h]

/-- Membership of a site path in a set equals membership of the path in the affine image. -/
theorem q9SitePath_mem_iff {P : ℝ → Rd d} {z : Rd d} {s : ℝ} (hs : 0 < s) (t : ℝ) (A : Set (Rd d)) :
    q9SitePath P z s t ∈ A ↔ P t ∈ q9Aff z s '' A := by
  constructor
  · intro h
    exact ⟨_, h, q9Aff_sitePath hs t⟩
  · rintro ⟨w, hw, hwP⟩
    have : w = q9SitePath P z s t := by
      simp only [q9SitePath, q9Aff] at hwP ⊢
      rw [← hwP]
      simp [smul_smul, inv_mul_cancel₀ hs.ne']
    rwa [← this]

theorem q9Aff_image_ball {z : Rd d} {s : ℝ} (hs : 0 < s) (a : ℝ) :
    q9Aff z s '' ball (0 : Rd d) a = ball z (s * a) := by
  have h := p2_image_affine_ball hs z (0 : Rd d) a
  rw [smul_zero, zero_add] at h
  exact h

theorem q9Aff_image_closedBall {z : Rd d} {s : ℝ} (hs : 0 < s) (a : ℝ) :
    q9Aff z s '' closedBall (0 : Rd d) a = closedBall z (s * a) := by
  have h := p2_image_affine_closedBall hs z (0 : Rd d) a
  rw [smul_zero, zero_add] at h
  exact h

theorem q9Aff_image_ann {z : Rd d} {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    q9Aff z s '' ann (0 : Rd d) a b = ann z (s * a) (s * b) := by
  have h := p2_image_affine_ann hs z (0 : Rd d) a b
  rw [smul_zero, zero_add] at h
  exact h

theorem q9Aff_image_annCl {z : Rd d} {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    q9Aff z s '' annCl (0 : Rd d) a b = annCl z (s * a) (s * b) := by
  have h := p2_image_affine_annCl hs z (0 : Rd d) a b
  rw [smul_zero, zero_add] at h
  exact h

theorem q9Aff_image_siteB {z : Rd d} {s : ℝ} (hs : 0 < s) :
    q9Aff z s '' siteB d = ball z (4 * s) := by
  rw [siteB, q9Aff_image_ball hs, mul_comm]

theorem q9Aff_image_siteA {z : Rd d} {s : ℝ} (hs : 0 < s) :
    q9Aff z s '' siteA d = ann z (s / 2) (7 * s / 2) := by
  rw [siteA, annA, q9Aff_image_ann hs]
  congr 1 <;> ring

theorem q9Aff_image_siteC {z : Rd d} {s : ℝ} (hs : 0 < s) :
    q9Aff z s '' siteC d = annCl z (3 * s / 2) (5 * s / 2) := by
  rw [siteC, q9Aff_image_annCl hs]
  congr 1 <;> ring

theorem q9_sitePath_mem_siteC_iff {P : ℝ → Rd d} {z : Rd d} {s : ℝ} (hs : 0 < s) (t : ℝ) :
    q9SitePath P z s t ∈ siteC d ↔ P t ∈ annCl z (3 * s / 2) (5 * s / 2) := by
  rw [q9SitePath_mem_iff hs, q9Aff_image_siteC hs]

theorem q9_sitePath_mem_siteA_iff {P : ℝ → Rd d} {z : Rd d} {s : ℝ} (hs : 0 < s) (t : ℝ) :
    q9SitePath P z s t ∈ siteA d ↔ P t ∈ ann z (s / 2) (7 * s / 2) := by
  rw [q9SitePath_mem_iff hs, q9Aff_image_siteA hs]

/-- Internal metrics of site normalizations in `B` are determined by the physical internal metric in `B_{4s}(z)`. -/
theorem q9SiteNorm_internal_siteB_congr {G G₂ : ContMetric d} {z : Rd d} {s S : ℝ} (hs : 0 < s)
    (hS : 0 < S) (h : ∀ u v, G.internal (ball z (4 * s)) u v = G₂.internal (ball z (4 * s)) u v)
    (u v : Rd d) :
    (q9SiteNorm G z s S).internal (siteB d) u v = (q9SiteNorm G₂ z s S).internal (siteB d) u v := by
  rw [q9SiteNorm_internal hs hS, q9SiteNorm_internal hs hS, q9Aff_image_siteB hs, h]

end HigherDimLQGContinuity
