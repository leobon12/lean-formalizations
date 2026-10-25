import SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.AroundTranslate
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.B2.Strong.Dilate

 

























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)

 

 
def closedAnn (z : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {w | r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂}

lemma isCompact_closedAnn (z : ℂ) (r₁ r₂ : ℝ) : IsCompact (closedAnn z r₁ r₂) := by
  refine (isCompact_closedBall z r₂).of_isClosed_subset ?_ fun w hw => by
    rw [mem_closedBall, dist_eq_norm]; exact hw.2
  exact (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
    (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)

 

def acrossIn (D : LSCMetric) (z : ℂ) (r₁ r₂ : ℝ) : ℝ≥0∞ :=
  compactPathInf D (closedAnn z r₁ r₂) (sphere z r₁) (sphere z r₂)

theorem measurable_acrossIn (z : ℂ) (r₁ r₂ : ℝ) :
    Measurable fun D : LSCMetric => acrossIn D z r₁ r₂ :=
  Uniqueness.Toolkit.CompactPathInfimum.compactPathInf_measurable (isCompact_closedAnn z r₁ r₂)
    (isCompact_sphere z r₁) (isCompact_sphere z r₂)

 
def annAt (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) : EuclideanAnnulus :=
  ⟨(z, r₁, r₂), h₁, h₁₂⟩

@[simp] lemma annAt_center (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).center = z := rfl
@[simp] lemma annAt_innerRadius (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).innerRadius = r₁ := rfl
@[simp] lemma annAt_outerRadius (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).outerRadius = r₂ := rfl

 
theorem acrossDist_le_acrossIn (D : LSCMetric) (z : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h₁₂ : r₁ < r₂) : acrossDist D (annAt z r₁ r₂ h₁ h₁₂) ≤ acrossIn D z r₁ r₂ := by
  unfold acrossIn compactPathInf
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun hE => le_iInf fun hF => ?_
  have hab : a ∈ Icc a b := ⟨le_rfl, hP.1⟩
  have hbb : b ∈ Icc a b := ⟨hP.1, le_rfl⟩
  calc acrossDist D (annAt z r₁ r₂ h₁ h₁₂) ≤ D (P a, P b) :=
        iInf₂_le_of_le (P a) hE (iInf₂_le (P b) hF)
    _ = edist (D.pt (P a)) (D.pt (P b)) := rfl
    _ ≤ D.len P a b := eVariationOn.edist_le (D.pt ∘ P) hab hbb

 
theorem compactPathInf_eq_iInf_internal (D : LSCMetric) (S E F : Set ℂ) :
    compactPathInf D S E F = ⨅ (p : S × S) (_ : (p.1 : ℂ) ∈ E) (_ : (p.2 : ℂ) ∈ F),
      D.internal S p := by
  apply le_antisymm
  · refine le_iInf fun p => le_iInf fun hE => le_iInf fun hF => ?_
    unfold LSCMetric.internal
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun ha => le_iInf fun hb => ?_
    exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPS (iInf_le_of_le (ha ▸ hE) (iInf_le_of_le (hb ▸ hF) le_rfl))))))
  · unfold compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPS => le_iInf fun hE => le_iInf fun hF => ?_
    refine iInf_le_of_le (⟨P a, hPS a ⟨le_rfl, hP.1⟩⟩, ⟨P b, hPS b ⟨hP.1, le_rfl⟩⟩)
      (iInf_le_of_le hE (iInf_le_of_le hF ?_))
    unfold LSCMetric.internal
    exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPS (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl))))))

 

theorem acrossIn_eq_of_internal_eq {D E : LSCMetric} {Y : Set ℂ} {z : ℂ} {r₁ r₂ : ℝ}
    (hY : closedAnn z r₁ r₂ ⊆ Y) (h : D.internal Y = E.internal Y) :
    acrossIn D z r₁ r₂ = acrossIn E z r₁ r₂ := by
  unfold acrossIn
  rw [compactPathInf_eq_iInf_internal, compactPathInf_eq_iInf_internal,
    Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq D E hY h]

 
theorem acrossIn_eq_mul_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0)
    (hcTop : c ≠ ∞) (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (z : ℂ) (r₁ r₂ : ℝ) :
    acrossIn E z r₁ r₂ = c * acrossIn D z r₁ r₂ := by
  unfold acrossIn compactPathInf
  simp only [Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale D E c hc0 hcTop hscale,
    Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale]
  simp only [ENNReal.mul_iInf_of_ne hc0 hcTop]

 

lemma isCurve_comp_iff {m M : LSCMetric} {T : ℂ → ℂ} (hm : ∀ x y, m (x, y) = M (T x, T y))
    (P : ℝ → ℂ) (a b : ℝ) : m.IsCurve P a b ↔ M.IsCurve (T ∘ P) a b := by
  unfold LSCMetric.IsCurve
  have he : ∀ s t, edist (m.pt (P s)) (m.pt (P t)) = edist (M.pt (T (P s))) (M.pt (T (P t))) :=
    fun s t => hm (P s) (P t)
  simp only [EMetric.continuousOn_iff, Function.comp_apply, he]

lemma len_comp_eq {m M : LSCMetric} {T : ℂ → ℂ} (hm : ∀ x y, m (x, y) = M (T x, T y))
    (P : ℝ → ℂ) (a b : ℝ) : m.len P a b = M.len (T ∘ P) a b := by
  unfold LSCMetric.len
  have := LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist (F := m.pt ∘ P)
    (G := M.pt ∘ (T ∘ P)) (c := 1) (fun s t => by rw [one_mul]; exact hm (P s) (P t)) (Icc a b)
  rwa [one_mul] at this

 
theorem compactPathInf_comp_eq {m M : LSCMetric} {T S : ℂ → ℂ} (hTS : ∀ x, T (S x) = x)
    (hST : ∀ x, S (T x) = x) (hm : ∀ x y, m (x, y) = M (T x, T y)) (K E F : Set ℂ) :
    compactPathInf m K E F = compactPathInf M (T '' K) (T '' E) (T '' F) := by
  have hT_inj : Function.Injective T := fun x y h => by rw [← hST x, h, hST]
  have hmem : ∀ (A : Set ℂ) (x : ℂ), T x ∈ T '' A ↔ x ∈ A := fun A x => hT_inj.mem_set_image
  apply le_antisymm
  · unfold compactPathInf
    refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQK => le_iInf fun hE => le_iInf fun hF => ?_
    have hQ' : T ∘ (S ∘ Q) = Q := funext fun t => hTS (Q t)
    have hP : m.IsCurve (S ∘ Q) a b := (isCurve_comp_iff hm _ a b).2 (by rwa [hQ'])
    have hPK : ∀ t ∈ Icc a b, (S ∘ Q) t ∈ K := fun t ht => by
      rw [← hmem]; simpa only [Function.comp_apply, hTS] using hQK t ht
    have hPE : (S ∘ Q) a ∈ E := by rw [← hmem]; simpa only [Function.comp_apply, hTS] using hE
    have hPF : (S ∘ Q) b ∈ F := by rw [← hmem]; simpa only [Function.comp_apply, hTS] using hF
    have hlen : m.len (S ∘ Q) a b = M.len Q a b := by rw [len_comp_eq hm, hQ']
    exact iInf_le_of_le (S ∘ Q) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPK (iInf_le_of_le hPE (iInf_le_of_le hPF hlen.le))))))
  · unfold compactPathInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPK => le_iInf fun hE => le_iInf fun hF => ?_
    exact iInf_le_of_le (T ∘ P) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le
      ((isCurve_comp_iff hm P a b).1 hP) (iInf_le_of_le (fun t ht => (hmem K _).2 (hPK t ht))
      (iInf_le_of_le ((hmem E _).2 hE) (iInf_le_of_le ((hmem F _).2 hF)
        (len_comp_eq hm P a b).ge))))))

lemma image_add_closedAnn (z c : ℂ) (r₁ r₂ : ℝ) :
    (fun x => x + z) '' closedAnn c r₁ r₂ = closedAnn (c + z) r₁ r₂ := by
  ext w
  simp only [mem_image, closedAnn, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [add_sub_add_right_eq_sub]
  · intro hw
    exact ⟨w - z, by rwa [sub_sub, add_comm z c], sub_add_cancel w z⟩

lemma image_add_sphere (z c : ℂ) (ρ : ℝ) : (fun x => x + z) '' sphere c ρ = sphere (c + z) ρ := by
  ext w
  simp only [mem_image, mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [add_sub_add_right_eq_sub]
  · intro hw
    exact ⟨w - z, by rwa [sub_sub, add_comm z c], sub_add_cancel w z⟩

lemma image_smul_closedAnn {r : ℝ} (hr : 0 < r) (c : ℂ) (r₁ r₂ : ℝ) :
    (fun x => r • x) '' closedAnn c r₁ r₂ = closedAnn (r • c) (r * r₁) (r * r₂) := by
  have hnorm : ∀ x : ℂ, ‖r • x - r • c‖ = r * ‖x - c‖ := fun x => by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  ext w
  simp only [mem_image, closedAnn, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hnorm]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hr.le, mul_le_mul_of_nonneg_left hx.2 hr.le⟩
  · intro hw
    refine ⟨r⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    have hw' : ‖w - r • c‖ = r * ‖r⁻¹ • w - c‖ := by
      rw [← hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hw'] at hw
    exact ⟨le_of_mul_le_mul_left hw.1 hr, le_of_mul_le_mul_left hw.2 hr⟩

lemma image_smul_sphere {r : ℝ} (hr : 0 < r) (c : ℂ) (ρ : ℝ) :
    (fun x => r • x) '' sphere c ρ = sphere (r • c) (r * ρ) := by
  have hnorm : ∀ x : ℂ, ‖r • x - r • c‖ = r * ‖x - c‖ := fun x => by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  ext w
  simp only [mem_image, mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hnorm, hx]
  · intro hw
    refine ⟨r⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
    have hw' : ‖w - r • c‖ = r * ‖r⁻¹ • w - c‖ := by
      rw [← hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hw'] at hw
    exact mul_left_cancel₀ hr.ne' hw

 
theorem acrossIn_translate (D E : LSCMetric) (z : ℂ) (hDE : ∀ x y : ℂ, E (x, y) = D (x + z, y + z))
    (c : ℂ) (r₁ r₂ : ℝ) : acrossIn E c r₁ r₂ = acrossIn D (c + z) r₁ r₂ := by
  unfold acrossIn
  rw [compactPathInf_comp_eq (T := fun x => x + z) (S := fun x => x - z)
    (fun x => sub_add_cancel x z) (fun x => add_sub_cancel_right x z) hDE,
    image_add_closedAnn, image_add_sphere, image_add_sphere]

 
theorem acrossIn_dilate (D E : LSCMetric) {r : ℝ} (hr : 0 < r)
    (hDE : ∀ x y : ℂ, E (x, y) = D (r • x, r • y)) (c : ℂ) (r₁ r₂ : ℝ) :
    acrossIn E c r₁ r₂ = acrossIn D (r • c) (r * r₁) (r * r₂) := by
  unfold acrossIn
  rw [compactPathInf_comp_eq (T := fun x => r • x) (S := fun x => r⁻¹ • x)
    (fun x => by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul])
    (fun x => by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]) hDE,
    image_smul_closedAnn hr, image_smul_sphere hr, image_smul_sphere hr]

end SupercriticalLQGUniqueness.B2.Polylog
