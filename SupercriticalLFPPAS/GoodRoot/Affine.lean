import SupercriticalLFPPAS.Separating.Lemma35Canonical
import SupercriticalLFPPAS.Core.Interfaces

/-!
# Affine covariance of good scales (§3.3)

Packet REP (`planning/packets/REP.md`), ingredient 2: the deterministic content of a good root scale,
`Core.GoodScale`, is covariant under the affine map `u ↦ z + r u`. If the physical metrics satisfy
`d₁(z + r u, z + r v) = a · d₂(u, v)` and `d₁'(z + r u, z + r v) = b · d₂'(u, v)` with `0 < a, b`,
then a good scale of `(d₂, d₂')` at `(0, 1)` with target bound `K` is a good scale of `(d₁, d₁')` at
`(z, r)` with target bound `K b / a` (`rep_goodScale_affine`). Paper §3.3, l. 386–394; SB2 §2.3 item 6
and D4 item 3 ("in physical units ... κ = κ_ε(r) (D-source) or κ_ε(r)⁻¹ (X̂-source)").

The transport is written for a general bijection `T` of the plane with `m(x, y) = k · M(T x, T y)`,
`k ∈ (0, ∞)` (curves, lengths, geodesics, internal metrics and internal set distances), following
`B2.Polylog.compactPathInf_comp_mul`; the separating-path clause also uses that `T` is a
homeomorphism (connected components) and Lipschitz (boundedness).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.GoodRoot

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Polylog (acrossIn annAt closedAnn)

/-! ### Transport under `m(x, y) = k · M(T x, T y)` -/

section Transport

variable {m M : LSCMetric} {k : ℝ≥0∞}

/-- **Geodesics transport.** -/
theorem rep_isGeodesicCurve_comp_mul_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤) {T : ℂ → ℂ}
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (P : ℝ → ℂ) (a b : ℝ) :
    LQGMetric.MetricGeometry.IsGeodesicCurve (m.pt ∘ P) a b ↔
      LQGMetric.MetricGeometry.IsGeodesicCurve (M.pt ∘ (T ∘ P)) a b := by
  have hc := B2.Polylog.isCurve_comp_mul_iff hk0 hkt hm P a b
  unfold LSCMetric.IsCurve at hc
  have hlen : LQGMetric.MetricGeometry.curveLength (m.pt ∘ P) a b =
      k * LQGMetric.MetricGeometry.curveLength (M.pt ∘ (T ∘ P)) a b :=
    B2.Polylog.len_comp_mul hm P a b
  have hed : edist ((m.pt ∘ P) a) ((m.pt ∘ P) b) =
      k * edist ((M.pt ∘ (T ∘ P)) a) ((M.pt ∘ (T ∘ P)) b) := hm (P a) (P b)
  unfold LQGMetric.MetricGeometry.IsGeodesicCurve
  rw [hlen, hed, ENNReal.mul_right_inj hk0 hkt]
  constructor
  · rintro ⟨hab, hcont, heq⟩
    exact ⟨hab, (hc.1 ⟨hab, hcont⟩).2, heq⟩
  · rintro ⟨hab, hcont, heq⟩
    exact ⟨hab, (hc.2 ⟨hab, hcont⟩).2, heq⟩

/-- **Internal metrics transport** (carriers matched by `T`). -/
theorem rep_internal_comp_mul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (T : ℂ ≃ ℂ)
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) {Y Y' : Set ℂ} (hY : ∀ x, x ∈ Y ↔ T x ∈ Y')
    (x y : Y) (x' y' : Y') (hx : T x = x') (hy : T y = y') :
    m.internal Y (x, y) = k * M.internal Y' (x', y') := by
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQY => le_iInf fun hQa => le_iInf fun hQb => ?_
    have hQ' : (T ∘ (T.symm ∘ Q)) = Q := funext fun t => T.apply_symm_apply (Q t)
    have hP : m.IsCurve (T.symm ∘ Q) a b :=
      (B2.Polylog.isCurve_comp_mul_iff hk0 hkt hm _ a b).2 (by rwa [hQ'])
    have hPY : ∀ t ∈ Icc a b, (T.symm ∘ Q) t ∈ Y := fun t ht => by
      rw [hY]
      simpa only [Function.comp_apply, T.apply_symm_apply] using hQY t ht
    have hPa : (T.symm ∘ Q) a = (x : ℂ) := by
      rw [Function.comp_apply, hQa, ← hx, Equiv.symm_apply_apply]
    have hPb : (T.symm ∘ Q) b = (y : ℂ) := by
      rw [Function.comp_apply, hQb, ← hy, Equiv.symm_apply_apply]
    have hlen : m.len (T.symm ∘ Q) a b = k * M.len Q a b := by
      rw [B2.Polylog.len_comp_mul hm, hQ']
    exact iInf_le_of_le (T.symm ∘ Q) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPY (iInf_le_of_le hPa (iInf_le_of_le hPb hlen.le))))))
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPY => le_iInf fun hPa => le_iInf fun hPb => ?_
    have hQa : (T ∘ P) a = (x' : ℂ) := by rw [Function.comp_apply, hPa, hx]
    have hQb : (T ∘ P) b = (y' : ℂ) := by rw [Function.comp_apply, hPb, hy]
    exact iInf_le_of_le (T ∘ P) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le
      ((B2.Polylog.isCurve_comp_mul_iff hk0 hkt hm P a b).1 hP) (iInf_le_of_le
      (fun t ht => (hY _).1 (hPY t ht)) (iInf_le_of_le hQa (iInf_le_of_le hQb
        (B2.Polylog.len_comp_mul hm P a b).ge))))))

/-- **Internal set distances transport** (carriers and endpoint sets matched by `T`). -/
theorem rep_internalSetDist_comp_mul (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (T : ℂ ≃ ℂ)
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) {Y Y' : Set ℂ} (hY : ∀ x, x ∈ Y ↔ T x ∈ Y')
    {B₁ B₂ B₁' B₂' : Set ℂ} (hB₁ : ∀ x, x ∈ B₁ ↔ T x ∈ B₁') (hB₂ : ∀ x, x ∈ B₂ ↔ T x ∈ B₂') :
    m.internalSetDist Y {p : Y | (p : ℂ) ∈ B₁} {p : Y | (p : ℂ) ∈ B₂} =
      k * M.internalSetDist Y' {p : Y' | (p : ℂ) ∈ B₁'} {p : Y' | (p : ℂ) ∈ B₂'} := by
  have hYs : ∀ q : Y', T.symm q ∈ Y := fun q => (hY _).2 (by rw [T.apply_symm_apply]; exact q.2)
  let e : Y → Y' := fun p => ⟨T p, (hY p).1 p.2⟩
  let e' : Y' → Y := fun q => ⟨T.symm q, hYs q⟩
  have he' : ∀ q : Y', T (e' q) = q := fun q => T.apply_symm_apply q
  unfold LSCMetric.internalSetDist
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun q₁ => le_iInf fun hq₁ => le_iInf fun q₂ => le_iInf fun hq₂ => ?_
    have h1 : e' q₁ ∈ {p : Y | (p : ℂ) ∈ B₁} := by
      change (T.symm q₁ : ℂ) ∈ B₁
      rw [hB₁, T.apply_symm_apply]
      exact hq₁
    have h2 : e' q₂ ∈ {p : Y | (p : ℂ) ∈ B₂} := by
      change (T.symm q₂ : ℂ) ∈ B₂
      rw [hB₂, T.apply_symm_apply]
      exact hq₂
    refine iInf₂_le_of_le (e' q₁) h1 (iInf₂_le_of_le (e' q₂) h2 ?_)
    rw [rep_internal_comp_mul hk0 hkt T hm hY (e' q₁) (e' q₂) q₁ q₂ (he' q₁) (he' q₂)]
  · refine le_iInf fun p₁ => le_iInf fun hp₁ => le_iInf fun p₂ => le_iInf fun hp₂ => ?_
    refine iInf₂_le_of_le (e p₁) ((hB₁ _).1 hp₁) (iInf₂_le_of_le (e p₂) ((hB₂ _).1 hp₂) ?_)
    rw [rep_internal_comp_mul hk0 hkt T hm hY p₁ p₂ (e p₁) (e p₂) rfl rfl]

end Transport

/-! ### The affine map `u ↦ r u + z` -/

section Affine

/-- `|T x − T y| = r |x − y|` for `T = p35AffHomeo hr z`. -/
theorem rep_dist_aff {r : ℝ} (hr : 0 < r) (z x y : ℂ) :
    dist (Separating.p35AffHomeo hr z x) (Separating.p35AffHomeo hr z y) = r * dist x y := by
  rw [Separating.p35AffHomeo_apply, Separating.p35AffHomeo_apply, dist_eq_norm, dist_eq_norm,
    add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem rep_aff_zero {r : ℝ} (hr : 0 < r) (z : ℂ) : Separating.p35AffHomeo hr z 0 = z := by
  rw [Separating.p35AffHomeo_apply, smul_zero, zero_add]

/-- `T x ∈ B_{rρ}(T y) ↔ x ∈ B_ρ(y)`. -/
theorem rep_mem_ball_aff {r : ℝ} (hr : 0 < r) (z y : ℂ) {ρ ρ' : ℝ} (hρ : ρ' = r * ρ) (x : ℂ) :
    x ∈ ball y ρ ↔ Separating.p35AffHomeo hr z x ∈ ball (Separating.p35AffHomeo hr z y) ρ' := by
  rw [mem_ball, mem_ball, rep_dist_aff hr, hρ]
  exact (mul_lt_mul_iff_right₀ hr).symm

/-- `T x ∈ Ā_{rs₁, rs₂}(z) ↔ x ∈ Ā_{s₁,s₂}(0)`. -/
theorem rep_mem_closedAnn_aff {r : ℝ} (hr : 0 < r) (z : ℂ) {s₁ s₂ s₁' s₂' : ℝ}
    (h₁ : s₁' = r * s₁) (h₂ : s₂' = r * s₂) (x : ℂ) :
    x ∈ closedAnn 0 s₁ s₂ ↔ Separating.p35AffHomeo hr z x ∈ closedAnn z s₁' s₂' := by
  have hn : ‖Separating.p35AffHomeo hr z x - z‖ = r * ‖x - 0‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, ← rep_dist_aff hr z x 0, rep_aff_zero]
  simp only [closedAnn, mem_ofPred_eq, hn, h₁, h₂]
  exact and_congr (mul_le_mul_iff_right₀ hr).symm (mul_le_mul_iff_right₀ hr).symm

/-- `T` is `r`-Lipschitz. -/
theorem rep_lipschitz_aff {r : ℝ} (hr : 0 < r) (z : ℂ) :
    LipschitzWith ⟨r, hr.le⟩ (Separating.p35AffHomeo hr z) :=
  LipschitzWith.of_dist_le_mul fun x y => (rep_dist_aff hr z x y).le

/-- The metric identity in the form `d₂(x, y) = a⁻¹ d₁(T x, T y)`. -/
theorem rep_hm_of_scale {d₁ d₂ : LSCMetric} {a : ℝ} (ha : 0 < a) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hd : ∀ u v : ℂ, d₁ (z + r • u, z + r • v) = ENNReal.ofReal a * d₂ (u, v)) :
    ∀ x y : ℂ, d₂ (x, y) =
      (ENNReal.ofReal a)⁻¹ * d₁ (Separating.p35AffHomeo hr z x, Separating.p35AffHomeo hr z y) := by
  intro x y
  rw [Separating.p35AffHomeo_apply, Separating.p35AffHomeo_apply, add_comm _ z, add_comm _ z, hd,
    ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top, one_mul]

/-- `ofReal (x (K b / a)) = ofReal (x K) · ofReal b · (ofReal a)⁻¹`. -/
theorem rep_ofReal_factor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x K : ℝ) :
    ENNReal.ofReal (x * (K * b / a)) =
      ENNReal.ofReal (x * K) * ENNReal.ofReal b * (ENNReal.ofReal a)⁻¹ := by
  rw [show x * (K * b / a) = x * K * (b / a) by ring, ENNReal.ofReal_mul' (div_pos hb ha).le,
    ENNReal.ofReal_div_of_pos ha, div_eq_mul_inv, mul_assoc]

/-- **Separating paths transport** (the clause `surround` of `Core.GoodScale`): if
`d₁(z + r·, z + r·) = a d₂` and `d₁'(z + r·, z + r·) = b d₂'`, the separating-path conclusion of
Lemma 3.5 for `(d₂, d₂')` at scale `1` around `K'` gives the one for `(d₁, d₁')` at scale `r`
around every `K` with `T⁻¹ K ⊆ K'`, with bound multiplied by `b / a`. -/
theorem rep_surroundProp_affine {d₁ d₁' d₂ d₂' : LSCMetric} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hd : ∀ u v : ℂ, d₁ (z + r • u, z + r • v) = ENNReal.ofReal a * d₂ (u, v))
    (hd' : ∀ u v : ℂ, d₁' (z + r • u, z + r • v) = ENNReal.ofReal b * d₂' (u, v))
    {Kp Kp' : Set ℂ} (hKp : ∀ p ∈ Kp, (Separating.p35AffHomeo hr z).symm p ∈ Kp') {η c : ℝ}
    (hS : Core.SurroundProp d₂ d₂' Kp' 1 η c) :
    Core.SurroundProp d₁ d₁' Kp r η (c * b / a) := by
  have hka0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkat : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 ha).ne'
  have hkb0 : (ENNReal.ofReal b)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkbt : (ENNReal.ofReal b)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hb).ne'
  have hm := rep_hm_of_scale ha z hr hd
  have hm' := rep_hm_of_scale hb z hr hd'
  have hdistT : ∀ x y, dist (Separating.p35AffHomeo hr z x) (Separating.p35AffHomeo hr z y) =
      r * dist x y := rep_dist_aff hr z
  set T := Separating.p35AffHomeo hr z
  have hdistS : ∀ x y, dist (T.symm x) (T.symm y) = r⁻¹ * dist x y := by
    intro x y
    have h := hdistT (T.symm x) (T.symm y)
    rw [T.apply_symm_apply, T.apply_symm_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  intro P α β hgeo hcont p hp hpP hα hβ
  set P' : ℝ → ℂ := T.symm ∘ P with hP'
  have hPP' : T ∘ P' = P := funext fun t => T.apply_symm_apply (P t)
  have hgeo' : LQGMetric.MetricGeometry.IsGeodesicCurve (d₂.pt ∘ P') α β := by
    rw [rep_isGeodesicCurve_comp_mul_iff hka0 hkat hm P' α β, hPP']
    exact hgeo
  have hcont' : ContinuousOn P' (Icc α β) := T.symm.continuous.comp_continuousOn hcont
  set p' := T.symm p with hp'
  have hpK' : p' ∈ Kp' := hKp p hp
  have hpP' : p' ∈ P' '' Icc α β := by
    obtain ⟨t, ht, rfl⟩ := hpP
    exact ⟨t, ht, rfl⟩
  have hsc : ∀ t, 2 * Real.sqrt η * r ≤ dist (P t) p → 2 * Real.sqrt η * 1 ≤ dist (P' t) p' := by
    intro t ht
    rw [hP', Function.comp_apply, hp', hdistS, mul_one]
    rw [le_inv_mul_iff₀ hr, mul_comm r]
    exact ht
  obtain ⟨σ', a', b', hσc, hσcont, hσball, hpσ, hcomp, hbdd, hlen⟩ :=
    hS P' α β hgeo' hcont' p' hpK' hpP' (hsc α hα) (hsc β hβ)
  have hTp : T p' = p := T.apply_symm_apply p
  have hcc := Homeomorph.image_connectedComponentIn T (s := (σ' '' Icc a' b')ᶜ) hpσ
  have hcomplC : ((T ∘ σ') '' Icc a' b')ᶜ = T '' (σ' '' Icc a' b')ᶜ := by
    rw [image_comp, Set.image_compl_eq T.bijective]
  refine ⟨T ∘ σ', a', b', ?_, T.continuous.comp_continuousOn hσcont, ?_, ?_, ?_, ?_, ?_⟩
  · exact (B2.Polylog.isCurve_comp_mul_iff hkb0 hkbt hm' σ' a' b').1 hσc
  · rintro _ ⟨t, ht, rfl⟩
    have h1 := hσball ⟨t, ht, rfl⟩
    rw [mem_ball] at h1 ⊢
    rw [Function.comp_apply, ← hTp, hdistT]
    calc r * dist (σ' t) p' < r * (2 * Real.sqrt η * 1) := (mul_lt_mul_iff_right₀ hr).2 h1
      _ = 2 * Real.sqrt η * r := by ring
  · rintro ⟨t, ht, hσt⟩
    apply hpσ
    refine ⟨t, ht, ?_⟩
    rw [hp', ← hσt, Function.comp_apply, Homeomorph.symm_apply_apply]
  · rw [hcomplC, ← hTp, ← hcc]
    intro x hx
    refine ⟨T.symm x, hcomp ?_, T.apply_symm_apply x⟩
    rw [mem_ball] at hx ⊢
    have hx' : dist x (T p') = r * dist (T.symm x) p' := by
      rw [← hdistT, T.apply_symm_apply x]
    rw [hx'] at hx
    rw [mul_one]
    exact (mul_lt_mul_iff_right₀ hr).1 (by linarith)
  · rw [hcomplC, ← hTp, ← hcc]
    exact (rep_lipschitz_aff hr z).isBounded_image hbdd
  · have hl1 : d₁'.len (T ∘ σ') a' b' = ENNReal.ofReal b * d₂'.len σ' a' b' := by
      rw [B2.Polylog.len_comp_mul hm' σ' a' b', ← mul_assoc,
        ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hb).ne' ENNReal.ofReal_ne_top, one_mul]
    have hl2 : d₂.len P' α β = (ENNReal.ofReal a)⁻¹ * d₁.len P α β := by
      rw [B2.Polylog.len_comp_mul hm P' α β, hPP']
    rw [hl1]
    calc ENNReal.ofReal b * d₂'.len σ' a' b' ≤
          ENNReal.ofReal b * (ENNReal.ofReal c * d₂.len P' α β) := by gcongr
      _ = ENNReal.ofReal (c * b / a) * d₁.len P α β := by
        rw [hl2, mul_div_assoc, ENNReal.ofReal_mul' (div_pos hb ha).le,
          ENNReal.ofReal_div_of_pos ha, div_eq_mul_inv]
        ring

/-- **Affine covariance of good scales.** If `d₁(z + r u, z + r v) = a d₂(u, v)` and
`d₁'(z + r u, z + r v) = b d₂'(u, v)` (`0 < a, b`), a good scale of `(d₂, d₂')` at `(0, 1)` with target
bound `K` is a good scale of `(d₁, d₁')` at `(z, r)` with target bound `K b / a` (same `η`, `d₀`, `A`). -/
theorem rep_goodScale_affine {d₁ d₁' d₂ d₂' : LSCMetric} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hd : ∀ u v : ℂ, d₁ (z + r • u, z + r • v) = ENNReal.ofReal a * d₂ (u, v))
    (hd' : ∀ u v : ℂ, d₁' (z + r • u, z + r • v) = ENNReal.ofReal b * d₂' (u, v))
    {η d₀ A K : ℝ} (hG : Core.GoodScale d₂ d₂' 0 1 one_pos η d₀ A K) :
    Core.GoodScale d₁ d₁' z r hr η d₀ A (K * b / a) := by
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have hb0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  have hka0 : (ENNReal.ofReal a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkat : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
  have hkb0 : (ENNReal.ofReal b)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
  have hkbt : (ENNReal.ofReal b)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hb0
  have hm := rep_hm_of_scale ha z hr hd
  have hm' := rep_hm_of_scale hb z hr hd'
  have hdistT : ∀ x y, dist (Separating.p35AffHomeo hr z x) (Separating.p35AffHomeo hr z y) =
      r * dist x y := rep_dist_aff hr z
  have hT0 : Separating.p35AffHomeo hr z 0 = z := rep_aff_zero hr z
  -- the unit-scale costs in terms of the physical ones
  have hacross : acrossIn d₂ 0 1 (2 * 1) = (ENNReal.ofReal a)⁻¹ * acrossIn d₁ z r (2 * r) := by
    rw [mul_one]
    exact Separating.p35_acrossIn_affine hka0 hkat z hr hm
  have haround : aroundDist d₂ (annAt 0 (7 * 1) (8 * 1) (by norm_num) (by norm_num)) =
      (ENNReal.ofReal a)⁻¹ * aroundDist d₁ (annAt z (7 * r) (8 * r) (by positivity) (by linarith)) := by
    rw [B2.Polylog.annAt_congr rfl (mul_one 7) (mul_one 8) _ _ (by norm_num) (by norm_num),
      Separating.p35_aroundDist_affine hka0 hkat z hr hm 7 8 (by norm_num) (by norm_num),
      B2.Polylog.annAt_congr rfl (mul_comm r 7) (mul_comm r 8) _ _ (by positivity) (by linarith)]
  set T := Separating.p35AffHomeo hr z
  refine ⟨?_, ?_, ?_⟩
  · -- (a) the ratio clause
    have h0 := hG.ratio
    rw [haround, hacross, mul_left_comm] at h0
    exact (ENNReal.mul_le_mul_iff_right hka0 hkat).1 h0
  · -- (b) the cross clause
    intro u v hu hv hle
    have hY₂ : ∀ x, x ∈ closedAnn 0 (1 / 2) (3 * 1) ↔ T x ∈ closedAnn z (r / 2) (3 * r) :=
      rep_mem_closedAnn_aff hr z (by ring) (by ring)
    have hY₃ : ∀ x, x ∈ closedAnn 0 (1 / 8) (16 * 1) ↔ T x ∈ closedAnn z (r / 8) (16 * r) :=
      rep_mem_closedAnn_aff hr z (by ring) (by ring)
    have hmemS : ∀ w : closedAnn z (r / 2) (3 * r), T.symm w ∈ closedAnn 0 (1 / 2) (3 * 1) :=
      fun w => (hY₂ _).2 (by rw [T.apply_symm_apply]; exact w.2)
    let u' : closedAnn 0 (1 / 2) (3 * 1) := ⟨T.symm u, hmemS u⟩
    let v' : closedAnn 0 (1 / 2) (3 * 1) := ⟨T.symm v, hmemS v⟩
    have hTu : T u' = u := T.apply_symm_apply u
    have hTv : T v' = v := T.apply_symm_apply v
    have hint : d₂.internal (closedAnn 0 (1 / 2) (3 * 1)) (u', v') =
        (ENNReal.ofReal a)⁻¹ * d₁.internal (closedAnn z (r / 2) (3 * r)) (u, v) :=
      rep_internal_comp_mul hka0 hkat T.toEquiv hm hY₂ u' v' u v hTu hTv
    have hdist' : ∀ w : closedAnn 0 (1 / 2) (3 * 1), ∀ ρ : ℝ, dist (T w) z = r * ρ →
        dist (w : ℂ) 0 = ρ := by
      intro w ρ hw
      rw [← hT0, hdistT] at hw
      exact mul_left_cancel₀ hr.ne' hw
    have hu' : dist (u' : ℂ) 0 = 1 := hdist' u' 1 (by rw [hTu, hu, mul_one])
    have hv' : dist (v' : ℂ) 0 = 2 * 1 := hdist' v' (2 * 1) (by rw [hTv, hv]; ring)
    have hle' : d₂.internal (closedAnn 0 (1 / 2) (3 * 1)) (u', v') ≤
        aroundDist d₂ (annAt 0 (7 * 1) (8 * 1) (by norm_num) (by norm_num)) := by
      rw [hint, haround]
      gcongr
    have hcross := hG.cross u' v' hu' hv' hle'
    have hB : ∀ (w : ℂ) (w' : ℂ), T w' = w → ∀ x, x ∈ ball w' (η * 1 / 2) ↔ T x ∈ ball w (η * r / 2) := by
      intro w w' hw x
      rw [← hw]
      exact rep_mem_ball_aff hr z w' (by ring) x
    have hsd := rep_internalSetDist_comp_mul hkb0 hkbt T.toEquiv hm' hY₃ (hB u u' hTu) (hB v v' hTv)
    have hsd' : d₁'.internalSetDist (closedAnn z (r / 8) (16 * r))
          {x | (x : ℂ) ∈ ball (u : ℂ) (η * r / 2)} {x | (x : ℂ) ∈ ball (v : ℂ) (η * r / 2)} =
        ENNReal.ofReal b * d₂'.internalSetDist (closedAnn 0 (1 / 8) (16 * 1))
          {x | (x : ℂ) ∈ ball (u' : ℂ) (η * 1 / 2)} {x | (x : ℂ) ∈ ball (v' : ℂ) (η * 1 / 2)} := by
      rw [hsd, ← mul_assoc, ENNReal.mul_inv_cancel hb0 ENNReal.ofReal_ne_top, one_mul]
    rw [hsd']
    calc ENNReal.ofReal b * d₂'.internalSetDist (closedAnn 0 (1 / 8) (16 * 1))
          {x | (x : ℂ) ∈ ball (u' : ℂ) (η * 1 / 2)} {x | (x : ℂ) ∈ ball (v' : ℂ) (η * 1 / 2)} ≤
        ENNReal.ofReal b * (ENNReal.ofReal ((1 + d₀ / 10) * K) *
          d₂.internal (closedAnn 0 (1 / 2) (3 * 1)) (u', v')) := by gcongr
      _ = ENNReal.ofReal ((1 + d₀ / 10) * (K * b / a)) *
          d₁.internal (closedAnn z (r / 2) (3 * r)) (u, v) := by
        rw [hint, rep_ofReal_factor ha hb]
        ring
  · -- (c) the separating paths
    have hS := rep_surroundProp_affine ha hb z hr hd hd'
      (Kp := sphere z r ∪ sphere z (2 * r)) (Kp' := sphere 0 1 ∪ sphere 0 (2 * 1)) ?_ hG.surround
    · rw [show d₀ / 10 * (K * b / a) = d₀ / 10 * K * b / a by ring]
      exact hS
    · intro p hp
      have hp' : dist (T (T.symm p)) (T 0) = r * dist (T.symm p) 0 := hdistT _ _
      rw [T.apply_symm_apply, hT0] at hp'
      rcases hp with hp | hp
      · left
        rw [mem_sphere] at hp ⊢
        rw [hp] at hp'
        exact (mul_left_cancel₀ hr.ne' (hp'.symm.trans (mul_one r).symm))
      · right
        rw [mem_sphere] at hp ⊢
        rw [hp] at hp'
        exact (mul_left_cancel₀ hr.ne' (hp'.symm.trans (by ring)))

end Affine

end SupercriticalLFPPAS.GoodRoot
