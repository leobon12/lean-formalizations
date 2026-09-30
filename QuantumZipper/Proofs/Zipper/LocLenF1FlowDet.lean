import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.F1LenInCanon
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.FlowRegSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6b: deterministic flow bookkeeping for the open-arc lengths

Open-arc copies (FOLLOW-PAPER-13 §1 substitution rule) of the deterministic lemmas of
`F1LenFlow.lean` (`F1.lenCocycle_det`), `F1LenInCanon.lean` (`F1.exists_eq_of_cont_unbdd`,
`F1.unzipLengths_canon_of_reg`) and `B3dLen.lean` (`B3d.unzipLengths_canon`).

Sheffield, arXiv:1012.4797, §1.4 ((1.8), canonical description) and §5.4, pp. 70–72
("unzipping by a fixed quantity of quantum boundary length"). Berestycki–Powell,
arXiv:2404.16642, Def 6.41 p. 229 (open-segment boundary measure).

Differences with the old versions: the lengths `unzipLengthsArc` are not automatically finite
(the local measure on an open arc may have infinite mass near the endpoints), so finiteness is
taken where it is used (`hfin`); the first passage time is identified from an exact hit
(`leftTimeArc_of_eq`, no finiteness needed); in the canonical rescaling only a local boundary
limit on the two open arcs (`ArcLimit`) is used. The deterministic signs `O⁻_t ≤ 0 ≤ O⁺_t` of the
side images are also proved here (`sideImages_fst_nonpos_of_cont`,
`sideImages_snd_nonneg_of_cont`, from `F1.exists_tendsto_fwdMap_left/right`). Own elementary
bookkeeping around the cited scaling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- `zipLenDownArc` is the canonicalization of the capacity unzipping at `lenTimeArc`. -/
theorem zipLenDownArc_eq_canonConfig (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) :
    zipLenDownArc γ ℓ c = canonConfig γ (zipCapDown γ (lenTimeArc γ ℓ c) c) := by
  simp only [zipLenDownArc, canonConfig, zipCapDown, canonical]
  refine Prod.ext rfl ?_
  funext s
  simp only
  rw [max_eq_left (mul_nonneg (sq_nonneg _) (le_max_right s 0))]

/-- If `L⁻` is strictly increasing on `[0,∞)` and `L⁻_t = ℓ`, the first passage time at `ℓ` is `t`. -/
theorem leftTimeArc_of_eq {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hmono : StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0)) {t ℓ : ℝ} (ht : 0 ≤ t)
    (e : (unzipLengthsArc γ c t).1 = ENNReal.ofReal ℓ) : leftTimeArc γ c ℓ = t := by
  unfold leftTimeArc lenTimeArc
  refine IsLeast.csInf_eq ⟨⟨ht, e.symm.le⟩, fun u hu => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have : (unzipLengthsArc γ c u).1 < (unzipLengthsArc γ c t).1 :=
    hmono (mem_Ici.2 hu.1) (mem_Ici.2 ht) hlt
  rw [e] at this
  exact absurd hu.2 (not_le.2 this)

/-- **Deterministic length cocycle, open arcs.** -/
theorem lenCocycleArc_det {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hmono : StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0))
    (hsurj : ∀ ℓ : ℝ, 0 < ℓ → ∃ t : ℝ, 0 ≤ t ∧ (unzipLengthsArc γ c t).1 = ENNReal.ofReal ℓ)
    (hcoc1 : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsArc γ c (u + s)).1 =
      (unzipLengthsArc γ c u).1 + (unzipLengthsArc γ (zipCapDown γ u c) s).1)
    (hcoc2 : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsArc γ c (u + s)).2 =
      (unzipLengthsArc γ c u).2 + (unzipLengthsArc γ (zipCapDown γ u c) s).2)
    (hcan : ∀ ℓ : ℝ, 0 < ℓ → 0 < scaleParam γ (zipCapDown γ (leftTimeArc γ c ℓ) c).1 ∧
      ∀ r : ℝ, 0 ≤ r → unzipLengthsArc γ (canonConfig γ (zipCapDown γ (leftTimeArc γ c ℓ) c)) r =
        unzipLengthsArc γ (zipCapDown γ (leftTimeArc γ c ℓ) c)
          (scaleParam γ (zipCapDown γ (leftTimeArc γ c ℓ) c).1 ^ 2 * r))
    (hfin : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).2 < ⊤)
    {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 ≤ s) :
    lenFArc γ c (ℓ + s) - lenFArc γ c ℓ = lenFArc γ (zipLenDownArc γ ℓ c) s := by
  obtain ⟨t₁, ht₁, e₁⟩ := hsurj ℓ hℓ
  obtain ⟨t₂, ht₂, e₂⟩ := hsurj (ℓ + s) (by linarith)
  have lt₁ : leftTimeArc γ c ℓ = t₁ := leftTimeArc_of_eq hmono ht₁ e₁
  have lt₂ : leftTimeArc γ c (ℓ + s) = t₂ := leftTimeArc_of_eq hmono ht₂ e₂
  have h12 : t₁ ≤ t₂ := by
    by_contra hlt
    push Not at hlt
    have := hmono (mem_Ici.2 ht₂) (mem_Ici.2 ht₁) hlt
    simp only [e₁, e₂] at this
    exact absurd this (not_lt.2 (ENNReal.ofReal_le_ofReal (by linarith)))
  set c₁ := zipCapDown γ t₁ c with hc₁
  set d := t₂ - t₁ with hd
  have hd0 : 0 ≤ d := sub_nonneg.2 h12
  have htd : t₁ + d = t₂ := by rw [hd]; ring
  have hfin₁ : (unzipLengthsArc γ c t₁).1 < ⊤ := by rw [e₁]; exact ENNReal.ofReal_lt_top
  have hmono₁ : StrictMonoOn (fun r => (unzipLengthsArc γ c₁ r).1) (Ici 0) := by
    intro x hx y hy hxy
    have := hmono (mem_Ici.2 (add_nonneg ht₁ hx)) (mem_Ici.2 (add_nonneg ht₁ hy))
      (by linarith : t₁ + x < t₁ + y)
    simp only [hcoc1 t₁ x ht₁ hx, hcoc1 t₁ y ht₁ hy] at this
    exact (ENNReal.add_lt_add_iff_left hfin₁.ne).1 this
  have hLd : (unzipLengthsArc γ c₁ d).1 = ENNReal.ofReal s := by
    have h := hcoc1 t₁ d ht₁ hd0
    rw [htd, e₂, e₁, ENNReal.ofReal_add hℓ.le hs] at h
    exact ((ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 h).symm
  have hR := hcoc2 t₁ d ht₁ hd0
  rw [htd] at hR
  have hf2 := hfin t₂ ht₂
  rw [hR] at hf2
  obtain ⟨hfa, hfb⟩ := ENNReal.add_lt_top.1 hf2
  have hlhs : lenFArc γ c (ℓ + s) - lenFArc γ c ℓ = (unzipLengthsArc γ c₁ d).2.toReal := by
    simp only [lenFArc, lt₁, lt₂]
    rw [hR, ENNReal.toReal_add hfa.ne hfb.ne]
    ring
  obtain ⟨ha, hcan'⟩ := hcan ℓ hℓ
  rw [lt₁] at ha hcan'
  obtain ⟨a, ha_def⟩ : ∃ a, a = scaleParam γ (zipCapDown γ t₁ c).1 := ⟨_, rfl⟩
  rw [← ha_def] at ha hcan'
  rw [← hc₁] at hcan'
  have ha2 : 0 < a ^ 2 := by positivity
  have hmono₂ : StrictMonoOn (fun r => (unzipLengthsArc γ (canonConfig γ c₁) r).1) (Ici 0) := by
    intro x hx y hy hxy
    show (unzipLengthsArc γ (canonConfig γ c₁) x).1 < (unzipLengthsArc γ (canonConfig γ c₁) y).1
    rw [hcan' x hx, hcan' y hy]
    exact hmono₁ (mem_Ici.2 (mul_nonneg ha2.le hx)) (mem_Ici.2 (mul_nonneg ha2.le hy))
      (mul_lt_mul_of_pos_left hxy ha2)
  have hdd : a ^ 2 * (d / a ^ 2) = d := by field_simp
  have hq0 : 0 ≤ d / a ^ 2 := div_nonneg hd0 ha2.le
  have hL₂ : (unzipLengthsArc γ (canonConfig γ c₁) (d / a ^ 2)).1 = ENNReal.ofReal s := by
    rw [hcan' _ hq0, hdd, hLd]
  have lt₃ : leftTimeArc γ (canonConfig γ c₁) s = d / a ^ 2 := leftTimeArc_of_eq hmono₂ hq0 hL₂
  have hz : zipLenDownArc γ ℓ c = canonConfig γ c₁ := by
    rw [zipLenDownArc_eq_canonConfig]
    show canonConfig γ (zipCapDown γ (leftTimeArc γ c ℓ) c) = _
    rw [lt₁]
  rw [hlhs, hz]
  show _ = ((unzipLengthsArc γ (canonConfig γ c₁) (leftTimeArc γ (canonConfig γ c₁) s)).2).toReal
  rw [lt₃, hcan' _ hq0, hdd]

/-- **Surjectivity by the intermediate value theorem** (open arcs; finiteness of `L⁻` explicit). -/
theorem exists_eq_of_cont_unbdd_arc {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hcont : ContinuousOn (fun t => (unzipLengthsArc γ c t).1.toReal) (Ici 0))
    (h0 : (unzipLengthsArc γ c 0).1 = 0)
    (hub : ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ ENNReal.ofReal M ≤ (unzipLengthsArc γ c t).1)
    (hfin : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 < ⊤)
    {ℓ : ℝ} (hℓ : 0 < ℓ) : ∃ t : ℝ, 0 ≤ t ∧ (unzipLengthsArc γ c t).1 = ENNReal.ofReal ℓ := by
  obtain ⟨T, hT, hTℓ⟩ := hub ℓ
  have hℓT : ℓ ≤ (unzipLengthsArc γ c T).1.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (hfin T hT).ne).1 hTℓ
  have hmem : ℓ ∈ Icc ((unzipLengthsArc γ c 0).1.toReal) ((unzipLengthsArc γ c T).1.toReal) := by
    rw [h0, ENNReal.toReal_zero]; exact ⟨hℓ.le, hℓT⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hT (hcont.mono Icc_subset_Ici_self) hmem
  refine ⟨t, ht.1, ?_⟩
  rw [← hft, ENNReal.ofReal_toReal (hfin t ht.1).ne]

/-- **Finiteness at all times from finiteness at the integer times**, for a quantity that is
additive along the flow (`f (u+s) = f u + g u s`). -/
theorem lt_top_of_nat_of_cocycle {f : ℝ → ℝ≥0∞} {g : ℝ → ℝ → ℝ≥0∞}
    (hcoc : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → f (u + s) = f u + g u s)
    (hn : ∀ n : ℕ, f n < ⊤) {t : ℝ} (ht : 0 ≤ t) : f t < ⊤ := by
  have hle : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have h := hcoc t ((⌈t⌉₊ : ℝ) - t) ht (sub_nonneg.2 hle)
  rw [add_sub_cancel] at h
  have := hn ⌈t⌉₊
  rw [h] at this
  exact (ENNReal.add_lt_top.1 this).1

/-! ## Canonical rescaling of the open-arc lengths -/

/-- **Local boundary limit on the two open arcs** of `η[0,t]` in the picture unzipped at time `t`:
the field is regular and has a local boundary limit on `(O⁻_t, 0) ∪ (0, O⁺_t)`. This is all
that the open-arc lengths read (B-P Def 6.41 p. 229); nothing is asked at `O^±_t` or at `0`. -/
def ArcLimit (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (t : ℝ) : Prop :=
  IsRegularSample (unzippedField γ c t) ∧ ∃ ν, HasBdryLimitOn γ (unzippedField γ c t)
    (Ioo (sideImages c.2 t).1 0 ∪ Ioo 0 (sideImages c.2 t).2) ν

/-- **Both open-arc lengths of the canonicalized configuration** (open-arc copy of
`B3d.unzipLengths_canon`): only a local boundary limit on the two arcs is used. -/
theorem unzipLengthsArc_canon {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ} (hγ : 0 < γ)
    (ha : 0 < scaleParam γ y) (hWmax : ∀ s, W (max s 0) = W s) {s : ℝ} (hs : 0 ≤ s)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ y ^ 2 * s) r).re)
      (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ y ^ 2 * s) r).re)
      (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hgood : ArcLimit γ (y, W) (scaleParam γ y ^ 2 * s))
    (hfield : RegEq (unzippedField γ (canonConfig γ (y, W)) s)
      (rescale (unzippedField γ (y, W) (scaleParam γ y ^ 2 * s)) (Qc γ) (scaleParam γ y))) :
    unzipLengthsArc γ (canonConfig γ (y, W)) s =
      unzipLengthsArc γ (y, W) (scaleParam γ y ^ 2 * s) := by
  set a := scaleParam γ y with ha_def
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm'⟩ := hR
  obtain ⟨hreg, ν, hν⟩ := hgood
  have e1 : (sideImages W (a ^ 2 * s)).1 = l := hl.limUnder_eq
  have e2 : (sideImages W (a ^ 2 * s)).2 = m := hm'.limUnder_eq
  simp only [e1, e2] at hν
  have havg := B3d.avgReg_eq_of_regEq hfield
  have hsub1 : Ioo (a * (l / a)) (a * 0) ⊆ Ioo l 0 ∪ Ioo 0 m := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact subset_union_left
  have hsub2 : Ioo (a * 0) (a * (m / a)) ⊆ Ioo l 0 ∪ Ioo 0 m := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact subset_union_right
  unfold unzipLengthsArc
  rw [B3d.canonConfig_snd_of_max hWmax, B3d.sideImages_fst_scale W ha hs hl,
    B3d.sideImages_snd_scale W ha hs hm', e1, e2]
  rw [arcLen_congr havg, arcLen_congr havg,
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν hsub1,
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν hsub2,
    arcLen_eq_of_hasBdryLimitOn hreg hν subset_union_left,
    arcLen_eq_of_hasBdryLimitOn hreg hν subset_union_right,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ ha.ne', mul_zero]

/-- **Signs of the side images** (deterministic): for a continuous driver with `W 0 = 0`,
`O⁻_t ≤ 0` (forward solutions started left of `W 0` stay left of the driver; `fwdMap = 0` for
swallowed points). -/
theorem sideImages_fst_nonpos_of_cont {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : (sideImages W t).1 ≤ 0 := by
  obtain ⟨l, hl⟩ := F1.exists_tendsto_fwdMap_left hW hW0 ht
  show limUnder (𝓝[<] (0 : ℝ)) (fun x : ℝ => (fwdMap W t x).re) ≤ 0
  rw [hl.limUnder_eq]
  refine le_of_tendsto hl ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  by_cases h : ∃ u, IsForwardSol W (x : ℂ) t u
  · obtain ⟨u, hu⟩ := h
    rw [F1.fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]
    have hn := RS.isForwardSol_neg hu
    rw [show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring] at hn
    have h := re_pos_isForwardSol_real hW.neg ht hn
      (by rw [Pi.neg_apply, hW0, neg_zero]; linarith [mem_Iio.1 hx]) t ⟨ht, le_rfl⟩
    simp only [Complex.neg_re] at h
    linarith
  · simp only [fwdMap, dif_neg h, Complex.zero_re, le_refl]

/-- **Signs of the side images** (deterministic): `0 ≤ O⁺_t`. -/
theorem sideImages_snd_nonneg_of_cont {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (sideImages W t).2 := by
  obtain ⟨l, hl⟩ := F1.exists_tendsto_fwdMap_right hW hW0 ht
  show 0 ≤ limUnder (𝓝[>] (0 : ℝ)) (fun x : ℝ => (fwdMap W t x).re)
  rw [hl.limUnder_eq]
  refine ge_of_tendsto hl ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  by_cases h : ∃ u, IsForwardSol W (x : ℂ) t u
  · obtain ⟨u, hu⟩ := h
    rw [F1.fwdMap_eq_of_isForwardSol hu ⟨ht, le_rfl⟩]
    exact (re_pos_isForwardSol_real hW ht hu (by rw [hW0]; exact hx) t ⟨ht, le_rfl⟩).le
  · simp only [fwdMap, dif_neg h, Complex.zero_re, le_refl]

/-- **Regularity package for the canonical rescaling at time `r`, open arcs** (copy of
`F1.CanonCore`, FlowRegReduce.lean, with `IsLQGGood` replaced by the local limit on the two open
arcs, `ArcLimit`; the side limits are deterministic and not included). Goodness off
`offSet c.2 _` would be too strong here: for `c = zipCapDown τ c₀` the root images of `c₀` lie
off `offSet c.2 _`, and nothing is known there. -/
def CanonRegArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (r : ℝ) : Prop :=
  0 < scaleParam γ c.1 ∧
  (∀ (d : ℂ) (r' : ℝ), 0 < r' → Thm18Asm.G1.ScaleConsistentAt c.1 (Qc γ) (scaleParam γ c.1)
      ((foldedCircle d r').map (fwdMapInv (canonConfig γ c).2 r))) ∧
  (∀ d ∈ Hbar, ∀ r' > 0,
      evalReg (unzippedField γ c (scaleParam γ c.1 ^ 2 * r)) (foldedCircle d r') =
        unzippedField γ c (scaleParam γ c.1 ^ 2 * r) (foldedCircle d r')) ∧
  ArcLimit γ c (scaleParam γ c.1 ^ 2 * r)

/-- **Canonical rescaling of the open-arc lengths** (deterministic; copy of
`F1.unzipLengths_canon_of_reg`). -/
theorem unzipLengthsArc_canon_of_reg {γ : ℝ} (hγ : 0 < γ) {c : FieldSample × (ℝ → ℝ)}
    (hW : Continuous c.2) (hW0 : c.2 0 = 0) (hWmax : ∀ s, c.2 (max s 0) = c.2 s) {r : ℝ}
    (hr : 0 ≤ r) (h : CanonRegArc γ c r) :
    unzipLengthsArc γ (canonConfig γ c) r =
      unzipLengthsArc γ c (scaleParam γ c.1 ^ 2 * r) := by
  obtain ⟨y, W⟩ := c
  obtain ⟨ha, hsc, hexact, hgood⟩ := h
  have has : 0 ≤ scaleParam γ y ^ 2 * r := mul_nonneg (sq_nonneg _) hr
  exact unzipLengthsArc_canon hγ ha hWmax hr (F1.exists_tendsto_fwdMap_left hW hW0 has)
    (F1.exists_tendsto_fwdMap_right hW hW0 has) hgood
    (WedgeUnzip.regEq_unzippedField_canonConfig hW hW0 hWmax ha hr hsc hexact)

end LocLen
end QuantumZipper
