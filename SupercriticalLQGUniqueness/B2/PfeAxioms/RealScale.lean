import SupercriticalLQGUniqueness.B2.PfeAxioms.RationalAxiomV

 













set_option autoImplicit false
noncomputable section

open Set Filter Topology
open Classical
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
abbrev PosRat := {q : ℚ // 0 < q}

def ratNormalizerValue
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (q : PosRat) : ℝ :=
  (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ : ℝ)

theorem ratNormalizerValue_pos
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (q : PosRat) :
    0 < ratNormalizerValue c q := (c _).property

 
theorem ratNormalizerValue_ratio_bounds
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ}
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (q r : PosRat) (hqr : (q : ℝ) < (r : ℝ)) :
    Λ⁻¹ * ((q : ℝ) / (r : ℝ)) ^ Λ ≤
      ratNormalizerValue c q / ratNormalizerValue c r ∧
      ratNormalizerValue c q / ratNormalizerValue c r ≤
        Λ * ((q : ℝ) / (r : ℝ)) ^ (-Λ) := by
  let δ : ℚ := q.1 / r.1
  have hδ : 0 < δ := div_pos q.property r.property
  have hδ1 : (δ : ℝ) < 1 := by
    dsimp [δ]
    rw [Rat.cast_div]
    exact (div_lt_one (Rat.cast_pos.mpr r.property)).mpr hqr
  have h := hV δ r.1 hδ hδ1 r.property
  have hnum : ((δ * r.1 : ℚ) : ℝ) = (q : ℝ) := by
    dsimp [δ]
    rw [div_mul_cancel₀ q.1 r.property.ne']
  simpa only [ratNormalizerValue, hnum, δ, Rat.cast_div] using h

 
def rationalRightFilter (r : Set.Ioi (0 : ℝ)) : Filter PosRat :=
  Filter.comap (fun q : PosRat => (q : ℝ)) (𝓝[>] (r : ℝ))

instance rationalRightFilter_neBot (r : Set.Ioi (0 : ℝ)) :
    NeBot (rationalRightFilter r) := by
  unfold rationalRightFilter
  apply Filter.comap_neBot
  intro s hs
  obtain ⟨u, hru, hu⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset'
      (show (r : ℝ) < (r : ℝ) + 1 by linarith)).mp hs
  obtain ⟨q, hrq, hqu⟩ := exists_rat_btwn (show (r : ℝ) < u from hru)
  have hq : 0 < q := Rat.cast_pos.mp (r.property.trans hrq)
  exact ⟨⟨q, hq⟩, hu ⟨hrq, hqu⟩⟩

 

def rationalRightLiminf
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (r : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  liminf (fun q : PosRat =>
    ENNReal.ofReal
      (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ : ℝ))
    (rationalRightFilter r)

 


theorem rationalRightLiminf_mem_Ioo_of_eventually_bounds
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (r : Set.Ioi (0 : ℝ))
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : b < ∞)
    (h : ∀ᶠ (q : PosRat) in rationalRightFilter r,
      a ≤ ENNReal.ofReal
        (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ : ℝ) ∧
      ENNReal.ofReal
        (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ : ℝ) ≤ b) :
    0 < rationalRightLiminf c r ∧ rationalRightLiminf c r < ∞ := by
  have hlow : a ≤ rationalRightLiminf c r :=
    Filter.le_liminf_of_le (by isBoundedDefault) (h.mono fun _ hq => hq.1)
  have hhigh : rationalRightLiminf c r ≤ b :=
    liminf_le_of_frequently_le' (h.frequently.mono fun _ hq => hq.2)
  exact ⟨ha.trans_le hlow, hhigh.trans_lt hb⟩

 

theorem rationalRightLiminf_pos_finite_of_rational_ratio
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (t : Set.Ioi (0 : ℝ)) :
    0 < rationalRightLiminf c t ∧ rationalRightLiminf c t < ∞ := by
  obtain ⟨R, htR, hRmax⟩ :=
    exists_rat_btwn (show (t : ℝ) < (t : ℝ) + 1 by linarith)
  let Rpos : PosRat := ⟨R, Rat.cast_pos.mp (t.property.trans htR)⟩
  have hR : 0 < (Rpos : ℝ) := Rat.cast_pos.mpr Rpos.property
  have htR' : (t : ℝ) < (Rpos : ℝ) := htR
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  let d : ℝ := (t : ℝ) / (Rpos : ℝ)
  have hd : 0 < d := div_pos t.property hR
  let A : ℝ := ratNormalizerValue c Rpos * (Λ⁻¹ * d ^ Λ)
  let B : ℝ := ratNormalizerValue c Rpos * (Λ * d ^ (-Λ))
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos (ratNormalizerValue_pos c Rpos)
      (mul_pos (inv_pos.mpr hΛpos) (Real.rpow_pos_of_pos hd _))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact (mul_pos (ratNormalizerValue_pos c Rpos)
      (mul_pos hΛpos (Real.rpow_pos_of_pos hd _))).le
  have hev : ∀ᶠ (q : PosRat) in rationalRightFilter t,
      (t : ℝ) < (q : ℝ) ∧ (q : ℝ) < (Rpos : ℝ) := by
    exact Filter.preimage_mem_comap (Ioo_mem_nhdsGT htR')
  have hbounds : ∀ᶠ (q : PosRat) in rationalRightFilter t,
      ENNReal.ofReal A ≤ ENNReal.ofReal (ratNormalizerValue c q) ∧
      ENNReal.ofReal (ratNormalizerValue c q) ≤ ENNReal.ofReal B := by
    filter_upwards [hev] with q hq
    have hqR : (q : ℝ) / (Rpos : ℝ) < 1 :=
      (div_lt_one hR).mpr hq.2
    have hdq : d ≤ (q : ℝ) / (Rpos : ℝ) :=
      div_le_div_of_nonneg_right hq.1.le hR.le
    have hlowpow : d ^ Λ ≤ ((q : ℝ) / (Rpos : ℝ)) ^ Λ :=
      Real.rpow_le_rpow hd.le hdq hΛpos.le
    have huppow : ((q : ℝ) / (Rpos : ℝ)) ^ (-Λ) ≤ d ^ (-Λ) :=
      Real.rpow_le_rpow_of_nonpos hd hdq (by linarith)
    have hratio := ratNormalizerValue_ratio_bounds c hV q Rpos hq.2
    have hden := ratNormalizerValue_pos c Rpos
    have hlow : A ≤ ratNormalizerValue c q := by
      have htmp : Λ⁻¹ * d ^ Λ ≤
          ratNormalizerValue c q / ratNormalizerValue c Rpos :=
        (mul_le_mul_of_nonneg_left hlowpow (by positivity)).trans hratio.1
      have htmp' := (le_div_iff₀ hden).mp htmp
      dsimp [A]
      nlinarith only [htmp']
    have hupp : ratNormalizerValue c q ≤ B := by
      have htmp : ratNormalizerValue c q / ratNormalizerValue c Rpos ≤
          Λ * d ^ (-Λ) :=
        hratio.2.trans (mul_le_mul_of_nonneg_left huppow hΛpos.le)
      have htmp' := (div_le_iff₀ hden).mp htmp
      dsimp [B]
      nlinarith only [htmp']
    exact ⟨ENNReal.ofReal_le_ofReal hlow, ENNReal.ofReal_le_ofReal hupp⟩
  have hA' : 0 < ENNReal.ofReal A := ENNReal.ofReal_pos.mpr hA
  have hB' : ENNReal.ofReal B < ∞ := ENNReal.ofReal_lt_top
  exact rationalRightLiminf_mem_Ioo_of_eventually_bounds c t hA' hB'
    (by simpa only [ratNormalizerValue] using hbounds)

 


def pfeNormalizerRaw
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (r : Set.Ioi (0 : ℝ)) : ℝ≥0∞ :=
  if ∃ q : PosRat, (q : ℝ) = (r : ℝ) then
    ENNReal.ofReal (c r : ℝ)
  else rationalRightLiminf c r

 

theorem pfeNormalizerRaw_rat
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (q : PosRat) :
    pfeNormalizerRaw c
      ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ =
      ENNReal.ofReal
        (c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ : ℝ) := by
  have hq : ∃ q' : PosRat, (q' : ℝ) = (q : ℝ) := ⟨q, rfl⟩
  simp only [pfeNormalizerRaw, ite_eq_left hq]

 

theorem pfeNormalizerRaw_pos_finite_of_rational_ratio
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (r : Set.Ioi (0 : ℝ)) :
    0 < pfeNormalizerRaw c r ∧ pfeNormalizerRaw c r < ∞ := by
  unfold pfeNormalizerRaw
  split_ifs with hr
  · exact ⟨ENNReal.ofReal_pos.mpr (c r).property, ENNReal.ofReal_lt_top⟩
  · exact rationalRightLiminf_pos_finite_of_rational_ratio c hΛ hV r

 

def pfeNormalizer
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ)) :
    Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ) :=
  fun r => ⟨(pfeNormalizerRaw c r).toReal,
    ENNReal.toReal_pos (pfeNormalizerRaw_pos_finite_of_rational_ratio
      c hΛ hV r).1.ne' (pfeNormalizerRaw_pos_finite_of_rational_ratio
      c hΛ hV r).2.ne⟩

theorem pfeNormalizer_rat
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (q : PosRat) :
    pfeNormalizer c hΛ hV
      ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ =
      c ⟨(q : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr q.property)⟩ := by
  apply Subtype.ext
  simp only [pfeNormalizer, pfeNormalizerRaw_rat,
    ENNReal.toReal_ofReal (c _).property.le]

 


theorem rationalRightLiminf_ratio_bounds
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    {Λ : ℝ} (hΛ : 1 < Λ)
    (hV : ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
      (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
          (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
          (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
        Λ * (δ : ℝ) ^ (-Λ))
    (t : Set.Ioi (0 : ℝ)) (R : PosRat) (htR : (t : ℝ) < (R : ℝ)) :
    Λ⁻¹ * ((t : ℝ) / (R : ℝ)) ^ Λ ≤
      (rationalRightLiminf c t).toReal / ratNormalizerValue c R ∧
    (rationalRightLiminf c t).toReal / ratNormalizerValue c R ≤
      Λ * ((t : ℝ) / (R : ℝ)) ^ (-Λ) := by
  have hR : 0 < (R : ℝ) := Rat.cast_pos.mpr R.property
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  let d : ℝ := (t : ℝ) / (R : ℝ)
  have hd : 0 < d := div_pos t.property hR
  let A : ℝ := ratNormalizerValue c R * (Λ⁻¹ * d ^ Λ)
  let B : ℝ := ratNormalizerValue c R * (Λ * d ^ (-Λ))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact (mul_pos (ratNormalizerValue_pos c R)
      (mul_pos (inv_pos.mpr hΛpos) (Real.rpow_pos_of_pos hd _))).le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact (mul_pos (ratNormalizerValue_pos c R)
      (mul_pos hΛpos (Real.rpow_pos_of_pos hd _))).le
  have hev : ∀ᶠ (q : PosRat) in rationalRightFilter t,
      (t : ℝ) < (q : ℝ) ∧ (q : ℝ) < (R : ℝ) :=
    Filter.preimage_mem_comap (Ioo_mem_nhdsGT htR)
  have hbounds : ∀ᶠ (q : PosRat) in rationalRightFilter t,
      ENNReal.ofReal A ≤ ENNReal.ofReal (ratNormalizerValue c q) ∧
      ENNReal.ofReal (ratNormalizerValue c q) ≤ ENNReal.ofReal B := by
    filter_upwards [hev] with q hq
    have hdq : d ≤ (q : ℝ) / (R : ℝ) :=
      div_le_div_of_nonneg_right hq.1.le hR.le
    have hlowpow : d ^ Λ ≤ ((q : ℝ) / (R : ℝ)) ^ Λ :=
      Real.rpow_le_rpow hd.le hdq hΛpos.le
    have huppow : ((q : ℝ) / (R : ℝ)) ^ (-Λ) ≤ d ^ (-Λ) :=
      Real.rpow_le_rpow_of_nonpos hd hdq (by linarith)
    have hratio := ratNormalizerValue_ratio_bounds c hV q R hq.2
    have hden := ratNormalizerValue_pos c R
    have hlow : A ≤ ratNormalizerValue c q := by
      have htmp : Λ⁻¹ * d ^ Λ ≤
          ratNormalizerValue c q / ratNormalizerValue c R :=
        (mul_le_mul_of_nonneg_left hlowpow (by positivity)).trans hratio.1
      have htmp' := (le_div_iff₀ hden).mp htmp
      dsimp [A]
      nlinarith only [htmp']
    have hupp : ratNormalizerValue c q ≤ B := by
      have htmp : ratNormalizerValue c q / ratNormalizerValue c R ≤
          Λ * d ^ (-Λ) :=
        hratio.2.trans (mul_le_mul_of_nonneg_left huppow hΛpos.le)
      have htmp' := (div_le_iff₀ hden).mp htmp
      dsimp [B]
      nlinarith only [htmp']
    exact ⟨ENNReal.ofReal_le_ofReal hlow, ENNReal.ofReal_le_ofReal hupp⟩
  have hlow : ENNReal.ofReal A ≤ rationalRightLiminf c t :=
    Filter.le_liminf_of_le (by isBoundedDefault) (hbounds.mono fun _ h => h.1)
  have hupp : rationalRightLiminf c t ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (hbounds.frequently.mono fun _ h => h.2)
  have hlow' : A ≤ (rationalRightLiminf c t).toReal := by
    simpa only [ENNReal.toReal_ofReal hA] using
      (ENNReal.toReal_mono (rationalRightLiminf_pos_finite_of_rational_ratio
        c hΛ hV t).2.ne hlow)
  have hupp' : (rationalRightLiminf c t).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hupp)
  constructor
  · apply (le_div_iff₀ (ratNormalizerValue_pos c R)).mpr
    dsimp [A] at hlow'
    nlinarith only [hlow']
  · apply (div_le_iff₀ (ratNormalizerValue_pos c R)).mpr
    dsimp [B] at hupp'
    nlinarith only [hupp']

set_option pp.fullNames true

end SupercriticalLQGUniqueness.B2.PfeAxioms
