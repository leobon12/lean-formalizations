import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsDG20SkSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.RealAxiomV
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Bridge
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer
import SupercriticalLQGUniqueness.B2.PfeLocal.L1Prob

 





















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

private theorem normalized_ratio_cancel' (δ r a b m : ℝ)
    (hr : r ≠ 0) (hb : b ≠ 0) (hm : m ≠ 0) :
    (((δ * r) * a / m) / (r * b / m)) = δ * a / b := by
  field_simp

 



theorem rational_ratio_bounds_of_limits (hS : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hratio : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) :
    ∀ ζ : ℝ, 0 < ζ → ∃ C : ℝ, 0 < C ∧
      ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
        C⁻¹ * (δ : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤
          (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
            (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
            (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
            (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
            (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
          C * (δ : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
  intro ζ hζ
  obtain ⟨C, hCpos, hC⟩ := (hS ξ Q hQ m hm).2.1 ζ hζ
  refine ⟨C, hCpos, ?_⟩
  intro δ r hδ hδ1 hr
  have hδpos : 0 < (δ : ℝ) := Rat.cast_pos.mpr hδ
  have hrpos : 0 < (r : ℝ) := Rat.cast_pos.mpr hr
  have hdrpos : 0 < ((δ * r : ℚ) : ℝ) := Rat.cast_pos.mpr (mul_pos hδ hr)
  let dr : ℚ := δ * r
  have hev : ∀ᶠ n in atTop, (e n : ℝ) < (δ : ℝ) * (r : ℝ) :=
    he.eventually (Iio_mem_nhds (mul_pos hδpos hrpos))
  let A : ℕ → ℝ := fun n => (dr : ℝ) *
    (m ⟨(e n : ℝ) / (dr : ℝ),
      Set.mem_Ioi.mpr (div_pos (e n).property hdrpos)⟩ : ℝ) /
      (m (e n) : ℝ)
  let B : ℕ → ℝ := fun n => (r : ℝ) *
    (m ⟨(e n : ℝ) / (r : ℝ),
      Set.mem_Ioi.mpr (div_pos (e n).property hrpos)⟩ : ℝ) /
      (m (e n) : ℝ)
  have hA : Tendsto A atTop
      (𝓝 (c ⟨(dr : ℝ), Set.mem_Ioi.mpr hdrpos⟩ : ℝ)) := hratio dr (mul_pos hδ hr)
  have hB : Tendsto B atTop
      (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩ : ℝ)) := hratio r hr
  have hAB : Tendsto (fun n => A n / B n) atTop
      (𝓝 ((c ⟨(dr : ℝ), Set.mem_Ioi.mpr hdrpos⟩ : ℝ) /
        (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩ : ℝ))) :=
    hA.div hB (ne_of_gt (c ⟨(r : ℝ), Set.mem_Ioi.mpr hrpos⟩).property)
  have hbound : ∀ᶠ n in atTop,
      C⁻¹ * (δ : ℝ) ^ ((ξ : ℝ) * Q + ζ) ≤ A n / B n ∧
      A n / B n ≤ C * (δ : ℝ) ^ ((ξ : ℝ) * Q - ζ) := by
    filter_upwards [hev] with n hn
    let e' : Set.Ioo (0 : ℝ) (δ : ℝ) :=
      ⟨(e n : ℝ) / (r : ℝ), div_pos (e n).property hrpos,
        (div_lt_iff₀ hrpos).mpr hn⟩
    have hstep := hC ⟨(δ : ℝ), hδpos, hδ1⟩ e'
    have he' : (⟨(e' : ℝ) / (δ : ℝ),
        Set.mem_Ioi.mpr (div_pos e'.property.1 hδpos)⟩ : Set.Ioi (0 : ℝ)) =
        ⟨(e n : ℝ) / (dr : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property hdrpos)⟩ := by
      apply Subtype.ext
      change ((e n : ℝ) / (r : ℝ)) / (δ : ℝ) =
        (e n : ℝ) / ((δ * r : ℚ) : ℝ)
      rw [Rat.cast_mul]
      field_simp
    have hcancel : A n / B n = (δ : ℝ) *
        (m ⟨(e' : ℝ) / (δ : ℝ),
          Set.mem_Ioi.mpr (div_pos e'.property.1 hδpos)⟩ : ℝ) /
          (m ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩ : ℝ) := by
      simp only [A, B]
      have heA : (⟨(e n : ℝ) / (dr : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property hdrpos)⟩ : Set.Ioi (0 : ℝ)) =
          ⟨(e' : ℝ) / (δ : ℝ),
            Set.mem_Ioi.mpr (div_pos e'.property.1 hδpos)⟩ := he'.symm
      have heB : (⟨(e n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property hrpos)⟩ : Set.Ioi (0 : ℝ)) =
          ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩ := rfl
      rw [heA, heB]
      simpa only [dr, Rat.cast_mul] using normalized_ratio_cancel' _ _ _ _ _ (ne_of_gt hrpos)
        (ne_of_gt (m ⟨(e' : ℝ), Set.mem_Ioi.mpr e'.property.1⟩).property)
        (ne_of_gt (m (e n)).property)
    rw [hcancel]
    exact hstep
  exact ⟨ge_of_tendsto hAB (hbound.mono fun n hn => hn.1),
    le_of_tendsto hAB (hbound.mono fun n hn => hn.2)⟩

 


theorem rational_axiomV_of_limits (hS : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hratio : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop
        (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) :
    ∃ Λ : ℝ, 1 < Λ ∧
      ∀ (δ r : ℚ) (hδ : 0 < δ), (δ : ℝ) < 1 → ∀ (hr : 0 < r),
        Λ⁻¹ * (δ : ℝ) ^ Λ ≤
          (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
            (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
            (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
        (c ⟨((δ * r : ℚ) : ℝ), Set.mem_Ioi.mpr
            (Rat.cast_pos.mpr (mul_pos hδ hr))⟩ : ℝ) /
            (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
          Λ * (δ : ℝ) ^ (-Λ) := by
  obtain ⟨C, hCpos, hC⟩ := rational_ratio_bounds_of_limits hS ξ Q hQ m hm e he c hratio 1 one_pos
  let a : ℝ := (ξ : ℝ) * Q
  let Λ : ℝ := max C (|a| + 2) + 1
  have hCΛ : C ≤ Λ := by dsimp [Λ]; linarith [le_max_left C (|a| + 2)]
  have hAΛ : |a| + 2 ≤ Λ := by dsimp [Λ]; linarith [le_max_right C (|a| + 2)]
  have hΛ1 : 1 < Λ := by linarith [abs_nonneg a]
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ1
  have hInv : Λ⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hΛpos hCpos).2 hCΛ
  refine ⟨Λ, hΛ1, ?_⟩
  intro δ r hδ hδ1 hr
  have hδpos : 0 < (δ : ℝ) := Rat.cast_pos.mpr hδ
  have hδle : (δ : ℝ) ≤ 1 := hδ1.le
  have hE1 : a + 1 ≤ Λ := by linarith [le_abs_self a]
  have hE2 : -Λ ≤ a - 1 := by linarith [neg_abs_le a]
  have hpow1 : (δ : ℝ) ^ Λ ≤ (δ : ℝ) ^ (a + 1) :=
    Real.rpow_le_rpow_of_exponent_ge hδpos hδle hE1
  have hpow2 : (δ : ℝ) ^ (a - 1) ≤ (δ : ℝ) ^ (-Λ) :=
    Real.rpow_le_rpow_of_exponent_ge hδpos hδle hE2
  have hbase := hC δ r hδ hδ1 hr
  constructor
  · calc
      Λ⁻¹ * (δ : ℝ) ^ Λ ≤ C⁻¹ * (δ : ℝ) ^ (a + 1) :=
        mul_le_mul hInv hpow1 (Real.rpow_nonneg hδpos.le _)
          (inv_nonneg.mpr hCpos.le)
      _ ≤ _ := by simpa only [a] using hbase.1
  · calc
      _ ≤ C * (δ : ℝ) ^ (a - 1) := by simpa only [a] using hbase.2
      _ ≤ Λ * (δ : ℝ) ^ (-Λ) :=
        mul_le_mul hCΛ hpow2 (Real.rpow_nonneg hδpos.le _) hΛpos.le

 


theorem exists_pfeNormalizer_of_limits (hS : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (he : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0))
    (c₀ : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hc₀ : ∀ r : ℚ, ∀ hr : 0 < r,
      Tendsto (fun n => (r : ℝ) *
        (m ⟨(e n : ℝ) / (r : ℝ),
          Set.mem_Ioi.mpr (div_pos (e n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
        (m (e n) : ℝ)) atTop
        (𝓝 (c₀ ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) :
    ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ r : ℚ, ∀ hr : 0 < r,
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(e n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (e n).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
          (m (e n) : ℝ)) atTop
          (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
      ∃ Λ : ℝ, 1 < Λ ∧
        ∀ δ : Set.Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
          Λ⁻¹ * (δ : ℝ) ^ Λ ≤
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
              (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
          (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
              (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
              (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
            Λ * (δ : ℝ) ^ (-Λ) := by
  obtain ⟨Λ, hΛ, hV⟩ := rational_axiomV_of_limits hS ξ Q hQ m hm e he c₀ hc₀
  refine ⟨PfeAxioms.pfeNormalizer c₀ hΛ hV, ?_, Λ, hΛ,
    PfeAxioms.pfeNormalizer_ratio_bounds c₀ hΛ hV⟩
  intro r hr
  simpa only [PfeAxioms.pfeNormalizer_rat c₀ hΛ hV ⟨r, hr⟩] using hc₀ r hr

 
theorem exists_canonical_heat_versions :
    ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ), (∀ δ, Measurable (V δ)) ∧
      ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z := by
  choose V hVm hV using PfeWeyl.exists_canonical_heat_version
  exact ⟨V, hVm, hV⟩

 
theorem nonempty_of_isProbabilityMeasure' {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 := measure_univ (μ := P)
  rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
  exact zero_ne_one h1

 


theorem exists_dg20CouplingData (hSB : PfeAxioms.Inputs.DG20LimitSkSB) (hS4 : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧ ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ),
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC)
        (L : Ω' → LSCMetric),
        DG20CouplingData ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L := by
  obtain ⟨φ₁, hφ₁, c₀, hc₀, hCouple⟩ := hSB ξ Q hQ m hm ε hε
  have he : Tendsto (fun n => (ε (φ₁ n) : ℝ)) atTop (𝓝 0) := hε.comp hφ₁.tendsto_atTop
  obtain ⟨c, hc, hΛ⟩ :=
    exists_pfeNormalizer_of_limits hS4 ξ Q hQ m hm (fun n => ε (φ₁ n)) he c₀ hc₀
  obtain ⟨V, hVm, hV⟩ := exists_canonical_heat_versions
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have := hprob
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L, hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom⟩ :=
    hCouple normGFFLaw id hcan V (PfeLocal.l1_isHeatSmoothing_canonical V hV)
  let _ : MeasurableSpace Ω' := M'
  have : StandardBorelSpace Ω' := SB'
  have : IsProbabilityMeasure P' := hP'
  have hsrc : ∀ n, Measurable fun g : DistC =>
      (g, rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g)) := fun n =>
    measurable_id.prodMk (Measurable.of_eval fun p =>
      PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ) (m (ε (φ₁ n))) (hVm (ε (φ₁ n))) p)
  have hLaw' : ∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
      normGFFLaw.map (fun g : DistC =>
        (g, rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g))) := fun n => hLaw n
  have hJ : ∀ n, AEMeasurable (fun ω => (hN n ω, F n ω)) P' := fun n =>
    PfeAxioms.aemeasurable_of_map_eq_nondirac normGFFLaw P' _ _ (hsrc n).aemeasurable
      (fun x => PfeAxioms.gff_joint_law_ne_dirac normGFFLaw id hcan.1
        (fun g => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g))
        (Measurable.of_eval fun p => PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ)
          (m (ε (φ₁ n))) (hVm (ε (φ₁ n))) p).aemeasurable x)
      (hLaw' n)
  have hNa0 : ∀ n, AEMeasurable (hN n) P' := fun n => measurable_fst.comp_aemeasurable (hJ n)
  have hNa : ∀ n, ∃ g : Ω' → DistC, Measurable g ∧ hN n =ᵐ[P'] g := fun n =>
    ⟨(hNa0 n).mk _, (hNa0 n).measurable_mk, (hNa0 n).ae_eq_mk⟩
  choose hN' hN'm hN'eq using hNa
  have hid : ∀ n, ∀ᵐ ω ∂P',
      F n ω = rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω)) := fun n =>
    PfeWeyl.ae_eq_rescaledLFPP_of_joint_law (ξ : ℝ) (m (ε (φ₁ n))) (hVm _) P'
      (hN n) (F n) (hFc n) (hLaw' n)
  have hlawN : ∀ n, P'.map (hN' n) = normGFFLaw := by
    intro n
    rw [← Measure.map_congr (hN'eq n)]
    have h1 : P'.map (hN n) = (P'.map (fun ω => (hN n ω, F n ω))).map Prod.fst := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hJ n)]
      rfl
    rw [h1, hLaw' n, Measure.map_map measurable_fst (hsrc n)]
    exact Measure.map_id
  have hall : ∀ᵐ ω ∂P', ∀ n, hN n ω = hN' n ω := ae_all_iff.2 hN'eq
  have hidall : ∀ᵐ ω ∂P', ∀ n,
      F n ω = rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω)) := ae_all_iff.2 hid
  refine ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN', L, ?_⟩
  refine
    { exponent := hQ
      normalizer := hm
      scale_tendsto := he
      ratio := hc
      ratio_bound := hΛ
      heat_measurable := hVm
      heat_ae := hV
      limit_field := hh'
      field_measurable := hN'm
      field_law := hlawN
      field_tendsto := ?_
      limit_measurable := hLm
      metric_tendsto := ?_
      rational_tendsto := ?_
      geometry := hGeom }
  · filter_upwards [hField, hall] with ω hω heq
    have hfun : (fun n => hN' n ω) = fun n => hN n ω := funext fun n => (heq n).symm
    rw [hfun]
    exact hω
  · filter_upwards [hLsc, hidall, hall] with ω hl hidω heq
    rw [PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto]
    have hfun : (fun n => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN' n ω))) =
        fun n => F n ω := funext fun n => by rw [hidω n, heq n]
    rw [hfun]
    exact hl
  · filter_upwards [hRat, hidall, hall] with ω hr hidω heq u v hu hv
    have hfun : (fun n => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN' n ω)) (u, v)) =
        fun n => F n ω (u, v) := funext fun n => by rw [hidω n, heq n]
    rw [hfun]
    exact hr u v hu hv

end SupercriticalLQGUniqueness.B2.Final
