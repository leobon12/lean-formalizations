import QuantumZipper.Proofs.Thm18.RTHmpFam
import QuantumZipper.Proofs.Zipper.SWCoreN2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-HMP (4): log growth of the circle averages of the free field

`RTHmp.hmp_family_ae`: a.s., eventually in `k`, `|X(fc(c, ρ)) − X(fc(0, 1))| ≤ a (k + 1)` on the
rational parameters `c = x + iy`, `|x| ≤ N`, `0 ≤ y ≤ N`, `ρ ∈ [2^{-k-1}, 2^{-k}]`
(`RTHmpFam.lean` + `RTHmpBC.lean`).

`RTHmp.freeCircLogGrowth_holds : FreeCircLogGrowthStmt`: with the continuous regular version
`G` of the free field (`WedgeTK.exists_isRegVersion`, which equals the raw values a.s. at every
fixed circle), the bound passes from the rational parameters to all of them by continuity and
density; radii in `[2^{-k₀}, N]` are handled by compactness. This is the logarithmic growth of the
circle-average process, Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab.
38 (2010), Prop. 2.1 and the proof of Lemma 3.1 (grid + union bound + modulus). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace R18
namespace RTHmp

open RegUnif SWCore

/-- The variance constant at box size `N`. -/
def hmpV (N : ℝ) : ℝ := 8 + 8 * |Real.log (6 * N + 3)|

theorem hmpV_nonneg (N : ℝ) : 0 ≤ hmpV N := by unfold hmpV; positivity

theorem hmpA_nonneg (d : ℕ) {V : ℝ} (hV : 0 ≤ V) : 0 ≤ hmpA d V := by
  have h := hmp_log4_nonneg d
  unfold hmpA
  have : 0 ≤ V / 2 + Real.log ((4 : ℝ) ^ d) + 1 := by linarith
  linarith

theorem norm_hmpC_sub_le (θ θ' : Fin 3 → ℝ) : ‖hmpC θ - hmpC θ'‖ ≤ 2 * ‖θ - θ'‖ := by
  have h : hmpC θ - hmpC θ' = hmpC (θ - θ') := Complex.ext (by simp [hmpC]) (by simp [hmpC])
  rw [h]
  refine (norm_hmpC_le _).trans ?_
  have h0 := norm_le_pi_norm (θ - θ') 0
  have h1 := norm_le_pi_norm (θ - θ') 1
  rw [Real.norm_eq_abs] at h0 h1
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **The family at all scales.** -/
theorem hmp_family_ae (hX : IsFreeGFFModConstH X P) {N : ℝ} (hN : 0 ≤ N) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ hmpD N k,
      |X ω (foldedCircle (hmpC θ) (θ 2)) - X ω (foldedCircle 0 1)| ≤
        hmpA 3 (hmpV N) * (k + 1) := by
  classical
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  have hadm0 : IsAdmissibleH μ₀ := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  set pairOf : (Fin 3 → ℝ) → WedgeTK.BPair := fun θ =>
    if h : 0 < θ 2 then
      ⟨(foldedCircle (hmpC θ) (θ 2), μ₀), D3Plus.isAdmissibleH_foldedCircle' _ h, hadm0,
        by rw [measure_univ, hμ₀, measure_univ]⟩
    else ⟨(μ₀, μ₀), hadm0, hadm0, rfl⟩ with hpairdef
  have hpair : ∀ θ, 0 < θ 2 → (pairOf θ).1 = (foldedCircle (hmpC θ) (θ 2), μ₀) := by
    intro θ h; simp only [hpairdef, dif_pos h]
  set Z : ℕ → (Fin 3 → ℝ) → Ω → ℝ := fun _ θ ω => X ω (pairOf θ).1.1 - X ω (pairOf θ).1.2
    with hZ
  have hG : ∀ k, IsGaussianProcess (Z k) P := fun _ => hX.gaussian.comp_right pairOf
  have hc : ∀ k θ, ∫ ω, Z k θ ω ∂P = 0 := fun _ θ =>
    hX.centered _ _ (pairOf θ).2.1 (pairOf θ).2.2.1 (pairOf θ).2.2.2
  have hZm : ∀ k θ, Measurable (Z k θ) := fun _ _ =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hpos : ∀ k, ∀ θ ∈ hmpD N k, 0 < θ 2 := fun k θ hθ =>
    lt_of_lt_of_le (radius_pos _) (hmpD_mem hθ).2.2.1
  have hDR : ∀ k, ∀ θ ∈ hmpD N k, ‖θ‖ ≤ N + 1 := by
    intro k θ hθ
    obtain ⟨h0, h1, h2⟩ := hmpD_mem hθ
    have hr1 := swcn2_radius_le_one k
    have hr0 := radius_pos (k + 1)
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_le]
    fin_cases i
    · exact ⟨by simp; linarith [h0.1], by simp; linarith [h0.2]⟩
    · exact ⟨by simp; linarith [h1.1], by simp; linarith [h1.2]⟩
    · exact ⟨by simp; linarith [h2.1], by simp; linarith [h2.2]⟩
  have hvar : ∀ k, ∀ θ ∈ hmpD N k, Var[Z k θ; P] ≤ hmpV N * (k + 1) := by
    intro k θ hθ
    obtain ⟨h0, h1, h2⟩ := hmpD_mem hθ
    have hρ := hpos k θ hθ
    have hρ1 : θ 2 ≤ 1 := h2.2.trans (swcn2_radius_le_one k)
    have hvZ : Var[Z k θ; P] = kernelCov2 neumannH (pairOf θ).1 (pairOf θ).1 :=
      swcn2_var_pair hX (pairOf θ).2.1 (pairOf θ).2.2.1 (pairOf θ).2.2.2
    rw [hvZ, hpair θ hρ]
    have hcN : ‖hmpC θ‖ ≤ 2 * N := by
      have := norm_hmpC_le θ
      have a0 : |θ 0| ≤ N := abs_le.2 ⟨h0.1, h0.2⟩
      have a1 : |θ 1| ≤ N := abs_le.2 ⟨by linarith [h1.1], h1.2⟩
      linarith
    set Rc : ℝ := 6 * N + 3 with hRc
    set B : ℝ := 2 * (|Real.log (θ 2)| + |Real.log Rc|) with hB
    have hkey := hmp_abs_kernelCov2_le (c := hmpC θ) (c' := 0) (Rb := 4 * N + 2) (B := B)
      (hmpC_mem_Hbar h1.1) (show (0 : ℂ) ∈ Hbar by simp [Hbar]) hρ one_pos
      (by linarith) (by simp; linarith) (fun x hx => by
        refine ⟨hmp_abs_hfc_le hρ (by linarith) (by linarith), ?_⟩
        have := hmp_abs_hfc_le (c := 0) (x := x) one_pos (R := Rc) (by linarith)
          (by simp; linarith)
        rw [Real.log_one, abs_zero, zero_add] at this
        have := abs_nonneg (Real.log (θ 2))
        linarith)
    have hl := abs_log_le_of_mem h2
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    refine (le_abs_self _).trans (hkey.trans ?_)
    simp only [hB, hmpV, ← hRc]
    have := abs_nonneg (Real.log Rc)
    nlinarith
  have hmod : ∀ k, ∀ θ ∈ hmpD N k, ∀ θ' ∈ hmpD N k, ‖θ - θ'‖ ≤ radius k ^ 2 →
      Var[fun ω => Z k θ ω - Z k θ' ω; P] ≤ 5 ^ 2 * (‖θ - θ'‖ / radius k) ^ (1 : ℝ) := by
    intro k θ hθ θ' hθ' _
    have hρ := hpos k θ hθ
    have hρ' := hpos k θ' hθ'
    have e : (fun ω => Z k θ ω - Z k θ' ω) = fun ω =>
        X ω (foldedCircle (hmpC θ) (θ 2)) - X ω (foldedCircle (hmpC θ') (θ' 2)) := by
      funext ω; simp only [hZ, hpair θ hρ, hpair θ' hρ']; ring
    rw [e, swcn2_var_pair hX (D3Plus.isAdmissibleH_foldedCircle' _ hρ)
      (D3Plus.isAdmissibleH_foldedCircle' _ hρ') (by rw [measure_univ, measure_univ])]
    have hk := E6.XAreaPC.abs_kernelCov2_fc_fc_le (hmpC_mem_Hbar (hmpD_mem hθ).2.1.1)
      (hmpC_mem_Hbar (hmpD_mem hθ').2.1.1) hρ hρ'
    refine (le_abs_self _).trans (hk.trans ?_)
    rw [Real.rpow_one]
    have hr := radius_pos k
    have hm : radius k / 2 ≤ min (θ 2) (θ' 2) := by
      rw [← radius_succ_eq]; exact le_min (hmpD_mem hθ).2.2.1 (hmpD_mem hθ').2.2.1
    have hnum : ‖hmpC θ - hmpC θ'‖ + |θ 2 - θ' 2| ≤ 3 * ‖θ - θ'‖ := by
      have h1 := norm_hmpC_sub_le θ θ'
      have h2 := norm_le_pi_norm (θ - θ') 2
      rw [Real.norm_eq_abs, Pi.sub_apply] at h2
      linarith
    have hδ : 0 ≤ ‖θ - θ'‖ := norm_nonneg _
    calc 4 * ((‖hmpC θ - hmpC θ'‖ + |θ 2 - θ' 2|) / min (θ 2) (θ' 2))
        ≤ 4 * (3 * ‖θ - θ'‖ / (radius k / 2)) := by
          gcongr
      _ = 24 * (‖θ - θ'‖ / radius k) := by field_simp; ring
      _ ≤ 5 ^ 2 * (‖θ - θ'‖ / radius k) := by
          have : 0 ≤ ‖θ - θ'‖ / radius k := div_nonneg hδ hr.le
          nlinarith
  have hmain := hmp_ae_eventually_le Z (D := hmpD N) (hmpD_countable N) (R := N + 1)
    (by linarith) hDR hG hc hZm (L := 5) (β := 1) one_pos le_rfl (by norm_num)
    (hmpV_nonneg N) hvar hmod
  filter_upwards [hmain] with ω hω
  filter_upwards [hω] with k hk θ hθ
  have h := hk θ hθ
  simp only [hZ, hpair θ (hpos k θ hθ)] at h
  exact h

theorem icc_subset_closure_rat {lo hi : ℝ} (h : lo < hi) :
    Icc lo hi ⊆ closure (Icc lo hi ∩ range ((↑) : ℚ → ℝ)) := by
  intro x hx
  have hx' : x ∈ closure (Ioo lo hi) := by rwa [closure_Ioo h.ne]
  have h1 : Ioo lo hi ⊆ closure (Ioo lo hi ∩ range ((↑) : ℚ → ℝ)) :=
    Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ)) isOpen_Ioo
  have h2 : closure (Ioo lo hi) ⊆ closure (Icc lo hi ∩ range ((↑) : ℚ → ℝ)) := by
    refine (closure_mono h1).trans ?_
    rw [closure_closure]
    exact closure_mono (inter_subset_inter_left _ Ioo_subset_Icc_self)
  exact h2 hx'

theorem hmpC_eq : hmpC = fun θ => ((θ 0 : ℝ) : ℂ) + ((θ 1 : ℝ) : ℂ) * Complex.I := by
  funext θ; apply Complex.ext <;> simp [hmpC]

/-- **Free-field log growth of the circle averages.** -/
theorem hmp_free_log_growth (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ Hbar, ‖c‖ ≤ R → ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      |evalReg (X ω) (foldedCircle c ρ)| ≤ C * (1 + |Real.log ρ|) := by
  classical
  obtain ⟨Gv, hGv⟩ := WedgeTK.exists_isRegVersion hX
  have hfam : ∀ N : ℕ, ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ θ ∈ hmpD ((N : ℝ) + 1) k,
      |X ω (foldedCircle (hmpC θ) (θ 2)) - X ω (foldedCircle 0 1)| ≤
        hmpA 3 (hmpV ((N : ℝ) + 1)) * (k + 1) := fun N => hmp_family_ae hX (by positivity)
  have hraw : ∀ N : ℕ, ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ θ ∈ hmpD ((N : ℝ) + 1) k,
      Gv ω (hmpC θ, θ 2) = X ω (foldedCircle (hmpC θ) (θ 2)) := fun N k =>
    (eventually_countable_ball (hmpD_countable _ k)).2 fun θ hθ =>
      hGv.raw _ (hmpC_mem_Hbar (hmpD_mem hθ).2.1.1) _
        (lt_of_lt_of_le (radius_pos _) (hmpD_mem hθ).2.2.1)
  have hraw0 := hGv.raw 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar]) 1 one_pos
  filter_upwards [ae_all_iff.2 hfam, ae_all_iff.2 fun N => ae_all_iff.2 (hraw N), hraw0,
    hGv.reg] with ω hB hr hr0 hreg
  intro R
  obtain ⟨N, hN⟩ := exists_nat_ge R
  set N1 : ℝ := (N : ℝ) + 1 with hN1
  have hN1p : 1 ≤ N1 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hB N)
  set K : Set (ℂ × ℝ) := (Hbar ∩ Metric.closedBall 0 N1) ×ˢ Icc (radius k₀) N1 with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall 0 N1).inter_left isClosed_Hbar).prod isCompact_Icc
  have hKsub : K ⊆ Hbar ×ˢ Ioi 0 := fun q hq =>
    ⟨hq.1.1, lt_of_lt_of_le (radius_pos k₀) hq.2.1⟩
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((hGv.cont ω).mono hKsub)
  set a := hmpA 3 (hmpV N1) with ha
  have ha0 : 0 ≤ a := hmpA_nonneg 3 (hmpV_nonneg N1)
  set g0 := Gv ω (0, 1) with hg0
  refine ⟨max M 0 + |g0| + 2 * a, by positivity, fun c hc hcR ρ hρ hρR => ?_⟩
  rw [hreg.evalReg_fc_of_mem hc hρ]
  have hl0 : 0 ≤ |Real.log ρ| := abs_nonneg _
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hg0n := abs_nonneg g0
  by_cases hρk : radius k₀ ≤ ρ
  · have hq : (c, ρ) ∈ K :=
      ⟨⟨hc, by rw [Metric.mem_closedBall, dist_zero_right]; linarith⟩, hρk, by linarith⟩
    have h1 := hM _ hq
    rw [Real.norm_eq_abs] at h1
    have h2 : |Gv ω (c, ρ)| ≤ max M 0 := h1.trans (le_max_left _ _)
    nlinarith
  push Not at hρk
  have hex : ∃ m : ℕ, radius (m + 1) < ρ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (2⁻¹ : ℝ) < 1)
    exact ⟨n, lt_of_le_of_lt (swcn2_radius_anti (Nat.le_succ n)) hn⟩
  set m := Nat.find hex with hmdef
  have hm : radius (m + 1) < ρ := Nat.find_spec hex
  have hρm : ρ ≤ radius m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0]
      have := swcn2_radius_le_one k₀
      have e : radius 0 = 1 := by simp [radius]
      rw [e]; linarith
    · obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have := Nat.find_min hex (show j < m by omega)
      push Not at this
      rw [hj]; exact this
  have hkm : k₀ ≤ m := by
    by_contra hlt
    push Not at hlt
    have := swcn2_radius_anti (show m + 1 ≤ k₀ by omega)
    linarith
  have hbox := hk₀ m hkm
  set S : Set (Fin 3 → ℝ) := Set.pi univ fun i => Icc (hmpLo N1 m i) (hmpHi N1 m i) with hS
  set f : (Fin 3 → ℝ) → ℝ := fun θ => Gv ω (hmpC θ, θ 2) - g0 with hf
  have hcont : Continuous fun θ : Fin 3 → ℝ => (hmpC θ, θ 2) := by
    rw [hmpC_eq]; fun_prop
  have hmaps : MapsTo (fun θ : Fin 3 → ℝ => (hmpC θ, θ 2)) S (Hbar ×ˢ Ioi 0) := by
    intro θ hθ
    have h1 := hθ 1 (mem_univ _)
    have h2 := hθ 2 (mem_univ _)
    simp only [hmpLo, hmpHi] at h1 h2
    exact ⟨hmpC_mem_Hbar h1.1, lt_of_lt_of_le (radius_pos _) h2.1⟩
  have hfc : ContinuousOn f S :=
    ((hGv.cont ω).comp hcont.continuousOn hmaps).sub continuousOn_const
  have hDS : hmpD N1 m ⊆ S := Set.pi_mono fun i _ => inter_subset_left
  have hlohi : ∀ i, hmpLo N1 m i < hmpHi N1 m i := by
    intro i
    fin_cases i
    · simp [hmpLo, hmpHi]; linarith
    · simp [hmpLo, hmpHi]; linarith
    · simp only [hmpLo, hmpHi]
      rw [radius_succ_eq]
      have := radius_pos m
      simp; linarith
  have hSD : S ⊆ closure (hmpD N1 m) := by
    rw [hmpD, closure_pi_set]
    exact Set.pi_mono fun i _ => icc_subset_closure_rat (hlohi i)
  have hbD : ∀ θ ∈ hmpD N1 m, |f θ| ≤ a * (m + 1) := fun θ hθ => by
    simp only [hf, hr N m θ hθ]
    rw [hr0]
    exact hbox θ hθ
  set θc : Fin 3 → ℝ := ![c.re, c.im, ρ] with hθc
  have hcre : |c.re| ≤ N1 := (Complex.abs_re_le_norm c).trans (by linarith)
  have hcim : c.im ≤ N1 := (le_abs_self _).trans ((Complex.abs_im_le_norm c).trans (by linarith))
  have hθcS : θc ∈ S := by
    intro i _
    fin_cases i
    · simp only [hθc, hmpLo, hmpHi]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, mem_Icc]
      exact ⟨by linarith [neg_abs_le c.re], by linarith [le_abs_self c.re]⟩
    · simp only [hθc, hmpLo, hmpHi]
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, mem_Icc]
      exact ⟨hc, hcim⟩
    · simp only [hθc, hmpLo, hmpHi]
      simp
      exact ⟨hm.le, hρm⟩
  have hbound := swcn2_le_of_dense hfc hDS hSD hbD θc hθcS
  have e : (hmpC θc, θc 2) = (c, ρ) := by
    refine Prod.ext ?_ ?_
    · apply Complex.ext <;> simp [hθc, hmpC]
    · simp [hθc]
  simp only [hf] at hbound
  rw [e] at hbound
  have hlogm : (m : ℝ) ≤ 2 * |Real.log ρ| := by
    have hr0' : 0 < radius m := radius_pos m
    have h1 : Real.log ρ ≤ Real.log (radius m) := Real.log_le_log hρ hρm
    have e2 : Real.log (radius m) = -(m * Real.log 2) := by
      simp [radius, Real.log_pow, Real.log_inv]
    have h2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hmn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h3 := neg_abs_le (Real.log ρ)
    nlinarith
  have hGb : |Gv ω (c, ρ)| ≤ |g0| + a * (m + 1) := by
    have := abs_sub_abs_le_abs_sub (Gv ω (c, ρ)) g0
    linarith
  nlinarith

end RTHmp
end R18
end QuantumZipper
