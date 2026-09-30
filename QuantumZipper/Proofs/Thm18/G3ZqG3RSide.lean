import QuantumZipper.Proofs.Thm18.G3ZqG3Unif
import QuantumZipper.Proofs.Thm18.G3RTail3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the `R(x)` side of `B → C` (R-c), proved

Generalized copy (D92) of `g3TCutToProfRStmt_of_tail` (`G3RMain.lean`) and
`g3TCutToProfRStmt_holds` (`G3RTail3.lean`), with the plain zoom at `R(x)` replaced by an abstract
zoom `Z'`. The region-1 tail node `g3TRegion1TailStmt_holds`, the change of measure `rside_core`,
the shift `g3Ψ` and all zoom-free lemmas are reused. Besides measurability (`hZm'`) the original
uses one property of the plain zoom: region locality at `R(x)` (region zoom and full zoom agree on
the margin event off the area-failure events, `g3p_symmDiff_subset_area₂` with
`G3TCutAreaStmt`, `G3TProfAreaStmt`), here the explicit hypothesis `G3pRegLocRZ` for the profiles
of schemes `B` and `C`; `g3pRegLocRZ_zoomLaw_cut/prof` prove it for the plain zoom.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, pp. 71–72 and Remark 5.7. Own bookkeeping copied
from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- **Region locality at `R(x)` for a family of profiles `gf η`** (hypothesis). -/
def G3pRegLocRZ (Z' : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) (gf : ℝ → ℂ → ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
    i.1 = (δ, η, C) →
    (g3pPalmLaw γ (gf i.η) i).real
      ((g3pVZ Z' γ (gf i.η) i ⁻¹' t ∩ {p | |g3pR γ (gf i.η) i p - i.t₂| + m < i.r₂}) ∆
        (g3pVfZ Z' γ (gf i.η) i ⁻¹' t ∩ {p | |g3pR γ (gf i.η) i p - i.t₂| + m < i.r₂})) ≤ ε

set_option maxHeartbeats 800000 in
/-- **(R-c) `R(x)`-side of `B → C`, from the region-1 tail node.** -/
theorem g3TCutToProfRZ (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hLB : G3pRegLocRZ Z' γ (g3wCut γ)) (hLC : G3pRegLocRZ Z' γ (fun _ => g3wProf γ)) :
    G3TCutToProfRStmtZ Z Z' γ := by
  have hT := g3TRegion1TailStmt_holds
  intro μ ν _ _ hB t ht δ η m hm ε hε
  have hν0 : 0 ≤ ν.real t := measureReal_nonneg
  have hν1 : ν.real t ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
  · obtain ⟨hη, hηδ, hδ4⟩ := hcon
    set i₀ : G3Idx := ⟨(δ, η, 0), hη, hηδ, hδ4⟩ with hi₀
    set ZB : ℝ := (g3pZ γ (g3wCut γ η) i₀).toReal with hZBdef
    set ZC : ℝ := (g3pZ γ (g3wProf γ) i₀).toReal with hZCdef
    have hZC : 0 < ZC := ENNReal.toReal_pos (g3pZ_pos_lt_top hγ hγ2 i₀).1.ne'
      (g3pZ_pos_lt_top hγ hγ2 i₀).2.ne
    have hZB : 0 ≤ ZB := ENNReal.toReal_nonneg
    set E₀ : Set (Ω₀ × ℝ) := {p | |g3pR γ (g3wProf γ) i₀ p - i₀.t₂| + m < i₀.r₂} with hE₀def
    have hE₀ : MeasurableSet[sig₂ i₀] E₀ :=
      measurableSet_lt ((continuous_abs.measurable.comp
        ((measurable_g3pR γ (g3wProf γ) i₀).sub_const _)).add_const _) measurable_const
    have hTt := tendsto_g3T hγ hγ2 i₀ (ae_g3F_pos hT hγ hγ2 i₀) hE₀
    obtain ⟨K, hK⟩ := (hTt.eventually (gt_mem_nhds
      (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ZC * ε / 4)))).exists
    have hTK : (g3T γ i₀ E₀ K).toReal ≤ ZC * ε / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hK.le
    set c : ℝ := ZB * K * 4 / ZC with hcdef
    have hc0 : 0 ≤ c := by positivity
    set e : ℝ := ε / (4 * (c + 1)) with hedef
    have he0 : 0 < e := by positivity
    have he1 : e ≤ ε / 4 := div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
    have hce' : c * e ≤ ε / 4 := by
      rw [show c * e = ε / 4 * (c / (c + 1)) by rw [hedef]; field_simp]
      exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    have hce : ZB * ((K : ℝ) * (2 * (e + e))) ≤ ZC * ε / 4 := by
      have : ZB * ((K : ℝ) * (2 * (e + e))) = (c * e) * ZC := by
        rw [hcdef]; field_simp; ring
      rw [this]; nlinarith
    filter_upwards [hB.2 t ht δ η m hm e he0, hLB t ht δ η m hm e he0,
      hLC t ht δ η m hm e he0] with C h1 h2 h3 i hi G hG
    have h₁ : i.1.1 = i₀.1.1 := by rw [hi]
    have h₂ : i.1.2.1 = i₀.1.2.1 := by rw [hi]
    have hiη : i.η = η := by show i.1.2.1 = η; rw [hi]
    set PB := g3pPalmLaw γ (g3wCut γ i.η) i with hPB
    set PC := g3pPalmLaw γ (g3wProf γ) i with hPC
    set RB := g3pR γ (g3wCut γ i.η) i ⁻¹' reg2 i with hRB
    set EB : Set (Ω₀ × ℝ) := {p | |g3pR γ (g3wCut γ i.η) i p - i.t₂| + m < i.r₂} with hEB
    set EC : Set (Ω₀ × ℝ) := {p | |g3pR γ (g3wProf γ) i p - i.t₂| + m < i.r₂} with hEC
    have hZBi : (g3pZ γ (g3wCut γ i.η) i).toReal = ZB := by
      rw [hZBdef, hiη, g3pZ_congr (g := g3wCut γ η) h₁ h₂]
    have hZCi : (g3pZ γ (g3wProf γ) i).toReal = ZC := by
      rw [hZCdef, g3pZ_congr (g := g3wProf γ) h₁ h₂]
    have hTi : g3T γ i EC K = g3T γ i₀ E₀ K := g3T_congr h₁ h₂ m K
    have hECm : MeasurableSet[sig₂ i] EC :=
      measurableSet_lt ((continuous_abs.measurable.comp
        ((measurable_g3pR γ (g3wProf γ) i).sub_const _)).add_const _) measurable_const
    have hVC : MeasurableSet[sig₂ i] (g3pVZ Z' γ (g3wProf γ) i ⁻¹' t) :=
      measurable_g3pVZ hZm' γ (g3wProf γ) i (measurableSet_lawCyl ht)
    set AC := g3pVZ Z' γ (g3wProf γ) i ⁻¹' t ∩ EC with hAC
    have hACm : MeasurableSet[sig₂ i] AC := hVC.inter hECm
    have hsub : ∀ x : ℝ, |x - i.t₂| + m < i.r₂ → x ∈ reg2 i := fun x hx => by
      have := (abs_lt.1 (show |x - i.t₂| < i.r₂ by linarith))
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hECR : EC ⊆ g3pR γ (g3wProf γ) i ⁻¹' reg2 i := fun p hp => hsub _ hp
    have hgood : ∀ᵐ p ∂PB,
        g3pν₀ γ (g3wCut γ i.η) i p.1 (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0 ∧
        g3pν₀ γ (g3wProf γ) i p.1 (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0 ∧
        g3pν₂ γ (g3wProf γ) i p.1 (Icc 0 (i.t₂ - i.r₂)) = 0 :=
      ae_palm_of_ae γ _ i ((ae_gap2_null hγ hγ2).mono fun ω h => h i)
    have hVeq : ∀ p, g3pR γ (g3wCut γ i.η) i p ∈ reg2 i →
        g3pR γ (g3wProf γ) i (g3Ψ γ i p) = g3pR γ (g3wCut γ i.η) i p →
        g3pVZ Z' γ (g3wProf γ) i (g3Ψ γ i p) = g3pVZ Z' γ (g3wCut γ i.η) i p := fun p _ e => by
      unfold g3pVZ
      rw [e, restrictField_circIn_g3pField_congr γ (g₁ := g3wCut γ i.η) (g₂ := g3wProf γ)
        (by simpa using g3wCut_eqOn_ball γ i false) p.1]
      rfl
    have hEeq : (g3Ψ γ i ⁻¹' EC ∩ RB : Set (Ω₀ × ℝ)) =ᵐ[PB] EB := by
      refine Filter.eventuallyEqSet_iff.2 (hgood.mono fun p hp => ?_)
      obtain ⟨hA1, hA2⟩ := g3pR_Ψ (p := p) hp.1 hp.2.1 hp.2.2
      constructor
      · rintro ⟨hE, hr⟩
        show |g3pR γ (g3wCut γ i.η) i p - i.t₂| + m < i.r₂
        rw [← hA1 hr]; exact hE
      · intro hE
        have hr : p ∈ RB := hsub _ hE
        refine ⟨?_, hr⟩
        show |g3pR γ (g3wProf γ) i (g3Ψ γ i p) - i.t₂| + m < i.r₂
        rw [hA1 hr]; exact hE
    have hAeq : (g3Ψ γ i ⁻¹' AC ∩ RB : Set (Ω₀ × ℝ)) =ᵐ[PB]
        (g3pVZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB : Set (Ω₀ × ℝ)) := by
      refine Filter.eventuallyEqSet_iff.2 (hgood.mono fun p hp => ?_)
      obtain ⟨hA1, hA2⟩ := g3pR_Ψ (p := p) hp.1 hp.2.1 hp.2.2
      constructor
      · rintro ⟨⟨hV, hE⟩, hr⟩
        have e := hA1 hr
        refine ⟨?_, ?_⟩
        · show g3pVZ Z' γ (g3wCut γ i.η) i p ∈ t
          rw [← hVeq p hr e]; exact hV
        · show |g3pR γ (g3wCut γ i.η) i p - i.t₂| + m < i.r₂
          rw [← e]; exact hE
      · rintro ⟨hV, hE⟩
        have hr : p ∈ RB := hsub _ hE
        have e := hA1 hr
        refine ⟨⟨?_, ?_⟩, hr⟩
        · show g3pVZ Z' γ (g3wProf γ) i (g3Ψ γ i p) ∈ t
          rw [hVeq p hr e]; exact hV
        · show |g3pR γ (g3wProf γ) i (g3Ψ γ i p) - i.t₂| + m < i.r₂
          rw [e]; exact hE
    have hRBm : Measurable (g3pR γ (g3wCut γ i.η) i) :=
      (measurable_g3pR γ _ i).mono (sig_le_g3 i _ _) le_rfl
    have hEBm : MeasurableSet EB :=
      measurableSet_lt ((continuous_abs.measurable.comp (hRBm.sub_const _)).add_const _)
        measurable_const
    have hVBm : MeasurableSet (g3pVZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB) :=
      ((measurable_g3pVZ hZm' γ _ i).mono (sig_le_g3 i _ _) le_rfl (measurableSet_lawCyl ht)).inter hEBm
    have hVfBm : MeasurableSet (g3pVfZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB) :=
      (measurable_g3pVfZ hZm' γ _ i (measurableSet_lawCyl ht)).inter hEBm
    have H : ∀ G', MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G' →
        |PB.real (g3Ψ γ i ⁻¹' AC ∩ RB ∩ G') - ν.real t * PB.real (g3Ψ γ i ⁻¹' EC ∩ RB ∩ G')|
          ≤ e + e := by
      intro G' hG'
      have hG'0 : MeasurableSet G' := outsideSigmaPalm_le_g3 i _ hG'
      rw [measureReal_congr (hAeq.inter EventuallyEq.rfl),
        measureReal_congr (hEeq.inter EventuallyEq.rfl)]
      have hb : |PB.real (g3pVfZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB ∩ G') -
          ν.real t * PB.real (EB ∩ G')| ≤ e := h1 i hi G' hG'
      have hsd := abs_real_inter_sub_le_of_symmDiff (P := PB) hVBm hVfBm hG'0
      have hfail : PB.real ((g3pVZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB) ∆
          (g3pVfZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB)) ≤ e :=
        h2 i hi
      calc |PB.real (g3pVZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB ∩ G') - ν.real t * PB.real (EB ∩ G')|
          ≤ |PB.real (g3pVZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB ∩ G') -
              PB.real (g3pVfZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB ∩ G')| +
            |PB.real (g3pVfZ Z' γ (g3wCut γ i.η) i ⁻¹' t ∩ EB ∩ G') -
              ν.real t * PB.real (EB ∩ G')| := abs_sub_le _ _ _
        _ ≤ e + e := add_le_add (hsd.trans hfail) hb
    have hcore := rside_core hγ hγ2 i K hACm hECm inter_subset_right hECR hG hν0 hν1 H
    simp only [ENNReal.coe_natCast, NNReal.coe_natCast] at hcore
    rw [hZBi, hZCi, hTi, abs_mul, abs_of_pos hZC] at hcore
    have hX : |PC.real (AC ∩ G) - ν.real t * PC.real (EC ∩ G)| ≤ ε / 2 := by
      have : ZC * |PC.real (AC ∩ G) - ν.real t * PC.real (EC ∩ G)| ≤ ZC * (ε / 2) := by
        nlinarith
      exact le_of_mul_le_mul_left this hZC
    -- back to full zooms of `C`
    have hRCm : Measurable (g3pR γ (g3wProf γ) i) :=
      (measurable_g3pR γ _ i).mono (sig_le_g3 i _ _) le_rfl
    have hECm0 : MeasurableSet EC := sig_le_g3 i _ _ _ hECm
    have hG0 : MeasurableSet G := outsideSigmaPalm_le_g3 i _ hG
    have hsdC := abs_real_inter_sub_le_of_symmDiff (P := PC)
      ((measurable_g3pVfZ hZm' γ (g3wProf γ) i (measurableSet_lawCyl ht)).inter hECm0)
      (sig_le_g3 i _ _ _ hACm) hG0
    have hfailC : PC.real ((g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩ EC) ∆ AC) ≤ e := by
      rw [symmDiff_comm]
      exact h3 i hi
    calc |PC.real (g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩ EC ∩ G) - ν.real t * PC.real (EC ∩ G)|
        ≤ |PC.real (g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩ EC ∩ G) - PC.real (AC ∩ G)| +
          |PC.real (AC ∩ G) - ν.real t * PC.real (EC ∩ G)| := abs_sub_le _ _ _
      _ ≤ e + ε / 2 := add_le_add (hsdC.trans hfailC) hX
      _ ≤ ε := by linarith
  · filter_upwards with C
    intro i hi
    have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
      have := i.2
      rwa [hi] at this
    exact absurd h2 hcon

end R18
end QuantumZipper
