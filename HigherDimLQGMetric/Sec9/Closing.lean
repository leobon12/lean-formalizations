import HigherDimLQGMetric.Sec9.Interfaces
import HigherDimLQGMetric.Freq.Cor55
import HigherDimLQGMetric.Freq.ScaleCount
import HigherDimLQGMetric.Sec6.Prop62Full
import HigherDimLQGMetric.Sharp.E3
import HigherDimLQGMetric.Metric.WeylAxioms
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.LGF.Exists

/-!
# Closing the sharp weak comparison gap

Packet S8f: the parameter construction and the final frequency contradiction in §9.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem s8f_gap_package (hOpt : OptUpperShape) (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hlt : (optUpper Dt D)⁻¹ < optUpper D Dt) :
    ∃ c0 c1 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar : ℝ,
      0 < pstar ∧ pstar ≤ 1 ∧ 0 < ℓU ∧ 0 < β₀U ∧
      TrapFamily d ξ Q D Dt (optUpper Dt D)⁻¹ (optUpper D Dt) c1 aL A₀L ℓL β₀L pstar ∧
      ConfigLocal d ξ Q D Dt ∧
      (∀ m : ℕ, Cor63 d ξ Q D Dt (optUpper Dt D)⁻¹ c0 c1 aL A₀L ℓL β₀L pstar m) ∧
      Cor55 d ξ Q Dt D ((optUpper Dt D)⁻¹)⁻¹ aL A₀L ℓL β₀L pstar ∧
      Cor55 d ξ Q D Dt (optUpper D Dt) aU A₀U ℓU β₀U pstar ∧
      (optUpper Dt D)⁻¹ < c0 ∧ c0 < c1 := by
  obtain ⟨hUpos, hoptU⟩ := hOpt d hd hξ hQ hD hDt
  obtain ⟨hLpos, hoptL⟩ := hOpt d hd hξ hQ hDt hD
  set Cs := optUpper D Dt with hCs_def
  set cs := (optUpper Dt D)⁻¹ with hcs_def
  have hcs : 0 < cs := inv_pos.mpr hLpos
  have hinv : cs⁻¹ = optUpper Dt D := inv_inv _
  obtain ⟨aU, A₀U, ℓU, β₀U, pU, haU, haA₀U, hℓU, -, hβ₀U, -, hpU, hUall⟩ :=
    section5Package_cor55 hd hξ hQ hD hDt (e5_sharp_moment hd hξ hQ hD) Cs hUpos hoptU
  obtain ⟨aL, A₀L, ℓL, β₀L, pL, haL, haA₀L, hℓL, -, hβ₀L, -, hpL, hLall⟩ :=
    section5Package_cor55 hd hξ hQ hDt hD (e5_sharp_moment hd hξ hQ hDt) (optUpper Dt D) hLpos hoptL
  set pstar := min (min pU pL) 1 with hpstar_def
  have hpstar : 0 < pstar := lt_min (lt_min hpU hpL) one_pos
  have hpstar1 : pstar ≤ 1 := min_le_right _ _
  have hpU' : pstar ∈ Set.Ioc 0 pU := ⟨hpstar, (min_le_left _ _).trans (min_le_left _ _)⟩
  have hpL' : pstar ∈ Set.Ioc 0 pL := ⟨hpstar, (min_le_left _ _).trans (min_le_right _ _)⟩
  obtain ⟨-, hCor55U⟩ := hUall pstar hpU'
  obtain ⟨hfreqL, hCor55L⟩ := hLall pstar hpL'
  -- the comparison constants (IsOptUpper, first clauses)
  have hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v) := by
    intro Ω _ P _ h hh
    filter_upwards [hoptU.1 P h hh, hoptL.1 P h hh] with ω hU hL u v
    refine ⟨?_, hU u v⟩
    have h1 := hL u v
    rw [← hinv] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hcs.le
    rwa [← mul_assoc, mul_inv_cancel₀ hcs.ne', one_mul] at h2
  -- c₁ < c₂ between c_* and C_*, then c₀ ∈ (c_*, c₁) with (10)
  set c1 := cs + (Cs - cs) / 3 with hc1_def
  set c2 := cs + 2 * (Cs - cs) / 3 with hc2_def
  have hcs1 : cs < c1 := by rw [hc1_def]; linarith
  have hc12 : c1 < c2 := by rw [hc1_def, hc2_def]; linarith
  have hc2Cs : c2 < Cs := by rw [hc2_def]; linarith
  set θ := aL / A₀L with hθ_def
  have hθ0 : 0 < θ := div_pos haL (haL.trans haA₀L)
  have hc1pos : 0 < c1 := hcs.trans hcs1
  have hgap : 0 < cs⁻¹ - c1⁻¹ := sub_pos.mpr ((inv_lt_inv₀ hc1pos hcs).mpr hcs1)
  set m := cs⁻¹ - θ * (cs⁻¹ - c1⁻¹) with hm_def
  have hm_lt : m < cs⁻¹ := by rw [hm_def]; nlinarith
  have hm_gt : c1⁻¹ < m := by
    have hθ1 : θ < 1 := (div_lt_one (haL.trans haA₀L)).mpr haA₀L
    rw [hm_def]; nlinarith
  have hmpos : 0 < m := (inv_pos.mpr hc1pos).trans hm_gt
  set c0 := (cs + m⁻¹) / 2 with hc0_def
  have hmcs : cs < m⁻¹ := by
    rw [← inv_inv cs]; exact (inv_lt_inv₀ (inv_pos.mpr hcs) hmpos).mpr hm_lt
  have hmc1 : m⁻¹ < c1 := by
    rw [← inv_inv c1]; exact (inv_lt_inv₀ hmpos (inv_pos.mpr hc1pos)).mpr hm_gt
  have hcs0 : cs < c0 := by rw [hc0_def]; linarith
  have hc01 : c0 < c1 := by rw [hc0_def]; linarith
  have hc0m : c0 < m⁻¹ := by rw [hc0_def]; linarith
  have h10 : cs⁻¹ - aL / A₀L * (cs⁻¹ - c1⁻¹) < c0⁻¹ := by
    have := (inv_lt_inv₀ (inv_pos.mpr hmpos) (hcs.trans hcs0)).mpr hc0m
    rwa [inv_inv] at this
  have hfreqL' : FrequencyLemma d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar := by rw [hinv]; exact hfreqL
  obtain ⟨hTrap, hLoc, hCor⟩ := sec6Package_of_sharp hd hξ hQ hD hDt hcs hcs1 hc12 hc2Cs hcomp
    hℓL hβ₀L hpstar hpstar1 hfreqL' h10
  have hCor55L' : Cor55 d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar := by rw [hinv]; exact hCor55L
  exact ⟨c0, c1, aL, A₀L, ℓL, β₀L, aU, A₀U, ℓU, β₀U, pstar, hpstar, hpstar1, hℓU, hβ₀U,
    hTrap, hLoc, hCor, hCor55L', hCor55U, hcs0, hc01⟩


private theorem s8f_quarter_intersection {W L U : Set ℤ} (hW : W.Finite)
    (hWpos : 0 < W.ncard) (hLsub : L ⊆ W) (hUsub : U ⊆ W)
    (hL : (3 / 4 : ℝ) * W.ncard ≤ (L.ncard : ℝ))
    (hU : (3 / 4 : ℝ) * W.ncard ≤ (U.ncard : ℝ)) : (L ∩ U).Nonempty := by
  by_contra h
  have hEmpty : L ∩ U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hcard := Set.ncard_inter_add_ncard_union L U (hW.subset hLsub) (hW.subset hUsub)
  rw [hEmpty, Set.ncard_empty, zero_add] at hcard
  have hcardR : ((L ∪ U).ncard : ℝ) = L.ncard + U.ncard := by
    exact_mod_cast hcard
  have hUnion : ((L ∪ U).ncard : ℝ) ≤ W.ncard := by
    exact_mod_cast Set.ncard_le_ncard (Set.union_subset hLsub hUsub) hW
  have hWposR : (0 : ℝ) < W.ncard := by exact_mod_cast hWpos
  linarith only [hL, hU, hcardR, hUnion, hWposR]

private theorem s8f_scaleWin_nonempty {ε R : ℝ} (hε : 0 < ε)
    (hεsmall : ε < (1 / 64 : ℝ)) (hR : 0 < R) :
    0 < (scaleWin ε R).ncard := by
  have hlog : 1 < Real.logb 64 ε⁻¹ := by
    have hεi : 64 < ε⁻¹ := by
      have hi : 0 < ε⁻¹ := inv_pos.mpr hε
      have hmul : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
      nlinarith [mul_pos (sub_pos.mpr hεsmall) hi]
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 64)] using
      (Real.logb_lt_logb (by norm_num : (1 : ℝ) < 64)
        (by norm_num : (0 : ℝ) < 64) hεi)
  have hc := s4c_scaleWin_count hε hεsmall hR
  have hp : (0 : ℝ) < (scaleWin ε R).ncard := by linarith only [hc, hlog]
  exact_mod_cast hp

private theorem s8f_window_contradiction {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    {cs Cs c0 aL A₀L ℓL β₀L aU A₀U ℓU β₀U pstar : ℝ}
    (hcs : 0 < cs) (hcs0 : cs < c0)
    (hCorL : Cor55 d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar)
    (hCorU : Cor55 d ξ Q D Dt Cs aU A₀U ℓU β₀U pstar)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {t : ℝ} (ht0 : 0 < t) (htCs : t < Cs)
    (ht : ∀ R : ℝ, 0 < R →
      ENNReal.ofReal pstar ≤ P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0) →
      P (h ⁻¹' WitEvent D Dt ξ Q Cs aU A₀U ℓU β₀U t R 0) < ENNReal.ofReal pstar) :
    False := by
  have hc0pos : 0 < c0 := hcs.trans hcs0
  have htc0 : 0 < c0⁻¹ ∧ c0⁻¹ < cs⁻¹ :=
    ⟨inv_pos.mpr hc0pos, (inv_lt_inv₀ hc0pos hcs).mpr hcs0⟩
  obtain ⟨R₀L, hR₀L, hLall⟩ := hCorL {c0⁻¹} (by simpa using htc0)
  obtain ⟨R₀U, hR₀U, hUall⟩ := hCorU {t} (by simpa using And.intro ht0 htCs)
  set R₁ := max R₀L R₀U with hR₁_def
  have hR₁ : 0 < R₁ := lt_of_lt_of_le hR₀L (le_max_left _ _)
  obtain ⟨ε₀L, hε₀L, hLwin⟩ := hLall R₁ (le_max_left _ _)
  obtain ⟨ε₀U, hε₀U, hUwin⟩ := hUall R₁ (le_max_right _ _)
  set δ := min (min ε₀L ε₀U) (1 / 64 : ℝ) / 2 with hδ_def
  have hminpos : 0 < min (min ε₀L ε₀U) (1 / 64 : ℝ) :=
    lt_min (lt_min hε₀L hε₀U) (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hminpos]
  have hδL : δ < ε₀L := by
    dsimp [δ]
    have h1 := min_le_left ε₀L ε₀U
    have h2 := min_le_left (min ε₀L ε₀U) (1 / 64 : ℝ)
    linarith only [h1, h2, hminpos]
  have hδU : δ < ε₀U := by
    dsimp [δ]
    have h1 := min_le_right ε₀L ε₀U
    have h2 := min_le_left (min ε₀L ε₀U) (1 / 64 : ℝ)
    linarith only [h1, h2, hminpos]
  have hδsmall : δ < (1 / 64 : ℝ) := by
    dsimp [δ]
    have := min_le_right (min ε₀L ε₀U) (1 / 64 : ℝ)
    linarith only [this, hminpos]
  let W : Set ℤ := scaleWin δ R₁
  let L : Set ℤ := {j ∈ W | ENNReal.ofReal pstar ≤
    P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ ((64 : ℝ) ^ j) 0)}
  let U : Set ℤ := {j ∈ W | ENNReal.ofReal pstar ≤
    P (h ⁻¹' WitEvent D Dt ξ Q Cs aU A₀U ℓU β₀U t ((64 : ℝ) ^ j) 0)}
  have hWfin : W.Finite := s4c_scaleWin_finite hδ hR₁
  have hWpos : 0 < W.ncard := s8f_scaleWin_nonempty hδ hδsmall hR₁
  have hLsub : L ⊆ W := fun _ hj => hj.1
  have hUsub : U ⊆ W := fun _ hj => hj.1
  have hLcount : (3 / 4 : ℝ) * W.ncard ≤ (L.ncard : ℝ) :=
    hLwin _ (by simp) P h hh δ hδ hδL
  have hUcount : (3 / 4 : ℝ) * W.ncard ≤ (U.ncard : ℝ) :=
    hUwin _ (by simp) P h hh δ hδ hδU
  obtain ⟨j, hjL, hjU⟩ := s8f_quarter_intersection hWfin hWpos hLsub hUsub hLcount hUcount
  exact not_le.mpr (ht _ (zpow_pos (by norm_num) j) hjL.2) hjU.2

/-- The closing argument of [S] §9: the two optimal constants coincide, since otherwise the
two Corollary 5.5 windows contradict claim (32). -/
theorem theorem14Sharp_of_parts (hOpt : OptUpperShape) (h32 : Claim32Stmt) :
    Theorem14SharpStmt := by
  intro d ξ Q hd hξ hQ D Dt hD hDt
  obtain ⟨hUpos, hoptU⟩ := hOpt d hd hξ hQ hD hDt
  obtain ⟨hLpos, hoptL⟩ := hOpt d hd hξ hQ hDt hD
  set Cs := optUpper D Dt with hCs_def
  set cs := (optUpper Dt D)⁻¹ with hcs_def
  have hcs : 0 < cs := inv_pos.mpr hLpos
  have hinv : cs⁻¹ = optUpper Dt D := inv_inv _
  have hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
          (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v) := by
    intro Ω _ P _ h hh
    filter_upwards [hoptU.1 P h hh, hoptL.1 P h hh] with ω hU hL u v
    refine ⟨?_, hU u v⟩
    have h1 := hL u v
    rw [← hinv] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hcs.le
    rwa [← mul_assoc, mul_inv_cancel₀ hcs.ne', one_mul] at h2
  have hcsCs : cs ≤ Cs := by
    obtain ⟨Ω, instΩ, P, h, instP, hh⟩ := exists_isWholeSpaceLGF (by omega : 1 ≤ d)
    letI := instΩ
    letI := instP
    obtain ⟨ω, hω⟩ := (hcomp P h hh).exists
    have hpos : 0 < (D (h ω)).1 (0, HigherDimLFPP.e₁ d) :=
      (D (h ω)).apply_pos (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
    have hlow := (hω 0 (HigherDimLFPP.e₁ d)).1
    have hhigh := (hω 0 (HigherDimLFPP.e₁ d)).2
    nlinarith only [hpos, hlow, hhigh]
  by_cases heq : cs = Cs
  · refine ⟨cs, hcs, ?_⟩
    intro Ω _ P _ h hh
    obtain ⟨_, f, _, h0lgf⟩ := hh
    let h0 : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
    have htrans := hD.ae_apply_compare hDt h0lgf.isLGFPlusCont
      (c := cs) (C := Cs) hcs.le (heq ▸ hcs) (hcomp P h0 h0lgf)
    filter_upwards [htrans] with ω hω
    intro g u v
    have hident : addFun (h0 ω) (f ω + g) = addFun (h ω) g := by
      dsimp [h0, addFun]
      rw [ofCont_add]
      abel
    have hpair := hω (f ω + g) u v
    rw [hident] at hpair
    rw [← heq] at hpair
    exact le_antisymm hpair.2 hpair.1
  · have hlt : cs < Cs := lt_of_le_of_ne hcsCs heq
    obtain ⟨c0, c1, aL, A₀L, ℓL, β₀L, aU, A₀U, ℓU, β₀U, pstar,
      hpstar, _, hℓU, hβ₀U, hTrap, hLoc, hCor, hCorL, hCorU, hcs0, _⟩ :=
      s8f_gap_package hOpt hd hξ hQ hD hDt hlt
    obtain ⟨Ω, instΩ, P, h, instP, hh⟩ := exists_isWholeSpaceLGF (by omega : 1 ≤ d)
    letI := instΩ
    letI := instP
    obtain ⟨t, ht0, htCs, ht⟩ :=
      h32 d hd hξ hQ hD hDt hcs hcsCs hpstar hℓU hβ₀U
        hcomp hTrap hLoc hCor P h hh
    exact False.elim (s8f_window_contradiction hcs hcs0 hCorL hCorU P h hh ht0 htCs ht)

/-- Assembly-facing wrapper: Proposition 8.6 and the macro-ratio and optimal-constant inputs
produce the sharp weak uniqueness statement. -/
theorem theorem14Sharp_of_inputs (hP86 : Prop86Stmt) (hOpt : OptUpperShape)
    (hMR : ∀ (d : ℕ) (ξ Q : ℝ), 2 ≤ d → MacroRatioShape d ξ Q)
    (h32 : Prop86Stmt → (∀ (d : ℕ) (ξ Q : ℝ), 2 ≤ d → MacroRatioShape d ξ Q) → Claim32Stmt) :
    Theorem14SharpStmt :=
  theorem14Sharp_of_parts hOpt (h32 hP86 hMR)

end HigherDimLQGMetric
