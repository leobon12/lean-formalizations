import QuantumZipper.Proofs.Thm18.DrvGoodDet
import QuantumZipper.Proofs.RS.RohdeSchrammSimple
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.RS.TipA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DRVGOOD: the SLE driver `√κ B` satisfies the certificate a.s. (`κ ≤ 4`)

Inputs: the radial Hölder bound (`RS.ae_radialGood_drive`, Rohde–Schramm, Ann. Math. 161 (2005),
Thm 3.6 / Prop 3.8), the simple chord (`RS.rohdeSchrammSimple`, RS Thm 6.1), and null hulls
(`NonSwallow.ae_volume_fwdHull_eq_zero`). The quantitative forms `CondI`, `CondP` follow by
compactness. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace QuantumZipper
namespace DrvGood

variable {W : ℝ → ℝ}

theorem tendsto_one_div_nhdsGT :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩

theorem trS_eq_of_radialGood (hRG : RS.RadialGood W) {t : ℝ} (ht : 0 ≤ t) :
    trS W t = trace W t :=
  ((hRG.tendsto ht).comp tendsto_one_div_nhdsGT).limUnder_eq

theorem condH_of_radialGood (hRG : RS.RadialGood W) : CondH W := by
  obtain ⟨-, -, -, -, δ, hδ, hb⟩ := hRG
  obtain ⟨δq, hδq0, hδq⟩ := exists_rat_btwn hδ
  refine ⟨δq, by exact_mod_cast hδq0, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hb N
  refine ⟨⌈max C 0⌉₊, fun t y y' ht htN hy hy1 hy' hy1' => ?_⟩
  have ht' : (t : ℝ) ∈ Icc (0 : ℝ) N := ⟨by exact_mod_cast ht, by exact_mod_cast htN⟩
  have hyI : (y : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by exact_mod_cast hy, by exact_mod_cast hy1⟩
  have hyI' : (y' : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨by exact_mod_cast hy', by exact_mod_cast hy1'⟩
  have h1 := hC t ht' y hyI
  have h2 := hC t ht' y' hyI'
  have hC' : C ≤ (⌈max C 0⌉₊ : ℝ) := (le_max_left C 0).trans (Nat.le_ceil _)
  have hC0 : (0 : ℝ) ≤ ⌈max C 0⌉₊ := Nat.cast_nonneg _
  have hr : ∀ z ∈ Ioc (0 : ℝ) 1, C * z ^ δ ≤ (⌈max C 0⌉₊ : ℝ) * z ^ (δq : ℝ) := by
    intro z hz
    have e1 : z ^ δ ≤ z ^ (δq : ℝ) := Real.rpow_le_rpow_of_exponent_ge hz.1 hz.2 hδq.le
    calc C * z ^ δ ≤ (⌈max C 0⌉₊ : ℝ) * z ^ δ :=
          mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hz.1.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left e1 hC0
  calc ‖fwdMapInv W (t : ℝ) (((y : ℝ) : ℂ) * I) - fwdMapInv W (t : ℝ) (((y' : ℝ) : ℂ) * I)‖
      ≤ ‖fwdMapInv W (t : ℝ) (((y : ℝ) : ℂ) * I) - trace W t‖ +
          ‖fwdMapInv W (t : ℝ) (((y' : ℝ) : ℂ) * I) - trace W t‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub
          (fwdMapInv W (t : ℝ) (((y : ℝ) : ℂ) * I)) (trace W t)
          (fwdMapInv W (t : ℝ) (((y' : ℝ) : ℂ) * I))
        rwa [norm_sub_rev (trace W t)] at this
    _ ≤ C * (y : ℝ) ^ δ + C * (y' : ℝ) ^ δ := add_le_add h1 h2
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hr _ hyI) (hr _ hyI')

theorem condIP_of_simple (hRG : RS.RadialGood W) (hs : IsSimpleChord (trace W)) :
    CondI W ∧ CondP W := by
  obtain ⟨-, hcont, hinj, hH, -⟩ := hs
  refine ⟨fun p q r s hp hpq hqr hrs => ?_, fun a b ha hab => ?_⟩
  · have hp' : (0 : ℝ) ≤ p := by exact_mod_cast hp
    have hK : IsCompact (Icc (p : ℝ) q ×ˢ Icc (r : ℝ) s) := isCompact_Icc.prod isCompact_Icc
    have hne : (Icc (p : ℝ) q ×ˢ Icc (r : ℝ) s).Nonempty :=
      ⟨((p : ℝ), (r : ℝ)), ⟨le_rfl, (by exact_mod_cast hpq.le : (p : ℝ) ≤ q)⟩,
        ⟨le_rfl, (by exact_mod_cast hrs.le : (r : ℝ) ≤ s)⟩⟩
    have hsubq : ∀ z ∈ Icc (p : ℝ) q ×ˢ Icc (r : ℝ) s, 0 ≤ z.1 ∧ 0 ≤ z.2 := fun z hz =>
      ⟨hp'.trans hz.1.1, hp'.trans (by
        have : (p : ℝ) ≤ r := by exact_mod_cast (hpq.trans hqr).le
        exact this.trans hz.2.1)⟩
    have hf : ContinuousOn (fun z : ℝ × ℝ => ‖trace W z.1 - trace W z.2‖)
        (Icc (p : ℝ) q ×ˢ Icc (r : ℝ) s) := by
      refine ContinuousOn.norm (ContinuousOn.sub ?_ ?_)
      · exact hcont.comp continuousOn_fst fun z hz => (hsubq z hz).1
      · exact hcont.comp continuousOn_snd fun z hz => (hsubq z hz).2
    obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne hf
    have hpos : 0 < ‖trace W z0.1 - trace W z0.2‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro he
      have := hinj (hsubq z0 hz0).1 (hsubq z0 hz0).2 he
      have h1 : z0.1 ≤ q := hz0.1.2
      have h2 : (r : ℝ) ≤ z0.2 := hz0.2.1
      have h3 : (q : ℝ) < r := by exact_mod_cast hqr
      linarith
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    refine ⟨m, fun u v hu1 hu2 hv1 hv2 => ?_⟩
    have hz : ((u : ℝ), (v : ℝ)) ∈ Icc (p : ℝ) q ×ˢ Icc (r : ℝ) s :=
      ⟨⟨(by exact_mod_cast hu1 : (p : ℝ) ≤ u), (by exact_mod_cast hu2 : (u : ℝ) ≤ q)⟩,
        ⟨(by exact_mod_cast hv1 : (r : ℝ) ≤ v), (by exact_mod_cast hv2 : (v : ℝ) ≤ s)⟩⟩
    rw [trS_eq_of_radialGood hRG (hsubq _ hz).1, trS_eq_of_radialGood hRG (hsubq _ hz).2]
    exact hm.le.trans (hmin hz)
  · have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hne : (Icc (a : ℝ) b).Nonempty := ⟨a, le_rfl, by exact_mod_cast hab.le⟩
    have hf : ContinuousOn (fun u => (trace W u).im) (Icc (a : ℝ) b) :=
      continuous_im.comp_continuousOn (hcont.mono fun u hu => ha'.le.trans hu.1)
    obtain ⟨u0, hu0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
    have hpos : 0 < (trace W u0).im := hH u0 (ha'.trans_le hu0.1)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    refine ⟨m, fun u hu1 hu2 => ?_⟩
    have hu : (u : ℝ) ∈ Icc (a : ℝ) b := ⟨by exact_mod_cast hu1, by exact_mod_cast hu2⟩
    rw [trS_eq_of_radialGood hRG (ha'.le.trans hu.1)]
    exact hm.le.trans (hmin hu)

/-- **The SLE driver is a.s. good**, `0 < κ ≤ 4`. -/
theorem ae_good_drive {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, Good (drive κ B ω) := by
  obtain ⟨B'', hm, hc, -, hB'', heq⟩ := RS.exists_good_version0 hB
  have hV : ∀ᵐ ω ∂P, ∀ n : ℕ, volume (fwdHull (drive κ B ω) n) = 0 := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => NonSwallow.ae_volume_fwdHull_eq_zero
      hB''.toIsPreBrownianReal hm hc hκ hκ4 n, heq] with ω hω he n
    have hdr : drive κ B ω = drive κ B'' ω := by funext r; simp [drive, he]
    rw [hdr]; exact hω n
  filter_upwards [RS.ae_radialGood_drive hB hκ (by linarith),
    RS.rohdeSchrammSimple κ hκ hκ4 P B hB, hV] with ω hRG hs hvol
  obtain ⟨hI, hP⟩ := condIP_of_simple hRG hs.1
  exact ⟨condH_of_radialGood hRG, hvol, hI, hP⟩

end DrvGood
end QuantumZipper
