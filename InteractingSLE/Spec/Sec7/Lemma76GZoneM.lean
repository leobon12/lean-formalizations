/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GSide

/-!
# The zone data by countable suprema, and the junction

Packet PROVE-LEMMA76G. For measurability the extreme chart points of the zones are written as countable suprema and
infima of chart points of untouched real points (`zoneDataM`); in the setting of a disjoint pair they agree with the
zone data (`IsSetting.zoneDataM_eq`). Also: the chart inverse sends `R₁` to the right end `b₁` of the first base
(`IsSetting.inv_R₁`, the junction).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open HalfPlaneSep Restart Supp7

/-- **The zone data by countable suprema and infima** (for measurability). -/
def zoneDataM (φ : ℂ → ℂ) (D : Set ℂ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) : ZW where
  T := fun x : ℝ => chartPt φ D (x : ℂ)
  a₂ := baseL β b
  b₂ := baseR β b
  a₁ := baseL α a
  b₁ := baseR α a
  L₂ := ⨆ n : ℕ, chartPt φ D ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)
  M₂ := 0
  R₂ := ⨅ n : ℕ, chartPt φ D ((baseR β b + (baseL α a - baseR β b) / ((n : ℝ) + 2) : ℝ) : ℂ)
  L₁ := ⨆ n : ℕ, chartPt φ D ((baseL α a - (baseL α a - baseR β b) / ((n : ℝ) + 2) : ℝ) : ℂ)
  M₁ := chartPt φ D (α a)
  R₁ := ⨅ n : ℕ, chartPt φ D ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)

/-- The supremum of a strictly increasing function on `S` equals the supremum along a sequence of `S` whose terms
eventually exceed every point of `S`. -/
theorem sSup_image_eq_iSup {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S) (hbdd : BddAbove (f '' S))
    {x : ℕ → ℝ} (hx : ∀ n, x n ∈ S) (hcof : ∀ y ∈ S, ∃ n, y < x n) : sSup (f '' S) = ⨆ n, f (x n) := by
  have hbdd' : BddAbove (range fun n => f (x n)) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM ⟨_, hx n, rfl⟩⟩
  refine le_antisymm (csSup_le ⟨_, ⟨_, hx 0, rfl⟩⟩ ?_) (ciSup_le fun n => le_csSup hbdd ⟨_, hx n, rfl⟩)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨n, hn⟩ := hcof y hy
  exact (hf hy (hx n) hn).le.trans (le_ciSup hbdd' n)

/-- The infimum version. -/
theorem sInf_image_eq_iInf {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictMonoOn f S) (hbdd : BddBelow (f '' S))
    {x : ℕ → ℝ} (hx : ∀ n, x n ∈ S) (hcof : ∀ y ∈ S, ∃ n, x n < y) : sInf (f '' S) = ⨅ n, f (x n) := by
  have hbdd' : BddBelow (range fun n => f (x n)) := by
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM ⟨_, hx n, rfl⟩⟩
  refine le_antisymm (le_ciInf fun n => csInf_le hbdd ⟨_, hx n, rfl⟩) (le_csInf ⟨_, ⟨_, hx 0, rfl⟩⟩ ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨n, hn⟩ := hcof y hy
  exact (ciInf_le hbdd' n).trans (hf (hx n) hy hn).le

theorem one_div_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat

theorem div_succ_succ_pos {c : ℝ} (hc : 0 < c) (n : ℕ) : 0 < c / ((n : ℝ) + 2) := div_pos hc (by positivity)

theorem div_succ_succ_lt {c : ℝ} (hc : 0 < c) (n : ℕ) : c / ((n : ℝ) + 2) < c :=
  div_lt_self hc (by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith)

/-- Small reals of the form `c/(n+2)`. -/
theorem exists_div_succ_succ_lt {c ε : ℝ} (hε : 0 < ε) : ∃ n : ℕ, c / ((n : ℝ) + 2) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (c / ε)
  refine ⟨n, (div_lt_iff₀ (by positivity)).2 ?_⟩
  rw [div_lt_iff₀ hε] at hn
  nlinarith

namespace IsSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

/-- **In the setting, the countable zone data are the zone data.** -/
theorem zoneDataM_eq : zoneDataM φ (activeDomain α a β b) α a β b = zoneData φ α a β b := by
  have h21 := hs.b₂_lt_a₁
  have hc : 0 < baseL α a - baseR β b := sub_pos.2 h21
  have hT := fun (S : Set ℝ) (hS : ∀ x ∈ S, IsUntouched α a β b x) => hs.T_strictMonoOn (φ := φ) hS
  have hL₂ : (⨆ n : ℕ, chartPt φ (activeDomain α a β b) ((baseL β b - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) =
      (zoneData φ α a β b).L₂ := by
    refine (sSup_image_eq_iSup (hT _ fun x hx => hs.untouched_of_zone (Or.inl hx)) hs.bddAbove₀
      (x := fun n : ℕ => baseL β b - 1 / ((n : ℝ) + 1))
      (fun n => mem_Iio.2 (sub_lt_self _ (one_div_succ_pos n))) fun y hy => ?_).symm
    have hy' : y < baseL β b := hy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy')
    exact ⟨n, lt_sub_comm.2 hn⟩
  have hR₂ : (⨅ n : ℕ, chartPt φ (activeDomain α a β b)
      ((baseR β b + (baseL α a - baseR β b) / ((n : ℝ) + 2) : ℝ) : ℂ)) = (zoneData φ α a β b).R₂ := by
    refine (sInf_image_eq_iInf (hT _ fun x hx => hs.untouched_of_zone (Or.inr (Or.inl hx))) hs.bddBelow₁
      (x := fun n : ℕ => baseR β b + (baseL α a - baseR β b) / ((n : ℝ) + 2))
      (fun n => ⟨lt_add_of_pos_right _ (div_succ_succ_pos hc n), lt_sub_iff_add_lt'.1 (div_succ_succ_lt hc n)⟩)
      fun y hy => ?_).symm
    obtain ⟨n, hn⟩ := exists_div_succ_succ_lt (sub_pos.2 hy.1)
    exact ⟨n, lt_sub_iff_add_lt'.1 hn⟩
  have hL₁ : (⨆ n : ℕ, chartPt φ (activeDomain α a β b)
      ((baseL α a - (baseL α a - baseR β b) / ((n : ℝ) + 2) : ℝ) : ℂ)) = (zoneData φ α a β b).L₁ := by
    refine (sSup_image_eq_iSup (hT _ fun x hx => hs.untouched_of_zone (Or.inr (Or.inl hx))) hs.bddAbove₁
      (x := fun n : ℕ => baseL α a - (baseL α a - baseR β b) / ((n : ℝ) + 2))
      (fun n => ⟨lt_sub_comm.2 (div_succ_succ_lt hc n), sub_lt_self _ (div_succ_succ_pos hc n)⟩)
      fun y hy => ?_).symm
    obtain ⟨n, hn⟩ := exists_div_succ_succ_lt (sub_pos.2 hy.2)
    exact ⟨n, lt_sub_comm.2 hn⟩
  have hR₁ : (⨅ n : ℕ, chartPt φ (activeDomain α a β b) ((baseR α a + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) =
      (zoneData φ α a β b).R₁ := by
    refine (sInf_image_eq_iInf (hT _ fun x hx => hs.untouched_of_zone (Or.inr (Or.inr hx))) hs.bddBelow₂
      (x := fun n : ℕ => baseR α a + 1 / ((n : ℝ) + 1))
      (fun n => mem_Ioi.2 (lt_add_of_pos_right _ (one_div_succ_pos n))) fun y hy => ?_).symm
    have hy' : baseR α a < y := hy
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy')
    exact ⟨n, lt_sub_iff_add_lt'.1 hn⟩
  simp only [zoneDataM, zoneData] at hL₂ hR₂ hL₁ hR₁ ⊢
  rw [hL₂, hR₂, hL₁, hR₁]

/-- **The junction**: the chart inverse sends `R₁` to the right end of the first base. -/
theorem inv_R₁ : ψ (zoneData φ α a β b).R₁ = ((baseR α a : ℝ) : ℂ) := by
  have hz := hs.zoneData_good
  set x : ℕ → ℝ := fun n => baseR α a + 1 / ((n : ℝ) + 1) with hx
  have hxb : ∀ n, baseR α a < x n := fun n => lt_add_of_pos_right _ (one_div_succ_pos n)
  have hxlim : Tendsto x atTop (𝓝 (baseR α a)) := by
    simpa [hx] using (tendsto_const_nhds (x := baseR α a)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  -- the chart points decrease to `R₁`
  have hTx : Tendsto (fun n => (zoneData φ α a β b).T (x n)) atTop (𝓝 (zoneData φ α a β b).R₁) := by
    have hanti : Antitone fun n => (zoneData φ α a β b).T (x n) := by
      refine antitone_nat_of_succ_le fun n => (hz.mono₂ (hxb (n + 1)) (hxb n) ?_).le
      simp only [hx]
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : 1 / (((n + 1 : ℕ) : ℝ) + 1) < 1 / ((n : ℝ) + 1) := by
        rw [one_div_lt_one_div (by positivity) h1]; push_cast; linarith
      exact (add_lt_add_iff_left _).2 h2
    have hbdd : BddBelow (range fun n => (zoneData φ α a β b).T (x n)) :=
      ⟨(zoneData φ α a β b).R₁, by rintro _ ⟨n, rfl⟩; exact (hz.lt_T₂ _ (hxb n)).le⟩
    have heq : (⨅ n, (zoneData φ α a β b).T (x n)) = (zoneData φ α a β b).R₁ := by
      have := congrArg ZW.R₁ hs.zoneDataM_eq
      simp only [zoneDataM] at this
      exact this
    rw [← heq]
    exact tendsto_atTop_ciInf hanti hbdd
  have hψc : Continuous fun w : ℝ => ψ w := hs.ψc.comp_continuous continuous_ofReal ofReal_mem_Hbar
  have h1 := (hψc.tendsto _).comp hTx
  have h2 : (fun n => ψ ((zoneData φ α a β b).T (x n))) = fun n => ((x n : ℝ) : ℂ) := by
    funext n
    exact hs.T_spec (hs.untouched_of_zone (Or.inr (Or.inr (hxb n))))
  rw [Function.comp_def, h2] at h1
  exact tendsto_nhds_unique h1 ((continuous_ofReal.tendsto _).comp hxlim)

end IsSetting

end Lemma76G

end Sec7

end InteractingSLE
