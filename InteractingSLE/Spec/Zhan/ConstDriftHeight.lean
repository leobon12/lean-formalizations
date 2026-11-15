/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightLower

/-!
# Zhan's height statement from the noncollision of lower real points

Packet PROVE-ZHAN-A7. Astra, *Formalization proofs and dependency audit* (ruling R35), "Eliminate all other terminal
cluster points" (`source/external/AstraIG1/ig1_formalization_proofs.txt` L1471–L1499), in the restart form of
PROVE-ZHAN-A6's route: the terminal minimal height `M = mm κ σ f` (a measurable functional of the Brownian path,
`ConstDriftHeightMeas.lean`) satisfies `M(θ_n f) ≤ M(f)` for every path (`mm_shiftPath_le`); the restarted path has the
same law, so `M(θ₁ f) = M(f)` almost surely; strictness at the minimal height (`mm_eq_zero_or_pi`) leaves `M ∈ {0, π}`;
the value `0` (a terminal cluster point on the lower line) forces `n − |ξ_n| ≤ csub(θ_n f) + R` for every `n ≥ 1`
(`sub_abs_drv_le`, through a restart for a cluster point at the source, `exists_shift_lower_cluster`), which has
probability zero because `csub ∘ θ_n` has the law of `csub` while `n − |ξ_n| → ∞`.

The lower-line step uses that the real points of the lower line are never swallowed during the strip life. This is the
named input `ConstDriftAliveStatement κ` (for `κ ≤ 4` it is the Bessel-dimension noncollision `1 + 4/κ ≥ 2` of the
lower gaps; it is not proved here).

## Main results

* `ConstDriftAliveStatement κ`: **named input** (lower real points are never swallowed);
* `ae_goodP`: on the canonical path space, almost surely the height statement holds;
* `constDriftHeightStatement_of_alive`: `ConstDriftAliveStatement κ → ConstDriftHeightStatement κ` (**conditional
  helper**);
* `stripEndpointStatement_of_alive`: with PROVE-ZHAN-A6, `ConstDriftAliveStatement κ → StripEndpointStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv fwdMap fwdHull IsForwardSol)
open QuantumZipper.RS (CPath canonBM toCPath)

universe u

namespace InteractingSLE

namespace Zhan

open Strip

/-- **Named input: lower real points are never swallowed.** For `|σ| < 1` and every Brownian motion `β`, almost
surely, for every strip path whose strip driver is `√κ β_t + σ t`, every real point `x ∈ (−1, ∞) ∖ {0}` of the chordal
chart (a point of the lower line `ℝ` of the strip other than the source) has a centred forward flow at every time of the
strip life. For `κ ≤ 4` this is the noncollision of the lower strip gaps (Bessel dimension `1 + 4/κ ≥ 2`). -/
def ConstDriftAliveStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (β : ℝ≥0 → Ω → ℝ),
    IsBrownianReal β P → ∀ᵐ ω ∂P, ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞),
      HasStripDriver w v ζ (fun t => Real.sqrt κ * β t ω + σ * t) →
        ∀ x : ℝ, -1 < x → x ≠ 0 → ∀ s : ℝ≥0, IsStripLife w v ζ s →
          ∃ u : ℝ → ℂ, IsForwardSol (extPath w) (x : ℂ) s u

namespace HeightLaw

variable {κ σ : ℝ}

/-- Sublinearity of a path. -/
def SubP (f : CPath) : Prop := Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0)

/-- Lower real points stay alive along every strip path of the path. -/
def AliveP (κ σ : ℝ) (f : CPath) : Prop :=
  ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞), HasStripDriver w v ζ (fun t => drv κ σ f t) →
    ∀ x : ℝ, -1 < x → x ≠ 0 → ∀ s : ℝ≥0, IsStripLife w v ζ s →
      ∃ u : ℝ → ℂ, IsForwardSol (extPath w) (x : ℂ) s u

/-- The conclusion of the height statement for a path. -/
def GoodP (κ σ : ℝ) (f : CPath) : Prop :=
  ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (η : ℝ≥0 → ℂ), HasStripDriver w v ζ (fun t => drv κ σ f t) →
    (∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) →
      ∀ ε > 0, EvLife w v ζ fun s => Real.pi - ε < arg (1 + η s)

/-- The lower-line bad set. -/
def badN (κ σ : ℝ) : Set CPath :=
  {f | SubP f ∧ ∀ n : ℕ, 0 < n → (n : ℝ) - |drv κ σ f n| ≤ csub κ σ (slope σ) (shiftPath n f) + hullR σ}

variable {μ : Measure CPath} [IsProbabilityMeasure μ]

/-- **The lower-line bad set is null**: on it `csub ∘ θ_n` exceeds `n − |ξ_n| − R → ∞`, while `csub ∘ θ_n` has the
law of `csub`. -/
theorem measure_badN (hshift : ∀ r : ℝ≥0, μ.map (shiftPath r) = μ) (hσ : |σ| < 1) : μ (badN κ σ) = 0 := by
  have hcm := measurable_csub (κ := κ) (σ := σ) (slope σ)
  set E : ℕ → Set CPath := fun K => {f | (K : ℝ) ≤ csub κ σ (slope σ) f} with hE
  have hEm : ∀ K, MeasurableSet (E K) := fun K => measurableSet_le measurable_const hcm
  -- `μ(badN) ≤ μ(E K)` for every `K`
  have hle : ∀ K : ℕ, μ (badN κ σ) ≤ μ (E K) := by
    intro K
    set C : ℕ → Set CPath := fun N => {f | ∀ n : ℕ, N + 1 ≤ n → (K : ℝ) ≤ csub κ σ (slope σ) (shiftPath n f)}
      with hC
    have hCm : Monotone C := fun N N' hNN' f hf n hn => hf n (le_trans (by omega) hn)
    have hsub : badN κ σ ⊆ ⋃ N, C N := by
      intro f hf
      obtain ⟨hs, hb⟩ := hf
      -- `n − |ξ_n| − R → ∞`
      have hlin : Tendsto (fun n : ℕ => (n : ℝ) - |drv κ σ f n| - hullR σ) atTop atTop := by
        obtain ⟨C0, hC0⟩ := sublinear_of_tendsto f.2 hs (Real.sqrt κ) ((1 - |σ|) / 2)
          (by linarith [abs_nonneg σ])
        refine tendsto_atTop_mono (fun n => ?_) (tendsto_atTop_add_const_right _
          (-(C0 + Real.sqrt κ * |f.1 0| + hullR σ)) ((tendsto_natCast_atTop_atTop).const_mul_atTop
            (show 0 < (1 - |σ|) / 2 by linarith)))
        have h1 := hC0 n (Nat.cast_nonneg n)
        have h2 : |drv κ σ f n| ≤ |Real.sqrt κ * f.1 (n : ℝ).toNNReal| + Real.sqrt κ * |f.1 0| + |σ| * n := by
          simp only [drv]
          calc |Real.sqrt κ * (f.1 (n : ℝ).toNNReal - f.1 0) + σ * n|
              ≤ |Real.sqrt κ * (f.1 (n : ℝ).toNNReal - f.1 0)| + |σ * n| := abs_add_le _ _
            _ ≤ |Real.sqrt κ * f.1 (n : ℝ).toNNReal| + Real.sqrt κ * |f.1 0| + |σ| * n := by
                rw [mul_sub, abs_mul σ, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
                have := abs_sub (Real.sqrt κ * f.1 (n : ℝ).toNNReal) (Real.sqrt κ * f.1 0)
                rw [abs_mul (Real.sqrt κ) (f.1 0), abs_of_nonneg (Real.sqrt_nonneg κ)] at this
                linarith
        nlinarith [Real.sqrt_nonneg κ, abs_nonneg (f.1 0)]
      obtain ⟨N, hN⟩ := (tendsto_atTop.1 hlin (K : ℝ)).exists_forall_of_atTop
      refine mem_iUnion.2 ⟨N, fun n hn => ?_⟩
      have h1 := hb n (by omega)
      have h2 := hN n (by omega)
      linarith
    have hCle : ∀ N, μ (C N) ≤ μ (E K) := by
      intro N
      have hsub' : C N ⊆ shiftPath (N + 1 : ℕ) ⁻¹' E K := fun f hf => hf (N + 1) le_rfl
      calc μ (C N) ≤ μ (shiftPath (N + 1 : ℕ) ⁻¹' E K) := measure_mono hsub'
        _ = μ.map (shiftPath (N + 1 : ℕ)) (E K) := (Measure.map_apply (measurable_shiftPath _) (hEm K)).symm
        _ = μ (E K) := by rw [hshift]
    calc μ (badN κ σ) ≤ μ (⋃ N, C N) := measure_mono hsub
      _ = ⨆ N, μ (C N) := hCm.measure_iUnion
      _ ≤ μ (E K) := iSup_le hCle
  -- `μ(E K) → 0`
  have hanti : Antitone E := fun K K' hKK' f hf => by
    show (K : ℝ) ≤ _
    exact le_trans (by exact_mod_cast hKK') (show (K' : ℝ) ≤ _ from hf)
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun K => (hEm K).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hempty : (⋂ K, E K) = ∅ := by
    ext f
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall, hE]
    obtain ⟨K, hK⟩ := exists_nat_gt (csub κ σ (slope σ) f)
    exact ⟨K, fun h => absurd (show (K : ℝ) ≤ _ from h) (not_le.2 hK)⟩
  rw [hempty, measure_empty] at hlim
  exact le_antisymm (ge_of_tendsto' hlim hle) bot_le

/-- **The minimal height is almost surely invariant under the restart**: `mm ∘ θ_n ≤ mm` pathwise, with equal laws. -/
theorem ae_mm_shift_eq (hshift : ∀ r : ℝ≥0, μ.map (shiftPath r) = μ) {n : ℕ} (hn : 0 < n) :
    ∀ᵐ f ∂μ, mm κ σ (shiftPath n f) = mm κ σ f := by
  have hm := measurable_mm (κ := κ) (σ := σ)
  have hnorm : ∀ f, ‖mm κ σ f‖ ≤ Real.pi := fun f => by
    have := limInfTopQ_mem (h₁ := hgt κ σ f) fun t _ => hgt_mem f t
    rw [Real.norm_eq_abs, abs_le]
    exact this
  have hint1 : Integrable (fun f => mm κ σ f) μ :=
    Integrable.of_bound hm.aestronglyMeasurable Real.pi (Eventually.of_forall hnorm)
  have hint2 : Integrable (fun f => mm κ σ (shiftPath n f)) μ :=
    Integrable.of_bound (hm.comp (measurable_shiftPath n)).aestronglyMeasurable Real.pi
      (Eventually.of_forall fun f => hnorm _)
  have heqi : ∫ f, mm κ σ (shiftPath n f) ∂μ = ∫ f, mm κ σ f ∂μ := by
    rw [← integral_map (measurable_shiftPath n).aemeasurable hm.aestronglyMeasurable, hshift]
  have hnn : 0 ≤ fun f => mm κ σ f - mm κ σ (shiftPath n f) := fun f =>
    sub_nonneg.2 (mm_shiftPath_le f hn)
  have h0 : ∫ f, (mm κ σ f - mm κ σ (shiftPath n f)) ∂μ = 0 := by
    rw [integral_sub hint1 hint2, heqi, sub_self]
  have := (integral_eq_zero_iff_of_nonneg hnn (hint1.sub hint2)).1 h0
  filter_upwards [this] with f hf
  simp only [Pi.zero_apply, sub_eq_zero] at hf
  exact hf.symm

/-- **The height statement on the canonical path space.** -/
theorem ae_goodP (hσ : |σ| < 1) (hshift : ∀ r : ℝ≥0, μ.map (shiftPath r) = μ) (hsub : ∀ᵐ f ∂μ, SubP f)
    (halive : ∀ᵐ f ∂μ, AliveP κ σ f) : ∀ᵐ f ∂μ, GoodP κ σ f := by
  have hbad := measure_badN (κ := κ) (μ := μ) hshift hσ
  have hnotbad : ∀ᵐ f ∂μ, f ∉ badN κ σ := measure_eq_zero_iff_ae_notMem.1 hbad
  have hshiftQ : ∀ r : ℚ, ∀ᵐ f ∂μ, AliveP κ σ (shiftPath ((r : ℝ)).toNNReal f) ∧
      shiftPath ((r : ℝ)).toNNReal f ∉ badN κ σ := fun r => by
    refine ae_of_ae_map (p := fun g => AliveP κ σ g ∧ g ∉ badN κ σ)
      (measurable_shiftPath ((r : ℝ)).toNNReal).aemeasurable ?_
    rw [hshift]
    exact halive.and hnotbad
  filter_upwards [hsub, halive, hnotbad, ae_mm_shift_eq (κ := κ) (σ := σ) hshift one_pos,
    ae_all_iff.2 hshiftQ] with f hs hal hnb hm1 hQ
  intro w v ζ η hd hη ε hε
  rcases mm_eq_zero_or_pi hσ hs hd hη one_pos hm1 with h0 | hπ
  · exfalso
    obtain ⟨z0, hz0, q, hq, hlim⟩ := exists_lower_cluster hσ hs hd hη h0
    by_cases hz00 : z0 = 0
    · subst hz00
      obtain ⟨r, -, p0, hp0, hp00, q', hq', hlim'⟩ :=
        exists_shift_lower_cluster hσ hs hd hη hq (by simpa using hlim)
      have hR := hasStripDriver_rs hd ((r : ℝ)).toNNReal
      have hηR := isGeneratingTrace_rsTrace hd hη ((r : ℝ)).toNNReal
      have hfR := tendsto_shiftPath hs ((r : ℝ)).toNNReal
      exact (hQ r).2 ⟨hfR, fun n hn => sub_abs_drv_le hσ hfR hR hηR ((hQ r).1 _ _ _ hR) hp0 hp00 hq' hlim' hn⟩
    · exact hnb ⟨hs, fun n hn => sub_abs_drv_le hσ hs hd hη (hal w v ζ hd) hz0 hz00 hq hlim hn⟩
  · exact evLife_of_mm_eq_pi hσ hs hd hη hπ ε hε

end HeightLaw

variable {κ : ℝ}

/-- **Zhan's height statement from the noncollision of lower real points** (conditional helper; its single hypothesis
is the named input `ConstDriftAliveStatement κ`). -/
theorem constDriftHeightStatement_of_alive (hA : ConstDriftAliveStatement.{0} κ) :
    ConstDriftHeightStatement.{u} κ := by
  intro σ hσ Ω mΩ P 𝓗 β hβ
  have hB : IsBrownianReal β P := hβ.1
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B, hBm, hBc, hB0, hBB, hBeq⟩ := QuantumZipper.RS.exists_good_version0 hB
  have hmeas := QuantumZipper.RS.measurable_toCPath hBm hBc
  set μ : Measure CPath := P.map (toCPath B hBc) with hμ
  have hμP : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 hP
  have hμB : IsBrownianReal canonBM μ :=
    QuantumZipper.RS.isBrownianReal_canonBM hBB.toIsPreBrownianReal hBm hBc
  have hshift : ∀ r : ℝ≥0, μ.map (HeightLaw.shiftPath r) = μ := by
    intro r
    have hBr : IsPreBrownianReal (fun t ω => B (r + t) ω - B r ω) P := hBB.toIsPreBrownianReal.shift r
    have hBrm : ∀ t, Measurable (fun ω => B (r + t) ω - B r ω) := fun t => (hBm _).sub (hBm _)
    have hBrc : ∀ ω, Continuous fun t => B (r + t) ω - B r ω := fun ω =>
      ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    rw [hμ, Measure.map_map (HeightLaw.measurable_shiftPath r) hmeas]
    have : HeightLaw.shiftPath r ∘ toCPath B hBc = toCPath (fun t ω => B (r + t) ω - B r ω) hBrc := by
      funext ω
      rfl
    rw [this]
    exact QuantumZipper.RS.map_toCPath_eq hBr hBB.toIsPreBrownianReal hBrm hBm hBrc hBc
  have hsub : ∀ᵐ f ∂μ, HeightLaw.SubP f := by
    filter_upwards [ProbabilityTheory.IsBrownianReal.tendsto_div_id_atTop hμB] with f hf
    exact hf
  have hzero : ∀ᵐ f ∂μ, f.1 0 = 0 := by
    rw [hμ, ae_map_iff hmeas.aemeasurable (measurableSet_eq_fun (HeightLaw.measurable_eval 0) measurable_const)]
    exact ae_of_all _ fun ω => hB0 ω
  have halive : ∀ᵐ f ∂μ, HeightLaw.AliveP κ σ f := by
    filter_upwards [hA σ hσ μ canonBM hμB, hzero] with f hf hf0
    intro w v ζ hd
    refine hf w v ζ ⟨hd.1, fun t => ?_⟩
    rw [hd.2 t]
    simp only [HeightLaw.drv, QuantumZipper.RS.canonBM, hf0, sub_zero, Real.toNNReal_coe]
  have hgood := HeightLaw.ae_goodP hσ hshift hsub halive
  filter_upwards [ae_of_ae_map hmeas.aemeasurable hgood, hBeq] with ω hω heq
  intro w v ζ η hd hη ε hε
  have hβ0 : β 0 ω = 0 := by rw [← heq 0]; exact hB0 ω
  refine hω w v ζ η ⟨hd.1, fun t => ?_⟩ hη ε hε
  rw [hd.2 t]
  simp only [HeightLaw.drv, toCPath, Real.toNNReal_coe, heq, hβ0, sub_zero]

/-- **Zhan's strip endpoint theorem (ii) from the noncollision of lower real points** (conditional helper, with
PROVE-ZHAN-A6's `stripEndpointStatement_of_height`). -/
theorem stripEndpointStatement_of_alive (hκ : 0 < κ) (hA : ConstDriftAliveStatement.{0} κ) :
    StripEndpointStatement.{u} κ :=
  stripEndpointStatement_of_height hκ (constDriftHeightStatement_of_alive hA)

end Zhan

end InteractingSLE
