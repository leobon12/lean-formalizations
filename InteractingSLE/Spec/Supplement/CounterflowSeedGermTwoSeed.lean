/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4Swallow
import InteractingSLE.Spec.Supplement.LP4ZeroOne
import InteractingSLE.Spec.Sec5.CfLineRegQSeed

/-!
# The germ of the two-seed law at its start

Packet PROVE-CFNORETURN2 (the named input `CfNoReturn.SeedGermStatement` of PROVE-CFNORETURN, ruling R59). For the
two-seed word `SLE_κ(r_L; r_R)` (`r_L, r_R > −2`, both marks at `0`) this file proves the two properties of the germ at
time `0` that `SeedGermStatement` asks for, as properties of the driving path:

* **hittable seed** (`ae_swallowed_right`, `κ > 4`, `r_R < κ/2 − 2`): almost surely, for every `T > 0` some real point
  `x > 0` is swallowed by time `T`. Route (PROVE-CFNORETURN §5 step 2): with positive probability some positive point is
  swallowed at a finite time (`frequently_swallowed_right`: the proof of PROVE-LP18's `LP.lp4RightSwallowStatement`,
  which never uses its bound on `r_L`); the event "some positive point is swallowed at a finite time" is dilation
  invariant, so Aux. lemma 128 (`LP.ZeroOne.aux128DriverStatement`) makes it almost sure; the dilation invariance of the
  driving law (`LP.ZeroOne.map_dilPath_map_killedPath`) makes `P(swallowed by T)` independent of `T > 0`, hence `1`.
  The left side is the reflection (`ae_swallowed_left`).
* **no return** (`ae_trace_ne_zero_twoSeed`, every `κ > 0`): if the two-seed word is complete (a continuous transient
  trace, `LP.IsCompleteForceWord`), almost surely no trace on `[0, ∞)` vanishes at a positive time. This is the scaling
  argument of `Sec5.CfLineRegQ.ae_trace_ne_zero_of_seed`, whose admissibility hypothesis only supplied the infinite
  lifetime (here `Sec2.Assembly2.ae_lifetime_eq_top_twoSeed`) and the transient trace (here the completeness).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.CfNoReturn.Germ

open QuantumZipper Sec2 Sec2.Assembly Sec7.RandRestart Sec7.Dilation LP LP.LP4S

/-! ### Positive probability of swallowing a positive point -/

section Positive

variable {κ rL rR : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **With positive probability the two-seed evolution swallows a positive point** (`κ > 4`, `r_L > −2`,
`−2 < r_R < κ/2 − 2`). This is the proof of `LP.lp4RightSwallowStatement` (PROVE-LP18), which does not use the bound
`r_L < κ/2 − 2` of its statement: LP2 at the ratio restart, the window, the bounded-energy deletion of the separated
left drift, and the ratio restart of the actual evolution. -/
theorem frequently_swallowed_right [IsProbabilityMeasure P] (hκ4 : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hRc : rR < κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∃ᵐ ω ∂P, ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
  have hκ : 0 < κ := by linarith
  obtain ⟨n, hn⟩ := exists_codeLaw_winSet_ne_zero hκ4 hR hRc
  set r : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have h0 : (-2 : ℝ) < (fun _ : Fin 1 => (0 : ℝ)) 0 := by norm_num
  have hL' : (-2 : ℝ) < (fun _ : Fin 1 => rL) 0 := hL
  have hR' : (-2 : ℝ) < (fun _ : Fin 1 => rR) 0 := hR
  -- the target word from `(−1, r)` swallows beyond its right mark with positive canonical probability
  have hK : codeLaw κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) allSet ((fun _ => -1), fun _ => r) ≠ 0 := by
    obtain ⟨Ω₁, m₁, P₁, hP₁, 𝓕₁, W₁, VL₁, VR₁, B₁, ζ₁, hE₁, hζ₁⟩ :=
      exists_twoForce hκ (ρL := fun _ => (0 : ℝ)) h0 (ρR := fun _ => rR) hR one_pos hr0.le
    have hF : IsOrderedForceWord (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => r) :=
      ⟨antitone_const, fun _ => by norm_num, monotone_const, fun _ => hr0.le⟩
    refine codeLaw_allSet_ne_zero_of_compare hκ hF (show (-1 : ℝ) < r by linarith) hR' (M := 1 / 2)
      (N := 1 / 4) (δ := 1 / 4) (by norm_num) (by norm_num) (by norm_num) hE₁ hζ₁ ?_
    rw [measure_winSet_eq_codeLaw hκ (fun _ _ => show (-1 : ℝ) < r by linarith) hE₁]
    exact hn
  -- the ratio restart of the actual evolution
  obtain ⟨A, T, -, hA0, hlaw, hgood⟩ := exists_ratio_restart hκ hL' hR' hE hr0 measurableSet_allSet
    (fun _ _ _ => Iff.rfl) (fun s w w' τ h hw => swalAll_congr s w w' τ h hw)
    (K := codeLaw κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) allSet ((fun _ => -1), fun _ => r))
    (fun L hL => codeLaw_allSet_ray hκ hL' hR' hr0.le hL)
  rw [frequently_ae_iff]
  have hsub : A ∩ {ω | SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω)} ⊆
      {ω | ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T} := by
    rintro ω ⟨hωA, hω⟩
    obtain ⟨-, hζω, hp, -⟩ := hgood ω hωA
    have hω' : SwalAll (wordAt W VL VR T ω) (fun t => W (T ω + t) ω - W (T ω) ω) ⊤ := by
      rw [← ENNReal.top_sub_coe (r := T ω), ← hζω]; exact hω
    exact exists_swallowed_of_swalAll hp (T ω) hω'
  intro h0'
  have := measure_mono_null hsub h0'
  rw [hlaw] at this
  exact mul_ne_zero hK hA0 this

end Positive

/-! ### Swallowing by a given time, as a Borel set of driving paths -/

/-- The driving paths under which some positive rational point is swallowed by time `T`. -/
def swalSet (T : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  ⋃ q : {q : ℚ // (0 : ℝ) < q}, (LP3.aliveSet 1 ((q : ℚ) : ℝ) q.2 T)ᶜ

theorem measurableSet_swalSet (T : ℝ≥0) : MeasurableSet (swalSet T) :=
  MeasurableSet.iUnion fun _ => (LP3.measurableSet_aliveSet _ _ _ _).compl

theorem mem_swalSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ≥0} :
    w ∈ swalSet T ↔ ∃ x : ℝ, 0 < x ∧ ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T := by
  have hWc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  constructor
  · intro h
    simp only [swalSet, mem_iUnion, mem_compl_iff] at h
    obtain ⟨q, hq⟩ := h
    rw [LP3.mem_aliveSet_iff hw hw0, LP4HB.pathDrive_one] at hq
    exact ⟨q, q.2, hq⟩
  · rintro ⟨x, hx, hT⟩
    obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn hx
    simp only [swalSet, mem_iUnion, mem_compl_iff]
    refine ⟨⟨q, hq0⟩, ?_⟩
    rw [LP3.mem_aliveSet_iff hw hw0, LP4HB.pathDrive_one]
    rintro ⟨v, hv⟩
    exact hT (QuantumZipper.RS.exists_isForwardSol_of_lt hWc T.coe_nonneg (by simpa [hw0] using hq0) hqx hv)

/-- Swallowing is monotone in the time. -/
theorem swalSet_mono {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T T' : ℝ≥0} (hTT' : T ≤ T')
    (h : w ∈ swalSet T) : w ∈ swalSet T' := by
  rw [mem_swalSet_iff hw hw0] at h ⊢
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, hx, LP4HB.isSwallowedBy_mono T.coe_nonneg (by exact_mod_cast hTT') hs⟩

/-- **Swallowing under dilation**: `dilPath c w` swallows a positive point by `T` iff `w` does by `c T`. -/
theorem dilPath_mem_swalSet_iff {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {T : ℝ≥0} : dilPath c w ∈ swalSet T ↔ w ∈ swalSet (c * T) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc
  have hdc := LP.continuous_dilPath (c := c) w hw
  have hd0 : dilPath c w 0 = 0 := LP.dilPath_zero hw0
  rw [mem_swalSet_iff hdc hd0, mem_swalSet_iff hw hw0]
  constructor
  · rintro ⟨x, hx, hT⟩
    have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h := LP4HB.isSwallowedBy_dilPath_of hci hT
    have hdd : ∀ s : ℝ≥0, dilPath c⁻¹ (dilPath c w) s = w s := fun s => by
      simp only [dilPath]
      have e1 : c * (c⁻¹ * s) = s := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      rw [e1, NNReal.coe_inv, Real.sqrt_inv, inv_inv, ← mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_pos.2 hc0).ne', one_mul]
    simp only [hdd] at h
    refine ⟨x / √((c⁻¹ : ℝ≥0) : ℝ), div_pos hx (Real.sqrt_pos.2 (by positivity)), ?_⟩
    have e : ((T : ℝ) / ((c⁻¹ : ℝ≥0) : ℝ)) = ((c * T : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_inv]; field_simp
    rw [← e]
    exact h
  · rintro ⟨x, hx, hT⟩
    refine ⟨x / √(c : ℝ), div_pos hx (Real.sqrt_pos.2 hc0), ?_⟩
    have h := LP4HB.isSwallowedBy_dilPath_of hc hT
    have e : ((c * T : ℝ≥0) : ℝ) / (c : ℝ) = (T : ℝ) := by
      rw [NNReal.coe_mul]; field_simp
    rwa [e] at h

/-! ### The hittable seed side is swallowed at arbitrarily small times -/

section Hit

variable {κ rL rR : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- On the good event the killed driving path is the driving path. -/
theorem ae_killedPath_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ZeroOne.killedPath W ζ ω = fun t => W t ω := by
  filter_upwards [ae_good hκ hL hR hE] with ω h
  funext t
  simp [ZeroOne.killedPath, Sec7.killedProc, h.1]

/-- The probability of a Borel event of the driving path is its probability under the law of the killed path. -/
theorem measure_path_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) :
    P {ω | (fun t => W t ω) ∈ S} = P.map (ZeroOne.killedPath W ζ) S := by
  rw [Measure.map_apply (ZeroOne.measurable_killedPath hE.2.1) hS]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_killedPath_eq hκ hL hR hE] with ω hk
  simp only [mem_preimage, hk]

/-- An event of the driving path of probability one holds almost surely. -/
theorem ae_mem_of_measure_eq_one [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S) (h1 : P {ω | (fun t => W t ω) ∈ S} = 1) :
    ∀ᵐ ω ∂P, (fun t => W t ω) ∈ S := by
  have hK := ZeroOne.measurable_killedPath hE.2.1
  rw [measure_path_eq hκ hL hR hE hS] at h1
  have hμ : IsProbabilityMeasure (P.map (ZeroOne.killedPath W ζ)) := inferInstance
  have h2 : ∀ᵐ y ∂(P.map (ZeroOne.killedPath W ζ)), y ∈ S :=
    (ae_mem_iff_measure_eq hS.nullMeasurableSet).2 (by rw [h1, measure_univ])
  filter_upwards [ae_of_ae_map hK.aemeasurable h2, ae_killedPath_eq hκ hL hR hE] with ω h hk
  rwa [hk] at h

/-- **Scaling**: the probability that a positive point is swallowed by time `T` does not depend on `T > 0`. -/
theorem measure_swalSet_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {T : ℝ≥0} (hT : T ≠ 0) :
    P {ω | (fun t => W t ω) ∈ swalSet T} = P {ω | (fun t => W t ω) ∈ swalSet 1} := by
  have hK := ZeroOne.measurable_killedPath hE.2.1
  have hdil := ZeroOne.map_dilPath_map_killedPath hκ hL hR hE hT
  have hm1 := measurableSet_swalSet 1
  rw [measure_path_eq hκ hL hR hE hm1, ← hdil, Measure.map_apply ZeroOne.measurable_dilPath hm1,
    Measure.map_apply hK (ZeroOne.measurable_dilPath hm1)]
  refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
  filter_upwards [ae_good hκ hL hR hE, ae_killedPath_eq hκ hL hR hE] with ω ⟨_, hw, hw0⟩ hk
  simp only [mem_preimage, hk]
  rw [dilPath_mem_swalSet_iff hT hw hw0, mul_one]

/-- **The hittable right seed side is swallowed at arbitrarily small times** (`κ > 4`, `r_L > −2`,
`−2 < r_R < κ/2 − 2`): almost surely, for every `T > 0` some real point `x > 0` is swallowed by time `T`. -/
theorem ae_swallowed_right [IsProbabilityMeasure P] (hκ4 : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hRc : rR < κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
  have hκ : 0 < κ := by linarith
  have hgood := ae_good hκ hL hR hE
  -- the zero–one law: a positive point is swallowed at a finite time, almost surely
  have hrs : ∀ᵐ ω ∂P, (fun t => W t ω) ∈ LP4HB.rightSet := by
    rcases ZeroOne.aux128DriverStatement κ hκ rL rR hL hR LP4HB.rightSet LP4HB.measurableSet_rightSet
      (fun c hc w hw hw0 => LP4HB.dilPath_mem_rightSet_iff hc hw hw0) P 𝓕 W VL VR B ζ hE with h | h
    · exact h
    · exfalso
      refine frequently_swallowed_right hκ4 hL hR hRc hE ?_
      filter_upwards [h, hgood] with ω hω ⟨_, hw, hw0⟩
      rwa [LP4HB.mem_rightSet_iff hw hw0] at hω
  -- swallowing by time `1` has probability one
  set A : ℕ → Set Ω := fun n => {ω | (Continuous fun t => W t ω) ∧ W 0 ω = 0 ∧
    (fun t => W t ω) ∈ swalSet ((n : ℝ≥0) + 1)} with hA
  have hAmono : Monotone A := by
    intro m n hmn ω hω
    obtain ⟨hw, hw0, hs⟩ := hω
    exact ⟨hw, hw0, swalSet_mono hw hw0 (by exact_mod_cast Nat.add_le_add_right hmn 1) hs⟩
  have hAeq : ∀ n, P (A n) = P {ω | (fun t => W t ω) ∈ swalSet 1} := fun n => by
    rw [← measure_swalSet_eq hκ hL hR hE (T := (n : ℝ≥0) + 1) (by positivity)]
    refine measure_congr (Filter.eventuallyEqSet_iff.2 ?_)
    filter_upwards [hgood] with ω ⟨_, hw, hw0⟩
    simp only [hA, mem_ofPred_eq, hw, hw0, true_and]
  have hU : ∀ᵐ ω ∂P, ω ∈ ⋃ n, A n := by
    filter_upwards [hrs, hgood] with ω hω ⟨_, hw, hw0⟩
    rw [LP4HB.mem_rightSet_iff hw hw0] at hω
    obtain ⟨x, hx, T, hT⟩ := hω
    obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
    refine mem_iUnion.2 ⟨n, hw, hw0, (mem_swalSet_iff hw hw0).2 ⟨x, hx, ?_⟩⟩
    refine LP4HB.isSwallowedBy_mono T.coe_nonneg ?_ hT
    push_cast
    linarith
  have h1 : P {ω | (fun t => W t ω) ∈ swalSet 1} = 1 := by
    have hUe : P (⋃ n, A n) = 1 := by
      rw [measure_congr (ae_eq_univ.2 (ae_iff.1 hU)), measure_univ]
    rw [hAmono.measure_iUnion] at hUe
    simp only [hAeq, ciSup_const] at hUe
    exact hUe
  -- every positive time
  have hall : ∀ n : ℕ, ∀ᵐ ω ∂P, (fun t => W t ω) ∈ swalSet ((n : ℝ≥0) + 1)⁻¹ := fun n => by
    refine ae_mem_of_measure_eq_one hκ hL hR hE (measurableSet_swalSet _) ?_
    rw [measure_swalSet_eq hκ hL hR hE (inv_ne_zero (by positivity)), h1]
  filter_upwards [ae_all_iff.2 hall, hgood] with ω hω ⟨_, hw, hw0⟩ T hT
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < T from hT)
  have hs := hω n
  rw [mem_swalSet_iff hw hw0] at hs
  obtain ⟨x, hx, hsw⟩ := hs
  refine ⟨x, hx, LP4HB.isSwallowedBy_mono (by positivity) ?_ hsw⟩
  rw [NNReal.coe_inv]
  push_cast
  rw [← one_div]
  exact hn.le

/-- **The hittable left seed side is swallowed at arbitrarily small times** (the reflection of
`ae_swallowed_right`): almost surely, for every `T > 0` some real point `x > 0` is swallowed by time `T` under the
reflected driver `−W`. -/
theorem ae_swallowed_left [IsProbabilityMeasure P] (hκ4 : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hLc : rL < κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => -W s.toNNReal ω) x T := by
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have hz : -twoSeedXR = twoSeedXL := by funext i; simp [twoSeedXR, twoSeedXL]
  have hz' : -twoSeedXL = twoSeedXR := by funext i; simp [twoSeedXR, twoSeedXL]
  rw [hz, hz'] at hEr
  simpa only [Pi.neg_apply] using ae_swallowed_right hκ4 hR hL hLc hEr

end Hit

/-! ### No return to the start, from the completeness of the two-seed word -/

/-- The tip of the Loewner chain is the value of a generating trace on `[0, ∞)`. -/
theorem loewnerTip_eq_trace {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w)
    (hw0 : w 0 = 0) (t : ℝ≥0) : loewnerTip (fun s : ℝ => w s.toNNReal) t = γ t := by
  have h := (isLoewnerTrace_of_isGeneratingTrace hγ).loewnerTip_eq (hw.comp continuous_real_toNNReal)
    (by simpa using hw0) t.coe_nonneg
  simpa using h

section NoReturn

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open Zhan ZhanGT4 Sec5.CfLineRegQ

/-- **A complete two-seed word does not return to its start** (every `κ > 0`, `r_L, r_R > −2`): if the word has a
continuous transient trace (`LP.IsCompleteForceWord`), then almost surely no trace on `[0, ∞)` vanishes at a positive
time. The scaling argument of `Sec5.CfLineRegQ.ae_trace_ne_zero_of_seed`: `P(inf_{t ≥ c} |η(t)| = 0)` does not depend
on `c > 0` (dilation and Theorem 2.2's uniqueness, `ZhanGT4.map_ratProc_eq_of_ordered`), and it tends to `0` as
`c → ∞` by transience. -/
theorem ae_trace_ne_zero_twoSeed [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hc : LP.IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR))
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → ∀ t : ℝ≥0, 0 < t → η t ≠ 0 := by
  have hF : IsOrderedForceWord twoSeedXL twoSeedXR :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := (ae_good hκ hL hR hE).mono fun _ h => h.1
  set X := ratProc ζ W with hX
  have hXm : Measurable X := measurable_ratProc hE.2.1
  -- the dilated evolutions have the same law of rational-time values
  have hlaw : ∀ c : ℝ≥0, c ≠ 0 → P.map (ratProc (fun ω => ζ ω / c) (dilProc c W)) = P.map X :=
    fun c hc => map_ratProc_eq_of_ordered hκ hF (hE.dilate_zero hc) hE
      (hζ.mono fun ω h => by simp only [h]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top) hζ
  -- the good event
  have hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ∃ ηs : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ ηs ∧
        Tendsto (fun t => ‖ηs t‖) atTop atTop := by
    filter_upwards [ae_good hκ hL hR hE, hc P 𝓕 W VL VR B ζ hE] with ω ⟨hζω, hwc, hw0⟩ ⟨ηs, hηs, htr⟩
    rw [hζω] at hηs
    exact ⟨hζω, hwc, hw0, ηs, hηs, htr hζω⟩
  -- the probability of `Z_c` does not depend on `c > 0`
  have hsc : ∀ c : ℝ≥0, c ≠ 0 → P (X ⁻¹' zeroSet c) = P (X ⁻¹' zeroSet 1) := by
    intro c hc
    set Xc := ratProc (fun ω => ζ ω / c) (dilProc c W) with hXc
    have hXcm : Measurable Xc := measurable_ratProc (hE.dilate_zero hc).2.1
    have heq : X ⁻¹' zeroSet c =ᵐ[P] Xc ⁻¹' zeroSet 1 := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩
      have hηc : Continuous ηs :=
        continuousOn_univ.1 (hηs.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      have hdil := hηs.dilate hc
      rw [ENNReal.top_div_of_ne_top ENNReal.coe_ne_top] at hdil
      have hdc : Continuous (dilPath c fun t => W t ω) :=
        continuous_const.mul (hwc.comp (continuous_const.mul continuous_id))
      have hd0 : dilPath c (fun t => W t ω) 0 = 0 := by simp [dilPath, hw0]
      have hXcω : Xc ω = fun q : ℚ≥0 => dilPath c (fun t => W t ω) q := by
        rw [hXc, ratProc_of_eq_top (ζ := fun ω => ζ ω / c) (W := dilProc c W) (ω := ω) (show ζ ω / c = ⊤ by
          rw [hζω]; exact ENNReal.top_div_of_ne_top ENNReal.coe_ne_top)]
        rfl
      have hXω : X ω = fun q : ℚ≥0 => W q ω := by rw [hX, ratProc_of_eq_top hζω]
      have hηdc : Continuous fun s : ℝ≥0 => (((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * s) :=
        continuousOn_univ.1 (hdil.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
      have e1 : X ω ∈ zeroSet c ↔ ∀ k : ℕ, ∃ q : ℚ≥0, c ≤ (q : ℝ≥0) ∧ ‖ηs q‖ < 1 / ((k : ℝ) + 1) := by
        rw [hXω]
        simp only [zeroSet, mem_iInter]
        exact forall_congr' fun k => mem_nearSet_iff hwc hw0 hηs
      have e2 : Xc ω ∈ zeroSet 1 ↔ ∀ k : ℕ, ∃ q : ℚ≥0, 1 ≤ (q : ℝ≥0) ∧
          ‖(((√(c : ℝ))⁻¹ : ℝ) : ℂ) * ηs (c * q)‖ < 1 / ((k : ℝ) + 1) := by
        rw [hXcω]
        simp only [zeroSet, mem_iInter]
        exact forall_congr' fun k => mem_nearSet_iff hdc hd0 hdil
      show X ω ∈ zeroSet c ↔ Xc ω ∈ zeroSet 1
      rw [e1, e2, forall_exists_rat_iff hηc, forall_exists_rat_iff hηdc, forall_exists_dilate_iff hc]
    rw [measure_congr heq, ← Measure.map_apply hXcm (measurableSet_zeroSet 1), hlaw c hc,
      Measure.map_apply hXm (measurableSet_zeroSet 1)]
  -- `P(Z_1) = 0`: the events `Z_{N+1}` decrease to a null event (transience)
  have hanti : Antitone fun N : ℕ => X ⁻¹' zeroSet ((N : ℝ≥0) + 1) := fun n m hnm =>
    preimage_mono (zeroSet_anti (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun N : ℕ => (hXm (measurableSet_zeroSet ((N : ℝ≥0) + 1))).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have h0 : P (⋂ N : ℕ, X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hgood] with ω ⟨hζω, hwc, hw0, ηs, hηs, htrω⟩ hmem
    obtain ⟨T, hT⟩ := eventually_atTop.1 (htrω.eventually_ge_atTop 1)
    obtain ⟨N, hN⟩ := exists_nat_ge T
    have h1 := mem_iInter.1 hmem N
    rw [mem_preimage, hX, ratProc_of_eq_top hζω] at h1
    obtain ⟨q, hq, hlt⟩ := (mem_nearSet_iff hwc hw0 hηs).1 (mem_iInter.1 h1 0)
    have hTq : T ≤ (q : ℝ≥0) := hN.trans ((le_add_of_nonneg_right zero_le).trans hq)
    have h2 := hT _ hTq
    norm_num at hlt
    linarith
  have hconst : ∀ N : ℕ, P (X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = P (X ⁻¹' zeroSet 1) :=
    fun N => hsc _ (by positivity)
  have h1 : P (X ⁻¹' zeroSet 1) = 0 := by
    have e : (⇑P ∘ fun N : ℕ => X ⁻¹' zeroSet ((N : ℝ≥0) + 1)) = fun _ => P (X ⁻¹' zeroSet 1) :=
      funext hconst
    rw [h0, e] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  -- conclusion
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, X ω ∉ zeroSet (1 / ((n : ℝ≥0) + 1)) := by
    rw [ae_all_iff]
    intro n
    have hz : P (X ⁻¹' zeroSet (1 / ((n : ℝ≥0) + 1))) = 0 := by rw [hsc _ (by positivity), h1]
    exact measure_eq_zero_iff_ae_notMem.1 hz
  filter_upwards [hgood, hall] with ω ⟨hζω, hwc, hw0, ηs, hηs, _⟩ hω η hη t ht hzero
  have hηc : Continuous ηs :=
    continuousOn_univ.1 (hηs.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηt : η t = ηs t := hη.eq_of_le hηs hwc.continuousOn hw0 le_top
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
  apply hω n
  rw [hX, ratProc_of_eq_top hζω]
  refine mem_iInter.2 fun k => (mem_nearSet_iff hwc hw0 hηs).2 ?_
  refine exists_rat_of_norm_lt hηc hn.le ?_
  rw [← hηt, hzero, norm_zero]
  positivity

/-- **The tip of a complete two-seed word does not vanish at positive times** (driving-path form of
`ae_trace_ne_zero_twoSeed`): almost surely `loewnerTip W t ≠ 0` for every `t > 0`. -/
theorem ae_tip_ne_zero_twoSeed [IsProbabilityMeasure P] (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hc : LP.IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR))
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → loewnerTip (fun s : ℝ => W s.toNNReal ω) t ≠ 0 := by
  filter_upwards [ae_trace_ne_zero_twoSeed hκ hL hR hc hE, ae_good hκ hL hR hE, hc P 𝓕 W VL VR B ζ hE]
    with ω h ⟨hζ, hw, hw0⟩ ⟨η, hη, _⟩ t ht
  rw [hζ] at hη
  rw [loewnerTip_eq_trace hη hw hw0 t]
  exact h η hη t ht

end NoReturn

end InteractingSLE.CfNoReturn.Germ
