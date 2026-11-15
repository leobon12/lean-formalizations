import InteractingSLE.Spec.Supplement.LP4HalfBall
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# LP4's straddle from one-sided swallowing, by the dilation zero–one law

Packet PROVE-LP17. Specification p. 482: "First obtain a positive-probability finite own stopping time at which the
physical leftmost and rightmost swallowed real points straddle `0` strictly. … Hence the new right extreme is
positive. Next wait for a left-seed collision and apply the reflected experiment."

The source makes the right extreme positive, then restarts and makes the left extreme negative. Here the second
restart is replaced by Aux. lemma 128 (the dilation zero–one law for two-seed driver events, landed:
`ZeroOne.aux128DriverStatement`): the event "some positive real point is swallowed at a finite time" is a measurable
dilation-invariant driver event (`rightSet`), so positive probability makes it almost sure; the reflected evolution
(`IsIntegratedSLEEvolution.reflect`, weights exchanged) does the same for the left side; together they straddle.

* `rightSet`, `measurableSet_rightSet`, `mem_rightSet_iff`, `dilPath_mem_rightSet_iff`;
* named input **`LP4RightSwallowStatement`**: for every two-seed evolution with `κ > 4`, `−2 < r_L, r_R < κ/2 − 2`,
  with positive probability some positive real point is swallowed at a finite time (a driving-only statement:
  no trace premise);
* **`lp4StraddleStatement_of_rightSwallow`**, and `lp4HalfBallStatement_of_rightSwallow`,
  `lp4Statement_of_rightSwallow` (with the stopping-time collar).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

universe u

namespace InteractingSLE.LP

/-- **Named input: one-sided swallowing with positive probability** (the right half of the first paragraph of LP4's
proof, specification p. 482: Lemma LP2 at a right-seed collision, scaling, and the bounded-energy deletion of the
separated left drift). For every two-seed evolution with `κ > 4` and `−2 < r_L, r_R < κ/2 − 2`, with positive
probability some real point `x > 0` is swallowed at a finite time. -/
def LP4RightSwallowStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 2 → -2 < rR → rR < κ / 2 - 2 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∃ᵐ ω ∂P, ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T

namespace LP4HB

/-! ### The driver event "a positive point is swallowed" -/

/-- The paths under which some positive rational point is swallowed by an integer time. -/
def rightSet : Set (ℝ≥0 → ℝ) :=
  ⋃ (q : {q : ℚ // (0 : ℝ) < q}) (n : ℕ), (LP3.aliveSet 1 ((q : ℚ) : ℝ) q.2 (n : ℝ≥0))ᶜ

theorem measurableSet_rightSet : MeasurableSet rightSet :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => (LP3.measurableSet_aliveSet _ _ _ _).compl

theorem pathDrive_one (w : ℝ≥0 → ℝ) : LP3.pathDrive 1 w = fun s : ℝ => w s.toNNReal := by
  funext s; simp [LP3.pathDrive]

/-- Swallowing is monotone in the time. -/
theorem isSwallowedBy_mono {V : ℝ → ℝ} {x T T' : ℝ} (hT : 0 ≤ T) (hTT' : T ≤ T')
    (h : ZhanGT4.IsSwallowedBy V x T) : ZhanGT4.IsSwallowedBy V x T' := fun ⟨v, hv⟩ =>
  h ⟨v, QuantumZipper.isForwardSol_restrict hv hT hTT'⟩

theorem mem_rightSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    w ∈ rightSet ↔ ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T := by
  have hWc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  constructor
  · intro h
    simp only [rightSet, mem_iUnion, mem_compl_iff] at h
    obtain ⟨q, n, hq⟩ := h
    rw [LP3.mem_aliveSet_iff hw hw0, pathDrive_one] at hq
    exact ⟨q, q.2, n, hq⟩
  · rintro ⟨x, hx, T, hT⟩
    obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn hx
    obtain ⟨n, hn⟩ := exists_nat_ge (T : ℝ)
    simp only [rightSet, mem_iUnion, mem_compl_iff]
    refine ⟨⟨q, hq0⟩, n, ?_⟩
    rw [LP3.mem_aliveSet_iff hw hw0, pathDrive_one]
    rintro ⟨v, hv⟩
    have hvT := QuantumZipper.isForwardSol_restrict hv T.coe_nonneg (by exact_mod_cast hn)
    exact hT (exists_isForwardSol_of_lt hWc T.coe_nonneg (by simpa [hw0] using hq0) hqx hvT)

/-- Scaling of swallowing: `x` is swallowed by `T` under `w` iff `x/√c` is swallowed by `T/c` under the dilation
`dilPath c w`. One direction (the other is the same with the inverse dilation). -/
theorem isSwallowedBy_dilPath_of {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} {x T : ℝ}
    (h : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T) :
    ZhanGT4.IsSwallowedBy (fun s : ℝ => Sec7.Dilation.dilPath c w s.toNNReal) (x / √(c : ℝ)) (T / c) := by
  rintro ⟨v, hv⟩
  have hc0 : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc
  have hsc : 0 < √(c : ℝ) := Real.sqrt_pos.2 hc0
  set a : ℝ := (√(c : ℝ))⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 hsc
  have hv' : IsForwardSol (fun s : ℝ => Sec7.Dilation.dilPath c w s.toNNReal) ((a * x : ℝ) : ℂ) (T / c) v := by
    have : (x / √(c : ℝ) : ℝ) = a * x := by rw [ha]; ring
    rw [← this]; exact hv
  have hv'' := LoewnerAlgebra.isForwardSol_scale (z := (x : ℂ)) ha0 (by push_cast at hv' ⊢; exact hv')
  have hS : T / c / a ^ 2 = T := by
    rw [ha, inv_pow, Real.sq_sqrt hc0.le]; field_simp
  rw [hS] at hv''
  refine h ⟨_, QuantumZipper.isForwardSol_congr_drive (fun r hr => ?_) hv''⟩
  simp only [Sec7.Dilation.dilPath]
  have hr0 : 0 ≤ r := hr.1
  have e1 : (c * (a ^ 2 * r).toNNReal : ℝ≥0) = r.toNNReal := by
    rw [← NNReal.coe_inj, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ hr0, ha, inv_pow, Real.sq_sqrt hc0.le]
    field_simp
  rw [e1, ha]
  field_simp

theorem dilPath_mem_rightSet_iff {c : ℝ≥0} (hc : c ≠ 0) {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    Sec7.Dilation.dilPath c w ∈ rightSet ↔ w ∈ rightSet := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc
  have hdc := continuous_dilPath (c := c) w hw
  have hd0 : Sec7.Dilation.dilPath c w 0 = 0 := dilPath_zero hw0
  rw [mem_rightSet_iff hdc hd0, mem_rightSet_iff hw hw0]
  constructor
  · rintro ⟨x, hx, T, hT⟩
    -- undo the dilation with `c⁻¹`
    have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
    have h := isSwallowedBy_dilPath_of hci hT
    have hdd : ∀ s : ℝ≥0, Sec7.Dilation.dilPath c⁻¹ (Sec7.Dilation.dilPath c w) s = w s := fun s => by
      simp only [Sec7.Dilation.dilPath]
      have e1 : c * (c⁻¹ * s) = s := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      rw [e1, NNReal.coe_inv, Real.sqrt_inv, inv_inv, ← mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_pos.2 hc0).ne', one_mul]
    simp only [hdd] at h
    refine ⟨x / √((c⁻¹ : ℝ≥0) : ℝ), div_pos hx (Real.sqrt_pos.2 (by positivity)),
      (T / (c⁻¹ : ℝ≥0) : ℝ).toNNReal, ?_⟩
    rw [Real.coe_toNNReal _ (div_nonneg T.coe_nonneg (by positivity))]
    exact h
  · rintro ⟨x, hx, T, hT⟩
    refine ⟨x / √(c : ℝ), div_pos hx (Real.sqrt_pos.2 hc0), (T / c : ℝ).toNNReal, ?_⟩
    rw [Real.coe_toNNReal _ (div_nonneg T.coe_nonneg hc0.le)]
    exact isSwallowedBy_dilPath_of hc hT


/-! ### Both sides from one side -/

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **One-sided swallowing is almost sure once it has positive probability** (Aux. lemma 128). -/
theorem ae_swallow_right [IsProbabilityMeasure P] (hκ : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    (hpos : ∃ᵐ ω ∂P, ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0,
      ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T) :
    ∀ᵐ ω ∂P, ∃ x : ℝ, 0 < x ∧ ∃ T : ℝ≥0, ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
  have hκ0 : 0 < κ := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) hκ0 hL hR
      Sec7.jacobiDiffusionExistsStatement hE
  have hc : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 := by
    filter_upwards [hζ, hE.2.2.2.2] with ω h1 h2
    rw [h1] at h2
    exact Sec7.IsIntegratedSLEPath.continuous_w_of_top h2
  rcases ZeroOne.aux128DriverStatement κ hκ0 rL rR hL hR rightSet measurableSet_rightSet
    (fun c hc w hw hw0 => dilPath_mem_rightSet_iff hc hw hw0) P 𝓕 W VL VR B ζ hE with h | h
  · filter_upwards [h, hc] with ω hω hcω
    exact (mem_rightSet_iff hcω.1 hcω.2).1 hω
  · exfalso
    obtain ⟨ω, hω, hnot, hcω⟩ := (hpos.and_eventually (h.and hc)).exists
    exact hnot ((mem_rightSet_iff hcω.1 hcω.2).2 hω)

/-- The reflected two-seed evolution (`(−W, −V^R, −V^L, −B)`, weights exchanged). -/
theorem reflect_twoSeed
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rR) (fun _ => rL) P 𝓕 (-W)
      (fun i => -VR i) (fun i => -VL i) (-B) ζ := by
  have h := hE.reflect
  have e1 : -twoSeedXR = twoSeedXL := by funext i; simp [twoSeedXL, twoSeedXR]
  have e2 : -twoSeedXL = twoSeedXR := by funext i; simp [twoSeedXL, twoSeedXR]
  rw [e1, e2] at h
  exact h

/-- Swallowing of `x` under `−W` is swallowing of `−x` under `W`. -/
theorem isSwallowedBy_neg {V : ℝ → ℝ} {x T : ℝ} (h : ZhanGT4.IsSwallowedBy (fun t => -V t) x T) :
    ZhanGT4.IsSwallowedBy V (-x) T := fun hal => by
  have := (LP3.alive_neg_iff (W := V) (x := -x) (T := T)).2 hal
  rw [neg_neg] at this
  exact h this

end LP4HB

/-- **The straddle from one-sided swallowing.** -/
theorem lp4StraddleStatement_of_rightSwallow (h : LP4RightSwallowStatement.{u}) : LP4StraddleStatement.{u} := by
  intro κ hκ rL rR hL hLc hR hRc _ Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hr := LP4HB.ae_swallow_right hκ hL hR hE (h κ hκ rL rR hL hLc hR hRc P 𝓕 W VL VR B ζ hE)
  have hE' := LP4HB.reflect_twoSeed hE
  have hl := LP4HB.ae_swallow_right hκ hR hL hE' (h κ hκ rR rL hR hRc hL hLc P 𝓕 _ _ _ _ ζ hE')
  refine (hr.and hl).frequently.mono ?_
  rintro ω ⟨⟨x, hx, T₁, h₁⟩, ⟨x', hx', T₂, h₂⟩⟩
  refine ⟨max T₁ T₂, -x', x, by linarith, hx, ?_, ?_⟩
  · have h₂' : ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) (-x') T₂ :=
      LP4HB.isSwallowedBy_neg (V := fun s : ℝ => W s.toNNReal ω) h₂
    exact LP4HB.isSwallowedBy_mono T₂.coe_nonneg (by exact_mod_cast le_max_right T₁ T₂) h₂'
  · exact LP4HB.isSwallowedBy_mono T₁.coe_nonneg (by exact_mod_cast le_max_left T₁ T₂) h₁

/-- **`LP4HalfBallStatement` from one-sided swallowing and the stopping-time collar.** -/
theorem lp4HalfBallStatement_of_rightSwallow
    (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ) (h : LP4RightSwallowStatement.{u}) :
    LP4HalfBallStatement.{u} :=
  lp4HalfBallStatement_of_straddle hcol (lp4StraddleStatement_of_rightSwallow h)

/-- **Proposition LP4 from one-sided swallowing and the stopping-time collar.** -/
theorem lp4Statement_of_rightSwallow (hcol : ∀ κ : ℝ, 4 < κ → ZhanGT4.StoppingCollarStatement.{u} κ)
    (h : LP4RightSwallowStatement.{u}) : LP4Statement.{u} :=
  lp4Statement_of_straddle hcol (lp4StraddleStatement_of_rightSwallow h)

end InteractingSLE.LP
