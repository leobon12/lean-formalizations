import QuantumZipper.Proofs.Zipper.E5HW0Zeta
import QuantumZipper.Proofs.Zipper.E5ESM6

/-!
# E5-HW0, part 2: measurability of the Palm density `w0` on the level space

Task E5-HW0 (Theorem 1.3, node E5). `E5.e5_esm_model` (`E5ESM7`) takes the hypothesis `hw0`
(measurability of `z ↦ w0 κ T B X ϖ δ z.1 (ofCompl P z.2)` on the level space
`ℝ≥0 × NullMeasurableSpace Ω P`, `w0 = e^ℓ e^{−γm/2} 1{ℓ < L⁻_T, −δ ≤ x(ℓ)}`, `E5ESM5`). Here it is
reduced to its two ingredients:

* `xLm` / `measurable_xLm`: the measurable surrogate of the Palm point `x(ℓ) = 0₋(T − T_ℓ)` (the
  rational infimum `zetaHatS` read at the level time `T − T_ℓ`); it equals `xL` at every sample
  where the `0₋` facts of `Wire2.ae_zeroMinus_Vr_facts` hold (`E5HW0Zeta`), which is used in
  `E5HW0Ver` for a version of `B` that is good at every sample.
* `measurable_w0_level_of`: the literal `hw0` follows from the two named inputs
  `Measurable (z ↦ mReg _ (ofCompl z.2))` and `Measurable (z ↦ xL κ T B X z.1 (ofCompl z.2))`
  (the level measurability of `lenA`, i.e. of the event `ℓ < L⁻_T`, is discharged here from the
  E-SM adaptedness input `measurable_lenA_compl_e5`).
* `palmTau_xL_eq_of`: at the level point the collision time is the level time,
  `τ_{x(ℓ)} = T − T_ℓ`, at every sample where the `0₋` facts hold — the level analogue of the `tauS` surrogate of `E5JointMeasCore`
  (`x ↦ τ_x` is only a.e.-measurable at fixed `x`, but at the *level* point the collision time is
  the measurable level time).

Measurability of `mReg` is supplied in `E5HW0Ver` (`aemeasurable_mReg`).

Sources: own elementary measure-theoretic arguments; the facts are the repository's
Rohde–Schramm simple-curve input (`Wire2.ae_zeroMinus_Vr_facts`); Sheffield, arXiv:1012.4797, §5.4,
does not discuss measurability.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **The level surrogate of the Palm point** `x(ℓ) = 0₋(T − T_ℓ)`: the rational infimum
surrogate `zetaHatS`, read at the level time `T − T_ℓ(ℓ, ω)`. -/
def xLm (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (g : ℚ → ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞)
    (z : ℝ≥0 × NullMeasurableSpace Ω P) : ℝ :=
  zetaHatS g z (T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ))

/-- The level time `(ℓ, ω) ↦ T_ℓ(ℓ, ω)` is measurable on the level space. -/
theorem measurable_levelTime_level (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) :
    Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P =>
      levelTime (lenA κ T B X) T.toNNReal p.1 (ofCompl P p.2) :=
  measurable_levelTime_uncurry (A := lenA κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P))
    (continuous_lenA hT.le) (monotone_lenA hT.le)
    (fun s => measurable_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc s) T.toNNReal

/-- **The level surrogate `xLm` is measurable** on the level space. -/
theorem measurable_xLm (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hBc : ∀ ω, Continuous (B · ω))
    {g : ℚ → ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞} (hg : ∀ q : ℚ, Measurable (g q)) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => xLm κ T B X P g z := by
  have hs : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      T - ((levelTime (lenA κ T B X) T.toNNReal z.1 (ofCompl P z.2) : ℝ≥0) : ℝ) :=
    measurable_const.sub
      (NNReal.continuous_coe.measurable.comp (measurable_levelTime_level hκ hκ4 hT hB hX hind hBc))
  exact (measurable_zetaHatS hg).comp (measurable_id.prodMk hs)

/-- **`hw0` from its named inputs**: if the Palm point is measurable on the level space and a
measurable version of `mReg` is available there, the Palm density is measurable. -/
theorem measurable_w0_level_of (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hBc : ∀ ω, Continuous (B · ω))
    (hm : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => E1.mReg κ T B X ϖ (ofCompl P z.2))
    (hx : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => xL κ T B X z.1 (ofCompl P z.2))
    (δ : ℝ) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => w0 κ T B X ϖ δ z.1 (ofCompl P z.2) := by
  have hlen : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      lenA κ T B X T.toNNReal (ofCompl P z.2) :=
    (measurable_lenA_compl_e5 hκ hκ4 hT hB hX hind hBc T.toNNReal).comp measurable_snd
  have hset : MeasurableSet {z : ℝ≥0 × NullMeasurableSpace Ω P |
      (z.1 : ℝ≥0∞) < lenA κ T B X T.toNNReal (ofCompl P z.2) ∧
        -δ ≤ xL κ T B X z.1 (ofCompl P z.2)} :=
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_fst) hlen).inter
      (measurableSet_le measurable_const hx)
  refine Measurable.mul (ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp (NNReal.continuous_coe.measurable.comp measurable_fst)))
    (Measurable.mul ?_ ?_)
  · exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.mul hm.neg).div_const 2))
  · exact measurable_const.indicator hset

/-- **The collision time at the level point is the level time** (pointwise form). At a sample
whose reversed driver satisfies the `0₋` facts of `Wire2.ae_zeroMinus_Vr_facts` and has a simple
curve hull, for every level `ℓ`, `τ_{x(ℓ)} = T − T_ℓ`: `x(ℓ) = 0₋(T − T_ℓ)` is the left end of the
swallowed interval at time `T − T_ℓ`, and the hitting time of that left end is the time itself. -/
theorem palmTau_xL_eq_of {κ T : ℝ} (hT : 0 < T) {ω : Ω} (hBcω : Continuous (B · ω))
    (hω : zeroMinus (Vr κ T B ω) 0 = 0 ∧ zeroMinus (Vr κ T B ω) T < 0 ∧
      StrictAntiOn (zeroMinus (Vr κ T B ω)) (Icc 0 T) ∧
      ContinuousOn (zeroMinus (Vr κ T B ω)) (Icc 0 T) ∧
      (∀ x ∈ Ioc (zeroMinus (Vr κ T B ω) T) 0,
        realHitTime (Vr κ T B ω) x = ENNReal.ofReal (realHitTime (Vr κ T B ω) x).toReal ∧
          (realHitTime (Vr κ T B ω) x).toReal ∈ Icc 0 T ∧
          zeroMinus (Vr κ T B ω) (realHitTime (Vr κ T B ω) x).toReal = x) ∧
      (∀ x ≤ 0, realHitTime (Vr κ T B ω) x < ENNReal.ofReal T ↔
        zeroMinus (Vr κ T B ω) T < x))
    (hKω : IsSimpleCurveHull (revHull (Vr κ T B ω) T)) (ℓ : ℝ≥0) :
    palmTau κ T B ω (xL κ T B X ℓ ω) =
      T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ) := by
  obtain ⟨hZ0, hZT, hSA, -, hspec, hiffT⟩ := hω
  have hWc : Continuous fun s : ℝ => Vr κ T B ω s :=
    B2.continuous_vrev (Thm14FromThm13.continuous_drive hBcω) T
  have hW0 : (fun s : ℝ => Vr κ T B ω s) 0 = 0 := B2.vrev_zero hT.le
  -- the hitting time of the threshold itself is the threshold
  have hkey : ∀ s ∈ Icc 0 T, (realHitTime (fun s : ℝ => Vr κ T B ω s)
      (zeroMinus (fun s : ℝ => Vr κ T B ω s) s)).toReal = s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · -- `s = 0`: the tip is hit at time `0`
      have hτ0 : realHitTime (fun s : ℝ => Vr κ T B ω s) 0 = 0 := by
        rw [Collision.realHitTime_eq_iSup_rat]
        refine le_antisymm (iSup_le fun q => ?_) bot_le
        by_cases hq : (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, IsRealRevSol
            (fun s : ℝ => Vr κ T B ω s) 0 (q : ℝ) u
        · rw [if_pos hq]
          exact absurd (CaraR.zero_mem_swallowedSet hW0 hq.1)
            (CaraR.not_mem_swallowedSet_iff.2 hq.2)
        · rw [if_neg hq]
      rw [← h0, show zeroMinus (fun s : ℝ => Vr κ T B ω s) 0 = 0 from hZ0, hτ0]
      simp
    · -- `s > 0`: `0₋(s)` is the left end of the swallowed interval, so it is swallowed at `s`
      have hKs : IsSimpleCurveHull (revHull (fun s : ℝ => Vr κ T B ω s) s) :=
        B5.isSimpleCurveHull_of_le hWc hW0 hT hKω h0 hs.2
      obtain ⟨hzs, b, hb0, hS⟩ := B5.swallowedSet_eq_Icc_zeroMinus hWc hW0 h0 hKs
      have hmem : zeroMinus (fun s : ℝ => Vr κ T B ω s) s ∈
          CaraR.swallowedSet (fun s : ℝ => Vr κ T B ω s) s := by
        rw [hS]; exact ⟨le_rfl, hzs.le.trans hb0⟩
      -- upper bound: the rational decomposition of `realHitTime`
      have hle : realHitTime (fun s : ℝ => Vr κ T B ω s)
          (zeroMinus (fun s : ℝ => Vr κ T B ω s) s) ≤ ENNReal.ofReal s := by
        rw [Collision.realHitTime_eq_iSup_rat]
        refine iSup_le fun q => ?_
        by_cases hq : (0 : ℝ) ≤ (q : ℝ) ∧ ∃ u, IsRealRevSol
            (fun s : ℝ => Vr κ T B ω s) (zeroMinus (fun s : ℝ => Vr κ T B ω s) s) (q : ℝ) u
        · rw [if_pos hq]
          have hqs : (q : ℝ) ≤ s := by
            by_contra hlt
            push Not at hlt
            exact absurd hmem (CaraR.not_mem_swallowedSet_of_time_le hlt.le
              (CaraR.not_mem_swallowedSet_iff.2 hq.2))
          exact ENNReal.ofReal_le_ofReal hqs
        · rw [if_neg hq]
          exact bot_le
      rcases eq_or_lt_of_le hs.2 with hsT | hsT
      · -- `s = T`: lower bound from the threshold identity at time `T`
        have hge : ENNReal.ofReal s ≤ realHitTime (fun s : ℝ => Vr κ T B ω s)
            (zeroMinus (fun s : ℝ => Vr κ T B ω s) s) := by
          refine not_lt.1 fun h => ?_
          rw [hsT] at h
          have := (hiffT _ (hsT ▸ hzs.le)).1 h
          exact lt_irrefl _ this
        rw [le_antisymm hle hge, ENNReal.toReal_ofReal hs.1]
      · -- `s < T`: `0₋(s)` lies in the collision region, invert `0₋`
        have hx : zeroMinus (Vr κ T B ω) s ∈ Ioc (zeroMinus (Vr κ T B ω) T) 0 :=
          ⟨hSA ⟨hs.1, hs.2⟩ ⟨hT.le, le_rfl⟩ hsT, hzs.le⟩
        obtain ⟨-, hI, hZ⟩ := hspec _ hx
        exact hSA.injOn hI hs hZ
  have hs : T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ) ∈ Icc 0 T := by
    refine ⟨?_, sub_le_self _ (by positivity)⟩
    rw [sub_nonneg]
    refine (NNReal.coe_le_coe.2 (levelTime_le (continuous_lenA hT.le) (monotone_lenA hT.le)
      T.toNNReal ℓ ω)).trans ?_
    exact (Real.coe_toNNReal T hT.le).le
  simp only [palmTau, xL]
  exact hkey _ hs

end E5
end QuantumZipper
