import QuantumZipper.Proofs.Zipper.LocLenR5aStmts
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.E6Id
import QuantumZipper.Proofs.Zipper.LocLenBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5b (D75): E6-ID with open-arc lengths

Copies of `E6.e6_id_raw_of_len` and `E6.e6_idLoc_rich` (LocRichId.lean) with
`unzipLengths ↦ unzipLengthsArc`, `zipLenDown ↦ zipLenDownArc`, from the open-arc inputs
`LenCollidedArcStmt` and `CanonZipRawArcStmt` (LocLenR5aStmts.lean). The only change in the proof:
the open-arc length identity (masses of `Ioo`) is turned into the closed one (masses of `Icc`)
because the boundary measure `ν₀` of the fixed-time field `h0f` has no atoms a.s.
(`B5.ae_nu0_regular`). Sheffield arXiv:1012.4797, §5.4, pp. 70–72; B-P arXiv:2404.16642
Prop 8.20.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.LocLen

open B2 E1 D3Plus E6

variable {Ω : Type} [MeasurableSpace Ω]

/-- The open-arc E6-ID length identity with closed intervals (no atoms of `ν₀`). -/
theorem lenCollidedArc_Icc {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hLen : LenCollidedArcStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T →
      (unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)) s).1 =
        qBoundaryMeasure (Real.sqrt κ) (h0f κ T B X ω)
          (Icc (zeroMinus (Vr κ T B ω) (T - u)) (zeroMinus (Vr κ T B ω) (T - u - s))) := by
  filter_upwards [hLen, B5.ae_nu0_regular RevCouplingReg.revCouplingBoundaryMeasureRegular
    hκ hκ4 hT hB hX hind] with ω h hν u s hu hs hus
  rw [h u s hu hs hus, measure_Icc_eq_Ioo_of_noAtoms (hν.1 _) (hν.1 _)]

/-- Copy of `E6.e6_id_raw_of_len` (LocRichId.lean:62) with open-arc lengths. -/
theorem e6_id_raw_of_lenArc {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (ϖ : Measure ℂ) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hLen : LenCollidedArcStmt κ T P B X) (hCZ : CanonZipRawArcStmt κ T P B X)
    (δ ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁) :
    ∀ᵐ ω ∂P, ∀ C x y, x ∈ Icc (-δ) 0 → realHitTime (Vr κ T B ω) y < ENNReal.ofReal T →
      -δ - 1 < y → y ≤ x →
      nuPalm κ T B X ϖ ω (Icc y x) = ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2)) →
      RawEq (zcC κ T B X ϖ C ω x) (zipLenDownArc (Real.sqrt κ) ℓ₁ (zcC κ T B X ϖ C ω y)) := by
  have hReg := RevCouplingReg.revCouplingBoundaryMeasureRegular
  have hRSS := RS.rohdeSchrammSimple
  filter_upwards [lenCollidedArc_Icc hκ hκ4 hT hB hX hind hLen, hCZ,
    B5.ae_nu0_regular hReg hκ hκ4 hT hB hX hind,
    B5.ae_zeroMinus_Vr_facts hRSS hκ hκ4.le hT P B hB,
    ae_nuPalm_eq_smul (κ := κ) hB hX hind hT.le ϖ] with ω hLenω hCZω hν0 hzm hsm
  intro C x y hx hy _ hyx hνyx
  obtain ⟨-, -, hanti, -, hspec, hlt⟩ := hzm
  set γ := Real.sqrt κ with hγ
  have hγ0 : γ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  set V := Vr κ T B ω
  set ν0 := qBoundaryMeasure γ (h0f κ T B X ω)
  have hfin0 : ∀ a b, ν0 (Icc a b) ≠ ∞ := fun a b => (hν0.2.2 a b).ne
  have hay : zeroMinus V T < y := (hlt y (hyx.trans hx.2)).1 hy
  obtain ⟨-, hτx, hzx⟩ := hspec x ⟨hay.trans_le hyx, hx.2⟩
  obtain ⟨-, hτy, hzy⟩ := hspec y ⟨hay, hyx.trans hx.2⟩
  set τx := (realHitTime V x).toReal with hτxd
  set τy := (realHitTime V y).toReal with hτyd
  have hτle : τx ≤ τy := by
    by_contra h
    push Not at h
    have := hanti hτy hτx h
    rw [hzx, hzy] at this
    linarith
  set u := T - τy with hu
  set t₀ := τy - τx with ht₀
  set k := -(mReg κ T B X ϖ ω) + C / γ with hk
  -- the left length unzipped from `C̄_y`
  have hLu : ∀ s, 0 ≤ s → u + s ≤ T → (unzipLengthsArc γ (zipCapDown γ u (cfg κ B X ω)) s).1 =
      ν0 (Icc (zeroMinus V (T - u)) (zeroMinus V (T - u - s))) :=
    fun s hs hus => hLenω u s (by linarith [hτy.2]) hs hus
  set c := ENNReal.ofReal (Real.exp (γ * k / 2))
  have hc : c = ENNReal.ofReal (Real.exp (γ * -(mReg κ T B X ϖ ω) / 2)) *
      ENNReal.ofReal (Real.exp (C / 2)) := by
    show ENNReal.ofReal (Real.exp (γ * k / 2)) = _
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    rw [hk]; field_simp
  have hsInf : sInf {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal ℓ₁ ≤
      c * (unzipLengthsArc γ (zipCapDown γ u (cfg κ B X ω)) s).1} = t₀ := by
    refine e6id_sInf_eq (ν := c • ν0) (zm := zeroMinus V) (T := T) ?_ ?_ hanti hτx hτy hzx hzy
      hτle ?_ ?_
    · intro a b hab
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hν0.2.1 a b hab).ne'
    · intro a b
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin0 a b)
    · intro s hs
      rw [Measure.smul_apply, smul_eq_mul]
      have := hLu s hs.1 (by linarith [hs.2, hτx.1])
      rw [this, show T - u = τy by ring, show τy - s = τy - s from rfl, hzy]
    · rw [Measure.smul_apply, smul_eq_mul, hc, mul_comm (ENNReal.ofReal _), mul_assoc,
        ← smul_eq_mul (a := ENNReal.ofReal (Real.exp (γ * -(mReg κ T B X ϖ ω) / 2))),
        ← Measure.smul_apply, ← hsm, hνyx, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [mul_left_comm, ← Real.exp_add, show C / 2 + -C / 2 = 0 by ring, Real.exp_zero, mul_one]
  have key := hCZω u t₀ k ℓ₁ (by linarith [hτy.2]) (by linarith) (by linarith [hτx.1]) hℓ₁
    hsInf.symm
  rw [show u + t₀ = T - τx by ring] at key
  exact Eq.symm key

/-- **The identity input `hIdLoc` of `e6_concrete_gen D3Plus.locRich`**, from the length part of
E6-ID (`LenCollidedStmt`) and the raw zip algebra. -/
theorem e6_idLoc_richArc {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (ϖ : Measure ℂ) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hLen : LenCollidedArcStmt κ T P B X) (hCZ : CanonZipRawArcStmt κ T P B X)
    (δ ℓ₁ : ℝ) (hℓ₁ : 0 < ℓ₁) :
    ∀ᵐ ω ∂P, ∀ C x y, x ∈ Icc (-δ) 0 → realHitTime (Vr κ T B ω) y < ENNReal.ofReal T →
      -δ - 1 < y → y ≤ x →
      nuPalm κ T B X ϖ ω (Icc y x) = ENNReal.ofReal (ℓ₁ * Real.exp (-C / 2)) →
      ∀ R, locRich R (zcC κ T B X ϖ C ω x) =
        locRich R (zipLenDownArc (Real.sqrt κ) ℓ₁ (zcC κ T B X ϖ C ω y)) := by
  filter_upwards [e6_id_raw_of_lenArc ϖ hκ hκ4 hT hB hX hind hLen hCZ δ ℓ₁ hℓ₁] with ω h
  intro C x y hx hy hy1 hyx hlen R
  exact locRich_congr (h C x y hx hy hy1 hyx hlen) R
end QuantumZipper.LocLen
