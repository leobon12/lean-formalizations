import QuantumZipper.Proofs.Zipper.LocLenR5aStmts
import QuantumZipper.Proofs.Zipper.LocLenR5cMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): the Palm regularity set with open-arc readings

Open-arc copies of `E6.gOut`, `E6.RegDet` (E6NodeReg.lean:44–58), `E6.E6PalmRegStmt`
(E6NodeAsm.lean:64), `E6.mem_regDet_of_good` (E6NodeReg.lean:60), `E6.FlowGoodStmt`,
`E6.FlowGoodAllStmt`, `E6.e6PalmGoodStmt_of_flow` (E6InReduce.lean:157–185), on top of the
open-arc local readers of R5c (`lenLocArc`, `tauLocArc`, `aLocArc`, `goodSetHitArc`,
`HitScaleGoodArc`, `conclusionsArc_of_mem`, `locRich_zipLenDownArc_congr_drive`,
`locRich_zipLenDownArc_eq_loc`; LocLenR5cRead/Drive/Main.lean). Substitution:
`zipLenDown ↦ zipLenDownArc`, `tHit ↦ lenTimeArc`, `HitScaleGood ↦ HitScaleGoodArc`.

Sources: Sheffield arXiv:1012.4797 §5.4 pp. 70–72 (locality of unzipping by quantum length);
own bookkeeping (verbatim copies).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace LocLen

open B2 E1 E6 D3Plus MeasUnzip CharFun R5c

/-- Copy of `E6.gOut` with the open-arc readers. -/
def gOutArc (γ κ ℓ : ℝ) (R T M : ℕ) : FullData → FullData := fun d =>
  outLoc (Nat.cast_nonneg T) γ κ R (Rp R T M) (pathX κ T)
    (d, tauLocArc γ κ ℓ T (Rp R T M) d, aLocArc γ κ ℓ T (Rp R T M) M d)

theorem measurable_gOutArc {γ κ ℓ : ℝ} (hκ : 0 < κ) (R T M : ℕ) :
    Measurable (gOutArc γ κ ℓ R T M) :=
  (measurable_outLoc (Nat.cast_nonneg T) γ κ R (Rp R T M) ((exists_pathExtract hκ).1 T)).comp
    (measurable_id.prodMk ((measurable_tauLocArc γ κ ℓ T (Rp R T M)).prodMk
      (measurable_aLocArc γ κ ℓ T (Rp R T M) M)))

/-- Copy of `E6.RegDet` with `zipLenDownArc` and the open-arc readers. -/
def RegDetArc (γ κ ℓ : ℝ) : Set Cfg :=
  {y | ∀ R T M : ℕ, 0 < T → locRich (Rp R T M) y ∈ goodSetHitArc γ κ ℓ R T M →
    locRich R (zipLenDownArc γ ℓ y) = gOutArc γ κ ℓ R T M (locRich (Rp R T M) y)}

/-- Open-arc copy of `E6.E6PalmRegStmt`. -/
def E6PalmRegArcStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ), E5.Setup κ T P B X ϖ →
    ∀ ℓ₁ : ℝ, 0 < ℓ₁ → ∀ᵐ ω ∂P, ∀ C x, realHitTime (Vr κ T B ω) x < ENNReal.ofReal T →
      zcC κ T B X ϖ C ω x ∈ RegDetArc (Real.sqrt κ) κ ℓ₁

/-- **Good zipper behaviour gives membership in `RegDetArc`** (copy of
`E6.mem_regDet_of_good`). -/
theorem mem_regDetArc_of_good {γ κ ℓ : ℝ} (hκ : 0 < κ) {y : Cfg} (hg : HitScaleGoodArc γ ℓ y) :
    y ∈ RegDetArc γ κ ℓ := by
  intro R T M hT0 hmem
  unfold gOutArc
  have hπ := exists_pathExtract hκ
  obtain ⟨hM, hreach, ht0, hτ, ha0, ha, hRT, hR'⟩ := conclusionsArc_of_mem hκ hT0 hg hmem
  have hcω := hg.cont
  have h0ω := hg.zero
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hTR' : (T : ℝ) ≤ (Rp R T M : ℕ) := by exact_mod_cast le_Rp R T M
  generalize Rp R T M = R' at hmem hτ ha hR' hTR' ⊢
  obtain ⟨x, W⟩ := y
  simp only at hM hreach ht0 hτ ha0 ha hRT hR' hcω h0ω ⊢
  set f := pathX κ T (locRich R' (x, W)).2 with hfdef
  set t := lenTimeArc γ ℓ (x, W) with htdef
  set a := scaleParam γ (unzippedField γ (x, W) t) with hadef
  have hWf : ∀ r ∈ Icc (0 : ℝ) T, Wof κ T hT f r = W r :=
    hπ.2 T _ W hcω fun s hs => by
      show W (min (s : ℝ) R') = W s
      rw [min_eq_left (hs.trans hTR')]
  have hWof0 : Wof κ T hT f 0 = 0 := (hWf 0 ⟨le_rfl, hT⟩).trans h0ω
  have hf : f ∈ PZ hT κ := hWof0
  have hcWof := continuous_Wof κ T hT f
  obtain ⟨hτ', hsc'⟩ := lenTimeArc_scale_congr_drive x hcω hcWof h0ω hWof0
    (fun r hr => (hWf r hr).symm) hreach
  have step1 := locRich_zipLenDownArc_congr_drive R x hcω hcWof h0ω hWof0
    (fun r hr => (hWf r hr).symm) hreach hRT
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hti : t ∈ Icc (0 : ℝ) T :=
    ⟨ht0.le, le_trans (le_add_of_nonneg_right (by positivity)) hRT⟩
  have hflow : ∀ u ∈ H, ‖u‖ ≤ a * R + 3 → ‖fwdMapInv (Wof κ T hT f) t u‖ + 3 ≤ R' := by
    intro u hu hub
    have hb := B5.norm_fwdMapInv_sub_le hcWof hWof0 ht0 (M := (M : ℝ)) (fun r hr => by
      rw [hWf r ⟨hr.1, hr.2.trans hti.2⟩]; exact hM r ⟨hr.1, hr.2.trans hti.2⟩) hu
    have h1 := norm_sub_norm_le (fwdMapInv (Wof κ T hT f) t u) u
    have h2 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt hti.2
    linarith
  rw [step1, locRich_zipLenDownArc_eq_loc hT hf x hτ' hti hsc' ha0 hflow]
  rw [hτ, ha]
  rfl

variable {Ω : Type} [MeasurableSpace Ω]

/-- Open-arc copy of `E6.FlowGoodStmt`. -/
def FlowGoodArcStmt (κ T ℓ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ u k : ℝ, 0 ≤ u → u ≤ T →
    HitScaleGoodArc (Real.sqrt κ) ℓ (canonConfig (Real.sqrt κ)
      (addConst (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).1 k,
        (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2))

/-- Open-arc copy of `E6.FlowGoodAllStmt`. -/
def FlowGoodArcAllStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → 0 < T →
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ ℓ : ℝ, 0 < ℓ → FlowGoodArcStmt κ T ℓ P B X

/-- **`E6PalmRegArcStmt` from the flow statement** (copy of `E6.e6PalmGoodStmt_of_flow` and
`E6.e6PalmRegStmt_of_good`). -/
theorem e6PalmRegArc_of_flow (h : FlowGoodArcAllStmt) : E6PalmRegArcStmt := by
  intro κ T Ω _ P _ B X ϖ hS ℓ₁ hℓ
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := hS
  filter_upwards [h κ T P B X hκ hκ4 hT hB hX hind ℓ₁ hℓ] with ω hω C x hx
  have hτ : (realHitTime (Vr κ T B ω) x).toReal < T := ENNReal.toReal_lt_of_lt_ofReal hx
  have hτ0 : 0 ≤ (realHitTime (Vr κ T B ω) x).toReal := ENNReal.toReal_nonneg
  exact mem_regDetArc_of_good hκ (hω (T - (realHitTime (Vr κ T B ω) x).toReal)
    (-(mReg κ T B X ϖ ω) + C / Real.sqrt κ) (by linarith) (by linarith))

end LocLen
end QuantumZipper
