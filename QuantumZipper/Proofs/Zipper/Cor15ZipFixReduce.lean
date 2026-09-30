import QuantumZipper.Proofs.Zipper.Cor15ZipFixBasic
import QuantumZipper.Proofs.Zipper.Cor15Markov2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D42 (COR15-ZIPFIX): the zip side of the D35 core modulo additive constants, and Corollary 1.5

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18),
Theorems 1.3–1.4 and §1.4: the zipped field is a free field plus `𝔥₀` **modulo additive
constants** only.

**Why the D35 zip nodes had to be restated.** `Cor15ZipOntoStmt`, `Cor15GenuineStmt`,
`Cor15ZipGenuineStmt`, `Cor15ZipVersionStmt` and `Cor15ZipVerLawStmt` are false as stated: they
ask for a genuine `(𝔥₀ + X', √κ B')` with `X'` (constant included) independent of the whole new
driver `B'`, but the constant of the zipped field is a function of the zipped driver segment
`B'|[0,a]` (take `X` normalized at a dyadic folded circle `σ₀`; matching the circle averages at
`σ₀` forces `evalReg X' (σ₀.map F_b) = G(b)` a.s. with `F_b = fwdMapInv (drive b) a`, and
independence, Fubini and the positive Neumann energy of `σ₀.map F_{b₁} − σ₀.map F_{b₂}` give a
contradiction). The unzip side (`Cor15MarkovStmt`, proved) is not affected.

**Restated nodes** (primed): the zip side holds modulo a random additive constant `lam`,
recorded with `ConfigEqC` (`Cor15ZipFixBasic`):

* `Cor15ZipGenuineStmt'`: `U_a c ∼_{lam} g'` for a genuine `g'`;
* `Cor15ZipOntoStmt'`: `D_a g'' ∼_{lam} c` for a genuine `g''`;
* `Cor15ShiftGoodStmt`: the a.s. good set on which `U_t`, `D_t` commute with additive constants
  (`CCGood` at a genuine `g` for `D_t` and for `U_0`, and at `D_t g` for `U_t`).

**Group algebra** (`grp_zipZip'`, `grp_mix'`, `grp_unzipZip'`): as in `Cor15GrpReduce`, with the
offset carried along; two configurations with the same offset to a third are `ConfigEq`, so the
random constant cancels. The old nodes imply the new ones (`lam = 0`), so this is a weakening.

Own bookkeeping (the paper gives no proof of Corollary 1.5).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

/-! ## The restated nodes -/

/-- **Zipped configuration is genuine modulo a random additive constant.** -/
def Cor15ZipGenuineStmt' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ (B' : ℝ≥0 → Ω → ℝ) (X' : Ω → FieldSample) (lam : Ω → ℝ),
      IsGrpSetup P B' X' ∧
      ∀ᵐ ω ∂P, ConfigEqC (zipCapUp (Real.sqrt κ) a (grpCfg κ B X ω)) (grpCfg κ B' X' ω) (lam ω)

/-- **Every genuine configuration is an unzipping, modulo a random additive constant.** -/
def Cor15ZipOntoStmt' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ (B' : ℝ≥0 → Ω → ℝ) (X' : Ω → FieldSample) (lam : Ω → ℝ),
      IsGrpSetup P B' X' ∧
      ∀ᵐ ω ∂P, ConfigEqC (zipCapDown (Real.sqrt κ) a (grpCfg κ B' X' ω)) (grpCfg κ B X ω) (lam ω)

/-- **The restated D35 core** (D42). -/
def Cor15GenuineStmt' : Prop := Cor15MarkovStmt ∧ Cor15ZipOntoStmt'

/-- **A.s. good set for shift-equivariance** of the capacity zipper at a genuine setup: `U_0` and
`D_t` at the genuine configuration, and `U_t` at its unzipping `D_t c` (`CCGood`: integrability
and convergence of the regularized averages against the pushed dyadic folded circles, and
convergence of the raw circle averages of the output). -/
def Cor15ShiftGoodStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    (∀ᵐ ω ∂P, CCGood (grpCfg κ B X ω).1
      (revMapInv (weldDriver (Real.sqrt κ) (grpCfg κ B X ω).1 0) 0) (Qc (Real.sqrt κ))) ∧
    ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P,
      CCGood (grpCfg κ B X ω).1 (fwdMapInv (grpCfg κ B X ω).2 t) (Qc (Real.sqrt κ)) ∧
      CCGood (zipCapDown (Real.sqrt κ) t (grpCfg κ B X ω)).1
        (revMapInv (weldDriver (Real.sqrt κ) (zipCapDown (Real.sqrt κ) t (grpCfg κ B X ω)).1 t) t)
        (Qc (Real.sqrt κ))

/-- **Onto (restated) from the zip node, the round trip `D_a U_a c ≈ c` and the good set**:
`U_a c ∼_{lam} g'` gives `D_a U_a c ∼_{lam} D_a g'` (good set at the genuine `g'`), and
`D_a U_a c ≈ c`. -/
theorem cor15ZipOntoStmt'_of (hSG : Cor15ShiftGoodStmt) (h1 : Cor15UnzipZipSelfStmt)
    (h2 : Cor15ZipGenuineStmt') : Cor15ZipOntoStmt' := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨B', X', lam, hS', e⟩ := h2 κ hκ hκ4 P B X hS a ha
  refine ⟨B', X', fun ω => -lam ω, hS', ?_⟩
  filter_upwards [e, h1 κ hκ hκ4 P B X hS a ha, (hSG κ hκ hκ4 P B' X' hS').2 a ha] with
    ω e1 r1 g1
  exact (zipCapDown_configEqC (γ := Real.sqrt κ) ha.le e1 g1.1).symm.of_configEq_right r1

/-! ## Group algebra with the offset carried along -/

/-- Zipping a configuration that is offset from an unzipping `D_t g` for which the round trip
holds. -/
theorem zipCapUp_of_eqC_down {γ t m : ℝ} {x g : FieldSample × (ℝ → ℝ)}
    (h : ConfigEqC x (zipCapDown γ t g) m)
    (hg : CCGood (zipCapDown γ t g).1 (revMapInv (weldDriver γ (zipCapDown γ t g).1 t) t) (Qc γ))
    (r : ConfigEq (zipCapUp γ t (zipCapDown γ t g)) g) : ConfigEqC (zipCapUp γ t x) g m :=
  (zipCapUp_configEqC h hg).of_configEq_right r

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- From the restated onto node: `D_t g₁ ∼_{lam} c` and `U_t c ∼_{−lam} g₁`. -/
theorem grp_onto_up' (h13 : theorem1_3) (hOn : Cor15ZipOntoStmt') (hSG : Cor15ShiftGoodStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X) {t : ℝ} (ht : 0 < t) :
    ∃ (B1 : ℝ≥0 → Ω → ℝ) (X1 : Ω → FieldSample) (lam : Ω → ℝ), IsGrpSetup P B1 X1 ∧
      ∀ᵐ ω ∂P, ConfigEqC (zipCapDown (Real.sqrt κ) t (grpCfg κ B1 X1 ω)) (grpCfg κ B X ω) (lam ω) ∧
        ConfigEqC (zipCapUp (Real.sqrt κ) t (grpCfg κ B X ω)) (grpCfg κ B1 X1 ω) (-lam ω) := by
  obtain ⟨B1, X1, lam, hS1, e⟩ := hOn κ hκ hκ4 P B X hS t ht
  refine ⟨B1, X1, lam, hS1, ?_⟩
  filter_upwards [e, grp_roundTrip h13 hκ hκ4 hS1 ht, (hSG κ hκ hκ4 P B1 X1 hS1).2 t ht] with
    ω e1 r1 g1
  exact ⟨e1, zipCapUp_of_eqC_down e1.symm g1.2 r1⟩

/-- **Zipping semigroup** `U_{s+t} c ≈ U_s (U_t c)` (`s ≥ 0`, `t > 0`), restated core. -/
theorem grp_zipZip' (h13 : theorem1_3) (hMk : Cor15MarkovStmt) (hOn : Cor15ZipOntoStmt')
    (hSG : Cor15ShiftGoodStmt) (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq (zipCapUp (Real.sqrt κ) (s + t) (grpCfg κ B X ω))
      (zipCapUp (Real.sqrt κ) s (zipCapUp (Real.sqrt κ) t (grpCfg κ B X ω))) := by
  rcases hs.lt_or_eq with hs | hs0
  · obtain ⟨B1, X1, lam, hS1, hc1⟩ := hOn κ hκ hκ4 P B X hS (s + t) (by linarith)
    obtain ⟨B2, X2, hS2, hc2⟩ := hMk κ hκ hκ4 P B1 X1 hS1 s hs
    filter_upwards [hc1, hc2, grp_roundTrip h13 hκ hκ4 hS1 (show 0 < s + t by linarith),
      grp_roundTrip h13 hκ hκ4 hS1 hs, grp_roundTrip h13 hκ hκ4 hS2 ht,
      grp_unzipSemigroup (κ := κ) hS1 hs ht,
      (hSG κ hκ hκ4 P B1 X1 hS1).2 (s + t) (by linarith), (hSG κ hκ hκ4 P B1 X1 hS1).2 s hs,
      (hSG κ hκ hκ4 P B2 X2 hS2).2 t ht] with ω e1 e2 r1 r1s r2 k1 G1 G1s G2
    rw [zipCapDown_congr_grpEq (γ := Real.sqrt κ) (t := t) ht.le e2] at k1
    have hc : ConfigEqC (grpCfg κ B X ω) (zipCapDown (Real.sqrt κ) t (grpCfg κ B2 X2 ω))
        (-lam ω) := e1.symm.of_configEq_right k1
    have hA := zipCapUp_of_eqC_down e1.symm G1.2 r1
    have hUt : ConfigEqC (zipCapUp (Real.sqrt κ) t (grpCfg κ B X ω))
        (zipCapDown (Real.sqrt κ) s (grpCfg κ B1 X1 ω)) (-lam ω) :=
      (zipCapUp_of_eqC_down hc G2.2 r2).of_configEq_right (grpEq_symm e2)
    exact hA.configEq_of_same (zipCapUp_of_eqC_down hUt G1s.2 r1s)
  · subst hs0
    obtain ⟨B1, X1, lam, hS1, hU⟩ := grp_onto_up' h13 hOn hSG hκ hκ4 hS ht
    filter_upwards [hU, grp_zipZero (κ := κ) hS1, (hSG κ hκ hκ4 P B1 X1 hS1).1] with
      ω u1 z1 G0
    rw [zero_add]
    exact u1.2.configEq_of_same ((zipCapUp_configEqC u1.2 G0).of_configEq_right z1)

/-- **Zipping an unzipped configuration** `Z_{s−a} c ≈ U_s (D_a c)` (`s, a > 0`, `s ≠ a`). -/
theorem grp_mix' (h13 : theorem1_3) (hMk : Cor15MarkovStmt) (hOn : Cor15ZipOntoStmt')
    (hSG : Cor15ShiftGoodStmt) (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X) {s a : ℝ}
    (hs : 0 < s) (ha : 0 < a) (hsa : s ≠ a) :
    ∀ᵐ ω ∂P, ConfigEq (zipCap (Real.sqrt κ) (s - a) (grpCfg κ B X ω))
      (zipCapUp (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) := by
  rcases lt_or_gt_of_ne hsa with hlt | hgt
  · obtain ⟨B1, X1, hS1, e⟩ := hMk κ hκ hκ4 P B X hS (a - s) (by linarith)
    filter_upwards [e, grp_unzipSemigroup (κ := κ) hS (show 0 < a - s by linarith) hs,
      grp_roundTrip h13 hκ hκ4 hS1 hs] with ω e1 k1 r1
    rw [show a - s + s = a by ring,
      zipCapDown_congr_grpEq (γ := Real.sqrt κ) (t := s) hs.le e1] at k1
    rw [zipCap_of_neg (show s - a < 0 by linarith), show -(s - a) = a - s by ring,
      zipCapUp_congr_configEq (γ := Real.sqrt κ) (t := s) k1]
    exact grpEq_trans e1 (grpEq_symm r1)
  · obtain ⟨B1, X1, hS1, e⟩ := hMk κ hκ hκ4 P B X hS a ha
    filter_upwards [e, grp_roundTrip h13 hκ hκ4 hS ha,
      grp_zipZip' h13 hMk hOn hSG hκ hκ4 hS1 (show 0 ≤ s - a by linarith) ha] with ω e1 r1 z1
    rw [zipCapUp_congr_configEq (γ := Real.sqrt κ) (t := a) e1] at r1
    rw [show s - a + a = s by ring] at z1
    rw [zipCap_of_nonneg (show 0 ≤ s - a by linarith),
      zipCapUp_congr_configEq (γ := Real.sqrt κ) (t := s) e1,
      ← zipCapUp_congr_configEq (γ := Real.sqrt κ) (t := s - a) r1]
    exact grpEq_symm z1

/-- **Unzipping a zipped configuration** `Z_{t−b} c ≈ D_b (U_t c)` (`b, t > 0`). -/
theorem grp_unzipZip' (h13 : theorem1_3) (hMk : Cor15MarkovStmt) (hOn : Cor15ZipOntoStmt')
    (hSG : Cor15ShiftGoodStmt) (hκ : 0 < κ) (hκ4 : κ < 4) (hS : IsGrpSetup P B X) {b t : ℝ}
    (hb : 0 < b) (ht : 0 < t) :
    ∀ᵐ ω ∂P, ConfigEq (zipCap (Real.sqrt κ) (t - b) (grpCfg κ B X ω))
      (zipCapDown (Real.sqrt κ) b (zipCapUp (Real.sqrt κ) t (grpCfg κ B X ω))) := by
  obtain ⟨B1, X1, lam, hS1, hU⟩ := grp_onto_up' h13 hOn hSG hκ hκ4 hS ht
  rcases lt_trichotomy b t with hbt | hbt | hbt
  · obtain ⟨B2, X2, hS2, e'⟩ := hMk κ hκ hκ4 P B1 X1 hS1 b hb
    filter_upwards [hU, e', grp_unzipSemigroup (κ := κ) hS1 hb (show 0 < t - b by linarith),
      grp_roundTrip h13 hκ hκ4 hS2 (show 0 < t - b by linarith),
      (hSG κ hκ hκ4 P B2 X2 hS2).2 (t - b) (by linarith), (hSG κ hκ hκ4 P B1 X1 hS1).2 b hb]
      with ω u1 e2 k1 r2 G2 Gd1
    rw [show b + (t - b) = t by ring,
      zipCapDown_congr_grpEq (γ := Real.sqrt κ) (t := t - b) (by linarith) e2] at k1
    have hc : ConfigEqC (grpCfg κ B X ω) (zipCapDown (Real.sqrt κ) (t - b) (grpCfg κ B2 X2 ω))
        (-lam ω) := u1.1.symm.of_configEq_right k1
    have hA := (zipCapUp_of_eqC_down hc G2.2 r2).of_configEq_right (grpEq_symm e2)
    rw [zipCap_of_nonneg (show 0 ≤ t - b by linarith)]
    exact hA.configEq_of_same (zipCapDown_configEqC hb.le u1.2 Gd1.1)
  · subst hbt
    filter_upwards [hU, grp_zipZero (κ := κ) hS, (hSG κ hκ hκ4 P B1 X1 hS1).2 b hb] with
      ω u1 z1 Gd1
    have hDU := (zipCapDown_configEqC hb.le u1.2 Gd1.1).trans u1.1
    rw [neg_add_cancel] at hDU
    rw [sub_self, zipCap_of_nonneg le_rfl]
    exact grpEq_trans z1 (grpEq_symm (configEqC_zero_iff.1 hDU))
  · obtain ⟨B2, X2, hS2, e2⟩ := hMk κ hκ hκ4 P B1 X1 hS1 t ht
    filter_upwards [hU, e2, grp_unzipSemigroup (κ := κ) hS1 ht (show 0 < b - t by linarith),
      (hSG κ hκ hκ4 P B1 X1 hS1).2 b hb, (hSG κ hκ hκ4 P B2 X2 hS2).2 (b - t) (by linarith)]
      with ω u1 e2 k1 Gd1 Gd2
    rw [show t + (b - t) = b by ring,
      zipCapDown_congr_grpEq (γ := Real.sqrt κ) (t := b - t) (by linarith) e2] at k1
    have hc : ConfigEqC (grpCfg κ B X ω) (grpCfg κ B2 X2 ω) (-lam ω) :=
      u1.1.symm.of_configEq_right e2
    have hA := zipCapDown_configEqC (γ := Real.sqrt κ) (show 0 ≤ b - t by linarith) hc Gd2.1
    rw [zipCap_of_neg (show t - b < 0 by linarith), show -(t - b) = b - t by ring]
    exact hA.configEq_of_same ((zipCapDown_configEqC hb.le u1.2 Gd1.1).of_configEq_right k1)

/-! ## The three named inputs of `Cor15BCases` and Corollary 1.5 -/

theorem cor15ZipZipStmt_of_genuine' (h13 : theorem1_3) (hSG : Cor15ShiftGoodStmt)
    (hG : Cor15GenuineStmt') : Cor15ZipZipStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind s t hs ht
  exact grp_zipZip' h13 hG.1 hG.2 hSG hκ hκ4 ⟨hB, hX, hind⟩ hs ht

theorem cor15ZipUnzipMixStmt_of_genuine' (h13 : theorem1_3) (hSG : Cor15ShiftGoodStmt)
    (hG : Cor15GenuineStmt') : Cor15ZipUnzipMixStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind s a hs ha hsa
  exact grp_mix' h13 hG.1 hG.2 hSG hκ hκ4 ⟨hB, hX, hind⟩ hs ha hsa

theorem cor15UnzipZipStmt_of_genuine' (h13 : theorem1_3) (hSG : Cor15ShiftGoodStmt)
    (hG : Cor15GenuineStmt') : Cor15UnzipZipStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind b t hb ht
  exact grp_unzipZip' h13 hG.1 hG.2 hSG hκ hκ4 ⟨hB, hX, hind⟩ hb ht

/-- **Corollary 1.5** from Theorem 1.3, the good set and the restated core. -/
theorem theorem1_5_of_theorem1_3_of_genuine' (h13 : theorem1_3) (hSG : Cor15ShiftGoodStmt)
    (hG : Cor15GenuineStmt') : theorem1_5 :=
  theorem1_5_of_theorem1_3_of_posGroup h13 (cor15ZipUnzipMixStmt_of_genuine' h13 hSG hG)
    (cor15UnzipZipStmt_of_genuine' h13 hSG hG) (cor15ZipZipStmt_of_genuine' h13 hSG hG)

end Cor15Group
end QuantumZipper
