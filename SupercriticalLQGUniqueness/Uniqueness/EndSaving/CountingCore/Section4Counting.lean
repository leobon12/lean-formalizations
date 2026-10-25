import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingChecks.ImageCount
import LQGMetric.Papers.GM.S3.GoodAnnulus
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic




 






set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore

open Finset

 

def AdmissibleConfiguration (r b : ℝ) (K₁ K₂ : Set ℂ)
    (Z : Finset (ℤ × ℤ)) : Prop :=
  0 < r ∧ Z.Nonempty ∧
    (∀ i ∈ Z, ∀ j ∈ Z, i ≠ j →
      Disjoint (Metric.ball (LQGMetric.GM.gridPt (r / 100) i) (4 * r))
        (Metric.ball (LQGMetric.GM.gridPt (r / 100) j) (4 * r))) ∧
    (∀ i ∈ Z, Disjoint (Metric.ball (LQGMetric.GM.gridPt (r / 100) i) (4 * r))
      (K₁ ∪ K₂ ∪ Metric.sphere (0 : ℂ) b))

 
theorem admissibleConfiguration_mono (r b : ℝ) (K₁ K₂ : Set ℂ)
    {Z W : Finset (ℤ × ℤ)} (hZ : AdmissibleConfiguration r b K₁ K₂ Z)
    (hWZ : W ⊆ Z) (hW : W.Nonempty) :
    AdmissibleConfiguration r b K₁ K₂ W := by
  refine ⟨hZ.1, hW, ?_, ?_⟩
  · intro i hi j hj hij
    exact hZ.2.2.1 i (hWZ hi) j (hWZ hj) hij
  · intro i hi
    exact hZ.2.2.2 i (hWZ hi)

 
def finiteBumpSum (Z : Finset (ℤ × ℤ)) (f : (ℤ × ℤ) → ℂ → ℝ) : ℂ → ℝ :=
  fun x => ∑ i ∈ Z, f i x

theorem finiteBumpSum_empty (f : (ℤ × ℤ) → ℂ → ℝ) :
    finiteBumpSum ∅ f = 0 := by
  funext x
  simp only [finiteBumpSum, sum_empty, Pi.zero_apply]

 

theorem stableSubset_image_count {α : Type*} [DecidableEq α]
    (S : Finset α) (k m : ℕ) (Φ : Finset α → Finset α)
    (hk : 2 * k ≤ S.card) (hmk : m ≤ k)
    (hsub : ∀ A ∈ S.powersetCard k, Φ A ⊆ A)
    (hcard : ∀ A ∈ S.powersetCard k, m ≤ (Φ A).card) :
    (S.card).choose k ≤ (S.card).choose (k - m) * ((S.powersetCard k).image Φ).card :=
  EndSaving.CountingChecks.image_count S k m Φ hk hmk hsub hcard

 


theorem stableDeletion_algebra {α : Type*} [DecidableEq α]
    (Z : Finset α) (Keep : Finset α → Finset α) (L : Finset α → ℝ)
    (B Cnew beta K : ℝ) (hZ : Z.Nonempty)
    (hB : 0 < B) (hbeta : 0 ≤ beta) (hmargin : beta < Cnew)
    (hKeep : ∀ W ⊆ Z, Keep W ⊆ W)
    (hupper : L Z ≤ L ∅ - Cnew * B * (Z.card : ℝ))
    (hincrement : ∀ W ⊆ Z, Keep W ≠ W →
      L (Keep W) ≤ L W + beta * B * ((W.card : ℝ) - ((Keep W).card : ℝ)))
    (hspent : ∀ W ⊆ Z, L ∅ ≤ L W + K * B * (W.card : ℝ)) :
    ∃ W : Finset α, W ⊆ Z ∧ W.Nonempty ∧ Keep W = W ∧
      (Cnew - beta) * (Z.card : ℝ) ≤ K * (W.card : ℝ) := by
  let a : ℝ := Cnew - beta
  have ha : 0 < a := by dsimp [a]; linarith
  have hZpos : (0 : ℝ) < Z.card := by exact_mod_cast hZ.card_pos
  have hbase : L Z ≤ L ∅ - a * B * (Z.card : ℝ) - beta * B * (Z.card : ℝ) := by
    dsimp [a]
    nlinarith [hupper]
  have hdesc : ∀ W : Finset α, W ⊆ Z →
      L W ≤ L ∅ - a * B * (Z.card : ℝ) - beta * B * (W.card : ℝ) →
      ∃ V : Finset α, V ⊆ W ∧ V.Nonempty ∧ Keep V = V ∧
        a * (Z.card : ℝ) ≤ K * (V.card : ℝ) := by
    intro W
    induction W using Finset.strongInductionOn with
    | _ W ih =>
      intro hWZ hInv
      have hne : W.Nonempty := by
        by_contra hempty
        have hWempty : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
        subst W
        have hs := hspent ∅ (empty_subset Z)
        simp only [card_empty, Nat.cast_zero, mul_zero, add_zero] at hs hInv
        nlinarith [mul_pos ha hB, hZpos]
      by_cases hfix : Keep W = W
      · have hs := hspent W hWZ
        refine ⟨W, Subset.rfl, hne, hfix, ?_⟩
        have hbetaW : 0 ≤ beta * B * (W.card : ℝ) :=
          mul_nonneg (mul_nonneg hbeta hB.le) (Nat.cast_nonneg _)
        have htotal : a * B * (Z.card : ℝ) ≤ K * B * (W.card : ℝ) := by
          linarith
        nlinarith [mul_pos ha hB]
      · have hKW : Keep W ⊆ W := hKeep W hWZ
        have hproper : Keep W ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨hKW, hfix⟩
        have hKWZ : Keep W ⊆ Z := hKW.trans hWZ
        have hinc := hincrement W hWZ hfix
        have hnext : L (Keep W) ≤ L ∅ - a * B * (Z.card : ℝ) -
            beta * B * ((Keep W).card : ℝ) := by
          nlinarith [hInv, hinc]
        obtain ⟨V, hVW, hVne, hVfix, hVbound⟩ := ih (Keep W) hproper hKWZ hnext
        exact ⟨V, hVW.trans hKW, hVne, hVfix, hVbound⟩
  obtain ⟨W, hWZ, hWne, hWfix, hWbound⟩ := hdesc Z Subset.rfl hbase
  exact ⟨W, hWZ, hWne, hWfix, hWbound⟩

 
theorem stableDeletion_card_ratio {α : Type*} [DecidableEq α]
    (Z : Finset α) (Keep : Finset α → Finset α) (L : Finset α → ℝ)
    (B Cnew beta K : ℝ) (hZ : Z.Nonempty)
    (hB : 0 < B) (hbeta : 0 ≤ beta) (hmargin : beta < Cnew) (hK : 0 < K)
    (hKeep : ∀ W ⊆ Z, Keep W ⊆ W)
    (hupper : L Z ≤ L ∅ - Cnew * B * (Z.card : ℝ))
    (hincrement : ∀ W ⊆ Z, Keep W ≠ W →
      L (Keep W) ≤ L W + beta * B * ((W.card : ℝ) - ((Keep W).card : ℝ)))
    (hspent : ∀ W ⊆ Z, L ∅ ≤ L W + K * B * (W.card : ℝ)) :
    ∃ W : Finset α, W ⊆ Z ∧ W.Nonempty ∧ Keep W = W ∧
      ((Cnew - beta) / K) * (Z.card : ℝ) ≤ (W.card : ℝ) := by
  obtain ⟨W, hWZ, hWne, hWfix, hbound⟩ :=
    stableDeletion_algebra Z Keep L B Cnew beta K hZ hB hbeta hmargin
      hKeep hupper hincrement hspent
  refine ⟨W, hWZ, hWne, hWfix, ?_⟩
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).2
  calc
    (Cnew - beta) * (Z.card : ℝ) ≤ K * (W.card : ℝ) := hbound
    _ = (W.card : ℝ) * K := mul_comm _ _

 


theorem finiteFamily_card_algebra {α : Type*} [DecidableEq α]
    (Z₀ Z₁ : Finset α) (B Cplus Cspent d Dold Dbump Dtilde Lpath : ℝ)
    (hZ₀ : Z₀.Nonempty) (hB : 0 < B) (hd : 0 < d)
    (hCplus : 0 ≤ Cplus) (_hCspent : 0 ≤ Cspent)
    (hnear : Cplus * Dbump - B ≤ Dtilde)
    (hsurgery : Dtilde ≤ Cplus * Lpath - d * B * (Z₁.card : ℝ))
    (hspent : Lpath ≤ Dold + Cspent * B * (Z₀.card : ℝ))
    (hmono : Dold ≤ Dbump) :
    d * (Z₁.card : ℝ) ≤ (1 + Cplus * Cspent) * (Z₀.card : ℝ) := by
  have hm : (1 : ℝ) ≤ Z₀.card := by exact_mod_cast hZ₀.card_pos
  have hstep : d * B * (Z₁.card : ℝ) ≤ B + Cplus * Cspent * B * (Z₀.card : ℝ) := by
    nlinarith [mul_nonneg hCplus (sub_nonneg.mpr hmono)]
  have hdB : 0 < d * B := mul_pos hd hB
  nlinarith [hdB]

 
theorem finiteFamily_card_ratio {α : Type*} [DecidableEq α]
    (Z₀ Z₁ : Finset α) (B Cplus Cspent d Dold Dbump Dtilde Lpath : ℝ)
    (hZ₀ : Z₀.Nonempty) (hB : 0 < B) (hd : 0 < d)
    (hCplus : 0 ≤ Cplus) (hCspent : 0 ≤ Cspent)
    (hnear : Cplus * Dbump - B ≤ Dtilde)
    (hsurgery : Dtilde ≤ Cplus * Lpath - d * B * (Z₁.card : ℝ))
    (hspent : Lpath ≤ Dold + Cspent * B * (Z₀.card : ℝ))
    (hmono : Dold ≤ Dbump) :
    (Z₁.card : ℝ) ≤ ((1 + Cplus * Cspent) / d) * (Z₀.card : ℝ) := by
  have hbound := finiteFamily_card_algebra Z₀ Z₁ B Cplus Cspent d
    Dold Dbump Dtilde Lpath hZ₀ hB hd hCplus hCspent hnear hsurgery hspent hmono
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).2
  calc
    (Z₁.card : ℝ) * d = d * (Z₁.card : ℝ) := mul_comm _ _
    _ ≤ (1 + Cplus * Cspent) * (Z₀.card : ℝ) := hbound

 


theorem finiteNeighbor_configuration_count {α : Type*} [DecidableEq α]
    (A : Finset α) (N : α → Finset α) (𝓕 : Finset (Finset α)) (R : ℕ)
    (hN : ∀ a ∈ A, (N a).card ≤ R)
    (hcover : ∀ Z ∈ 𝓕, ∀ z ∈ Z, ∃ a ∈ A, z ∈ N a) :
    𝓕.card ≤ 2 ^ (R * A.card) := by
  let C : Finset α := A.biUnion N
  have hF : 𝓕 ⊆ C.powerset := by
    intro Z hZ
    apply mem_powerset.mpr
    intro z hz
    obtain ⟨a, ha, hza⟩ := hcover Z hZ z hz
    exact mem_biUnion.mpr ⟨a, ha, hza⟩
  have hC : C.card ≤ R * A.card := by
    calc
      C.card ≤ ∑ a ∈ A, (N a).card := card_biUnion_le
      _ ≤ ∑ _a ∈ A, R := sum_le_sum hN
      _ = R * A.card := by simp [mul_comm]
  calc
    𝓕.card ≤ C.powerset.card := card_le_card hF
    _ = 2 ^ C.card := card_powerset C
    _ ≤ 2 ^ (R * A.card) := Nat.pow_le_pow_right (by omega) hC


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore
