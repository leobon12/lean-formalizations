import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegIteration




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory LQGMetric.Blueprint
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem card_filter_reflect (K : ℕ) (P Q : ℕ → Prop)
    (hPQ : ∀ i ∈ Finset.Icc 1 K, P i ↔ Q (K+1-i)) :
    ((Finset.Icc 1 K).filter P).card = ((Finset.Icc 1 K).filter Q).card := by
  classical
  apply Finset.card_bij (fun i _ => K+1-i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    constructor
    · omega
    · exact (hPQ i (Finset.mem_Icc.mpr hi.1)).mp hi.2
  · intro i hi j hj hij
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    refine ⟨K+1-j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · omega
      · exact (hPQ (K+1-j) (Finset.mem_Icc.mpr (by omega))).mpr (by simpa [Nat.sub_sub_self (by omega : j ≤ K+1)] using hj.2)
    · omega

private theorem regRadius_reverse (C : Objects.CorrectedEvent.Constants) (k K i : ℕ)
    (hi : i ∈ Finset.Icc 1 K) :
    regRadius (4^(K+1) * Objects.CorrectedEvent.lam k * C.r) i =
      4^(K+1-i) * Objects.CorrectedEvent.lam k * C.r := by
  have hiK : i ≤ K+1 := by
    have h := (Finset.mem_Icc.mp hi).2
    omega
  unfold regRadius
  have hpow : (4:ℝ)^(K+1) * (1/4:ℝ)^i = (4:ℝ)^(K+1-i) := by
    rw [show (1/4:ℝ)^i = ((4:ℝ)^i)⁻¹ by rw [one_div, inv_pow]]
    exact (pow_sub₀ (4:ℝ) (by norm_num) hiK).symm
  calc
    4^(K+1) * Objects.CorrectedEvent.lam k * C.r * (1/4:ℝ)^i =
      ((4:ℝ)^(K+1) * (1/4:ℝ)^i) * Objects.CorrectedEvent.lam k * C.r := by ring
    _ = _ := by rw [hpow]

 
theorem regGood_count_eq (C : Objects.CorrectedEvent.Constants) (D : LSCMetric)
    (k : ℕ) (w : ℂ) :
    countOcc (fun i => {g | Objects.CorrectedEvent.regGood C g
      (regRadius (4^((Objects.CorrectedEvent.regK k)+1) * Objects.CorrectedEvent.lam k * C.r) i) w})
      (Objects.CorrectedEvent.regK k) D =
    ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
      (fun j => Objects.CorrectedEvent.regGood C D (4^j * Objects.CorrectedEvent.lam k * C.r) w)).card := by
  classical
  unfold countOcc
  apply card_filter_reflect
  intro i hi
  change Objects.CorrectedEvent.regGood C D
    (regRadius (4^((Objects.CorrectedEvent.regK k)+1) * Objects.CorrectedEvent.lam k * C.r) i) w ↔
    Objects.CorrectedEvent.regGood C D (4^(Objects.CorrectedEvent.regK k+1-i) * Objects.CorrectedEvent.lam k * C.r) w
  rw [regRadius_reverse C k (Objects.CorrectedEvent.regK k) i hi]

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
