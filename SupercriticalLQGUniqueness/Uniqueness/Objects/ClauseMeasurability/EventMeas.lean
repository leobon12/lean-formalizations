import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CostMeas
import LQGMetric.Field.MeasurableAvg
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.GridCount




 



set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability

theorem measurable_normalizer (C : Objects.CorrectedEvent.Constants) (s : ℝ) (w : ℂ) :
    Measurable (fun g : LQGMetric.DistC => Objects.CorrectedEvent.normalizer C g s w) := by
  unfold Objects.CorrectedEvent.normalizer
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((measurable_const.mul
      (LQGMetric.measurable_circleAvg_left s w)).exp))

theorem measurableSet_S1 (C : Objects.CorrectedEvent.Constants)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D) :
    MeasurableSet {g | Objects.CorrectedEvent.S1 C (D g) g} := by
  have hN := measurable_normalizer C C.r 0
  have hA := (measurable_acr 0 C.r (1.5 * C.r)).comp hD
  have hB := (measurable_acr 0 (2.5 * C.r) (3 * C.r)).comp hD
  change MeasurableSet {g |
    ENNReal.ofReal C.A_across * Objects.CorrectedEvent.normalizer C g C.r 0 ≤
      Objects.CorrectedEvent.acr (D g) 0 C.r (1.5 * C.r) ∧
    ENNReal.ofReal C.A_across * Objects.CorrectedEvent.normalizer C g C.r 0 ≤
      Objects.CorrectedEvent.acr (D g) 0 (2.5 * C.r) (3 * C.r)}
  exact (measurableSet_le (measurable_const.mul hN) hA).inter
    (measurableSet_le (measurable_const.mul hN) hB)

theorem measurableSet_S2 (C : Objects.CorrectedEvent.Constants)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D) :
    MeasurableSet {g | Objects.CorrectedEvent.S2 C (D g) g} := by
  have hN := measurable_normalizer C C.r 0
  have hA := (measurable_around 0 (3 * C.r) (4 * C.r)
    (by linarith [C.rPos]) (by linarith [C.rPos])).comp hD
  change MeasurableSet {g |
    Objects.CorrectedEvent.around (D g) 0 (3 * C.r) (4 * C.r) ≤
      ENNReal.ofReal C.A_around * Objects.CorrectedEvent.normalizer C g C.r 0}
  exact measurableSet_le hA (measurable_const.mul hN)

private def goodCount {α ι : Type*} [DecidableEq ι]
    (S : Finset ι) (p : ι → α → Prop) (x : α) : ℕ := by
  classical
  exact (S.filter (fun i => p i x)).card

private theorem measurable_goodCount {α ι : Type*} [MeasurableSpace α]
    [DecidableEq ι] (S : Finset ι) (p : ι → α → Prop) :
    (∀ i ∈ S, MeasurableSet {x | p i x}) →
      Measurable (goodCount S p) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      change Measurable (fun _ : α => (0 : ℕ))
      exact measurable_const
  | @insert i S hi ih =>
      intro hp
      have hpi : MeasurableSet {x | p i x} := hp i (Finset.mem_insert_self ..)
      have hpS : ∀ j ∈ S, MeasurableSet {x | p j x} := by
        intro j hj
        exact hp j (Finset.mem_insert_of_mem hj)
      have hS := ih hpS
      have heq : goodCount (insert i S) p =
          (fun x => if p i x then goodCount S p x + 1
            else goodCount S p x) := by
        funext x
        by_cases hx : p i x <;> simp [goodCount, Finset.filter_insert, hx, hi, Nat.add_comm]
      rw [heq]
      exact Measurable.ite hpi (hS.add_const 1) hS

private def regMajority (C : Objects.CorrectedEvent.Constants)
    (D : LSCMetric) (k : ℕ) (z : ℂ) : Prop := by
  classical
  exact 2 * ((Finset.Icc 1 (Objects.CorrectedEvent.regK k)).filter
    (fun j => Objects.CorrectedEvent.regGood C D (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z)).card ≥
      Objects.CorrectedEvent.regK k

private theorem measurableSet_regMajority (C : Objects.CorrectedEvent.Constants)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (k : ℕ) (z : ℂ) :
    MeasurableSet {g | regMajority C (D g) k z} := by
  classical
  let p : ℕ → LQGMetric.DistC → Prop :=
    fun j g => Objects.CorrectedEvent.regGood C (D g) (4 ^ j * Objects.CorrectedEvent.lam k * C.r) z
  have hp : ∀ j ∈ Finset.Icc 1 (Objects.CorrectedEvent.regK k),
      MeasurableSet {g | p j g} := by
    intro j _
    apply measurableSet_regGood C D hD
    have hlam : 0 < Objects.CorrectedEvent.lam k := by unfold Objects.CorrectedEvent.lam; positivity
    exact mul_pos (mul_pos (pow_pos (by norm_num) _) hlam) C.rPos
  have hcount := measurable_goodCount (Finset.Icc 1 (Objects.CorrectedEvent.regK k)) p hp
  change MeasurableSet {g | Objects.CorrectedEvent.regK k ≤
    2 * goodCount (Finset.Icc 1 (Objects.CorrectedEvent.regK k)) p g}
  exact measurableSet_le measurable_const (measurable_const.mul hcount)

theorem measurableSet_S3 (C : Objects.CorrectedEvent.Constants)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D) :
    MeasurableSet {g | Objects.CorrectedEvent.S3 C (D g)} := by
  change MeasurableSet
    {g | ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
      regMajority C (D g) k z}
  have hsite (k : ℕ) : MeasurableSet
      {g | ∀ z ∈ Objects.CorrectedEvent.regSites C k, regMajority C (D g) k z} := by
    have h := MeasurableSet.biInter (regSites_countable C k)
      (fun z _ => measurableSet_regMajority C D hD k z)
    have heq : {g | ∀ z ∈ Objects.CorrectedEvent.regSites C k, regMajority C (D g) k z} =
        ⋂ z ∈ Objects.CorrectedEvent.regSites C k, {g | regMajority C (D g) k z} := by
      ext g
      simp only [mem_iInter, mem_ofPred_eq]
    rw [heq]
    exact h
  have hk (k : ℕ) : MeasurableSet
      {g | C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
        regMajority C (D g) k z} := by
    by_cases h : C.k0 ≤ k
    · simpa only [h, true_implies] using hsite k
    · have heq : {g | C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
          regMajority C (D g) k z} = (Set.univ : Set LQGMetric.DistC) := by
        ext g
        simp [h]
      rw [heq]
      exact MeasurableSet.univ
  have h := MeasurableSet.iInter hk
  have heq : {g | ∀ k : ℕ, C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
      regMajority C (D g) k z} =
      ⋂ k : ℕ, {g | C.k0 ≤ k → ∀ z ∈ Objects.CorrectedEvent.regSites C k,
        regMajority C (D g) k z} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq]
  rw [heq]
  exact h


end SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability
