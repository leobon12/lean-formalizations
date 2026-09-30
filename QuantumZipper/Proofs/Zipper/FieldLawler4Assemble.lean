import QuantumZipper.Proofs.Zipper.FieldLawler4NegSum
import QuantumZipper.Proofs.Zipper.FieldLawler4Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 4: `FLImageSumBoundStmt` from the per-crosscut chain

`fl4_imageSumBound_of`: `FLImageSumBoundStmt` (with `C = 256 π²`, `δ₀ = 1/4`) follows from the
per-crosscut data and inequality for positive and negative feet (`FL4PerArc`: the angles of the
preimage arc and Field–Lawler's chain on p. 9, `excR h (opposite half-line) ≤ fl2FluxR R g`),
by splitting the sum (`fl4_split_sum`) and Lemma 3.3 + (2.4) on each half (`fl4_pos_sum`,
`fl4_neg_sum`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The per-crosscut input for one sign `s = 1` (positive feet, flux into `(−∞,0]`) or
`s = −1` (negative feet, flux into `[0, ∞)`), in the setting of `FLImageSumBoundStmt`. -/
def FL4PerArc (s : ℝ) : Prop :=
  ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → 4 * ε ≤ R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ u ∈ Ioc 0 t, trace W u ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ u ∈ Ico 0 t, ‖trace W u‖ < R) → ‖trace W t‖ = R →
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t)) →
    ∀ (η : ℝ → ℂ) (a b : ℝ) (h : ℂ → ℝ),
      IsCrosscutH η → Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)) → Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)) →
      0 < s * a → 0 < s * b →
      arcH η ⊆ {p | ‖fwdMapInv W t p‖ = ε} → IsHarmMeas (hullComp η) (arcH η) h →
      ∃ α β : ℝ, ((if 0 < s then 0 ≤ α else 0 < α) ∧ α < β ∧ (if 0 < s then β < π else β ≤ π)) ∧
        fwdMapInv W t '' arcH η = flCircArc ε α β ∧
        ((ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ s * z.re} ∧
          (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ s * z.re}) ∧
        flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t ∧
        ∀ g : ℂ → ℝ, IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g →
          excR h (if 0 < s then Iic 0 else Ici 0) ≤ fl2FluxR R g

theorem fl4_imageSumBound_of (hP : FL4PerArc 1) (hN : FL4PerArc (-1)) :
    FLImageSumBoundStmt := by
  refine ⟨256 * π ^ 2, 1 / 4, by positivity, by norm_num, ?_⟩
  intro W hW hW0 t R ε ht hR hε hεδ htr0 hcont hinj hH hhull hlt htip htend S η a b h hfam hdisj
  have hR4 : 4 * ε ≤ R := by linarith
  have ha0 : ∀ j ∈ S, a j ≠ 0 := fun j hj e => by
    have := (hfam j hj).2.2.2.1; rw [e, zero_mul] at this; exact lt_irrefl _ this
  rw [fl4_split_sum S a (fun j J => excR (h j) J) ha0]
  have hbnd : ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π +
      ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π ≤
      ENNReal.ofReal (256 * π ^ 2 * (ε / R)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine le_of_eq (congrArg _ ?_)
    field_simp; ring
  refine le_trans (add_le_add ?_ ?_) hbnd
  · -- positive feet
    have hsign : ∀ j ∈ {j | j ∈ S ∧ 0 < a j}, 0 < 1 * a j ∧ 0 < 1 * b j := by
      rintro j ⟨hj, hpos⟩
      have hab := (hfam j hj).2.2.2.1
      exact ⟨by linarith, by rw [one_mul]; exact pos_of_mul_pos_right hab hpos.le⟩
    refine fl4_pos_sum hW hW0 ht hε hR4 htr0 hcont hH hhull hlt htip {j | j ∈ S ∧ 0 < a j} η h
      (fun j hj => fun z hz => by
        obtain ⟨u, hu, rfl⟩ := hz
        exact ((hfam j hj.1).1).2.2.1 hu)
      (fun i hi j hj hij => hdisj hi.1 hj.1 hij) (fun j hj => ?_) (fun j hj => ?_)
    · obtain ⟨α, β, hαβ, heq, hend, harc, -⟩ := hP W hW hW0 t R ε ht hR hε hR4 htr0 hcont hinj hH
        hhull hlt htip htend (η j) (a j) (b j) (h j) (hfam j hj.1).1 (hfam j hj.1).2.1
        (hfam j hj.1).2.2.1 (hsign j hj).1 (hsign j hj).2 (hfam j hj.1).2.2.2.2.1
        (hfam j hj.1).2.2.2.2.2
      simp only [one_mul, if_pos one_pos] at hαβ hend
      exact ⟨α, β, hαβ, heq, hend, harc⟩
    · intro α β g heq hg
      obtain ⟨α', β', -, heq', -, -, hper⟩ := hP W hW hW0 t R ε ht hR hε hR4 htr0 hcont hinj hH
        hhull hlt htip htend (η j) (a j) (b j) (h j) (hfam j hj.1).1 (hfam j hj.1).2.1
        (hfam j hj.1).2.2.1 (hsign j hj).1 (hsign j hj).2 (hfam j hj.1).2.2.2.2.1
        (hfam j hj.1).2.2.2.2.2
      rw [heq] at heq'
      rw [heq'] at hg
      have := hper g hg
      simpa only [if_pos one_pos] using this
  · -- negative feet
    have hsign : ∀ j ∈ {j | j ∈ S ∧ a j < 0}, 0 < -1 * a j ∧ 0 < -1 * b j := by
      rintro j ⟨hj, hneg⟩
      have hab := (hfam j hj).2.2.2.1
      refine ⟨by linarith, ?_⟩
      have : b j < 0 := by
        by_contra hc; push_neg at hc
        nlinarith
      linarith
    refine fl4_neg_sum hW hW0 ht hε hR4 htr0 hcont hH hhull hlt htip {j | j ∈ S ∧ a j < 0} η h
      (fun j hj => fun z hz => by
        obtain ⟨u, hu, rfl⟩ := hz
        exact ((hfam j hj.1).1).2.2.1 hu)
      (fun i hi j hj hij => hdisj hi.1 hj.1 hij) (fun j hj => ?_) (fun j hj => ?_)
    · obtain ⟨α, β, hαβ, heq, hend, harc, -⟩ := hN W hW hW0 t R ε ht hR hε hR4 htr0 hcont hinj hH
        hhull hlt htip htend (η j) (a j) (b j) (h j) (hfam j hj.1).1 (hfam j hj.1).2.1
        (hfam j hj.1).2.2.1 (hsign j hj).1 (hsign j hj).2 (hfam j hj.1).2.2.2.2.1
        (hfam j hj.1).2.2.2.2.2
      have hn : ¬ (0 : ℝ) < -1 := by norm_num
      simp only [if_neg hn] at hαβ
      refine ⟨α, β, hαβ, heq, ?_, harc⟩
      have tr : ∀ z, z ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ -1 * z.re} →
          z ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} := by
        rintro z (hz | hz)
        · exact Or.inl hz
        · exact Or.inr ⟨hz.1, by linarith [hz.2]⟩
      exact ⟨tr _ hend.1, tr _ hend.2⟩
    · intro α β g heq hg
      obtain ⟨α', β', -, heq', -, -, hper⟩ := hN W hW hW0 t R ε ht hR hε hR4 htr0 hcont hinj hH
        hhull hlt htip htend (η j) (a j) (b j) (h j) (hfam j hj.1).1 (hfam j hj.1).2.1
        (hfam j hj.1).2.2.1 (hsign j hj).1 (hsign j hj).2 (hfam j hj.1).2.2.2.2.1
        (hfam j hj.1).2.2.2.2.2
      rw [heq] at heq'
      rw [heq'] at hg
      have hn : ¬ (0 : ℝ) < -1 := by norm_num
      have := hper g hg
      simpa only [if_neg hn] using this

end FieldLawler
end QuantumZipper
