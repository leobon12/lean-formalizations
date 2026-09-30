import Mathlib.MeasureTheory.Measure.AEMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Sheffield's inverse argument for the group law (abstract form)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8, p. 26: `Z_t`
(`t > 0`) is the inverse of `Z_{−t}`, the maps preserve the law, and the group law `Z_{s+t} = Z_s Z_t`
then holds for all real `s, t`. Here: a family `T ℓ` of a.e.-measurable, law-preserving maps of a
measurable space with `T 0 = id`, `T (−ℓ) ∘ T ℓ = id`, `T ℓ ∘ T (−ℓ) = id` (`ℓ > 0`) and the
negative cocycle `T (−(a+b)) = T (−a) ∘ T (−b)`, all a.e., satisfies the group law a.e.
Pushing a.e. statements through the maps uses only `ae_of_ae_map`. The case analysis is an own
elementary argument (the paper leaves it implicit).
-/

open MeasureTheory

namespace QuantumZipper
namespace RT6Inv

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {T : ℝ → E → E}

/-- The hypotheses of the inverse argument. -/
structure InvFlow (μ : Measure E) (T : ℝ → E → E) : Prop where
  meas : ∀ ℓ, AEMeasurable (T ℓ) μ
  law : ∀ ℓ, μ.map (T ℓ) = μ
  zero : ∀ᵐ e ∂μ, T 0 e = e
  inv₁ : ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ e ∂μ, T (-ℓ) (T ℓ e) = e
  inv₂ : ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ e ∂μ, T ℓ (T (-ℓ) e) = e
  neg : ∀ a b : ℝ, 0 < a → 0 < b → ∀ᵐ e ∂μ, T (-(a + b)) e = T (-a) (T (-b) e)

/-- Push an a.e. statement through a law-preserving map. -/
theorem InvFlow.push (h : InvFlow μ T) (ℓ : ℝ) {p : E → Prop} (hp : ∀ᵐ e ∂μ, p e) :
    ∀ᵐ e ∂μ, p (T ℓ e) :=
  ae_of_ae_map (h.meas ℓ) (by rw [h.law ℓ]; exact hp)

/-- The zipping case `s, t > 0`. -/
theorem InvFlow.pos (h : InvFlow μ T) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ∀ᵐ e ∂μ, T (s + t) e = T s (T t e) := by
  have hu : 0 < s + t := add_pos hs ht
  have h1 := h.push t (h.push s (h.neg t s ht hs))
  have h2 := h.push t (h.inv₁ s hs)
  have h3 := h.inv₁ t ht
  have h4 := h.push t (h.push s (h.inv₂ (s + t) hu))
  filter_upwards [h1, h2, h3, h4] with e e1 e2 e3 e4
  rw [add_comm t s] at e1
  rw [← e4, e1, e2, e3]

/-- **The group law from the inverse identities** (Sheffield p. 26). -/
theorem InvFlow.group (h : InvFlow μ T) (s t : ℝ) :
    ∀ᵐ e ∂μ, T (s + t) e = T s (T t e) := by
  rcases lt_trichotomy s 0 with hs | hs | hs <;> rcases lt_trichotomy t 0 with ht | ht | ht
  · -- s, t < 0
    have := h.neg (-s) (-t) (by linarith) (by linarith)
    simp only [neg_neg, neg_add_rev] at this
    filter_upwards [this] with e he
    rw [show s + t = -(-t) + -(-s) by ring, neg_neg, neg_neg]
    simpa [neg_add_rev, add_comm] using he
  · -- t = 0
    subst ht
    filter_upwards [h.zero] with e he
    rw [he, add_zero]
  · -- s < 0 < t
    rcases lt_trichotomy t (-s) with h' | h' | h'
    · -- s + t < 0
      have hN := h.push t (h.neg (-s - t) t (by linarith) ht)
      filter_upwards [hN, h.inv₁ t ht] with e e1 e2
      rw [show -((-s - t) + t) = s by ring, e2, show -(-s - t) = s + t by ring] at e1
      exact e1.symm
    · -- s + t = 0
      have hst : s + t = 0 := by linarith
      rw [hst]
      have := h.inv₁ t ht
      rw [show -t = s by linarith] at this
      filter_upwards [h.zero, this] with e e1 e2
      rw [e1, e2]
    · -- s + t > 0
      have hP := h.push (s + t) (h.pos (s := -s) (t := s + t) (by linarith) (by linarith))
      have hI := h.push (s + t) (h.inv₁ (-s) (by linarith))
      filter_upwards [h.pos (s := -s) (t := s + t) (by linarith) (by linarith), hI]
        with e e1 e2
      rw [show -s + (s + t) = t by ring] at e1
      rw [e1, neg_neg] at *
      exact e2.symm
  · -- s = 0
    subst hs
    filter_upwards [h.push t h.zero] with e he
    rw [he, zero_add]
  · subst hs; subst ht
    filter_upwards [h.zero] with e e1
    rw [add_zero, e1, e1]
  · subst hs
    filter_upwards [h.push t h.zero] with e he
    rw [he, zero_add]
  · -- t < 0 < s
    rcases lt_trichotomy s (-t) with h' | h' | h'
    · -- s + t < 0: T (-(s + (-t - s))) = T (-s) ∘ T (-(-t - s))
      have hN := h.neg s (-t - s) hs (by linarith)
      rw [show -(s + (-t - s)) = t by ring, show -(-t - s) = s + t by ring] at hN
      filter_upwards [hN, h.push (s + t) (h.inv₂ s hs)] with e e1 e2
      rw [e1, e2]
    · have hst : s + t = 0 := by linarith
      rw [hst]
      have := h.inv₂ s hs
      rw [show -s = t by linarith] at this
      filter_upwards [h.zero, this] with e e1 e2
      rw [e1, e2]
    · -- s + t > 0: T s = T (s + t) ∘ T (-t)
      have hP := h.push t (h.pos (s := s + t) (t := -t) (by linarith) (by linarith))
      filter_upwards [hP, h.inv₂ (-t) (by linarith)] with e e1 e2
      rw [show s + t + -t = s by ring] at e1
      rw [neg_neg] at e2
      rw [e1, e2]
  · subst ht
    filter_upwards [h.zero] with e he
    rw [he, add_zero]
  · exact h.pos hs ht

end RT6Inv
end QuantumZipper
