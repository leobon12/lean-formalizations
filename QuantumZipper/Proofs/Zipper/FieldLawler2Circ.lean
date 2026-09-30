import QuantumZipper.Proofs.Zipper.FieldLawler2CircMob
import QuantumZipper.Proofs.Zipper.FieldLawler2C42Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler (4.1) / Corollary 4.2 for finitely many crosscuts on a circle (task FL2-C42CIRC)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
Corollary 4.2 and proof of Lemma 3.3, inequality (4.1), p. 11. FL: "Consider a Möbius
transformation of the Riemann sphere that sends C to R." We transport the real-line version
`fl2C42` (`FieldLawler2C42Main.lean`) along `fl2Mob ε` (`FieldLawler2CircMob.lean`), which maps
`ε e^{iθ}` to `tan(θ/2)` for `θ ∈ (−π, π)`, so that the arc `θ ∈ (α, β)` goes to the real
interval `(tan(α/2), tan(β/2))`.

Hypotheses: `D` open and bounded, the pole `−ε ∉ D`, the arcs `θ ∈ (α k, β k)` with
`−π < α k < β k < π` contained in `D`, pairwise disjoint, and the endpoints of each arc lie in
one connected `K_k ⊆ ℂ \ D` not containing `−ε` (FL's "only one component of `Dᶜ` meeting `C`",
in the plane after removing the pole of the Möbius map).
-/

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

/-- The open arc `{ε e^{iθ} : θ ∈ (α, β)}`. -/
def flCircArc (ε α β : ℝ) : Set ℂ := (fun θ : ℝ => (ε : ℂ) * exp (θ * I)) '' Ioo α β

section Circ

variable {ε : ℝ} (hε : 0 < ε)

lemma flCirc_exp (θ : ℝ) :
    exp (θ * I) = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

include hε in
lemma flCirc_den_ne {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) :
    (ε : ℂ) + ε * exp (θ * I) ≠ 0 := by
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hθ : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  intro h
  have hre := congrArg Complex.re h
  rw [flCirc_exp, hθ] at hre
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, zero_re] at hre
  nlinarith [mul_pos hε (mul_pos hc hc)]

include hε in
/-- `m(ε e^{iθ}) = tan(θ/2)` for `θ ∈ (−π, π)`. -/
lemma fl2Mob_circ {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) :
    fl2Mob ε ((ε : ℂ) * exp (θ * I)) = ((Real.tan (θ / 2) : ℝ) : ℂ) := by
  have hden := flCirc_den_ne hε h1 h2
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hsc := Real.sin_sq_add_cos_sq (θ / 2)
  have ht : Real.tan (θ / 2) * Real.cos (θ / 2) = Real.sin (θ / 2) := by
    rw [Real.tan_eq_sin_div_cos]; field_simp
  unfold fl2Mob
  rw [div_eq_iff hden, flCirc_exp, hcos, hsin]
  apply Complex.ext <;>
    simp only [add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im]
  · linear_combination (-2 * ε * Real.cos (θ / 2)) * ht
  · linear_combination (-2 * ε * Real.sin (θ / 2)) * ht - 2 * ε * hsc

lemma flCircArc_cont : Continuous fun θ : ℝ => (ε : ℂ) * exp (θ * I) := by fun_prop

include hε in
/-- The Möbius image of the arc `θ ∈ (α, β)` is the real interval `(tan(α/2), tan(β/2))`. -/
lemma fl2Mob_image_arc {α β : ℝ} (h1 : -π < α) (h2 : α < β) (h3 : β < π) :
    fl2Mob ε '' flCircArc ε α β = fl2C42Cut (Real.tan (α / 2)) (Real.tan (β / 2)) := by
  rw [flCircArc, image_image, fl2C42Cut]
  ext w; constructor
  · rintro ⟨θ, hθ, rfl⟩
    dsimp only
    rw [fl2Mob_circ hε (by linarith [hθ.1]) (by linarith [hθ.2])]
    refine ⟨Real.tan (θ / 2), ⟨?_, ?_⟩, rfl⟩
    · exact Real.strictMonoOn_tan ⟨by linarith, by linarith⟩
        ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ (by linarith [hθ.1])
    · exact Real.strictMonoOn_tan ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
        ⟨by linarith, by linarith⟩ (by linarith [hθ.2])
  · rintro ⟨t, ht, rfl⟩
    have ha := Real.arctan_strictMono ht.1
    have hb := Real.arctan_strictMono ht.2
    rw [Real.arctan_tan (by linarith) (by linarith)] at ha hb
    have hl := Real.neg_pi_div_two_lt_arctan t
    have hr := Real.arctan_lt_pi_div_two t
    refine ⟨2 * Real.arctan t, ⟨by linarith, by linarith⟩, ?_⟩
    simp only
    rw [fl2Mob_circ hε (by linarith) (by linarith)]
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.tan_arctan]

include hε in
/-- **Field–Lawler (4.1)** (EJP 20 (2015), proof of Lemma 3.3 via Corollary 4.2, p. 11) for
finitely many crosscuts `I k = {ε e^{iθ} : θ ∈ (α k, β k)}` on the circle `|z| = ε`: with `h k`
the harmonic measure of `I k` in `D \ I k`, `w` that of `⋃ I k` in `D \ ⋃ I k`, and `u k` that of
the other arcs, `∑_k h_k ≤ 2 w` on `D \ ⋃ I k`. Proof: FL's Möbius map `fl2Mob ε` sends the
circle to `ℝ`; apply the real-line version `fl2C42`. -/
theorem fl2C42Circ {n : ℕ} {D : Set ℂ} {α β : Fin n → ℝ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (hpD : -(ε : ℂ) ∉ D)
    (hαβ : ∀ k, -π < α k ∧ α k < β k ∧ β k < π)
    (hsub : ∀ k, flCircArc ε (α k) (β k) ⊆ D)
    (hK : ∀ k, ∃ K : Set ℂ, IsConnected K ∧ Disjoint K D ∧ -(ε : ℂ) ∉ K ∧
      (ε : ℂ) * exp (α k * I) ∈ K ∧ (ε : ℂ) * exp (β k * I) ∈ K)
    (hdisj : Pairwise fun i j => Disjoint (flCircArc ε (α i) (β i)) (flCircArc ε (α j) (β j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (D \ flCircArc ε (α k) (β k)) (flCircArc ε (α k) (β k)) (h k))
    {w : ℂ → ℝ}
    (hw : IsHarmMeas (D \ ⋃ k, flCircArc ε (α k) (β k)) (⋃ k, flCircArc ε (α k) (β k)) w)
    {u : Fin n → ℂ → ℝ}
    (hu : ∀ k, IsHarmMeas (D \ ⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i))
      (⋃ (i) (_ : i ≠ k), flCircArc ε (α i) (β i)) (u k)) :
    ∀ z ∈ D \ ⋃ k, flCircArc ε (α k) (β k), ∑ k, h k z ≤ 2 * w z := by
  set A : Fin n → Set ℂ := fun k => flCircArc ε (α k) (β k) with hA
  set C : Fin n → Set ℂ := fun k =>
    (fun θ : ℝ => (ε : ℂ) * exp (θ * I)) '' Icc (α k) (β k) with hC
  set a : Fin n → ℝ := fun k => Real.tan (α k / 2) with ha
  set b : Fin n → ℝ := fun k => Real.tan (β k / 2) with hb
  have hcut : ∀ k, fl2Mob ε '' A k = fl2C42Cut (a k) (b k) := fun k =>
    fl2Mob_image_arc hε (hαβ k).1 (hαβ k).2.1 (hαβ k).2.2
  have hCcl : ∀ k, IsClosed (C k) := fun k =>
    (isCompact_Icc.image (flCircArc_cont (ε := ε))).isClosed
  have hAC : ∀ k, A k ⊆ C k := fun k => image_mono Ioo_subset_Icc_self
  have hendα : ∀ k, (ε : ℂ) * exp (α k * I) ∉ D := fun k hz => by
    obtain ⟨K, -, hKD, -, hαK, -⟩ := hK k
    exact Set.disjoint_left.1 hKD hαK hz
  have hendβ : ∀ k, (ε : ℂ) * exp (β k * I) ∉ D := fun k hz => by
    obtain ⟨K, -, hKD, -, -, hβK⟩ := hK k
    exact Set.disjoint_left.1 hKD hβK hz
  have hCD : ∀ k, C k ∩ D ⊆ A k := by
    rintro k _ ⟨⟨θ, hθ, rfl⟩, hzD⟩
    rcases eq_or_lt_of_le hθ.1 with e | e
    · exact absurd hzD (e ▸ hendα k)
    rcases eq_or_lt_of_le hθ.2 with e' | e'
    · exact absurd hzD (e' ▸ hendβ k)
    exact ⟨θ, ⟨e, e'⟩, rfl⟩
  have hpC : ∀ k, -(ε : ℂ) ∉ C k := by
    rintro k ⟨θ, hθ, e⟩
    refine flCirc_den_ne hε (θ := θ) ?_ ?_ (by simp only at e; linear_combination e)
    · linarith [(hαβ k).1, hθ.1]
    · linarith [(hαβ k).2.2, hθ.2]
  have hpA : ∀ k, -(ε : ℂ) ∉ A k := fun k h => hpC k (hAC k h)
  -- openness and the pole, for the unions indexed by a predicate
  have hopen : ∀ P : Fin n → Prop, IsOpen (D \ ⋃ (i) (_ : P i), A i) := by
    intro P
    have e : D \ ⋃ (i) (_ : P i), A i = D \ ⋃ (i) (_ : P i), C i := by
      ext z
      simp only [Set.mem_sdiff, mem_iUnion]
      constructor
      · rintro ⟨hz, hn⟩
        exact ⟨hz, fun ⟨i, hi, hzC⟩ => hn ⟨i, hi, hCD i ⟨hzC, hz⟩⟩⟩
      · rintro ⟨hz, hn⟩
        exact ⟨hz, fun ⟨i, hi, hzA⟩ => hn ⟨i, hi, hAC i hzA⟩⟩
    rw [e]
    refine hD.sdiff (isClosed_iUnion_of_finite fun i => ?_)
    by_cases hi : P i
    · simpa [hi] using hCcl i
    · simp [hi]
  have hpcl : ∀ P : Fin n → Prop, -(ε : ℂ) ∉ closure (⋃ (i) (_ : P i), A i) := by
    intro P hp
    have h1 : closure (⋃ (i) (_ : P i), A i) ⊆ ⋃ i, C i :=
      closure_minimal (iUnion₂_subset fun i _ => (hAC i).trans (subset_iUnion C i))
        (isClosed_iUnion_of_finite hCcl)
    obtain ⟨i, hi⟩ := mem_iUnion.1 (h1 hp)
    exact hpC i hi
  have hpU : ∀ P : Fin n → Prop, -(ε : ℂ) ∉ ⋃ (i) (_ : P i), A i := fun P h =>
    hpcl P (subset_closure h)
  have himU : ∀ P : Fin n → Prop,
      fl2Mob ε '' (⋃ (i) (_ : P i), A i) = ⋃ (i) (_ : P i), fl2C42Cut (a i) (b i) := by
    intro P; rw [image_iUnion₂]; simp only [hcut]
  have hT : ∀ (P : Fin n → Prop) (g : ℂ → ℝ),
      IsHarmMeas (D \ ⋃ (i) (_ : P i), A i) (⋃ (i) (_ : P i), A i) g →
      IsHarmMeas (fl2Mob ε '' D \ ⋃ (i) (_ : P i), fl2C42Cut (a i) (b i))
        (⋃ (i) (_ : P i), fl2C42Cut (a i) (b i)) (fun v => g (fl2MobInv ε v)) := by
    intro P g hg
    have := fl2Mob_isHarmMeas hε (hopen P) (hDb.subset sdiff_subset) (fun h => hpD h.1)
      (hpcl P) hg
    rwa [fl2Mob_image_diff hε hpD (hpU P), himU P] at this
  have hK' : ∀ k, ∃ K : Set ℂ, IsConnected K ∧ Disjoint K (fl2Mob ε '' D) ∧
      ((a k : ℝ) : ℂ) ∈ K ∧ ((b k : ℝ) : ℂ) ∈ K := by
    intro k
    obtain ⟨K, hKc, hKD, hpK, hαK, hβK⟩ := hK k
    refine ⟨fl2Mob ε '' K, hKc.image _ fun z hz =>
      (fl2Mob_analyticAt (ε := ε) fun h => hpK (h ▸ hz)).continuousAt.continuousWithinAt,
      Set.disjoint_left.2 fun v hvK hvD => Set.disjoint_left.1 hKD
        ((fl2Mob_mem_image hε hpK).1 hvK).2 ((fl2Mob_mem_image hε hpD).1 hvD).2, ?_, ?_⟩
    · exact ⟨_, hαK, fl2Mob_circ hε (hαβ k).1 (by linarith [(hαβ k).2.1, (hαβ k).2.2])⟩
    · exact ⟨_, hβK, fl2Mob_circ hε (by linarith [(hαβ k).1, (hαβ k).2.1]) (hαβ k).2.2⟩
  have hmain := fl2C42 (D := fl2Mob ε '' D) (a := a) (b := b)
    (h := fun k v => h k (fl2MobInv ε v)) (w := fun v => w (fl2MobInv ε v))
    (u := fun k v => u k (fl2MobInv ε v))
    (fl2Mob_isOpen_image hε hD hpD)
    (fun k t ht => image_mono (hsub k) (by rw [hcut k]; exact ⟨t, ht, rfl⟩)) hK'
    (fun i j hij => Set.disjoint_left.2 fun t hti htj => by
      have hi : ((t : ℝ) : ℂ) ∈ fl2Mob ε '' A i := by rw [hcut i]; exact ⟨t, hti, rfl⟩
      have hj : ((t : ℝ) : ℂ) ∈ fl2Mob ε '' A j := by rw [hcut j]; exact ⟨t, htj, rfl⟩
      exact Set.disjoint_left.1 (hdisj hij) ((fl2Mob_mem_image hε (hpA i)).1 hi).2
        ((fl2Mob_mem_image hε (hpA j)).1 hj).2)
    (fun k => by
      have := hT (fun i => i = k) (h k) (by simpa using hh k)
      simpa using this)
    (by
      have := hT (fun _ => True) w (by simpa using hw)
      simpa using this)
    (fun k => hT (fun i => i ≠ k) (u k) (hu k))
  intro z hz
  have hz' : z ≠ -(ε : ℂ) := fun e => hpD (e ▸ hz.1)
  have hmz : fl2Mob ε z ∈ fl2Mob ε '' D \ ⋃ k, fl2C42Cut (a k) (b k) := by
    refine ⟨mem_image_of_mem _ hz.1, fun hm => ?_⟩
    have hU := himU (fun _ => True)
    simp only [iUnion_true] at hU
    rw [← hU] at hm
    have := ((fl2Mob_mem_image hε (by simpa using hpU (fun _ => True))).1 hm).2
    rw [fl2MobInv_flMob hε hz'] at this
    exact hz.2 this
  have := hmain _ hmz
  simpa only [fl2MobInv_flMob hε hz'] using this

end Circ

end FieldLawler
end QuantumZipper
