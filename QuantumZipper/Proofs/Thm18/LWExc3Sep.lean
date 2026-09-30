import QuantumZipper.Proofs.Thm18.LWExc3Min
import QuantumZipper.Proofs.Thm18.LWFarSideCross

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: a crossing arc separates the two real sides of a half-annulus

`lw3_sep`: let `η` be a crosscut of `ℍ` starting at `−1` that reaches beyond the circle
`|z + 1| = 2r`. A connected open set `W` in the upper half-annulus `{r/2 < |z + 1| < 2r} ∩ ℍ`
avoiding `η` cannot have in its closure both a point of the left real side and a point of the
right real side (both off `closure η`).

This is the separation step in the proof of the lower half of the key estimate of Lawler–Werness
(Ann. Probab. 41 (2013), sketch of proof of Lemma 4.3, p. 24; see `LWExc43.lean` for the plan).
Proof: join the two real points through `W` by a path `σ` in the closed upper half-annulus; the
piece of `η` from a point inside `|z + 1| < r/2` to a point outside `|z + 1| > 2r` is a path `τ`
in `ℍ`; by the crossing lemma `lwfSide_crossing` (winding numbers, `LWFarSideCross.lean`) they
meet, contradicting `W ∩ η = ∅`. Own elementary argument (the published sketch leaves it
implicit).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- The upper half-annulus `{r/2 < |z + 1| < 2r} ∩ ℍ`. -/
def lw3Ann (r : ℝ) : Set ℂ := {z | 0 < z.im ∧ r / 2 < ‖z + 1‖ ∧ ‖z + 1‖ < 2 * r}

lemma lw3_near_real {W K : Set ℂ} (hK : IsClosed K) (hWim : ∀ z ∈ W, 0 < z.im) {r x : ℝ}
    (hxW : (x : ℂ) ∈ closure W) (hxK : (x : ℂ) ∉ K)
    (hx1 : r / 2 < ‖(x : ℂ) + 1‖) (hx2 : ‖(x : ℂ) + 1‖ < 2 * r) :
    ∃ S : Set ℂ, IsPathConnected S ∧ (x : ℂ) ∈ S ∧ (S ∩ W).Nonempty ∧
      ∀ z ∈ S, 0 ≤ z.im ∧ r / 2 < ‖z + 1‖ ∧ ‖z + 1‖ < 2 * r ∧ z ∉ K := by
  set O : Set ℂ := Kᶜ ∩ {z | r / 2 < ‖z + 1‖} ∩ {z | ‖z + 1‖ < 2 * r} with hO
  have hOo : IsOpen O :=
    ((hK.isOpen_compl).inter (isOpen_lt continuous_const (by fun_prop))).inter
      (isOpen_lt (by fun_prop) continuous_const)
  have hxO : (x : ℂ) ∈ O := ⟨⟨hxK, hx1⟩, hx2⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hOo _ hxO
  obtain ⟨w, hwW, hwd⟩ := Metric.mem_closure_iff.1 hxW ε hε
  have hconv : Convex ℝ (ball (x : ℂ) ε ∩ {z | (0 : ℝ) ≤ Complex.imLm z}) :=
    (convex_ball _ _).inter (convex_halfSpace_ge Complex.imLm.isLinear 0)
  have hxS : (x : ℂ) ∈ ball (x : ℂ) ε ∩ {z | (0 : ℝ) ≤ Complex.imLm z} :=
    ⟨mem_ball_self hε, by simp⟩
  refine ⟨_, hconv.isPathConnected ⟨_, hxS⟩, hxS, ⟨w, ⟨?_, ?_⟩, hwW⟩, ?_⟩
  · rw [mem_ball, dist_comm]; exact hwd
  · have := hWim w hwW; simp; linarith
  · rintro z ⟨hzb, hzi⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hεO hzb
    exact ⟨by simpa using hzi, h2, h3, h1⟩

/-- **Separation of the two real sides.** -/
theorem lw3_sep {η : ℝ → ℂ} (hη : IsCrosscutH η) (h0 : Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ)))
    {r : ℝ} (hr : 0 < r) (hfar : ∃ p ∈ arcH η, 2 * r < ‖p + 1‖) {W : Set ℂ} (hWo : IsOpen W)
    (hWc : IsConnected W) (hWA : W ⊆ lw3Ann r) (hWη : Disjoint W (arcH η)) {x₁ x₂ : ℝ}
    (hx₁ : x₁ + 1 < 0) (hx₂ : 0 < x₂ + 1) (h₁W : (x₁ : ℂ) ∈ closure W)
    (h₂W : (x₂ : ℂ) ∈ closure W) (h₁K : (x₁ : ℂ) ∉ closure (arcH η))
    (h₂K : (x₂ : ℂ) ∉ closure (arcH η))
    (h₁a : r / 2 < ‖(x₁ : ℂ) + 1‖ ∧ ‖(x₁ : ℂ) + 1‖ < 2 * r)
    (h₂a : r / 2 < ‖(x₂ : ℂ) + 1‖ ∧ ‖(x₂ : ℂ) + 1‖ < 2 * r) : False := by
  have hWim : ∀ z ∈ W, 0 < z.im := fun z hz => (hWA hz).1
  obtain ⟨S₁, hS₁p, hx₁S, ⟨w₁, hw₁S, hw₁W⟩, hS₁⟩ :=
    lw3_near_real isClosed_closure hWim h₁W h₁K h₁a.1 h₁a.2
  obtain ⟨S₂, hS₂p, hx₂S, ⟨w₂, hw₂S, hw₂W⟩, hS₂⟩ :=
    lw3_near_real isClosed_closure hWim h₂W h₂K h₂a.1 h₂a.2
  have hWp : IsPathConnected W := (hWo.isConnected_iff_isPathConnected).1 hWc
  have hP : IsPathConnected (S₁ ∪ W ∪ S₂) :=
    (hS₁p.union hWp ⟨w₁, hw₁S, hw₁W⟩).union hS₂p ⟨w₂, Or.inr hw₂W, hw₂S⟩
  have hPprop : ∀ z ∈ S₁ ∪ W ∪ S₂,
      0 ≤ z.im ∧ r / 2 < ‖z + 1‖ ∧ ‖z + 1‖ < 2 * r ∧ z ∉ arcH η := by
    rintro z ((hz | hz) | hz)
    · obtain ⟨a1, a2, a3, a4⟩ := hS₁ z hz
      exact ⟨a1, a2, a3, fun ha => a4 (subset_closure ha)⟩
    · obtain ⟨a1, a2, a3⟩ := hWA hz
      exact ⟨a1.le, a2, a3, fun ha => hWη.le_bot ⟨hz, ha⟩⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hS₂ z hz
      exact ⟨a1, a2, a3, fun ha => a4 (subset_closure ha)⟩
  have hJ := hP.joinedIn _ (Or.inl (Or.inl hx₁S)) _ (Or.inr hx₂S)
  let γ := hJ.somePath
  have hγ : ∀ t, γ t ∈ S₁ ∪ W ∪ S₂ := hJ.somePath_mem
  let σ : Path ((x₁ + 1 : ℝ) : ℂ) ((x₂ + 1 : ℝ) : ℂ) :=
    (γ.map (f := fun z : ℂ => z + 1) (continuous_id.add continuous_const)).cast (by push_cast; rfl) (by push_cast; rfl)
  have hσt : ∀ t, σ t = γ t + 1 := fun t => rfl
  -- the piece of `η` from inside `B(−1, r/2)` to outside `B(−1, 2r)`
  have hev := (h0.eventually (ball_mem_nhds (-1 : ℂ) (half_pos hr))).and
    (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
  obtain ⟨s₁, hs₁b, hs₁I⟩ := hev.exists
  obtain ⟨p, ⟨s₂, hs₂I, rfl⟩, hp⟩ := hfar
  have hFsub : uIcc s₁ s₂ ⊆ Ioo 0 1 := ordConnected_Ioo.uIcc_subset hs₁I hs₂I
  have hFp : IsPathConnected (η '' uIcc s₁ s₂) :=
    ((convex_uIcc s₁ s₂).isPathConnected nonempty_uIcc).image' (hη.1.mono hFsub)
  have hJτ := hFp.joinedIn (η s₁) ⟨s₁, left_mem_uIcc, rfl⟩ (η s₂) ⟨s₂, right_mem_uIcc, rfl⟩
  let γτ := hJτ.somePath
  have hγτ : ∀ t, γτ t ∈ arcH η := fun t => image_mono hFsub (hJτ.somePath_mem t)
  let τ := γτ.map (f := fun z : ℂ => z + 1) (continuous_id.add continuous_const)
  have hτt : ∀ t, τ t = γτ t + 1 := fun t => rfl
  have hs₁' : ‖η s₁ + 1‖ < r / 2 := by
    rw [dist_eq_norm, sub_neg_eq_add] at hs₁b; exact hs₁b
  obtain ⟨t, t', he⟩ := lwfSide_crossing hx₁ hx₂ σ
    (fun t => by rw [hσt]; simpa using (hPprop _ (hγ t)).1) τ
    (fun t => by
      rw [hτt]
      obtain ⟨s, hs, hse⟩ := hγτ t
      have : 0 < (η s).im := hη.2.2.1 hs
      rw [← hse]; simpa using this)
    (fun t => by rw [hσt]; linarith [(hPprop _ (hγ t)).2.1])
    (fun t => by rw [hσt]; linarith [(hPprop _ (hγ t)).2.2.1])
  rw [hσt, hτt, add_left_inj] at he
  exact (hPprop _ (hγ t)).2.2.2 (he ▸ hγτ t')

end LWFar
end Thm18Asm
end QuantumZipper
