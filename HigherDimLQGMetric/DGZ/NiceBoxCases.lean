import HigherDimLQGMetric.DGZ.NiceBoxMeas

/-!
# DGZ §5.1–5.3: deterministic consequences of the nice-box conditions (packet L4a1)

Source: [2] Lemma 5.7 (the case split `ℬ₁`, `ℬ₂`, TeX l. 2286–2296), Prop 5.10 ((5.27), (5.28));
planning audit MA7 D-5.5–5.9 (Lemma 5.7: "if no pair of bad centres is `≥ R s_{j-1}` apart, any bad
centre `z` works in (c′)"), D-OSC ("Consequences used later" (P1), (P2)); blueprint Lemmas
`r2:lem:57`, `r2:lem:oscconds`(d), (e).

* Lattice form of the box relations (for counting): `obox_latPt_subset_scale_iff` (`B_{s'}(s' v) ⊆
  B_{N s'}(N s' u) ⟺ |v - N u|_∞ ≤ N - 1`), `latPt_mem_obox_iff` (`s' w ∈ B_{N s'}(N s' u) ⟺ |w - N
  u|_∞ < N`); for `B_{s'}(s' v) ⊆ B_{R s'}(s' w)` use L3a2's `obox_latPt_subset_iff` (`⟺ WithinInf
  (R - 1) v w`).
* `not_niceBox_add_two_cases` (DGZ Lemma 5.7, deterministic part): a bad `a_j`-box (`j ≥ 2`) fails
  (a′), or contains two bad `a_{j-1}`-boxes with centres `≥ R s_{j-1}` apart (`ℬ₁`), or has `z ∈
  𝒴_{j-1} ∩ B_{s_j}(x)` with a bad `a_{j-1}`-box inside `B_{R s_{j-1}}(z)` and `𝒞(x,z)` failing
  (`ℬ₂`).
* `osc_telescope` and `osc_le_of_niceOscCond` (D-OSC (P1)), `osc_le_of_niceOscOne` (D-OSC (P2)): the
  oscillation of `h_{0,n-a_i} = h_{n-a_i}` on a box around a point of `𝒴_i` is at most the sum of
  the (a′) bounds of the containing boxes at the levels `i < l ≤ m` and the `𝒥₂′` bound (for `i = 0`
  with `a₀ = 0`, the level-1 term is the (1′) bound `L`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## Lattice form of the box relations -/

/-- `B_{s'}(s' v) ⊆ B_{N s'}(N s' u)` iff `|v_i - N u_i| ≤ N - 1` for all `i`. -/
theorem obox_latPt_subset_scale_iff {s' : ℝ} (hs' : 0 < s') (N : ℕ) (u v : Zd d) :
    obox (latPt s' v) s' ⊆ obox (latPt (N * s') u) (N * s') ↔
      ∀ i, |v i - (N : ℤ) * u i| ≤ (N : ℤ) - 1 := by
  constructor
  · intro h i
    have h1 := abs_sub_le_of_obox_subset hs' h i
    rw [latPt_apply, latPt_apply] at h1
    have e : s' * (v i : ℝ) - N * s' * (u i : ℝ) = s' * ((v i : ℝ) - N * (u i : ℝ)) := by ring
    rw [e, abs_mul, abs_of_pos hs'] at h1
    have h2 : |(v i : ℝ) - N * (u i : ℝ)| ≤ (N : ℝ) - 1 := by
      have : s' * |(v i : ℝ) - N * (u i : ℝ)| ≤ s' * ((N : ℝ) - 1) := by linarith
      exact le_of_mul_le_mul_left this hs'
    have h3 : ((|v i - (N : ℤ) * u i| : ℤ) : ℝ) ≤ (((N : ℤ) - 1 : ℤ) : ℝ) := by
      push_cast
      exact h2
    exact_mod_cast h3
  · intro h z hz i
    have h1 : |z i - s' * (v i : ℝ)| < s' := by have := hz i; rwa [latPt_apply] at this
    have h2 : ((|v i - (N : ℤ) * u i| : ℤ) : ℝ) ≤ (((N : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast h i
    push_cast at h2
    rw [latPt_apply]
    calc |z i - N * s' * (u i : ℝ)| = |(z i - s' * (v i : ℝ)) +
          s' * ((v i : ℝ) - N * (u i : ℝ))| := by ring_nf
      _ ≤ |z i - s' * (v i : ℝ)| + s' * |(v i : ℝ) - N * (u i : ℝ)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_pos hs']
      _ < s' + s' * ((N : ℝ) - 1) := by
          have := mul_le_mul_of_nonneg_left h2 hs'.le
          linarith
      _ = N * s' := by ring

/-- `s' w ∈ B_{N s'}(N s' u)` iff `|w_i - N u_i| < N` for all `i`. -/
theorem latPt_mem_obox_iff {s' : ℝ} (hs' : 0 < s') (N : ℕ) (u w : Zd d) :
    latPt s' w ∈ obox (latPt (N * s') u) (N * s') ↔ ∀ i, |w i - (N : ℤ) * u i| < (N : ℤ) := by
  refine forall_congr' fun i => ?_
  rw [latPt_apply, latPt_apply]
  have e : s' * (w i : ℝ) - N * s' * (u i : ℝ) = s' * ((w i : ℝ) - N * (u i : ℝ)) := by ring
  rw [e, abs_mul, abs_of_pos hs', mul_comm (N : ℝ) s', mul_lt_mul_iff_right₀ hs']
  constructor
  · intro h
    have : ((|w i - (N : ℤ) * u i| : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by push_cast; exact h
    exact_mod_cast this
  · intro h
    have : ((|w i - (N : ℤ) * u i| : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this
    exact this

/-! ## The case split of DGZ Lemma 5.7 -/

/-- **The case split of DGZ Lemma 5.7** (deterministic; MA7 D-5.5–5.9, blueprint `r2:lem:57`): a bad
`a_{j+2}`-box at `x = s_{j+2} u` fails (a′), or (`ℬ₁`) contains two bad `a_{j+1}`-boxes whose
centres are `≥ R s_{j+1}` apart, or (`ℬ₂`) there is `z = s_{j+1} w ∈ B_{s_{j+2}}(x)` such that some
bad `a_{j+1}`-box lies in `B_{R s_{j+1}}(z)` and `𝒞(x,z)` fails (`R ≥ 1`). -/
theorem not_niceBox_add_two_cases (p : NiceParams) (H : ℕ → Rd d → ℝ) (hR : 1 ≤ p.R) {j : ℕ}
    {u : Zd d} (h : ¬ NiceBox p H (j + 2) u) :
    ¬ NiceOscCond p H (j + 2) u ∨
      (∃ v₁ v₂ : Zd d, obox (latPt (p.s (j + 1)) v₁) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
        obox (latPt (p.s (j + 1)) v₂) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
        ¬ NiceBox p H (j + 1) v₁ ∧ ¬ NiceBox p H (j + 1) v₂ ∧ ∃ i, (p.R : ℤ) ≤ |v₁ i - v₂ i|) ∨
      (∃ w : Zd d, latPt (p.s (j + 1)) w ∈ obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
        (∃ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
            obox (latPt (p.s (j + 1)) w) (p.R * p.s (j + 1)) ∧ ¬ NiceBox p H (j + 1) v) ∧
        ¬ NiceCEvent p H (j + 2) u w) := by
  rw [niceBox_add_two_iff] at h
  by_cases hA : NiceOscCond p H (j + 2) u
  · right
    have hbc := (not_and.1 h) hA
    rw [not_or] at hbc
    obtain ⟨hb, hnc⟩ := hbc
    push Not at hb
    obtain ⟨v₀, hv₀, hbad₀⟩ := hb
    by_cases hfar : ∃ v₁ v₂ : Zd d, obox (latPt (p.s (j + 1)) v₁) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
        obox (latPt (p.s (j + 1)) v₂) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) ∧
        ¬ NiceBox p H (j + 1) v₁ ∧ ¬ NiceBox p H (j + 1) v₂ ∧ ∃ i, (p.R : ℤ) ≤ |v₁ i - v₂ i|
    · exact Or.inl hfar
    · right
      have hs := p.s_pos (j + 1)
      have hclose : ∀ v : Zd d, obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) → ¬ NiceBox p H (j + 1) v →
          obox (latPt (p.s (j + 1)) v) (p.s (j + 1)) ⊆
            obox (latPt (p.s (j + 1)) v₀) (p.R * p.s (j + 1)) := by
        intro v hv hbad
        rw [mul_comm (p.R : ℝ)]
        refine (obox_latPt_subset_iff hs).2 fun i => ?_
        by_contra hlt
        push Not at hlt
        exact hfar ⟨v, v₀, hv, hv₀, hbad, hbad₀, i, by omega⟩
      have hcen : latPt (p.s (j + 1)) v₀ ∈ obox (latPt (p.s (j + 2)) u) (p.s (j + 2)) :=
        hv₀ fun i => by rw [sub_self, abs_zero]; exact hs
      have hself : obox (latPt (p.s (j + 1)) v₀) (p.s (j + 1)) ⊆
          obox (latPt (p.s (j + 1)) v₀) (p.R * p.s (j + 1)) := by
        rw [mul_comm (p.R : ℝ)]
        refine (obox_latPt_subset_iff hs).2 fun i => ?_
        rw [sub_self, abs_zero]
        omega
      exact ⟨v₀, hcen, ⟨v₀, hself, hbad₀⟩, fun hC => hnc ⟨v₀, hcen, hclose, hC⟩⟩
  · exact Or.inl hA

/-! ## Telescoping the oscillation conditions (D-OSC (P1), (P2)) -/

/-- **Telescoping**: on a set `B`, if every band `h_{n-a_l,n-a_{l-1}}` (`i < l ≤ m`) oscillates by
at most `c l` and `h_{n-a_m}` by at most `c₀`, then `h_{n-a_i}` oscillates by at most `∑_{i < l ≤ m}
c l + c₀` (`h_{n-a_i} = h_{n-a_m} + ∑_{i<l≤m} h_{n-a_l,n-a_{l-1}}` identically). -/
theorem osc_telescope (p : NiceParams) (H : ℕ → Rd d → ℝ) {B : Set (Rd d)} (c : ℕ → ℝ) {i : ℕ} :
    ∀ (m : ℕ) (c₀ : ℝ), i ≤ m →
      (∀ l, i < l → l ≤ m → ∀ z ∈ B, ∀ w ∈ B,
        |(H (p.n - p.a (l - 1)) z - H (p.n - p.a l) z) -
          (H (p.n - p.a (l - 1)) w - H (p.n - p.a l) w)| ≤ c l) →
      (∀ z ∈ B, ∀ w ∈ B, |H (p.n - p.a m) z - H (p.n - p.a m) w| ≤ c₀) →
      ∀ z ∈ B, ∀ w ∈ B, |H (p.n - p.a i) z - H (p.n - p.a i) w| ≤
        (∑ l ∈ Finset.Ioc i m, c l) + c₀
  | 0, c₀, him, _, htop => by
      obtain rfl : i = 0 := Nat.le_zero.1 him
      intro z hz w hw
      simpa using htop z hz w hw
  | m + 1, c₀, him, hosc, htop => by
      rcases Nat.lt_or_ge i (m + 1) with hlt | hge
      · have hm : i ≤ m := Nat.lt_succ_iff.1 hlt
        have htop' : ∀ z ∈ B, ∀ w ∈ B, |H (p.n - p.a m) z - H (p.n - p.a m) w| ≤
            c (m + 1) + c₀ := by
          intro z hz w hw
          have h1 := hosc (m + 1) hlt le_rfl z hz w hw
          have h2 := htop z hz w hw
          rw [Nat.add_sub_cancel] at h1
          calc |H (p.n - p.a m) z - H (p.n - p.a m) w|
              = |((H (p.n - p.a m) z - H (p.n - p.a (m + 1)) z) -
                  (H (p.n - p.a m) w - H (p.n - p.a (m + 1)) w)) +
                (H (p.n - p.a (m + 1)) z - H (p.n - p.a (m + 1)) w)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
            _ ≤ c (m + 1) + c₀ := by linarith
        have ih := osc_telescope p H c m (c (m + 1) + c₀) hm
          (fun l hl hlm => hosc l hl (Nat.le_succ_of_le hlm)) htop'
        intro z hz w hw
        rw [Finset.sum_Ioc_succ_top hm]
        have := ih z hz w hw
        linarith
      · obtain rfl : i = m + 1 := le_antisymm him hge
        intro z hz w hw
        simpa using htop z hz w hw

/-- **(P1) of D-OSC** (MA7; blueprint `r2:lem:oscconds`(d), structural form): let `y = s_i v` and
`r ≤ 8 s_i`. If for every level `i < l ≤ m` some `a_l`-box `B_{s_l}(s_l u_l)` with
`y ∈ B_{4s_l}(s_l u_l)` satisfies (a′), `𝒥₂′` holds and `y ∈ B₃(0)`, then
`osc_{B̄_r(y)} h_{n-a_i} ≤ ∑_{i<l≤m} K √a_{l-1} 2^{-(a_{l-1}-a_i)} + K √a_m 2^{-(a_m-a_i)}`. -/
theorem osc_le_of_niceOscCond (p : NiceParams) (H : ℕ → Rd d → ℝ) {i m : ℕ} (him : i ≤ m)
    (v : Zd d) {r : ℝ} (hr : r ≤ 8 * p.s i)
    (hbox : ∀ l, i < l → l ≤ m → ∃ u : Zd d,
      latPt (p.s i) v ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧ NiceOscCond p H l u)
    (hJ : EventJ2' p H m) (hy : latPt (p.s i) v ∈ obox (0 : Rd d) 3) :
    ∀ z ∈ cbox (latPt (p.s i) v) r, ∀ w ∈ cbox (latPt (p.s i) v) r,
      |H (p.n - p.a i) z - H (p.n - p.a i) w| ≤
        (∑ l ∈ Finset.Ioc i m, p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a i)) +
          p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a i) := by
  have hsub : cbox (latPt (p.s i) v) r ⊆ cbox (latPt (p.s i) v) (8 * p.s i) :=
    fun z hz k => (hz k).trans hr
  refine osc_telescope p H _ m _ him (fun l hl hlm z hz w hw => ?_)
    (fun z hz w hw => hJ i him v hy z (hsub hz) w (hsub hw))
  obtain ⟨u, hu, hosc⟩ := hbox l hl hlm
  exact hosc i hl v hu z (hsub hz) w (hsub hw)

/-- **(P2) of D-OSC** (MA7; blueprint `r2:lem:oscconds`(e), structural form, `a₀ = 0`): let
`w = s₀ v ∈ B₃(0)`, `r ≤ 3 s₀`, let the `a₁`-box at `s₁ u₁` contain `w` and satisfy (1′), and for
`2 ≤ l ≤ m` let some `a_l`-box with `w ∈ B_{4s_l}(s_l u_l)` satisfy (a′); with `𝒥₂′`:
`osc_{B̄_r(w)} h_n ≤ L + ∑_{1<l≤m} K √a_{l-1} 2^{-(a_{l-1}-a_0)} + K √a_m 2^{-(a_m-a_0)}`. -/
theorem osc_le_of_niceOscOne (p : NiceParams) (H : ℕ → Rd d → ℝ) (ha0 : p.a 0 = 0) {m : ℕ}
    (hm : 1 ≤ m) (v : Zd d) {r : ℝ} (hr : r ≤ 3 * p.s 0) {u₁ : Zd d}
    (hu₁ : latPt (p.s 0) v ∈ obox (latPt (p.s 1) u₁) (p.s 1)) (h1 : NiceOscOne p H u₁)
    (hbox : ∀ l, 1 < l → l ≤ m → ∃ u : Zd d,
      latPt (p.s 0) v ∈ obox (latPt (p.s l) u) (4 * p.s l) ∧ NiceOscCond p H l u)
    (hJ : EventJ2' p H m) (hy : latPt (p.s 0) v ∈ obox (0 : Rd d) 3) :
    ∀ z ∈ cbox (latPt (p.s 0) v) r, ∀ w ∈ cbox (latPt (p.s 0) v) r,
      |H p.n z - H p.n w| ≤
        (p.L + ∑ l ∈ Finset.Ioc 1 m,
          p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0)) +
          p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a 0) := by
  have hs0 := p.s_pos 0
  have hsub3 : cbox (latPt (p.s 0) v) r ⊆ cbox (latPt (p.s 0) v) (3 * p.s 0) :=
    fun z hz k => (hz k).trans hr
  have hsub8 : cbox (latPt (p.s 0) v) r ⊆ cbox (latPt (p.s 0) v) (8 * p.s 0) :=
    fun z hz k => (hz k).trans (by linarith)
  have hn : p.n - p.a 0 = p.n := by rw [ha0, Nat.sub_zero]
  set c : ℕ → ℝ := fun l => if l = 1 then p.L else
    p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0) with hc
  have h := osc_telescope p H (B := cbox (latPt (p.s 0) v) r) c m
    (p.K * √(p.a m : ℝ) * (2 : ℝ)⁻¹ ^ (p.a m - p.a 0)) (Nat.zero_le m)
    (fun l hl hlm z hz w hw => ?_) (fun z hz w hw => hJ 0 (Nat.zero_le m) v hy z (hsub8 hz) w
      (hsub8 hw))
  · intro z hz w hw
    have hzw := h z hz w hw
    rw [hn] at hzw
    have hsplit : ∑ l ∈ Finset.Ioc 0 m, c l = p.L + ∑ l ∈ Finset.Ioc 1 m,
        p.K * √(p.a (l - 1) : ℝ) * (2 : ℝ)⁻¹ ^ (p.a (l - 1) - p.a 0) := by
      have e : Finset.Ioc 0 m = insert 1 (Finset.Ioc 1 m) := by
        ext l
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      rw [e, Finset.sum_insert (by simp)]
      congr 1
      refine Finset.sum_congr rfl fun l hl => ?_
      have : l ≠ 1 := by
        have := (Finset.mem_Ioc.1 hl).1
        omega
      simp only [hc, this, ite_false]
    rw [hsplit] at hzw
    exact hzw
  · by_cases hl1 : l = 1
    · subst hl1
      have := h1 v hu₁ z (hsub3 hz) w (hsub3 hw)
      simp only [hc, ite_true]
      rw [show 1 - 1 = 0 from rfl, hn]
      exact this
    · obtain ⟨u, hu, hosc⟩ := hbox l (by omega) hlm
      simp only [hc, hl1, ite_false]
      exact hosc 0 hl v hu z (hsub8 hz) w (hsub8 hw)

end DGZ

end HigherDimLQGMetric
