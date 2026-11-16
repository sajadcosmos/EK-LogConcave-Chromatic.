/-
  EKLogConcave.lean

  Lean 4 / Mathlib formalisation accompanying
  "Log-concavity meets Enestrom--Kakeya: inner radii for the roots of chromatic and
   matroid characteristic polynomials" by Sajad A. Sheikh.

  Toolchain: leanprover/lean4:v4.34.1, Mathlib v4.34.1.

  Classical inputs (Rota's sign theorem, the Adiprasito--Huh--Katz log-concavity theorem,
  Crapo's beta invariant, the Tutte--Crapo activity expansion, Whitney's broken-circuit
  theorem, Stanley's factorisation) are not re-proved: they enter the statements below as
  explicit hypotheses (positivity, log-concavity, `w 0 = 1`, `chi(1) = 0`, activity data).
  Everything else is proved here from Mathlib, without `sorry` and without extra axioms.
-/
import Mathlib

noncomputable section

namespace EKLC

/-! # Part A. Rigid ratio annulus (Theorem 3.1) -/

section PartA

open Finset Complex


/-- The polynomial with real coefficients `a 0, …, a N`, evaluated at `z`. -/
def evalSeq (a : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ := ∑ k ∈ range (N + 1), (a k : ℂ) * z ^ k

/-- Positive and log-concave coefficients `a 0, …, a N`. -/
structure PosLC (a : ℕ → ℝ) (N : ℕ) : Prop where
  pos : ∀ k ≤ N, 0 < a k
  lc : ∀ k, k + 2 ≤ N → a k * a (k + 2) ≤ a (k + 1) ^ 2

/-- consecutive ratios are nondecreasing -/
lemma ratio_step {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) {k : ℕ} (hk : k + 2 ≤ N) :
    a k / a (k + 1) ≤ a (k + 1) / a (k + 2) := by
  have h0 := h.pos k (by omega); have h1 := h.pos (k+1) (by omega); have h2 := h.pos (k+2) hk
  rw [div_le_div_iff₀ h1 h2]; nlinarith [h.lc k hk]

lemma ratio_mono {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) {i j : ℕ} (hij : i ≤ j) (hj : j + 1 ≤ N) :
    a i / a (i + 1) ≤ a j / a (j + 1) := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h' | h'
    · subst h'; exact le_rfl
    · exact (ih (by omega) (by omega)).trans (ratio_step h (by omega))

/-! ### The Eneström–Kakeya core for nondecreasing coefficients -/

/-- telescoped coefficients -/
def tel (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => b 0
  | k + 1 => b (k + 1) - b k

lemma tel_identity (b : ℕ → ℝ) (w : ℂ) (N : ℕ) :
    (1 - w) * ∑ k ∈ range (N + 1), (b k : ℂ) * w ^ k
      = ∑ k ∈ range (N + 1), (tel b k : ℂ) * w ^ k - (b N : ℂ) * w ^ (N + 1) := by
  induction N with
  | zero => simp [tel]; ring
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ (fun k => (tel b k : ℂ) * w ^ k) (N + 1)]
    have : tel b (N + 1) = b (N + 1) - b N := rfl
    rw [this]; push_cast; ring

lemma tel_sum (b : ℕ → ℝ) (N : ℕ) : ∑ k ∈ range (N + 1), tel b k = b N := by
  induction N with
  | zero => simp [tel]
  | succ N ih => rw [sum_range_succ, ih]; simp [tel]

lemma tel_nonneg {b : ℕ → ℝ} {N : ℕ} (hb0 : 0 ≤ b 0)
    (hmono : ∀ k, k < N → b k ≤ b (k + 1)) {k : ℕ} (hk : k ≤ N) : 0 ≤ tel b k := by
  cases k with
  | zero => simpa [tel] using hb0
  | succ k => simp only [tel]; linarith [hmono k (by omega)]

/-- Eneström–Kakeya for nondecreasing positive coefficients: zeros lie in the closed unit disc. -/
lemma ek_core {b : ℕ → ℝ} {N : ℕ} (hb0 : 0 < b 0) (hmono : ∀ k, k < N → b k ≤ b (k + 1))
    {w : ℂ} (hw : ∑ k ∈ range (N + 1), (b k : ℂ) * w ^ k = 0) : ‖w‖ ≤ 1 := by
  by_contra hlt; push Not at hlt
  have hbN : 0 < b N := by
    have : ∀ k ≤ N, 0 < b k := by
      intro k hk; induction k with
      | zero => exact hb0
      | succ k ih => exact lt_of_lt_of_le (ih (by omega)) (hmono k (by omega))
    exact this N le_rfl
  have hid := tel_identity b w N
  rw [hw, mul_zero] at hid
  have key : (b N : ℂ) * w ^ (N + 1) = ∑ k ∈ range (N + 1), (tel b k : ℂ) * w ^ k := by
    linear_combination hid
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbN] at hn
  have hle : ‖∑ k ∈ range (N + 1), (tel b k : ℂ) * w ^ k‖ ≤ b N * ‖w‖ ^ N := by
    calc ‖∑ k ∈ range (N + 1), (tel b k : ℂ) * w ^ k‖
        ≤ ∑ k ∈ range (N + 1), ‖(tel b k : ℂ) * w ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ range (N + 1), tel b k * ‖w‖ ^ N := by
          apply sum_le_sum; intro k hk
          have hk' : k ≤ N := by simpa [Nat.lt_succ_iff] using mem_range.mp hk
          have ht := tel_nonneg hb0.le hmono hk'
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlt.le hk') ht
      _ = b N * ‖w‖ ^ N := by rw [← sum_mul, tel_sum]
  have : b N * ‖w‖ ^ (N + 1) ≤ b N * ‖w‖ ^ N := hn ▸ hle
  have hpos : 0 < b N * ‖w‖ ^ N := mul_pos hbN (pow_pos (by linarith) _)
  rw [pow_succ, ← mul_assoc] at this
  nlinarith

/-- two-term equality case: `‖α + β w‖ = α + β` with `α, β > 0`, `‖w‖ = 1` forces `w = 1`. -/
lemma two_term_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {w : ℂ} (hw : ‖w‖ = 1)
    (h : α + β ≤ ‖(α : ℂ) + (β : ℂ) * w‖) : w = 1 := by
  have hsq : (α + β) ^ 2 ≤ ‖(α : ℂ) + (β : ℂ) * w‖ ^ 2 := by
    have : 0 ≤ α + β := by linarith
    exact pow_le_pow_left₀ this h 2
  rw [← Complex.normSq_eq_norm_sq] at hsq
  have hw2 : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq w; rw [hw, Complex.normSq_apply] at this; nlinarith
  have hexp : Complex.normSq ((α : ℂ) + (β : ℂ) * w)
      = (α + β * w.re) ^ 2 + (β * w.im) ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hexp] at hsq
  have e : (α + β * w.re) ^ 2 + (β * w.im) ^ 2 = α ^ 2 + 2 * α * β * w.re + β ^ 2 := by
    linear_combination β ^ 2 * hw2
  have h1 : α * β * (1 - w.re) ≤ 0 := by nlinarith
  have hab : 0 < α * β := mul_pos hα hβ
  have hre : 1 ≤ w.re := by
    by_contra hc; push Not at hc
    have : 0 < α * β * (1 - w.re) := mul_pos hab (by linarith)
    linarith
  have hre1 : w.re = 1 := by nlinarith [sq_nonneg w.im]
  have him : w.im = 0 := by nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

/-- Strict form: if moreover `b 0 < b 1`, no zero lies on the unit circle. -/
lemma ek_core_strict {b : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N) (hb0 : 0 < b 0)
    (hmono : ∀ k, k < N → b k ≤ b (k + 1)) (h01 : b 0 < b 1)
    {w : ℂ} (hw : ∑ k ∈ range (N + 1), (b k : ℂ) * w ^ k = 0) : ‖w‖ < 1 := by
  rcases lt_or_eq_of_le (ek_core hb0 hmono hw) with h | h
  · exact h
  exfalso
  have hid := tel_identity b w N
  rw [hw, mul_zero] at hid
  have key : (b N : ℂ) * w ^ (N + 1) = ∑ k ∈ range (N + 1), (tel b k : ℂ) * w ^ k := by
    linear_combination hid
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have t0 : tel b 0 = b 0 := rfl
  have t1 : tel b (0 + 1) = b 1 - b 0 := rfl
  rw [sum_range_succ', sum_range_succ', t0, t1] at key
  simp only [pow_zero, mul_one, zero_add, pow_one] at key
  set T := ∑ k ∈ range M, (tel b (k + 1 + 1) : ℂ) * w ^ (k + 1 + 1) with hT
  have hbN : b (M+1) = b 1 + ∑ k ∈ range M, tel b (k + 1 + 1) := by
    have := tel_sum b (M + 1)
    rw [sum_range_succ', sum_range_succ', t0, t1] at this
    linarith
  have hTle : ‖T‖ ≤ ∑ k ∈ range M, tel b (k + 1 + 1) := by
    calc ‖T‖ ≤ ∑ k ∈ range M, ‖(tel b (k + 1 + 1) : ℂ) * w ^ (k + 1 + 1)‖ := norm_sum_le _ _
      _ = ∑ k ∈ range M, tel b (k + 1 + 1) := by
          apply sum_congr rfl; intro k hk
          have ht := tel_nonneg hb0.le hmono (k := k + 1 + 1) (by simp at hk; omega)
          rw [norm_mul, norm_pow, h, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ht]
  have hnorm : ‖(b (M+1) : ℂ) * w ^ (M + 1 + 1)‖ = b (M+1) := by
    have hpos : 0 < b (M+1) := by
      have : ∀ k ≤ M + 1, 0 < b k := by
        intro k hk; induction k with
        | zero => exact hb0
        | succ k ih => exact lt_of_lt_of_le (ih (by omega)) (hmono k (by omega))
      exact this _ le_rfl
    rw [norm_mul, norm_pow, h, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have h2 : (b 0 : ℂ) + ((b 1 - b 0 : ℝ) : ℂ) * w = (b (M+1) : ℂ) * w ^ (M + 1 + 1) - T := by
    rw [key]; push_cast; ring
  have hge : b 0 + (b 1 - b 0) ≤ ‖(b 0 : ℂ) + ((b 1 - b 0 : ℝ) : ℂ) * w‖ := by
    rw [h2]
    have := norm_sub_norm_le ((b (M+1) : ℂ) * w ^ (M + 1 + 1)) T
    rw [hnorm] at this; linarith
  have hw1 := two_term_eq hb0 (by linarith) h hge
  subst hw1
  have : ∑ k ∈ range (M + 1 + 1), (b k : ℂ) * 1 ^ k ≠ 0 := by
    simp only [one_pow, mul_one]
    have hpos : 0 < ∑ k ∈ range (M + 1 + 1), b k := by
      apply sum_pos _ (by simp)
      intro k hk; simp at hk
      have : ∀ k ≤ M + 1, 0 < b k := by
        intro k hk; induction k with
        | zero => exact hb0
        | succ k ih => exact lt_of_lt_of_le (ih (by omega)) (hmono k (by omega))
      exact this k (by omega)
    exact_mod_cast hpos.ne'
  exact this hw


/-! ### Theorem (rigid ratio annulus) -/

lemma pos_all {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) {k : ℕ} (hk : k ≤ N) : 0 < a k := h.pos k hk

/-- Outer half of the rigid ratio annulus. -/
theorem rigid_outer {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) (hN : 1 ≤ N) {z : ℂ}
    (hz : evalSeq a N z = 0) : ‖z‖ ≤ a (N - 1) / a N ∧
      (a 0 / a 1 < a (N - 1) / a N → ‖z‖ < a (N - 1) / a N) := by
  set β := a (N - 1) / a N with hβ
  have hβpos : 0 < β := div_pos (h.pos _ (by omega)) (h.pos _ le_rfl)
  set b : ℕ → ℝ := fun k => a k * β ^ k with hb
  have hb0 : 0 < b 0 := by simp [hb]; exact h.pos 0 (by omega)
  have hmono : ∀ k, k < N → b k ≤ b (k + 1) := by
    intro k hk
    have hr : a k / a (k + 1) ≤ β := by
      have := ratio_mono h (i := k) (j := N - 1) (by omega) (by omega)
      rwa [show N - 1 + 1 = N by omega] at this
    have hk1 := h.pos (k + 1) (by omega)
    simp only [hb, pow_succ]
    rw [div_le_iff₀ hk1] at hr
    have : 0 ≤ β ^ k := by positivity
    nlinarith
  set w := z / (β : ℂ) with hw
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβpos.ne'
  have hsum : ∑ k ∈ range (N + 1), (b k : ℂ) * w ^ k = 0 := by
    rw [← hz, evalSeq]; apply sum_congr rfl; intro k _
    simp only [hb, hw]; push_cast; rw [div_pow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (pow_ne_zero _ hβc)]
  have hzw : ‖z‖ = β * ‖w‖ := by
    rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβpos]; field_simp
  refine ⟨?_, ?_⟩
  · have := ek_core hb0 hmono hsum
    rw [hzw]; nlinarith
  · intro hng
    have h01 : b 0 < b 1 := by
      have ha1 := h.pos 1 hN; have ha0 := h.pos 0 (by omega)
      simp only [hb, pow_zero, mul_one, pow_one]
      rw [div_lt_iff₀ ha1] at hng; linarith
    have := ek_core_strict hN hb0 hmono h01 hsum
    rw [hzw]; nlinarith

/-- reversal of a coefficient sequence -/
def rev (a : ℕ → ℝ) (N : ℕ) : ℕ → ℝ := fun k => a (N - k)

lemma rev_PosLC {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) : PosLC (rev a N) N where
  pos k hk := h.pos _ (by omega)
  lc k hk := by
    simp only [rev]
    have := h.lc (N - k - 2) (by omega)
    rw [show N - k - 2 + 2 = N - k by omega, show N - k - 2 + 1 = N - (k + 1) by omega] at this
    rw [show N - (k + 2) = N - k - 2 by omega]; linarith

lemma evalSeq_rev {a : ℕ → ℝ} {N : ℕ} {z : ℂ} (hz0 : z ≠ 0) :
    evalSeq (rev a N) N z⁻¹ = (z ^ N)⁻¹ * evalSeq a N z := by
  simp only [evalSeq, rev, mul_sum]
  rw [← sum_range_reflect (fun k => (z ^ N)⁻¹ * ((a k : ℂ) * z ^ k))]
  apply sum_congr rfl; intro k hk
  have hk' : k ≤ N := by simp at hk; omega
  simp only [show N + 1 - 1 - k = N - k by omega]
  have : z ^ N = z ^ (N - k) * z ^ k := by rw [← pow_add]; congr 1; omega
  rw [this, inv_pow]; field_simp

/-- Inner half of the rigid ratio annulus. -/
theorem rigid_inner {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) (hN : 1 ≤ N) {z : ℂ}
    (hz : evalSeq a N z = 0) : a 0 / a 1 ≤ ‖z‖ ∧
      (a 0 / a 1 < a (N - 1) / a N → a 0 / a 1 < ‖z‖) := by
  have ha0 := h.pos 0 (by omega); have ha1 := h.pos 1 hN
  have hz0 : z ≠ 0 := by
    rintro rfl
    have : evalSeq a N 0 = (a 0 : ℂ) := by
      simp [evalSeq, sum_range_succ']
    rw [this] at hz; exact (ne_of_gt ha0) (by exact_mod_cast hz)
  have hr := rigid_outer (rev_PosLC h) hN (z := z⁻¹)
    (by rw [evalSeq_rev hz0, hz, mul_zero])
  simp only [rev, show N - (N - 1) = 1 by omega, Nat.sub_self] at hr
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [norm_inv] at hr
  refine ⟨?_, ?_⟩
  · have := hr.1
    rw [inv_le_comm₀ hzpos (div_pos ha1 ha0), inv_div] at this; exact this
  · intro hng
    have haN := h.pos N le_rfl; have haN1 := h.pos (N - 1) (by omega)
    have hng' : a N / a (N - 1) < a 1 / a 0 := by
      rw [div_lt_div_iff₀ haN1 ha0]; rw [div_lt_div_iff₀ ha1 haN] at hng; linarith
    have := hr.2 hng'
    rw [inv_lt_comm₀ hzpos (div_pos ha1 ha0), inv_div] at this; exact this

/-- **Theorem 3.1** (rigid ratio annulus). -/
theorem rigid_annulus {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) (hN : 1 ≤ N) {z : ℂ}
    (hz : evalSeq a N z = 0) :
    (a 0 / a 1 ≤ ‖z‖ ∧ ‖z‖ ≤ a (N - 1) / a N) ∧
    (a 0 / a 1 < a (N - 1) / a N → a 0 / a 1 < ‖z‖ ∧ ‖z‖ < a (N - 1) / a N) ∧
    (a 0 / a 1 = a (N - 1) / a N → ‖z‖ = a 0 / a 1) := by
  have ho := rigid_outer h hN hz; have hi := rigid_inner h hN hz
  refine ⟨⟨hi.1, ho.1⟩, fun hng => ⟨hi.2 hng, ho.2 hng⟩, fun heq => ?_⟩
  have := ho.1; rw [← heq] at this; exact le_antisymm this hi.1

/-- In the log-concave setting, non-geometricity is equivalent to `ρ₀ < ρ_{N-1}`:
if the first and last ratios agree, all ratios agree. -/
theorem geometric_of_first_eq_last {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N)
    (heq : a 0 / a 1 = a (N - 1) / a N) {k : ℕ} (hk : k + 1 ≤ N) :
    a k / a (k + 1) = a 0 / a 1 := by
  apply le_antisymm
  · have := ratio_mono h (i := k) (j := N - 1) (by omega) (by omega)
    rw [show N - 1 + 1 = N by omega] at this; rw [heq]; exact this
  · exact ratio_mono h (Nat.zero_le k) hk

end PartA

/-! # Part B. Vieta in reciprocal form and dominance (Corollary 3.2) -/

section PartB

open Finset Polynomial


/-- logarithmic derivative at the origin: `p'(0)/p(0)` -/
def L (p : ℂ[X]) : ℂ := p.coeff 1 / p.coeff 0

lemma coeff_one_mul (p q : ℂ[X]) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp

lemma L_mul {p q : ℂ[X]} (hp : p.coeff 0 ≠ 0) (hq : q.coeff 0 ≠ 0) :
    L (p * q) = L p + L q := by
  simp only [L, coeff_one_mul, mul_coeff_zero]; field_simp; ring

lemma L_X_sub_C (z : ℂ) : L (X - C z) = -z⁻¹ := by
  simp [L, coeff_X, coeff_C]

lemma coeff_zero_prod_ne {s : Multiset ℂ} (hs : ∀ z ∈ s, z ≠ 0) :
    ((s.map (fun z => X - C z)).prod).coeff 0 ≠ 0 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_coeff_zero]
    refine mul_ne_zero ?_ (ih fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    simpa using hs a (Multiset.mem_cons_self a s)

lemma L_prod {s : Multiset ℂ} (hs : ∀ z ∈ s, z ≠ 0) :
    L ((s.map (fun z => X - C z)).prod) = -(s.map (fun z => z⁻¹)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [L, coeff_one]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, z ≠ 0 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha := hs a (Multiset.mem_cons_self a s)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [L_mul (by simpa using ha) (coeff_zero_prod_ne hs'), L_X_sub_C a, ih hs']; ring

/-- **Vieta, reciprocal form.** For `p ≠ 0` over `ℂ` with `p(0) ≠ 0`,
the sum of reciprocals of the roots equals `-p'(0)/p(0)`. -/
theorem sum_inv_roots {p : ℂ[X]} (h0 : p.coeff 0 ≠ 0) :
    (p.roots.map (fun z => z⁻¹)).sum = -(p.coeff 1 / p.coeff 0) := by
  have hp : p ≠ 0 := by rintro rfl; simp at h0
  have hsplit : p.roots.card = p.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hsplit
  have hroots : ∀ z ∈ p.roots, z ≠ 0 := by
    intro z hz hz0; subst hz0
    have := (mem_roots hp).mp hz; rw [IsRoot, ← coeff_zero_eq_eval_zero] at this; exact h0 this
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hL : L p = L ((p.roots.map (fun z => X - C z)).prod) := by
    conv_lhs => rw [← hfac]
    simp only [L, coeff_C_mul]
    field_simp
  rw [L_prod hroots] at hL; simp only [L] at hL; rw [hL]; ring

/-- the polynomial with coefficient sequence `a 0, …, a N` -/
def polyOf (a : ℕ → ℝ) (N : ℕ) : ℂ[X] := ∑ k ∈ range (N + 1), C (a k : ℂ) * X ^ k

lemma polyOf_coeff (a : ℕ → ℝ) (N k : ℕ) :
    (polyOf a N).coeff k = if k ≤ N then (a k : ℂ) else 0 := by
  simp only [polyOf, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hk : k ≤ N
  · simp only [hk, ↓reduceIte]; rw [sum_eq_single k]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro hk'; simp at hk'; omega
  · simp only [hk, ↓reduceIte]; apply sum_eq_zero; intro j hj
    simp at hj; have : k ≠ j := by omega
    simp [this]

lemma polyOf_eval (a : ℕ → ℝ) (N : ℕ) (z : ℂ) : (polyOf a N).eval z = evalSeq a N z := by
  simp [polyOf, evalSeq, eval_finsetSum]

/-- **Corollary 3.2 (dominance, reciprocal form).** For positive, log-concave, non-geometric
coefficients, every root `z` satisfies `‖z‖⁻¹ < ‖∑ 1/z_j‖`, and `‖∑ 1/z_j‖ = a 1 / a 0`. -/
theorem dominance_inv {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) (hN : 1 ≤ N)
    (hng : a 0 / a 1 < a (N - 1) / a N) :
    ‖((polyOf a N).roots.map (fun z => z⁻¹)).sum‖ = a 1 / a 0 ∧
    ∀ z ∈ (polyOf a N).roots, ‖z‖⁻¹ < ‖((polyOf a N).roots.map (fun z => z⁻¹)).sum‖ := by
  have ha0 := h.pos 0 (by omega); have ha1 := h.pos 1 hN
  have h0 : (polyOf a N).coeff 0 ≠ 0 := by
    rw [polyOf_coeff]; simp only [Nat.zero_le, ↓reduceIte]; exact_mod_cast ha0.ne'
  have hS := sum_inv_roots h0
  have hval : ‖((polyOf a N).roots.map (fun z => z⁻¹)).sum‖ = a 1 / a 0 := by
    rw [hS, polyOf_coeff, polyOf_coeff]
    simp only [hN, Nat.zero_le, ↓reduceIte]
    rw [norm_neg, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos ha1 ha0)]
  refine ⟨hval, fun z hz => ?_⟩
  have hp : polyOf a N ≠ 0 := by rintro hc; rw [hc] at h0; simp at h0
  have hz' : evalSeq a N z = 0 := by
    rw [← polyOf_eval]; exact (mem_roots hp).mp hz
  have hin := (rigid_inner h hN hz').2 hng
  have hzpos : 0 < ‖z‖ := lt_of_le_of_lt (div_pos ha0 ha1).le hin
  rw [hval, inv_lt_comm₀ hzpos (div_pos ha1 ha0), inv_div]; exact hin


lemma polyOf_natDegree {a : ℕ → ℝ} {N : ℕ} (haN : a N ≠ 0) : (polyOf a N).natDegree = N := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]; intro k hk
    rw [polyOf_coeff]; have : ¬ k ≤ N := by omega
    simp [this]
  · rw [polyOf_coeff]; simp; exact_mod_cast haN

/-- **Corollary 3.2 (dominance, direct form).** For positive, log-concave, non-geometric
coefficients, `‖∑ z_j‖ = a (N-1) / a N` and every root satisfies `‖z‖ < ‖∑ z_j‖`. -/
theorem dominance_sum {a : ℕ → ℝ} {N : ℕ} (h : PosLC a N) (hN : 1 ≤ N)
    (hng : a 0 / a 1 < a (N - 1) / a N) :
    ‖(polyOf a N).roots.sum‖ = a (N - 1) / a N ∧
    ∀ z ∈ (polyOf a N).roots, ‖z‖ < ‖(polyOf a N).roots.sum‖ := by
  have haN := h.pos N le_rfl; have haN1 := h.pos (N - 1) (by omega)
  have hdeg := polyOf_natDegree (a := a) haN.ne'
  have hlc : (polyOf a N).leadingCoeff = (a N : ℂ) := by
    rw [leadingCoeff, hdeg, polyOf_coeff]; simp
  have hnext : (polyOf a N).nextCoeff = (a (N - 1) : ℂ) := by
    rw [nextCoeff_of_natDegree_pos (by omega), hdeg, polyOf_coeff]; simp
  have hS := (IsAlgClosed.splits (polyOf a N)).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnext, hlc] at hS
  have haNc : (a N : ℂ) ≠ 0 := by exact_mod_cast haN.ne'
  have hsum : (polyOf a N).roots.sum = -((a (N - 1) / a N : ℝ) : ℂ) := by
    push_cast; field_simp; linear_combination hS
  have hval : ‖(polyOf a N).roots.sum‖ = a (N - 1) / a N := by
    rw [hsum, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos haN1 haN)]
  refine ⟨hval, fun z hz => ?_⟩
  have hp : polyOf a N ≠ 0 := by
    intro hc; have := congrArg natDegree hc; rw [hdeg] at this; simp at this; omega
  have hz' : evalSeq a N z = 0 := by rw [← polyOf_eval]; exact (mem_roots hp).mp hz
  rw [hval]; exact (rigid_outer h hN hz').2 hng

end PartB

/-! # Part C. Matroid layer (Lemma 4.5, Proposition 4.4, Theorems 4.6, 4.8, 4.9, Proposition 6.3) -/

section PartC

open Finset


/-! ## Matroid layer

The classical inputs are encoded as hypotheses: positivity of the Whitney numbers
(Rota), their log-concavity (Adiprasito–Huh–Katz), `w 0 = 1`. -/

/-- the characteristic polynomial `∑ (-1)^k w_k λ^{r-k}` evaluated at `λ` -/
def chiSeq (w : ℕ → ℝ) (r : ℕ) (l : ℂ) : ℂ :=
  ∑ k ∈ range (r + 1), (-1 : ℂ) ^ k * (w k : ℂ) * l ^ (r - k)

/-- `h(M) = w_{r-1} / w_r` -/
def hInv (w : ℕ → ℝ) (r : ℕ) : ℝ := w (r - 1) / w r

lemma evalSeq_rev_neg (w : ℕ → ℝ) (r : ℕ) (l : ℂ) :
    evalSeq (rev w r) r (-l) = (-1) ^ r * chiSeq w r l := by
  simp only [evalSeq, rev, chiSeq, mul_sum]
  rw [← sum_range_reflect (fun k => (-1 : ℂ) ^ r * ((-1 : ℂ) ^ k * (w k : ℂ) * l ^ (r - k)))]
  apply sum_congr rfl; intro j hj
  have hj' : j ≤ r := by simp at hj; omega
  simp only [show r + 1 - 1 - j = r - j by omega, show r - (r - j) = j by omega]
  rw [neg_pow]
  have : (-1 : ℂ) ^ r = (-1) ^ (r - j) * (-1) ^ j := by rw [← pow_add]; congr 1; omega
  rw [this]
  have h2 : ((-1 : ℂ) ^ (r - j)) * (-1) ^ (r - j) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(-1 : ℂ) ^ j * (w (r - j) : ℂ) * l ^ j) * h2

/-- non-geometricity of the reversed Whitney sequence from `w 2 < w 1 ^ 2` -/
lemma nongeom_rev {w : ℕ → ℝ} {r : ℕ} (hr : 2 ≤ r) (h : PosLC w r) (hw0 : w 0 = 1)
    (hng : w 2 < w 1 ^ 2) :
    rev w r 0 / rev w r 1 < rev w r (r - 1) / rev w r r := by
  have hR := rev_PosLC h
  simp only [rev, Nat.sub_zero, Nat.sub_self, show r - (r - 1) = 1 by omega]
  have hm := ratio_mono hR (i := 0) (j := r - 2) (Nat.zero_le _) (by omega)
  simp only [rev, Nat.sub_zero, show r - (0 + 1) = r - 1 by omega,
    show r - (r - 2) = 2 by omega, show r - (r - 2 + 1) = 1 by omega] at hm
  have hw1 := h.pos 1 (by omega)
  have : w 2 / w 1 < w 1 / w 0 := by rw [hw0, div_one, div_lt_iff₀ hw1]; nlinarith
  linarith

/-- **Theorem 4.8 (inner radius of `χ_M`), abstract form.** -/
theorem mainA {w : ℕ → ℝ} {r : ℕ} (hr : 2 ≤ r) (h : PosLC w r) (hw0 : w 0 = 1)
    (hng : w 2 < w 1 ^ 2) {l : ℂ} (hl : chiSeq w r l = 0) :
    1 / hInv w r < ‖l‖ ∧ ‖l‖ < w 1 := by
  have hR := rev_PosLC h
  have hz : evalSeq (rev w r) r (-l) = 0 := by rw [evalSeq_rev_neg, hl, mul_zero]
  have hA := rigid_annulus hR (by omega) hz
  have hn := nongeom_rev hr h hw0 hng
  obtain ⟨h1, h2⟩ := hA.2.1 hn
  simp only [rev, Nat.sub_zero, Nat.sub_self, show r - (r - 1) = 1 by omega,
    norm_neg] at h1 h2
  refine ⟨?_, by rw [hw0, div_one] at h2; exact h2⟩
  rw [hInv, one_div_div]; exact h1

/-- consequence with `h(M) ≤ r`: every root satisfies `‖λ‖ > 1/r`. -/
theorem mainA_rank {w : ℕ → ℝ} {r : ℕ} (hr : 2 ≤ r) (h : PosLC w r) (hw0 : w 0 = 1)
    (hng : w 2 < w 1 ^ 2) (hle : hInv w r ≤ r) {l : ℂ} (hl : chiSeq w r l = 0) :
    1 / (r : ℝ) < ‖l‖ := by
  have := (mainA hr h hw0 hng hl).1
  have hpos : 0 < hInv w r := div_pos (h.pos _ (by omega)) (h.pos _ le_rfl)
  calc 1 / (r : ℝ) ≤ 1 / hInv w r := one_div_le_one_div_of_le hpos hle
    _ < ‖l‖ := this

/-- **Theorem 4.6, lower half (`h > 1`), analytic proof:** since `χ_M(1) = 0`. -/
theorem h_gt_one {w : ℕ → ℝ} {r : ℕ} (hr : 2 ≤ r) (h : PosLC w r) (hw0 : w 0 = 1)
    (hng : w 2 < w 1 ^ 2) (hone : chiSeq w r 1 = 0) : 1 < hInv w r := by
  have := (mainA hr h hw0 hng hone).1
  have hpos : 0 < hInv w r := div_pos (h.pos _ (by omega)) (h.pos _ le_rfl)
  rw [norm_one, div_lt_one hpos] at this; exact this

/-- **Theorem 4.6, activity form.** If `w_r` counts a nonempty family of bases of external
activity zero and `w_{r-1}` is the sum of their internal activities, each in `[1, r]`,
then `1 ≤ h ≤ r`, and `h = r` iff every activity equals `r`. -/
theorem h_bounds_activity {ι : Type*} (B : Finset ι) (hB : B.Nonempty) (ia : ι → ℕ) (r : ℕ)
    (hia : ∀ b ∈ B, 1 ≤ ia b ∧ ia b ≤ r) :
    let h := (∑ b ∈ B, (ia b : ℝ)) / B.card
    1 ≤ h ∧ h ≤ r ∧ (h = r ↔ ∀ b ∈ B, ia b = r) := by
  intro h
  have hc : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hlo : (B.card : ℝ) ≤ ∑ b ∈ B, (ia b : ℝ) := by
    rw [card_eq_sum_ones, Nat.cast_sum]; apply sum_le_sum; intro b hb
    exact_mod_cast (hia b hb).1
  have hhi : ∑ b ∈ B, (ia b : ℝ) ≤ B.card * r := by
    rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]; apply sum_le_sum; intro b hb
    simp; exact_mod_cast (hia b hb).2
  refine ⟨by rw [le_div_iff₀ hc]; linarith, by rw [div_le_iff₀ hc]; linarith, ?_⟩
  constructor
  · intro heq b hb
    have hsum : ∑ b ∈ B, ((r : ℝ) - ia b) = 0 := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
      have : ∑ b ∈ B, (ia b : ℝ) = B.card * r := by
        have := heq; simp only [h] at this; rw [div_eq_iff hc.ne'] at this; linarith
      linarith
    have hnn : ∀ b ∈ B, 0 ≤ (r : ℝ) - ia b := fun b hb => by
      have := (hia b hb).2; simp; exact_mod_cast this
    have := (sum_eq_zero_iff_of_nonneg hnn).mp hsum b hb
    have : (ia b : ℝ) = r := by linarith
    exact_mod_cast this
  · intro hall
    simp only [h]; rw [div_eq_iff hc.ne']
    rw [sum_congr rfl (fun b hb => by rw [hall b hb])]; simp; ring

/-- **Lemma 4.5 (non-geometricity), arithmetic core.** If the rank-two flats have sizes
`s F ≥ 2`, `w₂ = ∑ (s F - 1)` and `∑ C(s F, 2) = C(w₁, 2)`, then `w₂ ≤ C(w₁,2) < w₁²`, and
`μ̄₂ = w₂ - w₁ + 1 ≤ C(w₁-1, 2) < (w₁-1)²` when `w₁ ≥ 2`. -/
theorem nongeom_core {ι : Type*} (S : Finset ι) (s : ι → ℕ) (hs : ∀ F ∈ S, 2 ≤ s F)
    (w1 w2 : ℕ) (hw1 : 1 ≤ w1) (hw2 : w2 = ∑ F ∈ S, (s F - 1))
    (hpairs : ∑ F ∈ S, (s F).choose 2 = w1.choose 2) :
    w2 ≤ w1.choose 2 ∧ w1.choose 2 < w1 ^ 2 ∧
      (2 ≤ w1 → (w2 + 1 - w1 ≤ (w1 - 1).choose 2 ∧ (w1 - 1).choose 2 < (w1 - 1) ^ 2)) := by
  have hle : w2 ≤ w1.choose 2 := by
    rw [hw2, ← hpairs]; apply sum_le_sum; intro F hF
    have h2 := hs F hF
    obtain ⟨t, ht⟩ : ∃ t, s F = t + 2 := ⟨s F - 2, by omega⟩
    rw [ht, Nat.choose_two_right]
    have : (t + 2) * (t + 2 - 1) = (t + 2) * (t + 1) := by congr 1
    rw [this]
    have : 2 * (t + 1) ≤ (t + 2) * (t + 1) := Nat.mul_le_mul_right _ (by omega)
    have h3 : (t + 1) ≤ (t + 2) * (t + 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr; linarith
    omega
  have hlt : ∀ n, 1 ≤ n → n.choose 2 < n ^ 2 := by
    intro n hn
    rw [Nat.choose_two_right]
    have : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
    have : n * (n - 1) < n ^ 2 := by
      rw [sq]; apply Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  refine ⟨hle, hlt w1 hw1, fun h2 => ⟨?_, hlt (w1 - 1) (by omega)⟩⟩
  have hpas : w1.choose 2 = (w1 - 1).choose 2 + (w1 - 1) := by
    obtain ⟨t, rfl⟩ : ∃ t, w1 = t + 1 := ⟨w1 - 1, by omega⟩
    simp [Nat.choose_succ_succ', add_comm]
  omega

/-- **Lemma 2.2 / Proposition 4.4 (mediant).** -/
theorem mediant {x1 x2 y1 y2 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (x1 + x2) / (y1 + y2) = (y1 / (y1 + y2)) * (x1 / y1) + (1 - y1 / (y1 + y2)) * (x2 / y2) := by
  field_simp; ring

/-- the mediant lies between the two ratios, strictly if they differ -/
theorem mediant_lt_max {x1 x2 y1 y2 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2) (hlt : x2 / y2 < x1 / y1) :
    (x1 + x2) / (y1 + y2) < x1 / y1 := by
  rw [div_lt_div_iff₀ (by linarith) hy1]; rw [div_lt_div_iff₀ hy2 hy1] at hlt; nlinarith

/-- **Proposition 4.4 (deletion–contraction mediant), abstract form.**
With `w_k(M) = w_k(M\e) + w_{k-1}(M/e)`, `h(M)` is a convex combination of `h(M\e)` and `h(M/e)`. -/
theorem h_mediant (wd wc : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r) (hd : 0 < wd r) (hc : 0 < wc (r - 1)) :
    (wd (r - 1) + wc (r - 2)) / (wd r + wc (r - 1)) =
      (wd r / (wd r + wc (r - 1))) * hInv wd r +
      (1 - wd r / (wd r + wc (r - 1))) * hInv wc (r - 1) := by
  rw [hInv, hInv, show r - 1 - 1 = r - 2 by omega]; exact mediant hd hc

/-! ### The reduced characteristic polynomial -/

/-- **Theorem 4.9(b), abstract form** (`r ≥ 3`). For the reduced coefficients `μ̄`
(positive and log-concave by AHK, `μ̄₀ = 1`), every root of
`χ̄(λ) = ∑_{k<r} (-1)^k μ̄_k λ^{r-1-k}` satisfies `μ̄_{r-1}/μ̄_{r-2} < ‖λ‖ < μ̄₁`. -/
theorem mainB {mu : ℕ → ℝ} {r : ℕ} (hr : 3 ≤ r) (h : PosLC mu (r - 1)) (hmu0 : mu 0 = 1)
    (hng : mu 2 < mu 1 ^ 2) {l : ℂ} (hl : chiSeq mu (r - 1) l = 0) :
    mu (r - 1) / mu (r - 2) < ‖l‖ ∧ ‖l‖ < mu 1 := by
  have := mainA (r := r - 1) (by omega) h hmu0 hng hl
  rw [hInv, one_div_div, show r - 1 - 1 = r - 2 by omega] at this; exact this

/-- the case `r = 2`: `χ̄(λ) = λ - μ̄₁`, whose only root is `μ̄₁` -/
theorem mainB_rank_two {mu : ℕ → ℝ} (hmu0 : mu 0 = 1) {l : ℂ} (hl : chiSeq mu 1 l = 0) :
    l = mu 1 := by
  simp [chiSeq, sum_range_succ, hmu0] at hl; linear_combination hl

/-- relation between `μ̄` and `w`: the inner radius of `χ̄` is `1/(h-1)`. -/
theorem reduced_radius {w mu : ℕ → ℝ} {r : ℕ} (hwr : w r = mu (r - 1))
    (hwr1 : w (r - 1) = mu (r - 1) + mu (r - 2)) (hpos : 0 < mu (r - 1)) :
    mu (r - 1) / mu (r - 2) = 1 / (hInv w r - 1) := by
  rw [hInv, hwr, hwr1, add_div, div_self hpos.ne', add_sub_cancel_left, one_div_div]

/-- `1 < h < r` gives `1/(h-1) > 1/(r-1)`. -/
theorem reduced_rank_bound {h : ℝ} {r : ℕ} (h1 : 1 < h) (hr : h < r) :
    1 / ((r : ℝ) - 1) < 1 / (h - 1) := by
  apply one_div_lt_one_div_of_lt (by linarith); linarith

/-- **Proposition 6.3 (ridges), abstract form.** If a pure complex has `F` facets and `R > 0`
ridges, each facet containing `r - 1` ridges, the average number of facets on a ridge is
`(r-1)/(h-1)` where `h - 1 = R/F`; it is `≥ 2` iff `h ≤ (r+1)/2`. -/
theorem ridge_average {F R : ℝ} {r : ℕ} (hF : 0 < F) (hR : 0 < R) :
    ((r : ℝ) - 1) * F / R = ((r : ℝ) - 1) / (R / F) ∧
    (2 ≤ ((r : ℝ) - 1) * F / R ↔ 1 + R / F ≤ ((r : ℝ) + 1) / 2) := by
  refine ⟨by field_simp, ?_⟩
  rw [le_div_iff₀ hR, add_div' _ _ _ hF.ne', div_le_div_iff₀ hF (by norm_num)]
  constructor <;> intro h <;> nlinarith

end PartC

/-! # Part D. Cycles (Theorem 5.5, Proposition 5.3(a)) -/

section PartD

open Finset Complex Polynomial Filter Topology


/-! ## Cycles -/

/-- `‖1 - e^{iθ}‖ = 2 |sin(θ/2)|` in the form we use -/
lemma norm_one_sub_exp (θ : ℝ) : ‖1 - Complex.exp (I * θ)‖ = 2 * |Real.sin (θ / 2)| := by
  rw [← norm_neg, neg_sub, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]

/-- `sin(π k / m) ≥ sin(π / m)` for `1 ≤ k ≤ m - 1` -/
lemma sin_ge_of_mem {m k : ℕ} (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hk2 : k ≤ m - 1) :
    Real.sin (Real.pi / m) ≤ Real.sin (Real.pi * k / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmem : Real.pi * k / m ∈ Set.Icc (Real.pi / m) (Real.pi - Real.pi / m) := by
    have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ m - 1 := by
      have : (k : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hk2
      rw [Nat.cast_sub (by omega)] at this; simpa using this
    constructor
    · rw [div_le_div_iff_of_pos_right hm0]; nlinarith [Real.pi_pos]
    · rw [show Real.pi - Real.pi / m = Real.pi * (m - 1) / m by field_simp]
      rw [div_le_div_iff_of_pos_right hm0]; nlinarith [Real.pi_pos]
  have hpm : 0 ≤ Real.pi / m := div_nonneg Real.pi_pos.le hm0.le
  have hpm2 : Real.pi / m ≤ Real.pi - Real.pi / m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    rw [le_sub_iff_add_le, ← two_mul, mul_div_assoc']
    rw [div_le_iff₀ hm0]; nlinarith [Real.pi_pos]
  have := strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc
    (x := Real.pi / m) (y := Real.pi - Real.pi / m)
    ⟨hpm, by linarith [div_nonneg Real.pi_pos.le hm0.le]⟩
    ⟨by linarith, by linarith⟩ hmem
  rwa [Real.sin_pi_sub, min_self] at this

/-- **Key estimate for Theorem 5.5.** If `ζ^m = 1`, `ζ ≠ 1`, `m ≥ 2`, then
`‖1 - ζ‖ ≥ 2 sin(π/m)`, with equality for `ζ = e^{2πi/m}`. -/
theorem one_sub_root_of_unity {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ} (hζ : ζ ^ m = 1) (hne : ζ ≠ 1) :
    2 * Real.sin (Real.pi / m) ≤ ‖1 - ζ‖ := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨i, hi, rfl⟩ := (Complex.isPrimitiveRoot_exp m (by omega)).eq_pow_of_pow_eq_one hζ
  have hi0 : i ≠ 0 := by rintro rfl; simp at hne
  rw [← Complex.exp_nat_mul]
  have : (i : ℂ) * (2 * Real.pi * I / m) = I * ((2 * Real.pi * i / m : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, norm_one_sub_exp]
  have hsin := sin_ge_of_mem (m := m) (k := i) hm (by omega) (by omega)
  have hθ : 2 * Real.pi * i / m / 2 = Real.pi * i / m := by ring
  rw [hθ]
  have hpos : 0 ≤ Real.sin (Real.pi / m) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le (by positivity))
      (div_le_self Real.pi_pos.le (by exact_mod_cast (by omega : 1 ≤ m)))
  rw [abs_of_nonneg (hpos.trans hsin)]; linarith

theorem one_sub_root_of_unity_eq {m : ℕ} (hm : 2 ≤ m) :
    ‖1 - Complex.exp (2 * Real.pi * I / m)‖ = 2 * Real.sin (Real.pi / m) := by
  have : 2 * Real.pi * I / m = I * ((2 * Real.pi / m : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_one_sub_exp, show 2 * Real.pi / m / 2 = Real.pi / m by ring]
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le (by positivity))
      (div_le_self Real.pi_pos.le (by exact_mod_cast (by omega : 1 ≤ m))))]

/-- chromatic polynomial of `C_n` factorises as `y (y^{n-1} + (-1)^n)`, `y = q - 1` -/
theorem cycle_factor (n : ℕ) (hn : 1 ≤ n) (q : ℂ) :
    (q - 1) ^ n + (-1) ^ n * (q - 1) = (q - 1) * ((q - 1) ^ (n - 1) + (-1) ^ n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [pow_succ]; ring

/-- **Theorem 5.5 (cycles).** Every chromatic root `q = 1 + ω` of `C_n` (`n ≥ 3`) with
`ω^{n-1} = (-1)^{n+1}` and `ω ≠ -1` satisfies `‖q‖ ≥ 2 sin(π/(n-1))`; the value is attained. -/
theorem cycle_roots {n : ℕ} (hn : 3 ≤ n) {ω : ℂ} (hω : ω ^ (n - 1) = (-1) ^ (n + 1))
    (hne : ω ≠ -1) : 2 * Real.sin (Real.pi / (n - 1 : ℕ)) ≤ ‖1 + ω‖ := by
  have hz : (-ω) ^ (n - 1) = 1 := by
    rw [neg_pow, hω, ← pow_add]
    rw [show n - 1 + (n + 1) = 2 * n by omega, pow_mul]; norm_num
  have := one_sub_root_of_unity (m := n - 1) (by omega) hz (by intro h; apply hne; linear_combination -h)
  simpa [sub_neg_eq_add] using this

theorem cycle_roots_attained {n : ℕ} (hn : 3 ≤ n) :
    ∃ ω : ℂ, ω ^ (n - 1) = (-1) ^ (n + 1) ∧ ω ≠ -1 ∧
      ‖1 + ω‖ = 2 * Real.sin (Real.pi / (n - 1 : ℕ)) := by
  set m := n - 1 with hm
  refine ⟨-Complex.exp (2 * Real.pi * I / m), ?_, ?_, ?_⟩
  · rw [neg_pow, ← Complex.exp_nat_mul,
      show (m : ℂ) * (2 * Real.pi * I / m) = 2 * Real.pi * I by
        field_simp [show (m : ℂ) ≠ 0 by exact_mod_cast (by omega : m ≠ 0)]]
    rw [Complex.exp_two_pi_mul_I, mul_one, show n + 1 = m + 2 by omega, pow_add]; norm_num
  · intro h
    have h1 : Complex.exp (2 * Real.pi * I / m) = 1 := by linear_combination -h
    exact (Complex.isPrimitiveRoot_exp m (by omega)).ne_one (by omega) h1
  · have := one_sub_root_of_unity_eq (m := m) (by omega)
    simpa [sub_eq_add_neg] using this

/-- `2 sin(π/m) < 1 ↔ m > 6` for `m ≥ 2` (so the smallest nonzero root of `C_n` is below `1`
iff `n ≥ 8`). The hypothesis `m ≥ 2` is necessary: for `m = 1`, `2 sin π = 0`. -/
theorem two_sin_lt_one_iff {m : ℕ} (hm : 2 ≤ m) : 2 * Real.sin (Real.pi / m) < 1 ↔ 6 < m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hle : Real.pi / m ≤ Real.pi / 2 := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hm2
  have hx : 0 ≤ Real.pi / m := div_nonneg Real.pi_pos.le hm0.le
  constructor
  · intro h; by_contra hc; push Not at hc
    have hm6 : (m : ℝ) ≤ 6 := by exact_mod_cast hc
    have h6 : Real.pi / 6 ≤ Real.pi / m := div_le_div_of_nonneg_left Real.pi_pos.le hm0 hm6
    have : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi / m) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hle h6
    rw [Real.sin_pi_div_six] at this; linarith
  · intro h
    have hm6 : (6 : ℝ) < m := by exact_mod_cast h
    have : Real.pi / m < Real.pi / 6 := div_lt_div_of_pos_left Real.pi_pos (by norm_num) hm6
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) this
    rw [Real.sin_pi_div_six] at this; linarith

/-- the ratio of truth to bound for cycles tends to `π`:
`(m - 1) sin(π/m) → π` as `m → ∞` (here `m = n - 1`). -/
theorem cycle_ratio_tendsto :
    Tendsto (fun m : ℕ => ((m : ℝ) - 1) * Real.sin (Real.pi / m)) atTop (𝓝 Real.pi) := by
  -- squeeze: (m-1)(π/m - (π/m)^3/6) ≤ (m-1) sin(π/m) ≤ (m-1) π/m
  have hup : Tendsto (fun m : ℕ => ((m : ℝ) - 1) * (Real.pi / m)) atTop (𝓝 Real.pi) := by
    have : (fun m : ℕ => ((m : ℝ) - 1) * (Real.pi / m)) =ᶠ[atTop]
        fun m : ℕ => Real.pi - Real.pi * (1 / (m : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp
    rw [tendsto_congr' this]
    have h1 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := Real.pi)).sub (h1.const_mul Real.pi)
  have hlow : Tendsto (fun m : ℕ => ((m : ℝ) - 1) * (Real.pi / m - (Real.pi / m) ^ 3 / 6))
      atTop (𝓝 Real.pi) := by
    have h1 : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have : (fun m : ℕ => ((m : ℝ) - 1) * (Real.pi / m - (Real.pi / m) ^ 3 / 6)) =ᶠ[atTop]
        fun m : ℕ => Real.pi - Real.pi * (1 / (m : ℝ))
          - (Real.pi ^ 3 / 6) * (1 / (m : ℝ)) ^ 2 + (Real.pi ^ 3 / 6) * (1 / (m : ℝ)) ^ 3 := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      have : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp; ring
    rw [tendsto_congr' this]
    have := ((tendsto_const_nhds (x := Real.pi)).sub (h1.const_mul Real.pi)).sub
      ((h1.pow 2).const_mul (Real.pi ^ 3 / 6)) |>.add ((h1.pow 3).const_mul (Real.pi ^ 3 / 6))
    simpa using this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hx : 0 < Real.pi / m := div_pos Real.pi_pos (by exact_mod_cast (by omega : 0 < m))
    exact mul_le_mul_of_nonneg_left (Real.sin_gt_sub_cube hx).le hm1
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    exact mul_le_mul_of_nonneg_left (Real.sin_le (div_nonneg Real.pi_pos.le (by positivity))) hm1

/-- **Proposition 5.3(a), cycles.** For `P(C_n) = (X-1)^n + (-1)^n (X-1)`, the absolute values
of the coefficients of `q` and `q²` are `n - 1` and `C(n,2)`, hence `h(C_n) = n/2`. -/
theorem cycle_coeffs (n : ℕ) (hn : 3 ≤ n) :
    let P : ℚ[X] := (X - C 1) ^ n + C ((-1) ^ n) * (X - C 1)
    P.coeff 1 = (-1) ^ (n - 1) * (n - 1 : ℚ) ∧ P.coeff 2 = (-1) ^ n * (n.choose 2 : ℚ) ∧
      (n.choose 2 : ℚ) / (n - 1) = n / 2 := by
  intro P
  have hsub : (X - C (1 : ℚ)) = X + C (-1) := by simp [sub_eq_add_neg]
  refine ⟨?_, ?_, ?_⟩
  · simp only [P, coeff_add, hsub, coeff_X_add_C_pow, coeff_C_mul, coeff_add, coeff_X_one, coeff_C]
    simp
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  · simp only [P, coeff_add, hsub, coeff_X_add_C_pow, coeff_C_mul, coeff_X, coeff_C]
    simp
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    simp [pow_add]
  · rw [Nat.choose_two_right, Nat.cast_div (by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      simpa [mul_comm] using Nat.even_mul_succ_self k |>.two_dvd) (by norm_num)]
    have : (n : ℚ) - 1 ≠ 0 := by
      have : (3 : ℚ) ≤ n := by exact_mod_cast hn
      linarith
    field_simp
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring

end PartD

/-! # Part E. Families and structural identities (Propositions 5.1, 5.3, 6.2, Example 4.10) -/

section PartE

open Finset Polynomial


/-! ## Families and structural identities -/

/-- `h` of a polynomial `p` with `p(0) ≠ 0`: the sum of reciprocals of its roots, `= -p'(0)/p(0)`. -/
def hpoly (p : ℂ[X]) : ℂ := -L p

/-- **Proposition 4.2(d) / 5.1(b) (additivity).** `h` is additive over products
(direct sums of matroids, blocks of graphs). -/
theorem hpoly_mul {p q : ℂ[X]} (hp : p.coeff 0 ≠ 0) (hq : q.coeff 0 ≠ 0) :
    hpoly (p * q) = hpoly p + hpoly q := by
  simp only [hpoly, L_mul hp hq]; ring

/-- **Proposition 5.1(e) (gluing along an edge).** If `P(G₁)/q = (q-1) u₁` and
`P(G)/q = u₁ · P(G₂)/q`, then `h(G) = h(G₁) + h(G₂) - 1`. -/
theorem hpoly_glue {u₁ p₂ : ℂ[X]} (hu : u₁.coeff 0 ≠ 0) (hp : p₂.coeff 0 ≠ 0) :
    hpoly (u₁ * p₂) = hpoly ((X - C 1) * u₁) + hpoly p₂ - 1 := by
  have h1 : (X - C (1 : ℂ)).coeff 0 ≠ 0 := by simp
  rw [hpoly_mul hu hp, hpoly_mul h1 hu]
  simp only [hpoly, L_X_sub_C]; simp; ring

/-- the class `𝒞`: if `h(G_i) = n_i/2` then the glued graph on `n₁ + n₂ - 2` vertices has `h = n/2` -/
theorem glue_half {h₁ h₂ n₁ n₂ : ℝ} (e₁ : h₁ = n₁ / 2) (e₂ : h₂ = n₂ / 2) :
    h₁ + h₂ - 1 = (n₁ + n₂ - 2) / 2 := by rw [e₁, e₂]; ring

/-- **Proposition 5.3(b) (chordal graphs).** If `1 ≤ d i ≤ i - 1` for `2 ≤ i ≤ n`, then
`H_{n-1} ≤ ∑_{i=2}^n 1/d_i ≤ n - 1`; equality on the left iff `d i = i - 1` for all `i`,
on the right iff `d i = 1` for all `i`. Indices are shifted: `i = j + 2`, `j < n - 1`. -/
theorem chordal_bounds (n : ℕ) (d : ℕ → ℕ) (hd : ∀ j < n, 1 ≤ d j ∧ d j ≤ j + 1) :
    let S := ∑ j ∈ range n, (1 : ℝ) / d j
    let H := ∑ j ∈ range n, (1 : ℝ) / (j + 1)
    H ≤ S ∧ S ≤ n ∧ (S = H ↔ ∀ j < n, d j = j + 1) ∧ (S = n ↔ ∀ j < n, d j = 1) := by
  intro S H
  have hdpos : ∀ j < n, (0 : ℝ) < d j := fun j hj => by exact_mod_cast (hd j hj).1
  have hterm1 : ∀ j ∈ range n, (1 : ℝ) / (j + 1) ≤ 1 / d j := by
    intro j hj; have hj := mem_range.mp hj
    apply one_div_le_one_div_of_le (hdpos j hj); exact_mod_cast (hd j hj).2
  have hterm2 : ∀ j ∈ range n, (1 : ℝ) / d j ≤ 1 := by
    intro j hj; have hj := mem_range.mp hj
    rw [div_le_one (hdpos j hj)]; exact_mod_cast (hd j hj).1
  refine ⟨sum_le_sum hterm1, ?_, ?_, ?_⟩
  · calc S ≤ ∑ j ∈ range n, (1 : ℝ) := sum_le_sum hterm2
      _ = n := by simp
  · constructor
    · intro heq j hj
      have hsum : ∑ i ∈ range n, ((1 : ℝ) / d i - 1 / (i + 1)) = 0 := by
        rw [sum_sub_distrib]; simp only [S, H] at heq; linarith
      have hnn : ∀ i ∈ range n, 0 ≤ (1 : ℝ) / d i - 1 / (i + 1) :=
        fun i hi => sub_nonneg.mpr (hterm1 i hi)
      have := (sum_eq_zero_iff_of_nonneg hnn).mp hsum j (mem_range.mpr hj)
      have h' : (1 : ℝ) / d j = 1 / (j + 1) := by linarith
      have hdj := hdpos j hj
      rw [div_eq_div_iff hdj.ne' (by positivity), one_mul, one_mul] at h'
      exact_mod_cast h'.symm
    · intro hall; apply sum_congr rfl; intro j hj
      rw [hall j (mem_range.mp hj)]; push_cast; ring
  · constructor
    · intro heq j hj
      have hsum : ∑ i ∈ range n, (1 - (1 : ℝ) / d i) = 0 := by
        have h1 : ∑ i ∈ range n, (1 : ℝ) = n := by simp
        rw [sum_sub_distrib, h1]; simp only [S] at heq; linarith
      have hnn : ∀ i ∈ range n, 0 ≤ 1 - (1 : ℝ) / d i := fun i hi => sub_nonneg.mpr (hterm2 i hi)
      have := (sum_eq_zero_iff_of_nonneg hnn).mp hsum j (mem_range.mpr hj)
      have h' : (1 : ℝ) / d j = 1 := by linarith
      rw [div_eq_one_iff_eq (hdpos j hj).ne'] at h'
      exact_mod_cast h'.symm
    · intro hall
      simp only [S]; rw [sum_congr rfl (fun j hj => by rw [hall j (mem_range.mp hj)])]; simp

/-- **Proposition 6.2 (supersolvable).** If one exponent equals `1` and the other `r - 1`
exponents are integers `≥ 2`, then `∑ 1/e_i ≤ (r+1)/2`, with equality iff they all equal `2`. -/
theorem supersolvable_bound (r : ℕ) (e : ℕ → ℕ) (he : ∀ j < r - 1, 2 ≤ e j) (hr : 1 ≤ r) :
    1 + ∑ j ∈ range (r - 1), (1 : ℝ) / e j ≤ ((r : ℝ) + 1) / 2 ∧
    (1 + ∑ j ∈ range (r - 1), (1 : ℝ) / e j = ((r : ℝ) + 1) / 2 ↔ ∀ j < r - 1, e j = 2) := by
  have hpos : ∀ j < r - 1, (0 : ℝ) < e j := fun j hj => by
    have := he j hj; exact_mod_cast (by omega : 0 < e j)
  have hterm : ∀ j ∈ range (r - 1), (1 : ℝ) / e j ≤ 1 / 2 := by
    intro j hj; have hj := mem_range.mp hj
    apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast he j hj
  have hcount : ∑ j ∈ range (r - 1), (1 : ℝ) / 2 = ((r : ℝ) - 1) / 2 := by
    rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_sub hr]; ring
  refine ⟨?_, ?_⟩
  · have := sum_le_sum hterm; rw [hcount] at this; linarith
  · constructor
    · intro heq j hj
      have hsum : ∑ i ∈ range (r - 1), ((1 : ℝ) / 2 - 1 / e i) = 0 := by
        rw [sum_sub_distrib, hcount]; linarith
      have hnn : ∀ i ∈ range (r - 1), 0 ≤ (1 : ℝ) / 2 - 1 / e i :=
        fun i hi => sub_nonneg.mpr (hterm i hi)
      have := (sum_eq_zero_iff_of_nonneg hnn).mp hsum j (mem_range.mpr hj)
      have h' : (1 : ℝ) / e j = 1 / 2 := by linarith
      rw [div_eq_div_iff (hpos j hj).ne' (by norm_num), one_mul, one_mul] at h'
      exact_mod_cast h'.symm
    · intro hall
      rw [sum_congr rfl (fun j hj => by rw [hall j (mem_range.mp hj)])]
      push_cast; rw [hcount]; ring

/-! ### Uniform matroids -/

/-- alternating partial sums of binomial coefficients -/
theorem alt_partial_sum (N j : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ range (j + 1), (-1 : ℤ) ^ k * (N.choose k : ℤ) = (-1) ^ j * ((N - 1).choose j : ℤ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ']; push_cast; ring

/-- **Example 4.10(a).** `h(U_{r,N}) = C(N, r-1) / C(N-1, r-1) = N / (N - r + 1)`. -/
theorem uniform_h (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) :
    (N.choose (r - 1) : ℝ) / ((N - 1).choose (r - 1)) = N / (N - r + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have key := Nat.choose_mul_succ_eq n (r - 1)
  simp only [Nat.add_sub_cancel]
  have hc : (0 : ℝ) < (n.choose (r - 1) : ℝ) := by exact_mod_cast Nat.choose_pos (by omega)
  have hd : (0 : ℝ) < (n : ℝ) + 1 - r + 1 := by
    have : (r : ℝ) ≤ n + 1 := by exact_mod_cast hrN
    linarith
  push_cast
  rw [div_eq_div_iff hc.ne' hd.ne']
  have : ((n + 1 - (r - 1) : ℕ) : ℝ) = (n : ℝ) + 1 - r + 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub hr]; push_cast; ring
  have key' : (n.choose (r - 1) : ℝ) * (n + 1) = ((n + 1).choose (r - 1) : ℝ) * (n + 1 - r + 1) := by
    rw [← this]; exact_mod_cast key
  linarith

/-- the uniform matroid satisfies Conjecture 6.1: for `N ≥ r + 1`,
`N/(N-r+1) ≤ (r+1)/2`, with equality iff `r = 1` or `N = r + 1`. -/
theorem uniform_conj (N r : ℕ) (hr : 1 ≤ r) (hN : r + 1 ≤ N) :
    (N : ℝ) / (N - r + 1) ≤ ((r : ℝ) + 1) / 2 ∧
      ((N : ℝ) / (N - r + 1) = ((r : ℝ) + 1) / 2 ↔ r = 1 ∨ N = r + 1) := by
  have hNr : (r : ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : (0 : ℝ) < N - r + 1 := by linarith
  have key : ((r : ℝ) + 1) / 2 - N / (N - r + 1) = ((r : ℝ) - 1) * (N - r - 1) / (2 * (N - r + 1)) := by
    field_simp; ring
  have hnn : 0 ≤ ((r : ℝ) - 1) * (N - r - 1) / (2 * (N - r + 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq
    have : ((r : ℝ) - 1) * (N - r - 1) = 0 := by
      have h0 : ((r : ℝ) - 1) * (N - r - 1) / (2 * (N - r + 1)) = 0 := by linarith
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · linarith
    rcases mul_eq_zero.mp this with h | h
    · left; exact_mod_cast (by linarith : (r : ℝ) = 1)
    · right; exact_mod_cast (by linarith : (N : ℝ) = r + 1)
  · rintro (h | h)
    · subst h; field_simp; ring
    · subst h; push_cast; field_simp; ring

/-- **Example 4.10(b) / Section 6 (projective geometries).** For `q ≥ 2` and `r ≥ 1`,
`h = ∑_{i<r} q^{-i} ≤ (r+1)/2`: every term with `i ≥ 1` is at most `1/2`. -/
theorem pg_bound (q : ℝ) (hq : 2 ≤ q) (r : ℕ) (hr : 1 ≤ r) :
    ∑ i ∈ range r, (q ^ i)⁻¹ ≤ ((r : ℝ) + 1) / 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [sum_range_succ']
  have : ∀ i ∈ range s, (q ^ (i + 1))⁻¹ ≤ 1 / 2 := by
    intro i _
    rw [inv_le_comm₀ (by positivity) (by norm_num), one_div, inv_inv]
    calc (2 : ℝ) ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ (i + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have := sum_le_sum this
  simp at this ⊢; linarith

end PartE

end EKLC
