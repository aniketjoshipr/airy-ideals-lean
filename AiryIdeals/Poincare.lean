import Mathlib

/-!
# A polynomial Poincaré lemma

The proofs of Lemma 2.20 and Theorem 2.17 in the paper use Poincaré's lemma: a closed
polynomial one-form `∑ₐ pₐ dxₐ` is exact, `pₐ = ∂ₐ q`, and the primitive `q` can be taken
to have degree at most one more than the `pₐ` and no constant term.

Over a field of characteristic zero we write down an explicit primitive: if
`w = ∑ₐ xₐ pₐ`, then `q` is obtained from `w` by dividing each monomial of degree `d` by `d`.
The proof is the usual one, using the Euler operator `E = ∑ₐ xₐ ∂ₐ`.
-/

open MvPolynomial Finset

namespace AiryIdeals

set_option linter.unusedSectionVars false

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K]

/-- The Euler operator `E = ∑ₐ xₐ ∂ₐ`. -/
noncomputable def euler (p : MvPolynomial σ K) : MvPolynomial σ K :=
  ∑ i, X i * pderiv i p

lemma coeff_X_mul_pderiv (i : σ) (p : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (X i * pderiv i p).coeff m = (m i : K) * p.coeff m := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    split_ifs with h
    · subst h; simp [nsmul_eq_mul]
    · simp

/-- The Euler operator multiplies a monomial of degree `d` by `d`. -/
lemma coeff_euler (p : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (euler p).coeff m = (m.degree : K) * p.coeff m := by
  simp [euler, coeff_X_mul_pderiv, Finsupp.degree_eq_sum, Finset.sum_mul]

/-- In characteristic zero, a polynomial all of whose partial derivatives vanish is constant. -/
lemma eq_C_of_pderiv_eq_zero {f : MvPolynomial σ K} (h : ∀ i, pderiv i f = 0) :
    f = C (f.coeff 0) := by
  classical
  have he : euler f = 0 := by simp [euler, h]
  ext m
  by_cases hm : m = 0
  · subst hm; simp
  · have h0 : (m.degree : K) * f.coeff m = 0 := by rw [← coeff_euler, he]; simp
    have hd : (m.degree : K) ≠ 0 := by
      exact_mod_cast (Finsupp.degree_eq_zero_iff m).not.mpr hm
    rw [coeff_C]; simp only [Ne.symm hm, ↓reduceIte]
    exact (mul_eq_zero.mp h0).resolve_left hd

/-- The explicit primitive of a polynomial one-form `p = ∑ₐ pₐ dxₐ`. -/
noncomputable def primitive (p : σ → MvPolynomial σ K) : MvPolynomial σ K :=
  let w := ∑ a, X a * p a
  ∑ m ∈ w.support, monomial m (w.coeff m / (m.degree : K))

lemma coeff_primitive (p : σ → MvPolynomial σ K) (m : σ →₀ ℕ) :
    (primitive p).coeff m = (∑ a, X a * p a).coeff m / (m.degree : K) := by
  classical
  unfold primitive
  simp only []
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, zero_div]

@[simp]
lemma primitive_zero : primitive (0 : σ → MvPolynomial σ K) = 0 := by
  simp [primitive]

lemma coeff_zero_primitive (p : σ → MvPolynomial σ K) : (primitive p).coeff 0 = 0 := by
  simp [coeff_primitive]

/-- **Poincaré lemma** for polynomial one-forms: the primitive of a closed form is a primitive. -/
theorem pderiv_primitive {p : σ → MvPolynomial σ K}
    (hp : ∀ a b, pderiv a (p b) = pderiv b (p a)) (b : σ) :
    pderiv b (primitive p) = p b := by
  classical
  have hw : pderiv b (∑ a, X a * p a) = p b + euler (p b) := by
    rw [map_sum]
    simp only [Derivation.leibniz, smul_eq_mul, pderiv_X]
    rw [Finset.sum_add_distrib, add_comm]
    congr 1
    · simp [Pi.single_apply]
    · unfold euler
      exact Finset.sum_congr rfl fun a _ => by rw [hp b a]
  ext m
  have h1 := congrArg (fun f : MvPolynomial σ K => f.coeff m) hw
  rw [coeff_pderiv, MvPolynomial.coeff_add, coeff_euler] at h1
  rw [coeff_pderiv, coeff_primitive]
  have hdeg : ((m + Finsupp.single b 1).degree : K) = (m.degree : K) + 1 := by
    simp [map_add, Finsupp.degree_single]
  have hne : (m.degree : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m.degree
  rw [hdeg, div_mul_eq_mul_div, h1, div_eq_iff hne]
  ring

lemma totalDegree_primitive_le {p : σ → MvPolynomial σ K} {n : ℕ}
    (hp : ∀ a, (p a).totalDegree ≤ n) : (primitive p).totalDegree ≤ n + 1 := by
  classical
  have hw : (∑ a, X a * p a).totalDegree ≤ n + 1 := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun a _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    have := hp a
    omega
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  exact (totalDegree_monomial_le _ _).trans ((le_totalDegree hm).trans hw)

end AiryIdeals
