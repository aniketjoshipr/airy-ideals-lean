import AiryIdeals.Poincare

/-!
# The Weyl algebra and its Bernstein filtration (Section 2.2)

We realise the Weyl algebra `𝒟_A = K[x_A]⟨∂_A⟩` concretely, as operators on the polynomial
ring `K[x_A]`: everything lives in the algebra `Op σ K = End_K (K[x_A])`. There,
`xOp a` is multiplication by `xₐ` and `dOp a` is the partial derivative `∂ₐ`.

The **Bernstein filtration** gives degree one to both `xₐ` and `∂ₐ`. We define it as
`F n = gens ^ n`, where `gens = span {1, xₐ, ∂ₐ}`. So `F n` is spanned by the products of at
most `n` generators, and `F i * F j ≤ F (i + j)` holds automatically.

The paper defines `𝒟_A` abstractly by generators and relations. In characteristic zero the
operator realisation is faithful, so it is the same algebra. Working with operators means we
get associativity, and the action on the polynomial module, for free.

The main results of this file are:
* `mulOp_mem_bernstein`: multiplication by a polynomial of degree `≤ n` lies in `F n`;
* `bernstein_decomp`: the "normal ordering" step used in Lemma 2.29. Every `T ∈ F (n+1)`
  can be written as `T = g + ∑ₐ dₐ ∂ₐ`, with `g` a polynomial of degree `≤ n+1` and
  `dₐ ∈ F n`;
* `bernstein_degree`: operators in `F n` raise the degree of polynomials by at most `n`.
-/

open MvPolynomial

namespace AiryIdeals

set_option linter.unusedSectionVars false

variable (σ K : Type*) [Field K]

/-- The ambient algebra of `K`-linear operators on `K[x_A]`. -/
abbrev Op := Module.End K (MvPolynomial σ K)

/-- The ring structure on `Op σ K`, registered directly. Without it, nested instance searches
(for example for left ideals of `𝒟̂_A^ħ`) fail to unify `Op σ K` with `Module.End ?R ?M`. -/
noncomputable instance (priority := high) opRing : Ring (Op σ K) := Module.End.instRing

variable {σ K}

/-- Multiplication operators, as a `K`-algebra map `K[x_A] → Op`. -/
noncomputable def mulOp : MvPolynomial σ K →ₐ[K] Op σ K := Algebra.lmul K _

@[simp] lemma mulOp_apply (f g : MvPolynomial σ K) : mulOp f g = f * g := rfl

/-- The operator `xₐ`. -/
noncomputable def xOp (a : σ) : Op σ K := mulOp (X a)

/-- The operator `∂ₐ`. -/
noncomputable def dOp (a : σ) : Op σ K := (pderiv a).toLinearMap

@[simp] lemma dOp_apply (a : σ) (f : MvPolynomial σ K) : dOp a f = pderiv a f := rfl

/-- The basic commutation relation `[∂ₐ, f] = ∂ₐ f`. -/
lemma dOp_mul_mulOp (a : σ) (f : MvPolynomial σ K) :
    dOp a * mulOp f = mulOp (pderiv a f) + mulOp f * dOp a := by
  refine LinearMap.ext fun g => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp_apply, dOp_apply,
    Derivation.leibniz, smul_eq_mul]
  ring

lemma mulOp_comm (f g : MvPolynomial σ K) : mulOp f * mulOp g = mulOp g * mulOp f := by
  rw [← map_mul, mul_comm, map_mul]

variable (σ K)

/-- The generating subspace `span {1, xₐ, ∂ₐ}` of the Bernstein filtration. -/
noncomputable def gens : Submodule K (Op σ K) :=
  Submodule.span K ({1} ∪ Set.range xOp ∪ Set.range dOp)

/-- The **Bernstein filtration** `F n = span {1, xₐ, ∂ₐ} ^ n`. -/
noncomputable def bernstein (n : ℕ) : Submodule K (Op σ K) := gens σ K ^ n

variable {σ K}

lemma one_mem_gens : (1 : Op σ K) ∈ gens σ K :=
  Submodule.subset_span (by simp)

lemma xOp_mem_gens (a : σ) : xOp a ∈ gens σ K :=
  Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩))

lemma dOp_mem_gens (a : σ) : dOp a ∈ gens σ K :=
  Submodule.subset_span (Or.inr ⟨a, rfl⟩)

lemma bernstein_mono {m n : ℕ} (h : m ≤ n) : bernstein σ K m ≤ bernstein σ K n :=
  pow_le_pow_right' (Submodule.one_le.mpr one_mem_gens) h

lemma bernstein_mul_mem {m n : ℕ} {S T : Op σ K} (hS : S ∈ bernstein σ K m)
    (hT : T ∈ bernstein σ K n) : S * T ∈ bernstein σ K (m + n) := by
  rw [bernstein, pow_add]
  exact Submodule.mul_mem_mul hS hT

lemma algebraMap_mem_bernstein (r : K) (n : ℕ) : algebraMap K (Op σ K) r ∈ bernstein σ K n :=
  bernstein_mono (Nat.zero_le n) (by simp [bernstein])

lemma one_mem_bernstein (n : ℕ) : (1 : Op σ K) ∈ bernstein σ K n := by
  simpa using algebraMap_mem_bernstein (σ := σ) (1 : K) n

lemma gens_le_bernstein {n : ℕ} (hn : 1 ≤ n) : gens σ K ≤ bernstein σ K n := by
  simpa [bernstein] using bernstein_mono (σ := σ) (K := K) hn

lemma xOp_mem_bernstein (a : σ) {n : ℕ} (hn : 1 ≤ n) : xOp a ∈ bernstein σ K n :=
  gens_le_bernstein hn (xOp_mem_gens a)

lemma dOp_mem_bernstein (a : σ) {n : ℕ} (hn : 1 ≤ n) : dOp a ∈ bernstein σ K n :=
  gens_le_bernstein hn (dOp_mem_gens a)

/-- Multiplication by a monomial of degree `d` lies in `F d`. -/
lemma mulOp_monomial_mem (m : σ →₀ ℕ) (c : K) :
    mulOp (monomial m c) ∈ bernstein σ K m.degree := by
  induction m using Finsupp.induction with
  | zero =>
    simpa [← C_apply, ← algebraMap_eq] using algebraMap_mem_bernstein (σ := σ) c 0
  | single_add a b f _ _ ih =>
    rw [monomial_single_add, map_mul, map_add, Finsupp.degree_single, map_pow]
    exact bernstein_mul_mem (Submodule.pow_mem_pow _ (xOp_mem_gens a) b) ih

/-- Multiplication by a polynomial of degree `≤ n` lies in `F n`. -/
lemma mulOp_mem_bernstein {f : MvPolynomial σ K} {n : ℕ} (hf : f.totalDegree ≤ n) :
    mulOp f ∈ bernstein σ K n := by
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => bernstein_mono ?_ (mulOp_monomial_mem m _)
  exact (le_totalDegree hm).trans hf

lemma totalDegree_pderiv_le (i : σ) (f : MvPolynomial σ K) :
    (pderiv i f).totalDegree ≤ f.totalDegree := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [pderiv_monomial]
  refine (totalDegree_monomial_le _ _).trans ((Finsupp.degree_mono tsub_le_self).trans ?_)
  exact le_totalDegree hm

/-- Partial derivatives lower the total degree by one. -/
lemma totalDegree_pderiv_le_sub (i : σ) (f : MvPolynomial σ K) :
    (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmi : m i = 0
  · simp [hmi]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have h1 := le_totalDegree hm
    have h2 : (m - Finsupp.single i 1).degree + (Finsupp.single i 1).degree = m.degree := by
      rw [← map_add, tsub_add_cancel_of_le]
      exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hmi)
    rw [Finsupp.degree_single] at h2
    change (m - Finsupp.single i 1).degree ≤ _
    change m.degree ≤ _ at h1
    omega

/-! ### Normal ordering -/

variable [Fintype σ]

/-- `T` can be written as `g + ∑ₐ dₐ ∂ₐ`, with `g` of degree `≤ n + 1` and `dₐ ∈ F n`. -/
def NormalForm (n : ℕ) (T : Op σ K) : Prop :=
  ∃ g : MvPolynomial σ K, g.totalDegree ≤ n + 1 ∧ ∃ d : σ → Op σ K,
    (∀ a, d a ∈ bernstein σ K n) ∧ T = mulOp g + ∑ a, d a * dOp a

lemma NormalForm.zero (n : ℕ) : NormalForm n (0 : Op σ K) :=
  ⟨0, by simp, 0, fun _ => zero_mem _, by simp⟩

lemma NormalForm.add {n : ℕ} {S T : Op σ K} (hS : NormalForm n S) (hT : NormalForm n T) :
    NormalForm n (S + T) := by
  obtain ⟨g, hg, d, hd, rfl⟩ := hS
  obtain ⟨g', hg', d', hd', rfl⟩ := hT
  refine ⟨g + g', (totalDegree_add _ _).trans (max_le hg hg'), d + d',
    fun a => add_mem (hd a) (hd' a), ?_⟩
  simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

lemma NormalForm.smul {n : ℕ} {T : Op σ K} (r : K) (hT : NormalForm n T) :
    NormalForm n (r • T) := by
  obtain ⟨g, hg, d, hd, rfl⟩ := hT
  refine ⟨r • g, (totalDegree_smul_le _ _).trans hg, r • d,
    fun a => Submodule.smul_mem _ r (hd a), ?_⟩
  simp [smul_add, Finset.smul_sum, map_smul]

lemma NormalForm.mono {m n : ℕ} (h : m ≤ n) {T : Op σ K} (hT : NormalForm m T) :
    NormalForm n T := by
  obtain ⟨g, hg, d, hd, rfl⟩ := hT
  exact ⟨g, by omega, d, fun a => bernstein_mono h (hd a), rfl⟩

/-- Elements of `F 1 = span {1, xₐ, ∂ₐ}` are in normal form. -/
lemma normalForm_of_mem_gens {T : Op σ K} (hT : T ∈ gens σ K) : NormalForm 0 T := by
  classical
  induction hT using Submodule.span_induction with
  | zero => exact NormalForm.zero 0
  | add _ _ _ _ h₁ h₂ => exact h₁.add h₂
  | smul r _ _ h => exact h.smul r
  | mem T hT =>
    rcases hT with (hT | ⟨a, rfl⟩) | ⟨a, rfl⟩
    · rw [Set.mem_singleton_iff] at hT
      subst hT
      exact ⟨1, by simp, 0, fun _ => zero_mem _, by simp⟩
    · exact ⟨X a, by simp [totalDegree_X], 0, fun _ => zero_mem _, by simp [xOp]⟩
    · refine ⟨0, by simp, Pi.single a 1, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h; simpa using one_mem_bernstein (σ := σ) (K := K) 0
        · simp [h]
      · simp [Pi.single_apply]

/-- Left multiplication by a generator moves normal forms from level `n` to level `n + 1`. -/
lemma NormalForm.gens_mul {n : ℕ} {S T : Op σ K} (hS : S ∈ gens σ K) (hT : NormalForm n T) :
    NormalForm (n + 1) (S * T) := by
  classical
  obtain ⟨g, hg, d, hd, rfl⟩ := hT
  induction hS using Submodule.span_induction with
  | zero => simpa using NormalForm.zero (n + 1)
  | add _ _ _ _ h₁ h₂ => simpa [add_mul] using h₁.add h₂
  | smul r _ _ h => simpa [smul_mul_assoc] using h.smul r
  | mem S hS =>
    rcases hS with (hS | ⟨b, rfl⟩) | ⟨b, rfl⟩
    · rw [Set.mem_singleton_iff] at hS
      subst hS
      rw [one_mul]
      exact NormalForm.mono (Nat.le_succ n) ⟨g, hg, d, hd, rfl⟩
    · refine ⟨X b * g, ?_, fun a => xOp b * d a, fun a => ?_, ?_⟩
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · simpa [add_comm] using bernstein_mul_mem (xOp_mem_bernstein b le_rfl) (hd a)
      · simp [mul_add, Finset.mul_sum, xOp, mul_assoc]
    · refine ⟨pderiv b g, (totalDegree_pderiv_le b g).trans (by omega),
        fun a => dOp b * d a + if a = b then mulOp g else 0, fun a => ?_, ?_⟩
      · refine add_mem ?_ ?_
        · simpa [add_comm] using bernstein_mul_mem (dOp_mem_bernstein b le_rfl) (hd a)
        · split_ifs
          · exact mulOp_mem_bernstein hg
          · exact zero_mem _
      · simp only [mul_add, dOp_mul_mulOp, Finset.mul_sum, add_mul, Finset.sum_add_distrib,
          ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]
        abel

/-- **Normal ordering.** Every `T ∈ F (n + 1)` can be written as `g + ∑ₐ dₐ ∂ₐ`, with `g` a
polynomial of degree `≤ n + 1` and `dₐ ∈ F n`. -/
theorem bernstein_decomp {n : ℕ} {T : Op σ K} (hT : T ∈ bernstein σ K (n + 1)) :
    NormalForm n T := by
  induction n generalizing T with
  | zero =>
    rw [bernstein, zero_add, pow_one] at hT
    exact normalForm_of_mem_gens hT
  | succ n ih =>
    rw [bernstein, pow_succ'] at hT
    induction hT using Submodule.mul_induction_on' with
    | mem_mul_mem S hS T hT => exact NormalForm.gens_mul hS (ih hT)
    | add _ _ _ _ h₁ h₂ => exact h₁.add h₂

omit [Fintype σ] in
/-- Elements of `F 0` are scalars. -/
lemma mem_bernstein_zero {T : Op σ K} (hT : T ∈ bernstein σ K 0) :
    ∃ r : K, T = mulOp (C r) := by
  rw [bernstein, pow_zero, Submodule.mem_one] at hT
  obtain ⟨r, rfl⟩ := hT
  exact ⟨r, by rw [← algebraMap_eq, AlgHom.commutes]⟩

omit [Fintype σ] in
/-- Operators in `F n` raise the degree of polynomials by at most `n`. -/
theorem bernstein_degree {n : ℕ} {T : Op σ K} (hT : T ∈ bernstein σ K n)
    {f : MvPolynomial σ K} {j : ℕ} (hf : f.totalDegree ≤ j) : (T f).totalDegree ≤ n + j := by
  induction hT using Submodule.pow_induction_on_left' generalizing f j with
  | algebraMap r =>
    simpa using (totalDegree_smul_le r f).trans hf
  | add S T i _ _ hS hT =>
    exact (totalDegree_add _ _).trans (max_le (hS hf) (hT hf))
  | mem_mul S hS i T _ ih =>
    have key : ∀ g : MvPolynomial σ K, g.totalDegree ≤ i + j →
        (S g).totalDegree ≤ i + 1 + j := by
      intro g hg
      induction hS using Submodule.span_induction with
      | zero => simp
      | add _ _ _ _ h₁ h₂ => exact (totalDegree_add _ _).trans (max_le h₁ h₂)
      | smul r _ _ h => exact (totalDegree_smul_le _ _).trans h
      | mem S hS =>
        rcases hS with (hS | ⟨b, rfl⟩) | ⟨b, rfl⟩
        · rw [Set.mem_singleton_iff] at hS
          subst hS
          simp only [Module.End.one_apply]; omega
        · simp only [xOp, mulOp_apply]
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X]; omega
        · exact (totalDegree_pderiv_le b g).trans (by omega)
    exact key _ (ih hf)

end AiryIdeals

namespace AiryIdeals

/-! ### Commutators lower the Bernstein degree by two (the commutator estimate) -/

variable {σ K : Type*} [Field K]

lemma mulOp_C_mem_bernstein_zero (r : K) : mulOp (C r : MvPolynomial σ K) ∈ bernstein σ K 0 :=
  mulOp_mem_bernstein (by simp)

/-- Commutators of two generators are scalars. -/
lemma gens_comm_mem {S T : Op σ K} (hS : S ∈ gens σ K) (hT : T ∈ gens σ K) :
    S * T - T * S ∈ bernstein σ K 0 := by
  classical
  induction hS using Submodule.span_induction with
  | zero => simp
  | add _ _ _ _ h₁ h₂ =>
    have : _ := add_mem h₁ h₂
    convert this using 1; noncomm_ring
  | smul r _ _ h =>
    have : _ := Submodule.smul_mem _ r h
    convert this using 1; simp [smul_sub]
  | mem S hS =>
    induction hT using Submodule.span_induction with
    | zero => simp
    | add _ _ _ _ h₁ h₂ =>
      have : _ := add_mem h₁ h₂
      convert this using 1; noncomm_ring
    | smul r _ _ h =>
      have : _ := Submodule.smul_mem _ r h
      convert this using 1; simp [smul_sub]
    | mem T hT =>
      have hxx : ∀ a b : σ, xOp a * xOp b - xOp b * xOp a = (0 : Op σ K) := fun a b => by
        simp [xOp, mulOp_comm]
      have hdd : ∀ a b : σ, dOp a * dOp b - dOp b * dOp a = (0 : Op σ K) := fun a b => by
        refine LinearMap.ext fun f => ?_
        simp [pderiv_comm]
      have hdx : ∀ a b : σ, dOp a * xOp b - xOp b * dOp a ∈ bernstein σ K 0 := fun a b => by
        rw [xOp, dOp_mul_mulOp, add_sub_cancel_right, pderiv_X]
        by_cases h : a = b
        · subst h; simpa using mulOp_C_mem_bernstein_zero (σ := σ) (1 : K)
        · simp [Pi.single_apply, Ne.symm h]
      rcases hS with (hS | ⟨a, rfl⟩) | ⟨a, rfl⟩ <;>
        rcases hT with (hT | ⟨b, rfl⟩) | ⟨b, rfl⟩
      all_goals first
        | (rw [Set.mem_singleton_iff] at hS; subst hS; simp)
        | (rw [Set.mem_singleton_iff] at hT; subst hT; simp)
        | (rw [hxx]; exact zero_mem _)
        | (rw [hdd]; exact zero_mem _)
        | exact hdx a b
        | (rw [← neg_sub]; exact neg_mem (hdx b a))

/-- `[gens, F (n+1)] ⊆ F n`. -/
lemma gens_comm_bernstein {n : ℕ} {S T : Op σ K} (hS : S ∈ gens σ K)
    (hT : T ∈ bernstein σ K (n + 1)) : S * T - T * S ∈ bernstein σ K n := by
  induction n generalizing T with
  | zero =>
    rw [bernstein, zero_add, pow_one] at hT
    exact gens_comm_mem hS hT
  | succ n ih =>
    rw [bernstein, pow_succ'] at hT
    induction hT using Submodule.mul_induction_on' with
    | mem_mul_mem g hg T hT =>
      have h1 := bernstein_mul_mem (gens_comm_mem hS hg) hT
      have h2 := bernstein_mul_mem (gens_le_bernstein le_rfl hg) (ih hT)
      rw [zero_add] at h1
      rw [add_comm] at h2
      have := add_mem h1 h2
      convert this using 1
      noncomm_ring
    | add _ _ _ _ h₁ h₂ =>
      have := add_mem h₁ h₂
      convert this using 1; noncomm_ring

/-- **Commutator estimate.** `[F (m+1), F (n+1)] ⊆ F (m+n)`, i.e. commutators lower the Bernstein
degree by two. -/
theorem bernstein_comm_mem {m n : ℕ} {S T : Op σ K} (hS : S ∈ bernstein σ K (m + 1))
    (hT : T ∈ bernstein σ K (n + 1)) : S * T - T * S ∈ bernstein σ K (m + n) := by
  induction m generalizing S with
  | zero =>
    rw [bernstein, zero_add, pow_one] at hS
    rw [zero_add]
    exact gens_comm_bernstein hS hT
  | succ m ih =>
    rw [bernstein, pow_succ'] at hS
    induction hS using Submodule.mul_induction_on' with
    | mem_mul_mem g hg S hS =>
      have h1 := bernstein_mul_mem (gens_le_bernstein le_rfl hg) (ih hS)
      have h2 := bernstein_mul_mem (gens_comm_bernstein hg hT) hS
      rw [show 1 + (m + n) = m + 1 + n by omega] at h1
      rw [show n + (m + 1) = m + 1 + n by omega] at h2
      have := add_mem h1 h2
      convert this using 1
      noncomm_ring
    | add _ _ _ _ h₁ h₂ =>
      have := add_mem h₁ h₂
      convert this using 1; noncomm_ring

/-- Elements of `F 0` are central. -/
lemma bernstein_zero_comm {S : Op σ K} (hS : S ∈ bernstein σ K 0) (T : Op σ K) :
    S * T = T * S := by
  rw [bernstein, pow_zero, Submodule.mem_one] at hS
  obtain ⟨r, rfl⟩ := hS
  exact Algebra.commutes r T

end AiryIdeals
