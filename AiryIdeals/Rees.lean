import AiryIdeals.Weyl

/-!
# The completed Rees Weyl algebra and its polynomial module (Sections 2.2 and 2.3)

* `OpSeries σ K = Op⟦ħ⟧` is formal power series in `ħ` whose coefficients are operators on
  `K[x_A]`.
* `PolySeries σ K = K[x_A]⟦ħ⟧` is formal power series in `ħ` with polynomial coefficients.
  `OpSeries` acts on `PolySeries` by `(∑ ħⁱ Pᵢ) • (∑ ħʲ fⱼ) = ∑ ħⁱ⁺ʲ Pᵢ(fⱼ)`. This gives the
  standard action of `ħ`-dependent differential operators on `ħ`-dependent functions.
* The **completed Rees Weyl algebra** `rees σ K = 𝒟̂_A^ħ = ∏ₙ ħⁿ Fₙ 𝒟_A` is the subalgebra of
  `OpSeries` of series whose `ħⁿ` coefficient lies in the Bernstein filtration `F n`.
* The **completed Rees polynomial module** `reesPoly σ K = M̂_A^ħ = ∏ₙ ħⁿ Fₙ M_A` is the
  submodule of `PolySeries` of series whose `ħⁿ` coefficient has degree `≤ n`.
-/

open PowerSeries Finset

namespace AiryIdeals

set_option linter.unusedSectionVars false

variable (σ K : Type*) [Field K]

/-- Formal power series in `ħ` with coefficients in the operators `Op σ K`. -/
abbrev OpSeries := PowerSeries (Op σ K)

/-- Formal power series in `ħ` with coefficients in the polynomial ring `K[x_A]`. -/
abbrev PolySeries := PowerSeries (MvPolynomial σ K)

variable {σ K}

/-! ### The action of operator series on polynomial series -/

/-- The action `(∑ ħⁱ Pᵢ) • (∑ ħʲ fⱼ) = ∑ ħⁱ⁺ʲ Pᵢ(fⱼ)`. -/
noncomputable def act (P : OpSeries σ K) (f : PolySeries σ K) : PolySeries σ K :=
  PowerSeries.mk fun n => ∑ p ∈ antidiagonal n, coeff p.1 P (coeff p.2 f)

lemma coeff_act (n : ℕ) (P : OpSeries σ K) (f : PolySeries σ K) :
    coeff n (act P f) = ∑ p ∈ antidiagonal n, coeff p.1 P (coeff p.2 f) := coeff_mk _ _

lemma act_add_left (P Q : OpSeries σ K) (f : PolySeries σ K) :
    act (P + Q) f = act P f + act Q f := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act, sum_add_distrib]

lemma act_add_right (P : OpSeries σ K) (f g : PolySeries σ K) :
    act P (f + g) = act P f + act P g := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act, sum_add_distrib]

@[simp] lemma act_zero_left (f : PolySeries σ K) : act 0 f = 0 := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act]

@[simp] lemma act_zero_right (P : OpSeries σ K) : act P 0 = 0 := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act]

lemma act_one (f : PolySeries σ K) : act 1 f = f := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_act, sum_eq_single (0, n)]
  · simp
  · rintro ⟨i, j⟩ h hne
    rw [HasAntidiagonal.mem_antidiagonal] at h
    have : i ≠ 0 := by rintro rfl; simp_all
    simp [coeff_one, this]
  · simp

lemma act_mul (P Q : OpSeries σ K) (f : PolySeries σ K) :
    act (P * Q) f = act P (act Q f) := by
  refine PowerSeries.ext fun n => ?_
  classical
  simp only [coeff_act, coeff_mul, LinearMap.sum_apply, map_sum, Module.End.mul_apply,
    sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;> aesop (add simp [add_assoc])

lemma act_smul_left (r : K) (P : OpSeries σ K) (f : PolySeries σ K) :
    act (r • P) f = r • act P f := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act, Finset.smul_sum]

lemma act_smul_right (r : K) (P : OpSeries σ K) (f : PolySeries σ K) :
    act P (r • f) = r • act P f := by
  refine PowerSeries.ext fun n => ?_; simp [coeff_act, Finset.smul_sum]

lemma act_sum_left {ι : Type*} (s : Finset ι) (P : ι → OpSeries σ K) (f : PolySeries σ K) :
    act (∑ i ∈ s, P i) f = ∑ i ∈ s, act (P i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, act_add_left, ih]

noncomputable instance : Module (OpSeries σ K) (PolySeries σ K) where
  smul := act
  one_smul := act_one
  mul_smul := act_mul
  smul_zero := act_zero_right
  smul_add := act_add_right
  add_smul P Q f := act_add_left P Q f
  zero_smul := act_zero_left

lemma smul_def (P : OpSeries σ K) (f : PolySeries σ K) : P • f = act P f := rfl

/-- Constant (`ħ`-independent) series act coefficientwise. -/
lemma coeff_act_C (T : Op σ K) (f : PolySeries σ K) (n : ℕ) :
    coeff n (act (C T) f) = T (coeff n f) := by
  rw [coeff_act, sum_eq_single (0, n)]
  · simp
  · rintro ⟨i, j⟩ h hne
    rw [HasAntidiagonal.mem_antidiagonal] at h
    have : i ≠ 0 := by rintro rfl; simp_all
    simp [coeff_C, this]
  · simp

/-- Multiplication-operator series act by multiplication. -/
lemma act_map_mulOp (g f : PolySeries σ K) :
    act (PowerSeries.map mulOp.toRingHom g) f = g * f := by
  refine PowerSeries.ext fun n => ?_
  simp [coeff_act, coeff_mul, coeff_map]

lemma act_X_mul (P : OpSeries σ K) (f : PolySeries σ K) :
    act (X * P) f = X * act P f := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [coeff_act]
  · rw [coeff_act, coeff_succ_X_mul, coeff_act, Finset.Nat.sum_antidiagonal_succ]
    simp [coeff_act]

lemma act_mul_X (P : OpSeries σ K) (f : PolySeries σ K) :
    act P (X * f) = X * act P f := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [coeff_act]
  · rw [coeff_act, coeff_succ_X_mul, coeff_act, Finset.Nat.sum_antidiagonal_succ']
    simp [coeff_succ_X_mul]

lemma coeff_act_C_right (P : OpSeries σ K) (v : MvPolynomial σ K) (n : ℕ) :
    coeff n (act P (C v)) = coeff n P v := by
  rw [coeff_act, sum_eq_single (n, 0)]
  · simp
  · rintro ⟨i, j⟩ h hne
    rw [HasAntidiagonal.mem_antidiagonal] at h
    have : j ≠ 0 := by rintro rfl; simp_all
    simp [coeff_C, this]
  · simp

/-- Faithfulness: an operator series is determined by its action on constants. -/
lemma act_injective {P Q : OpSeries σ K}
    (h : ∀ v : MvPolynomial σ K, act P (C v) = act Q (C v)) : P = Q := by
  refine PowerSeries.ext fun n => LinearMap.ext fun v => ?_
  have := congrArg (coeff n) (h v)
  rwa [coeff_act_C_right, coeff_act_C_right] at this

/-! ### Coefficientwise partial derivatives -/

/-- The partial derivative `∂ₐ` applied to each coefficient of a series. -/
noncomputable def dSerFun (a : σ) (f : PolySeries σ K) : PolySeries σ K :=
  PowerSeries.mk fun n => MvPolynomial.pderiv a (coeff n f)

lemma coeff_dSerFun (a : σ) (f : PolySeries σ K) (n : ℕ) :
    coeff n (dSerFun a f) = MvPolynomial.pderiv a (coeff n f) := coeff_mk _ _

/-- The partial derivative `∂ₐ` acting coefficientwise on `K[x_A]⟦ħ⟧`, as a derivation. -/
noncomputable def dSer (a : σ) : Derivation K (PolySeries σ K) (PolySeries σ K) where
  toFun := dSerFun a
  map_add' f g := by refine PowerSeries.ext fun n => ?_; simp [coeff_dSerFun]
  map_smul' r f := by refine PowerSeries.ext fun n => ?_; simp [coeff_dSerFun]
  map_one_eq_zero' := by
    refine PowerSeries.ext fun n => ?_
    change coeff n (dSerFun a 1) = _
    rw [coeff_dSerFun, coeff_one]
    split_ifs <;> simp
  leibniz' f g := by
    refine PowerSeries.ext fun n => ?_
    change coeff n (dSerFun a (f * g)) = coeff n (f * dSerFun a g + g * dSerFun a f)
    rw [map_add, mul_comm g, coeff_dSerFun, coeff_mul, coeff_mul, coeff_mul, map_sum,
      ← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    simp only [coeff_dSerFun, Derivation.leibniz, smul_eq_mul]
    ring

lemma coeff_dSer (a : σ) (f : PolySeries σ K) (n : ℕ) :
    coeff n (dSer a f) = MvPolynomial.pderiv a (coeff n f) := coeff_dSerFun a f n

lemma dSer_X (a : σ) : dSer a (X : PolySeries σ K) = 0 := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_dSer, coeff_X]
  split_ifs <;> simp

lemma dSer_X_mul (a : σ) (f : PolySeries σ K) : dSer a (X * f) = X * dSer a f := by
  rw [Derivation.leibniz, dSer_X, smul_zero, add_zero, smul_eq_mul]

lemma dSer_C (a : σ) (v : MvPolynomial σ K) :
    dSer a (C v : PolySeries σ K) = C (MvPolynomial.pderiv a v) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_dSer, coeff_C, coeff_C]
  split_ifs <;> simp

lemma act_C_dOp (a : σ) (f : PolySeries σ K) : act (C (dOp a)) f = dSer a f := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_act_C, coeff_dSer, dOp_apply]

/-! ### The completed Rees Weyl algebra -/

variable (σ K)

/-- The **completed Rees Weyl algebra** `𝒟̂_A^ħ = ∏ₙ ħⁿ Fₙ 𝒟_A` (Definition 2.12). Its elements
are power series `∑ ħⁿ Pₙ` with `Pₙ` in the `n`-th piece of the Bernstein filtration. -/
noncomputable def rees : Subalgebra K (OpSeries σ K) where
  carrier := {P | ∀ n, coeff n P ∈ bernstein σ K n}
  mul_mem' {P Q} hP hQ n := by
    rw [coeff_mul]
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp]
    exact bernstein_mul_mem (hP _) (hQ _)
  add_mem' hP hQ n := by rw [map_add]; exact add_mem (hP n) (hQ n)
  algebraMap_mem' r n := by
    rw [PowerSeries.algebraMap_apply, coeff_C]
    split_ifs
    · exact algebraMap_mem_bernstein r n
    · exact zero_mem _

/-- Notation-friendly name for the completed Rees Weyl algebra, as a type. -/
abbrev ReesWeyl := ↥(rees σ K)

variable {σ K}

lemma mem_rees {P : OpSeries σ K} : P ∈ rees σ K ↔ ∀ n, coeff n P ∈ bernstein σ K n :=
  Iff.rfl

/-- `ħ` as an element of `𝒟̂_A^ħ`. -/
noncomputable def hbar : ReesWeyl σ K :=
  ⟨X, fun n => by
    rw [coeff_X]
    split_ifs with h
    · subst h; exact one_mem_bernstein 1
    · exact zero_mem _⟩

/-- `ħ xₐ` as an element of `𝒟̂_A^ħ`. -/
noncomputable def hx (a : σ) : ReesWeyl σ K :=
  ⟨C (xOp a) * X, fun n => by
    rw [coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h; simpa using xOp_mem_bernstein (K := K) a le_rfl
    · simp⟩

/-- `ħ ∂ₐ` as an element of `𝒟̂_A^ħ`. -/
noncomputable def hd (a : σ) : ReesWeyl σ K :=
  ⟨C (dOp a) * X, fun n => by
    rw [coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h; simpa using dOp_mem_bernstein (K := K) a le_rfl
    · simp⟩

@[simp] lemma coe_hbar : ((hbar : ReesWeyl σ K) : OpSeries σ K) = X := rfl
@[simp] lemma coe_hd (a : σ) : ((hd a : ReesWeyl σ K) : OpSeries σ K) = C (dOp a) * X := rfl
@[simp] lemma coe_hx (a : σ) : ((hx a : ReesWeyl σ K) : OpSeries σ K) = C (xOp a) * X := rfl

lemma hbar_mul_comm (P : ReesWeyl σ K) : hbar * P = P * hbar :=
  Subtype.ext (commute_X (P : OpSeries σ K)).symm.eq

lemma hbar_pow_mul_injective (k : ℕ) {P Q : ReesWeyl σ K} (h : hbar ^ k * P = hbar ^ k * Q) :
    P = Q := by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_hbar] at this
  exact X_pow_mul_injective this

/-! ### The completed Rees polynomial module -/

variable (σ K)

/-- The **completed Rees polynomial module** `M̂_A^ħ = ∏ₙ ħⁿ Fₙ M_A`: power series
`∑ ħⁿ fₙ` with `fₙ` a polynomial of degree `≤ n` (Definition 2.18). -/
noncomputable def reesPoly : Submodule (ReesWeyl σ K) (PolySeries σ K) where
  carrier := {f | ∀ n, (coeff n f).totalDegree ≤ n}
  zero_mem' n := by simp
  add_mem' {f g} hf hg n := by
    rw [map_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hf n) (hg n))
  smul_mem' P f hf n := by
    change (coeff n (act (P : OpSeries σ K) f)).totalDegree ≤ n
    rw [coeff_act]
    refine MvPolynomial.totalDegree_finsetSum_le fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [← hp]
    exact bernstein_degree (P.2 p.1) (hf p.2)

variable {σ K}

lemma mem_reesPoly {f : PolySeries σ K} : f ∈ reesPoly σ K ↔ ∀ n, (coeff n f).totalDegree ≤ n :=
  Iff.rfl

lemma rees_smul_def (P : ReesWeyl σ K) (f : PolySeries σ K) :
    P • f = act (P : OpSeries σ K) f := rfl

/-- A polynomial series `∑ ħⁿ fₙ` with `deg fₙ ≤ n`, viewed as a multiplication operator in
`𝒟̂_A^ħ`. Such operators are what the paper calls "polynomials" in `𝒟̂_A^ħ`. -/
noncomputable def polyOp (f : reesPoly σ K) : ReesWeyl σ K :=
  ⟨PowerSeries.map mulOp.toRingHom (f : PolySeries σ K), fun n => by
    rw [coeff_map]
    exact mulOp_mem_bernstein (f.2 n)⟩

lemma act_polyOp (f : reesPoly σ K) (g : PolySeries σ K) :
    act (polyOp f : OpSeries σ K) g = (f : PolySeries σ K) * g :=
  act_map_mulOp _ _

lemma act_hd (a : σ) (f : PolySeries σ K) :
    act ((hd a : ReesWeyl σ K) : OpSeries σ K) f = X * dSer a f := by
  rw [coe_hd, (commute_X (C (dOp a))).eq, act_X_mul, act_C_dOp]

lemma act_hbar (f : PolySeries σ K) : act ((hbar : ReesWeyl σ K) : OpSeries σ K) f = X * f := by
  rw [coe_hbar, ← mul_one (X : OpSeries σ K), act_X_mul, act_one]

/-- Faithfulness of the action of `𝒟̂_A^ħ` on `K[x_A]⟦ħ⟧`. -/
lemma rees_ext {P Q : ReesWeyl σ K} (h : ∀ f : PolySeries σ K, P • f = Q • f) : P = Q :=
  Subtype.ext (act_injective fun v => h (C v))

/-- The map `f ↦ polyOp f` is injective (detected by acting on `1`). -/
lemma act_polyOp_one (f : reesPoly σ K) : (polyOp f) • (1 : PolySeries σ K) = f := by
  rw [rees_smul_def, act_polyOp, mul_one]

end AiryIdeals
