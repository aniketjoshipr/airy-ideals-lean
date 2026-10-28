import AiryIdeals.MainTheorem

/-!
# Transvections (Section 2.4) and the twisted-module form of Theorem 2.28

Let `S` be a stable potential and `Z = exp(-S)`. Following the paper, the **transvection**
`φ_S` is conjugation by the exponential: `φ_S(P) = e^{-S} ∘ P ∘ e^{S}`. It fixes `ħ` and
`ħxₐ`, and sends `ħ∂ₐ ↦ H̄ₐ = ħ∂ₐ + ħ∂ₐS`.

We construct `φ_S` as a `K`-algebra automorphism of `𝒟̂_A^ħ`. The only real work is to show
that the conjugate of an element of `𝒟̂_A^ħ` is again in `𝒟̂_A^ħ`:
* the conjugates of `ħ`, `ħxₐ` and `ħ∂ₐ` are in `𝒟̂_A^ħ` (this uses `deg q^{(n+1)} ≤ n+1`);
* conjugation is multiplicative, so the conjugate of `ħᵐ Pₘ` with `Pₘ ∈ Fₘ` is too;
* conjugation is compatible with `ħ`-adic limits, which handles `P = ∑ₘ ħᵐ Pₘ`.

Multiplicativity, bijectivity and uniqueness all follow from the faithfulness of the action of
`𝒟̂_A^ħ` on `K[x_A]⟦ħ⟧`.

*Remark.* Definition 2.21 of the paper also allows non-stable transvections with `q^{(1)} ≠ 0`.
These do not extend to the completion. If `q^{(1)} = c·x₁` then `φ(ħ∂₁) = ħ∂₁ + c`, and the
image of `∑ₘ ħᵐ ∂₁ᵐ ∈ 𝒟̂_A^ħ` would have `ħ⁰` coefficient `∑ₘ cᵐ`, which does not make sense.
The paper's main results only use stable transvections, and those are what we construct here.

Main results:
* `StablePotential.transvection`: the automorphism `φ_S`;
* `IsAiryIdeal.exists_transvection` (**Theorem 2.28**): `I = φ_S(I_can)` for a stable
  transvection `φ_S`;
* `IsAiryIdeal.quotientEquivTwisted` (**Theorem 2.28**, second part): `𝒟̂_A^ħ / I` is
  isomorphic to the twisted module `^φ M̂_A^ħ`.
-/

open PowerSeries Finset

namespace AiryIdeals

set_option linter.unusedSectionVars false

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K]

/-! ### Generalities on the action -/

lemma act_sub_left (P Q : OpSeries σ K) (f : PolySeries σ K) :
    act (P - Q) f = act P f - act Q f := by
  rw [← smul_def, ← smul_def, ← smul_def, sub_smul]

lemma act_X_pow_mul_left (P : OpSeries σ K) (k : ℕ) (f : PolySeries σ K) :
    act (X ^ k * P) f = X ^ k * act P f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, act_X_mul, ih, ← mul_assoc, ← pow_succ']

lemma X_pow_dvd_act_sub {P Q : OpSeries σ K} {k : ℕ} (h : X ^ k ∣ P - Q) (f : PolySeries σ K) :
    X ^ k ∣ act P f - act Q f := by
  obtain ⟨R, hR⟩ := h
  rw [← act_sub_left, hR, act_X_pow_mul_left]
  exact dvd_mul_right _ _

lemma coeff_act_congr {P Q : OpSeries σ K} {n : ℕ} (h : ∀ i ≤ n, coeff i P = coeff i Q)
    (f : PolySeries σ K) : coeff n (act P f) = coeff n (act Q f) := by
  rw [coeff_act, coeff_act]
  refine sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [h p.1 (by omega)]

lemma X_pow_dvd_sub_trunc (P : OpSeries σ K) (N : ℕ) :
    X ^ N ∣ P - ∑ m ∈ range N, C (coeff m P) * X ^ m := by
  refine X_pow_dvd_iff.mpr fun k hk => ?_
  simp only [map_sub, map_sum, coeff_C_mul_X_pow]
  rw [sum_ite_eq, if_pos (mem_range.mpr hk), sub_self]

lemma C_smul_eq (r : K) (T : Op σ K) :
    (C (r • T) : OpSeries σ K) = algebraMap K (OpSeries σ K) r * C T := by
  rw [PowerSeries.algebraMap_apply, ← map_mul, Algebra.smul_def]

lemma algebraMap_rees_smul (r : K) (f : PolySeries σ K) :
    algebraMap K (ReesWeyl σ K) r • f = r • f := by
  rw [rees_smul_def]
  change act (algebraMap K (OpSeries σ K) r) f = _
  rw [Algebra.algebraMap_eq_smul_one, act_smul_left, act_one]

/-! ### Conjugation by a unit -/

section Conj

variable (U Ui : PolySeries σ K) (hUU : U * Ui = 1)

/-- `P` has a conjugate `U ∘ P ∘ U⁻¹` in `𝒟̂_A^ħ`. -/
def HasConj (P : OpSeries σ K) : Prop :=
  ∃ Y ∈ rees σ K, ∀ f, act Y f = U * act P (Ui * f)

variable {U Ui}
include hUU

lemma hasConj_add {P Q : OpSeries σ K} (hP : HasConj U Ui P) (hQ : HasConj U Ui Q) :
    HasConj U Ui (P + Q) := by
  obtain ⟨Y, hY, hYf⟩ := hP
  obtain ⟨Y', hY', hY'f⟩ := hQ
  exact ⟨Y + Y', add_mem hY hY', fun f => by simp [act_add_left, hYf, hY'f, mul_add]⟩

lemma hasConj_mul {P Q : OpSeries σ K} (hP : HasConj U Ui P) (hQ : HasConj U Ui Q) :
    HasConj U Ui (P * Q) := by
  obtain ⟨Y, hY, hYf⟩ := hP
  obtain ⟨Y', hY', hY'f⟩ := hQ
  refine ⟨Y * Y', mul_mem hY hY', fun f => ?_⟩
  rw [act_mul, hY'f, hYf, ← mul_assoc, mul_comm Ui U, hUU, one_mul, act_mul]

lemma hasConj_algebraMap (r : K) : HasConj U Ui (algebraMap K (OpSeries σ K) r) := by
  refine ⟨_, (rees σ K).algebraMap_mem r, fun f => ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, act_smul_left, act_smul_left, act_one, act_one,
    mul_smul_comm, ← mul_assoc, hUU, one_mul]

lemma hasConj_zero : HasConj U Ui (0 : OpSeries σ K) := by
  simpa using hasConj_algebraMap hUU (0 : K)

lemma hasConj_sum {ι : Type*} (s : Finset ι) {P : ι → OpSeries σ K}
    (h : ∀ i ∈ s, HasConj U Ui (P i)) : HasConj U Ui (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasConj_zero hUU
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact hasConj_add hUU (h i (mem_insert_self i s)) (ih fun j hj => h j (mem_insert_of_mem hj))

variable (hD : ∀ b, ∃ q ∈ reesPoly σ K, ∀ f,
    U * (X * dSer b (Ui * f)) = X * dSer b f + q * f)
include hD

/-- The generators `ħ`, `ħxₐ`, `ħ∂ₐ` have conjugates in `𝒟̂_A^ħ`. -/
lemma hasConj_C_mul_X {g : Op σ K} (hg : g ∈ gens σ K) : HasConj U Ui (C g * X) := by
  induction hg using Submodule.span_induction with
  | zero => simpa using hasConj_zero hUU
  | add _ _ _ _ h₁ h₂ => simpa [add_mul] using hasConj_add hUU h₁ h₂
  | smul r _ _ h =>
    rw [C_smul_eq, mul_assoc]
    exact hasConj_mul hUU (hasConj_algebraMap hUU r) h
  | mem g hg =>
    rcases hg with (hg | ⟨b, rfl⟩) | ⟨b, rfl⟩
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      refine ⟨_, (hbar : ReesWeyl σ K).2, fun f => ?_⟩
      rw [map_one, one_mul, act_hbar, ← mul_one (X : OpSeries σ K), act_X_mul, act_one]
      linear_combination -(X * f) * hUU
    · refine ⟨_, (hx b : ReesWeyl σ K).2, fun f => ?_⟩
      have hC : (C (xOp b) : OpSeries σ K) =
          PowerSeries.map mulOp.toRingHom (C (MvPolynomial.X b)) := by
        rw [map_C]; rfl
      simp only [coe_hx]
      rw [(commute_X _).eq, act_X_mul, act_X_mul, hC, act_map_mulOp, act_map_mulOp]
      linear_combination -(X * C (MvPolynomial.X b) * f) * hUU
    · obtain ⟨q, hq, hqf⟩ := hD b
      refine ⟨_, (barOp (fun _ => ⟨q, hq⟩) b).2, fun f => ?_⟩
      have := barOp_smul (fun _ => ⟨q, hq⟩) b f
      rw [rees_smul_def] at this
      rw [this, ← coe_hd, act_hd, hqf]

/-- `ħᵐ T` has a conjugate for `T ∈ Fₘ`. -/
lemma hasConj_C_mul_X_pow {m : ℕ} {T : Op σ K} (hT : T ∈ bernstein σ K m) :
    HasConj U Ui (C T * X ^ m) := by
  induction hT using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, mul_one, ← PowerSeries.algebraMap_apply]
    exact hasConj_algebraMap hUU r
  | add x y i _ _ hx hy => simpa [add_mul] using hasConj_add hUU hx hy
  | mem_mul g hg i T _ ih =>
    have : (C (g * T) : OpSeries σ K) * X ^ (i + 1) = (C g * X) * (C T * X ^ i) := by
      rw [map_mul, pow_succ', mul_assoc, mul_assoc]
      congr 1
      rw [← mul_assoc, (commute_X (C T)).eq, mul_assoc]
    rw [this]
    exact hasConj_mul hUU (hasConj_C_mul_X hUU hD hg) ih

/-- Every element of `𝒟̂_A^ħ` has a conjugate in `𝒟̂_A^ħ`, by `ħ`-adic approximation. -/
theorem hasConj_of_mem {P : OpSeries σ K} (hP : P ∈ rees σ K) : HasConj U Ui P := by
  have htrunc : ∀ N, HasConj U Ui (∑ m ∈ range N, C (coeff m P) * X ^ m) := fun N =>
    hasConj_sum hUU _ fun m _ => hasConj_C_mul_X_pow hUU hD (hP m)
  choose Y hY hYf using fun n => htrunc (n + 1)
  -- conjugating something `O(ħ^{n+1})` gives something `O(ħ^{n+1})`
  have hconj_dvd : ∀ {A B : OpSeries σ K} {n : ℕ}, X ^ (n + 1) ∣ A - B → ∀ h : PolySeries σ K,
      X ^ (n + 1) ∣ U * act A (Ui * h) - U * act B (Ui * h) := fun hAB h => by
    rw [← mul_sub]; exact dvd_mul_of_dvd_right (X_pow_dvd_act_sub hAB _) _
  have hdiff : ∀ {n N : ℕ}, n ≤ N → X ^ (n + 1) ∣ P - ∑ m ∈ range (N + 1), C (coeff m P) * X ^ m :=
    fun hnN => (pow_dvd_pow X (by omega)).trans (X_pow_dvd_sub_trunc P _)
  -- stability of the coefficients
  have hstab : ∀ n N, n ≤ N → coeff n (Y N) = coeff n (Y n) := by
    intro n N hnN
    refine LinearMap.ext fun v => ?_
    rw [← coeff_act_C_right, ← coeff_act_C_right, hYf, hYf]
    have h1 := hconj_dvd (hdiff hnN) (C v)
    have h2 := hconj_dvd (hdiff (le_refl n)) (C v)
    have := X_pow_dvd_iff.mp (dvd_sub h2 h1) n (Nat.lt_succ_self n)
    rwa [sub_sub_sub_cancel_left, map_sub, sub_eq_zero] at this
  refine ⟨PowerSeries.mk fun n => coeff n (Y n), fun n => by
    rw [coeff_mk]; exact hY n n, fun f => PowerSeries.ext fun n => ?_⟩
  rw [coeff_act_congr (Q := Y n) (fun i hi => by rw [coeff_mk, hstab i n hi]) f, hYf]
  have := X_pow_dvd_iff.mp (hconj_dvd (hdiff (le_refl n)) f) n (Nat.lt_succ_self n)
  rw [map_sub, sub_eq_zero] at this
  exact this.symm

/-- The conjugate `U ∘ P ∘ U⁻¹` of `P ∈ 𝒟̂_A^ħ`. -/
noncomputable def conjFun (P : ReesWeyl σ K) : ReesWeyl σ K :=
  ⟨(hasConj_of_mem hUU hD P.2).choose, (hasConj_of_mem hUU hD P.2).choose_spec.1⟩

lemma conjFun_smul (P : ReesWeyl σ K) (f : PolySeries σ K) :
    conjFun hUU hD P • f = U * (P • (Ui * f)) :=
  (hasConj_of_mem hUU hD P.2).choose_spec.2 f

/-- Conjugation `P ↦ U ∘ P ∘ U⁻¹`, as a `K`-algebra endomorphism of `𝒟̂_A^ħ`. -/
noncomputable def conjAlgHom : ReesWeyl σ K →ₐ[K] ReesWeyl σ K where
  toFun := conjFun hUU hD
  map_one' := by
    refine rees_ext fun f => ?_
    rw [conjFun_smul, one_smul, one_smul, ← mul_assoc, hUU, one_mul]
  map_mul' P Q := by
    refine rees_ext fun f => ?_
    rw [conjFun_smul, mul_smul, mul_smul, conjFun_smul, conjFun_smul, ← mul_assoc Ui U,
      mul_comm Ui U, hUU, one_mul]
  map_zero' := by
    refine rees_ext fun f => ?_
    rw [conjFun_smul, zero_smul, zero_smul, mul_zero]
  map_add' P Q := by
    refine rees_ext fun f => ?_
    rw [conjFun_smul, add_smul, add_smul, conjFun_smul, conjFun_smul, mul_add]
  commutes' r := by
    refine rees_ext fun f => ?_
    rw [conjFun_smul, algebraMap_rees_smul, algebraMap_rees_smul, mul_smul_comm, ← mul_assoc,
      hUU, one_mul]

lemma conjAlgHom_smul (P : ReesWeyl σ K) (f : PolySeries σ K) :
    conjAlgHom hUU hD P • f = U * (P • (Ui * f)) :=
  conjFun_smul hUU hD P f

end Conj

/-! ### The transvection `φ_S` -/

namespace StablePotential

variable (S : StablePotential σ K)

/-- `e^{S} = Z⁻¹`. -/
noncomputable def Zinv : PolySeries σ K := ↑S.isUnit_Z.unit⁻¹

lemma Z_mul_Zinv : S.Z * S.Zinv = 1 := by simp [Zinv]
lemma Zinv_mul_Z : S.Zinv * S.Z = 1 := by rw [mul_comm, Z_mul_Zinv]

lemma dSer_Zinv (b : σ) : dSer b S.Zinv = dSer b S.S * S.Zinv := by
  have h := congrArg (dSer b) S.Z_mul_Zinv
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, dSer_Z, smul_eq_mul, smul_eq_mul] at h
  have : S.Z * (dSer b S.Zinv - dSer b S.S * S.Zinv) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((IsUnit.mul_right_eq_zero S.isUnit_Z).mp this)

lemma neg_dPot_mem (b : σ) : -(S.dPot b : PolySeries σ K) ∈ reesPoly σ K :=
  neg_mem (S.dPot b).2

lemma hD_Z (b : σ) : ∃ q ∈ reesPoly σ K, ∀ f,
    S.Z * (X * dSer b (S.Zinv * f)) = X * dSer b f + q * f := by
  refine ⟨S.dPot b, (S.dPot b).2, fun f => ?_⟩
  rw [Derivation.leibniz, dSer_Zinv, smul_eq_mul, smul_eq_mul]
  change _ = X * dSer b f + X * dSer b S.S * f
  linear_combination (X * dSer b f + X * dSer b S.S * f) * S.Z_mul_Zinv

lemma hD_Zinv (b : σ) : ∃ q ∈ reesPoly σ K, ∀ f,
    S.Zinv * (X * dSer b (S.Z * f)) = X * dSer b f + q * f := by
  refine ⟨-(S.dPot b : PolySeries σ K), S.neg_dPot_mem b, fun f => ?_⟩
  rw [Derivation.leibniz, dSer_Z, smul_eq_mul, smul_eq_mul]
  change _ = X * dSer b f + -(X * dSer b S.S) * f
  linear_combination (X * dSer b f - X * dSer b S.S * f) * S.Zinv_mul_Z

/-- The **stable transvection** `φ_S : P ↦ e^{-S} P e^{S}`, an automorphism of `𝒟̂_A^ħ`. -/
noncomputable def transvection : ReesWeyl σ K ≃ₐ[K] ReesWeyl σ K :=
  AlgEquiv.ofAlgHom (conjAlgHom S.Z_mul_Zinv S.hD_Z) (conjAlgHom S.Zinv_mul_Z S.hD_Zinv)
    (AlgHom.ext fun P => rees_ext fun f => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, conjAlgHom_smul, ← mul_assoc,
        S.Z_mul_Zinv, S.Zinv_mul_Z, one_mul])
    (AlgHom.ext fun P => rees_ext fun f => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, conjAlgHom_smul, ← mul_assoc,
        S.Z_mul_Zinv, S.Zinv_mul_Z, one_mul])

/-- `φ_S` is conjugation by `e^{-S}`. -/
lemma transvection_smul (P : ReesWeyl σ K) (f : PolySeries σ K) :
    S.transvection P • f = S.Z * (P • (S.Zinv * f)) :=
  conjAlgHom_smul S.Z_mul_Zinv S.hD_Z P f

lemma transvection_symm_smul (P : ReesWeyl σ K) (f : PolySeries σ K) :
    S.transvection.symm P • f = S.Zinv * (P • (S.Z * f)) :=
  conjAlgHom_smul S.Zinv_mul_Z S.hD_Zinv P f

/-- `φ_S(ħ) = ħ`. -/
lemma transvection_hbar : S.transvection hbar = hbar := by
  refine rees_ext fun f => ?_
  rw [transvection_smul, hbar_smul, hbar_smul]
  linear_combination X * f * S.Z_mul_Zinv

/-- `φ_S(ħxₐ) = ħxₐ`. -/
lemma transvection_hx (a : σ) : S.transvection (hx a) = hx a := by
  refine rees_ext fun f => ?_
  rw [transvection_smul, rees_smul_def, rees_smul_def]
  have hC : (C (xOp a) : OpSeries σ K) =
      PowerSeries.map mulOp.toRingHom (C (MvPolynomial.X a)) := by rw [map_C]; rfl
  simp only [coe_hx]
  rw [(commute_X _).eq, act_X_mul, act_X_mul, hC, act_map_mulOp, act_map_mulOp]
  linear_combination X * C (MvPolynomial.X a) * f * S.Z_mul_Zinv

/-- `φ_S(ħ∂ₐ) = H̄ₐ = ħ∂ₐ + ħ∂ₐS`. -/
lemma transvection_hd (a : σ) : S.transvection (hd a) = S.barH a := by
  refine rees_ext fun f => ?_
  rw [transvection_smul, hd_smul, barH, barOp_smul, Derivation.leibniz, dSer_Zinv,
    smul_eq_mul, smul_eq_mul]
  change _ = X * dSer a f + X * dSer a S.S * f
  linear_combination (X * dSer a f + X * dSer a S.S * f) * S.Z_mul_Zinv

/-- `⟨H̄ₐ⟩ = φ_S(I_can)`: `P ∈ ⟨H̄ₐ⟩ ↔ φ_S⁻¹(P) ∈ I_can`. -/
lemma mem_ideal_iff (P : ReesWeyl σ K) : P ∈ S.ideal ↔ S.transvection.symm P ∈ Ican σ K := by
  constructor
  · intro hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨a, rfl⟩ := hP
      rw [← transvection_hd, AlgEquiv.symm_apply_apply]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul r _ _ h => rw [smul_eq_mul, map_mul]; exact Submodule.smul_mem _ _ h
  · intro hP
    rw [← S.transvection.apply_symm_apply P]
    generalize S.transvection.symm P = Q at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨a, rfl⟩ := hQ
      rw [transvection_hd]
      exact Submodule.subset_span ⟨a, rfl⟩
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | smul r _ _ h => rw [smul_eq_mul, map_mul]; exact Submodule.smul_mem _ _ h

end StablePotential

/-- **Theorem 2.28.** An Airy ideal is the image `I = φ(I_can)` of the canonical ideal under a
stable transvection `φ`, that is, an automorphism of `𝒟̂_A^ħ` with `φ(ħ) = ħ`, `φ(ħxₐ) = ħxₐ`
and `φ(ħ∂ₐ) = ħ∂ₐ + ∑_{n≥2} ħⁿ ∂ₐ q^{(n+1)}`. -/
theorem IsAiryIdeal.exists_transvection {I : LeftIdeal σ K} (hI : IsAiryIdeal I) :
    ∃ S : StablePotential σ K,
      S.transvection hbar = hbar ∧ (∀ a, S.transvection (hx a) = hx a) ∧
      (∀ a, S.transvection (hd a) = hd a + polyOp (S.dPot a)) ∧
      ∀ P, P ∈ I ↔ S.transvection.symm P ∈ Ican σ K := by
  obtain ⟨S, rfl⟩ := hI.exists_potential
  exact ⟨S, S.transvection_hbar, S.transvection_hx, S.transvection_hd, S.mem_ideal_iff⟩

end AiryIdeals
