import Mathlib

/-!
# The exponential of a power series with no constant term

The partition function of an Airy ideal has the form `Z = exp F`, with `F ∈ ħ·K[x_A]⟦ħ⟧`.
This file defines `hexp F = ∑ₖ Fᵏ / k!` for a power series `F` with zero constant term, over
any commutative algebra `B` over a field of characteristic zero. The sum converges
`ħ`-adically: only the terms with `k ≤ n` contribute to the `ħⁿ` coefficient.

The key fact is the chain rule `D (exp F) = D F * exp F`, valid for every derivation `D` that
acts coefficientwise.
-/

open PowerSeries Finset

namespace AiryIdeals

variable {K B : Type*} [Field K] [CharZero K] [CommRing B] [Algebra K B]

variable (K) in
/-- The truncated exponential `∑_{k < N} Fᵏ / k!`. -/
noncomputable def expTrunc (N : ℕ) (F : PowerSeries B) : PowerSeries B :=
  ∑ k ∈ range N, ((k.factorial : K)⁻¹) • F ^ k

variable (K) in
/-- The exponential `exp F = ∑ₖ Fᵏ / k!` of a power series. It is meaningful when `F` has
zero constant term. -/
noncomputable def hexp (F : PowerSeries B) : PowerSeries B :=
  PowerSeries.mk fun n => coeff n (expTrunc K (n + 1) F)

lemma coeff_pow_eq_zero_of_lt {F : PowerSeries B} (hF : constantCoeff F = 0) {n k : ℕ}
    (h : n < k) : coeff n (F ^ k) = 0 :=
  X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hF) k) n h

lemma coeff_expTrunc_succ {F : PowerSeries B} (hF : constantCoeff F = 0) {n M : ℕ}
    (h : n < M) : coeff n (expTrunc K (M + 1) F) = coeff n (expTrunc K M F) := by
  rw [expTrunc, sum_range_succ, map_add, coeff_smul, coeff_pow_eq_zero_of_lt hF h, smul_zero,
    add_zero, expTrunc]

lemma coeff_expTrunc_eq {F : PowerSeries B} (hF : constantCoeff F = 0) {n N : ℕ} (h : n < N) :
    coeff n (expTrunc K N F) = coeff n (expTrunc K (n + 1) F) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · rw [coeff_expTrunc_succ hF h, ih h]
    · rw [h]

lemma coeff_hexp {F : PowerSeries B} (hF : constantCoeff F = 0) {n N : ℕ} (h : n < N) :
    coeff n (hexp K F) = coeff n (expTrunc K N F) := by
  rw [hexp, coeff_mk, coeff_expTrunc_eq hF h]

lemma X_pow_dvd_hexp_sub {F : PowerSeries B} (hF : constantCoeff F = 0) (N : ℕ) :
    X ^ N ∣ hexp K F - expTrunc K N F :=
  X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, coeff_hexp hF hi, sub_self]

lemma constantCoeff_hexp {F : PowerSeries B} (hF : constantCoeff F = 0) :
    constantCoeff (hexp K F) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_hexp hF (Nat.zero_lt_one)]
  simp [expTrunc]

lemma isUnit_hexp {F : PowerSeries B} (hF : constantCoeff F = 0) : IsUnit (hexp K F) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_hexp hF]
  exact isUnit_one

lemma map_smul_powerSeries {B' : Type*} [CommRing B'] [Algebra K B'] (ψ : B →ₐ[K] B')
    (r : K) (G : PowerSeries B) :
    PowerSeries.map ψ.toRingHom (r • G) = r • PowerSeries.map ψ.toRingHom G := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply, map_C]
  simp

lemma map_hexp {B' : Type*} [CommRing B'] [Algebra K B'] (ψ : B →ₐ[K] B')
    {F : PowerSeries B} (hF : constantCoeff F = 0) :
    PowerSeries.map ψ.toRingHom (hexp K F) = hexp K (PowerSeries.map ψ.toRingHom F) := by
  have hF' : constantCoeff (PowerSeries.map ψ.toRingHom F) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hF,
      map_zero]
  refine PowerSeries.ext fun n => ?_
  rw [coeff_map, coeff_hexp hF (Nat.lt_succ_self n), coeff_hexp hF' (Nat.lt_succ_self n),
    ← coeff_map]
  congr 1
  simp only [expTrunc, map_sum]
  exact sum_congr rfl fun k _ => by rw [← map_pow]; exact map_smul_powerSeries ψ _ _

/-- Derivative of a truncated exponential. -/
lemma derivation_expTrunc (D : Derivation K (PowerSeries B) (PowerSeries B))
    (F : PowerSeries B) (M : ℕ) :
    D (expTrunc K (M + 1) F) = D F * expTrunc K M F := by
  have key : ∀ k : ℕ, D (((k + 1).factorial : K)⁻¹ • F ^ (k + 1)) =
      D F * ((k.factorial : K)⁻¹ • F ^ k) := by
    intro k
    rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, mul_smul_comm, mul_comm (F ^ k)]
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [expTrunc, map_sum, sum_range_succ', expTrunc, mul_sum]
  simp only [key, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    Derivation.map_one_eq_zero, add_zero]

/-- **Chain rule** for the exponential, for derivations acting coefficientwise. -/
lemma derivation_hexp (D : Derivation K (PowerSeries B) (PowerSeries B)) (d : B → B)
    (hD : ∀ f n, coeff n (D f) = d (coeff n f)) {F : PowerSeries B}
    (hF : constantCoeff F = 0) : D (hexp K F) = D F * hexp K F := by
  refine PowerSeries.ext fun n => ?_
  have h1 : coeff n (D (hexp K F)) = coeff n (D (expTrunc K (n + 2) F)) := by
    rw [hD, hD, coeff_hexp hF (by omega : n < n + 2)]
  have h2 : coeff n (D F * hexp K F) = coeff n (D F * expTrunc K (n + 1) F) := by
    have := X_pow_dvd_iff.mp (dvd_mul_of_dvd_right (X_pow_dvd_hexp_sub (K := K) hF (n + 1))
      (D F)) n (Nat.lt_succ_self n)
    rwa [mul_sub, map_sub, sub_eq_zero] at this
  rw [h1, h2, derivation_expTrunc]

end AiryIdeals
