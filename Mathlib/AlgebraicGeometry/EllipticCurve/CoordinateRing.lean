/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Coordinate ring of an elliptic curve

We show that the (affine) coordinate ring of an elliptic curve is a Dedekind domain.

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Non-principal.20ideal.20in.20Dedekind.20domain/near/538662428
for a proof outline.
-/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

abbrev Polynomial.toRatFunc {R} [CommRing R] : R[X] →+* FractionRing R[X] :=
  algebraMap ..

lemma Polynomial.toRatFunc_X_ne_zero {R} [CommRing R] [Nontrivial R] : (X : R[X]).toRatFunc ≠ 0 :=
  by simp

namespace WeierstrassCurve

def CoordinateRing.variableChange {R} [CommRing R] (W : WeierstrassCurve.Affine R)
    (e : VariableChange R) : W.CoordinateRing ≃ₐ[R] (e • W).CoordinateRing := by
  sorry /- The isomorphism is given by `(X, Y) ↔ (u²X + r, u³Y + u²sX + t)`. -/

namespace Affine
/- A type synonym of WeierstrassCurve to give access to affine versions of the Weierstrass
polynomial and coordinate ring, etc. -/

variable {K : Type*} [Field K] (E : WeierstrassCurve.Affine K)

notation:10000 K"(X)" => FractionRing K[X]

/-- Another implementation of the function field of a Weierstrass curve, as `K(X)[Y]` modulo
the Weierstrass polynomial. -/
abbrev FunctionField' := AdjoinRoot <| E.polynomial.map (algebraMap K[X] K(X))
-- another implementation could be K(X) ⊗[K[X]] E.CoordinateRing

instance : Fact (Irreducible <| E.polynomial.map (algebraMap K[X] K(X))) := by
  sorry
  -- use Gauss lemma: Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map

attribute [local instance] Polynomial.algebra in
instance : Algebra E.CoordinateRing E.FunctionField' :=
  Ideal.Quotient.algebraQuotientOfLEComap <| by
    sorry

instance : IsScalarTower K[X] E.CoordinateRing E.FunctionField' := by
  sorry

instance : Module.Free K[X] E.CoordinateRing := .of_basis (CoordinateRing.basis E)
instance : Module.Finite K[X] E.CoordinateRing := E.monic_polynomial.finite_adjoinRoot
instance : FiniteDimensional K(X) E.FunctionField' := (E.monic_polynomial.map _).finite_adjoinRoot

variable (p q : K(X))

-- rename to `addMulY`?
def comb : E.FunctionField' := p • 1 + q • .mk _ X

-- An arbitrary element of the function field can be written in the form p(X) + q(X)Y
theorem FunctionField'.exists_comb_eq (f : E.FunctionField') :
    ∃ p q : K(X), E.comb p q = f := by
  sorry
  -- mimic the proof of `CoordinateRing.exists_smul_basis_eq`
  -- may need to develop some basis API

instance : FaithfulSMul E.CoordinateRing E.FunctionField' :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr <| by
    sorry
  /- Write an element in the coordinate ring K[E] as p+qY using
    `CoordinateRing.exists_smul_basis_eq`, and show its image can't be zero unless p = q = 0. -/

instance : IsFractionRing E.CoordinateRing E.FunctionField' := .of_field _ _ <| by
  sorry

-- may be unnecessary for the final goal
theorem isIntegral_coordinateRing_iff {f : E.FunctionField'} :
    IsIntegral E.CoordinateRing f ↔ IsIntegral K[X] f := by
  sorry -- use that E.CoordinateRing is integral over K[X]

-- this deals with the q = 0 case
theorem isIntegral_algebraMap_iff {p : K(X)} :
    IsIntegral K[X] (algebraMap _ E.FunctionField' p) ↔ p ∈ toRatFunc.range := by
  sorry -- use that K[X] is integrally closed in K(X), and `isIntegral_algHom_iff`

def trace : K(X) :=
  2 * p - q * (C E.a₁ * X + C E.a₃).toRatFunc

def norm : K(X) :=
  p ^ 2 - p * q * (C E.a₁ * X + C E.a₃).toRatFunc -
    q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆).toRatFunc

-- If q ≠ 0, the minimal polynomial of f = p + qY is quadratic, given by Z² - Tr(f)Z + N(f).
theorem minpoly_comb (hq : q ≠ 0) :
    minpoly K(X) (E.comb p q) = X ^ 2 - C (E.trace p q) * X + C (E.norm p q) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · sorry
  · sorry
  · sorry

theorem trace_sq_sub_four_mul_norm :
    E.trace p q ^ 2 - 4 * E.norm p q = q ^ 2 * E.twoTorsionPolynomial.toPoly.toRatFunc := by
  sorry

theorem isIntegral_of_sq_add_mem_range {R A} [CommRing R] [Ring A] [Algebra R A] (r₀ r₁ : R) (a : A)
    (h : a ^ 2 + algebraMap R A r₁ * a + algebraMap R A r₀ ∈ (algebraMap R A).range) :
    IsIntegral R a := by
  sorry

/- If q and N(p+qY) lie in K[X], then p satisfies a monic quadratic equation
with coefficients in K[X], so p is integral over K[X] and therefore in K[X]. -/
theorem left_mem_of_right_mem_of_norm_mem (hq : q ∈ toRatFunc.range)
    (hn : E.norm p q ∈ toRatFunc.range) : p ∈ toRatFunc.range := by
  sorry -- obtain from hq, rewrite E.norm, then apply `isIntegral_of_sq_add_mem_range`

variable {p q} (int : IsIntegral K[X] (E.comb p q))
include int

theorem trace_mem_of_isIntegral : E.trace p q ∈ toRatFunc.range := by
  sorry -- use minpoly.isIntegrallyClosed_eq_field_fractions'

theorem norm_mem_of_isIntegral : E.norm p q ∈ toRatFunc.range := by
  sorry -- ditto

variable [E.IsElliptic]

section IsUnit2

variable (h2 : IsUnit (2 : K))

-- `E.twoTorsionPolynomial` is nonzero (if char K ≠ 2) and separable since E is an elliptic curve.
theorem separable_twoTorsionPolynomial : E.twoTorsionPolynomial.toPoly.Separable := by
  sorry
  /- use `WeierstrassCurve.twoTorsionPolynomial_discr_ne_zero`,
    `Cubic.discr_ne_zero_iff_roots_nodup`,
    `Polynomial.nodup_aroots_iff_of_splits` with `AlgebraicClosure K` -/

/- By `trace_sq_sub_four_mul_norm`, `q² * E.twoTorsionPolynomial` is in K[X],
but `E.twoTorsionPolynomial` is separable, hence squarefree, so q ∈ K[X].
Use `Polynomial.Separable.squarefree` and
`UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`.
Maybe extract a lemma for `UniqueFactorizationMonoid`. -/
theorem right_mem_of_isIntegral : q ∈ toRatFunc.range := by
  sorry

theorem left_mem_of_isIntegral : p ∈ toRatFunc.range := by
  sorry /- apply `left_mem_of_right_mem_of_norm_mem` to
    `norm_mem_of_isIntegral` and `right_mem_of_isIntegral(_of_char_two)`. -/

end IsUnit2

section Char2

variable [CharP K 2]

theorem a₁_or_a₃_ne_zero_of_char_two : E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  sorry -- use `WeierstrassCurve.Δ_of_char_two`

theorem trace_eq_of_char_two : E.trace p q = q * (C E.a₁ * X + C E.a₃).toRatFunc := by
  sorry

/- If a₁ = 0, then a₃ ≠ 0 by `a₁_or_a₃_ne_zero_of_char_two`, and Tr(p+qY) = a₃q ∈ K[X],
so q ∈ K[X]. -/
theorem right_mem_of_isIntegral_of_a₁_ne_zero (h : E.a₁ = 0) : q ∈ toRatFunc.range := by
  sorry

/- If a₁ ≠ 0, we may assume it is in normal form, so that a₁ = 1 and a₃ = a₄ = 0, and
a₆ = Δ ≠ 0 by `Δ_of_isCharTwoJNeZeroNF_of_char_two`.
We can come back to prove this assuming only a₁ ≠ 0 after we've shown the coordinate ring is
integrally closed. -/
theorem mem_of_isIntegral_of_isCharTwoJNeZeroNF [E.IsCharTwoJNeZeroNF] :
    p ∈ toRatFunc.range ∧ q ∈ toRatFunc.range := by
  have hq : q * X.toRatFunc ∈ toRatFunc.range := by
    sorry -- we have Tr(p+qY) = qX in this case, so just use `trace_eq_of_char_two`
  have : IsIntegral K[X] (p * X.toRatFunc) := by
    sorry -- Since `E.norm p q ∈ K[X]`, we have `X² * E.norm p q ∈ K[X]` as well.
    -- Expand the definition of norm, and apply `isIntegral_of_sq_add_mem_range`
  have ⟨p', hp⟩ : p * X.toRatFunc ∈ toRatFunc.range := by
    sorry -- since K[X] is integrally closed
  have ⟨q', hq⟩ := hq
  have ⟨N, hN⟩ := E.norm_mem_of_isIntegral int
  have hN : p' ^ 2 + p' * q' * X + q' ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₆) = X ^ 2 * N := by
    sorry -- X² times the definition of norm
  have : p'.coeff 0 ^ 2 + q'.coeff 0 ^ 2 * E.a₆ = 0 := by
    sorry -- compare the constant term of the two sides of hN
  have : p'.coeff 0 * q'.coeff 0 = 0 := by
    sorry -- compare the X coefficient of the two sides of hN
    -- We are in characteristic 2, so p² has no linear term for any polynomial p.
  have hp0 : p'.coeff 0 = 0 := sorry
  have hq0 : q'.coeff 0 = 0 := sorry
  refine ⟨⟨p'.divX, ?_⟩, q'.divX, ?_⟩ <;> refine mul_right_cancel₀ toRatFunc_X_ne_zero ?_ <;>
    simp only [← map_mul, ← hp, ← hq]
  · conv_rhs => rw [← p'.divX_mul_X_add, hp0, C_0, add_zero]
  · conv_rhs => rw [← q'.divX_mul_X_add, hq0, C_0, add_zero]

end Char2

variable (h : IsUnit (2 : K) ∨ E.a₁ = 0 ∨ E.IsCharTwoJNeZeroNF)
include h

theorem comb_mem_of_isIntegral : E.comb p q ∈ (algebraMap E.CoordinateRing _).range := by
  sorry

omit int

namespace CoordinateRing

/-- The affine coordinate ring of an elliptic curve is the integral closure of the
1-variable polynomial ring in the function field. -/
private theorem isIntegralClosure :
    IsIntegralClosure E.CoordinateRing K[X] E.FunctionField' := by
  refine ⟨FaithfulSMul.algebraMap_injective .., fun {f} ↦ ⟨fun int ↦ ?_, ?_⟩⟩
  · obtain ⟨p, q, rfl⟩ := f.exists_comb_eq; exact E.comb_mem_of_isIntegral int h
  · rintro ⟨f, rfl⟩; exact isIntegral_trans _ (isIntegral_algebraMap ..)

private theorem isIntegrallyClosedIn : IsIntegrallyClosedIn E.CoordinateRing E.FunctionField' :=
  have := CoordinateRing.isIntegralClosure E h
  .of_isIntegralClosure K[X]

end CoordinateRing

omit h

instance : IsIntegrallyClosed E.CoordinateRing := by
  by_cases h2 : (2 : K) = 0
  · have := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Nat.prime_two h2)
    by_cases h₁ : E.a₁ = 0
    · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
        (CoordinateRing.isIntegrallyClosedIn E <| .inr <| .inl h₁)
    · have := E.toCharTwoJNeZeroNF h₁
      have := (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
        (CoordinateRing.isIntegrallyClosedIn _ <| .inr <| .inr <| E.toCharTwoJNeZeroNF_spec h₁)
      exact .of_equiv (CoordinateRing.variableChange E (E.toCharTwoJNeZeroNF h₁)).toRingEquiv.symm
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
      (CoordinateRing.isIntegrallyClosedIn E <| .inl <| Ne.isUnit h2)

example : IsIntegralClosure E.CoordinateRing K[X] E.FunctionField' := inferInstance
example : IsIntegrallyClosedIn E.CoordinateRing E.FunctionField' := inferInstance

instance : Algebra.IsSeparable K(X) E.FunctionField' := by
  sorry
  /- The generator Y is separable over K(X), since in characteristic 2,
    a₁ and a₃ cannot both vanish by `a₁_or_a₃_ne_zero_of_char_two`,
    so the linear term of the minimal polynomial of Y does not vanish. -/

instance : IsDedekindDomain E.CoordinateRing :=
  IsIntegralClosure.isDedekindDomain K[X] K(X) E.FunctionField' _

end WeierstrassCurve.Affine
