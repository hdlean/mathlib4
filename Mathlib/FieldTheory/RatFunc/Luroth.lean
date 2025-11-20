/-
Copyright (c) 2025 Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Junyan Xu
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Lüroth's theorem

The goal of this project is to prove Lüroth's theorem, which says that for every field K,
every intermediate field between K and the rational function field K(X) is either K or
isomorphic to K(X) as an K-algebra. The proof depends on the following lemma on degrees of
rational functions:

If `f` is a rational function, i.e. an element in the field `K(X)` (`FractionRing K[X]`)
for some field `K`, we can write `f = p / q` where `p` and `q` are coprime polynomials in `K[X]`
with `q` nonzero.

We define the degree of `f` to be the larger of the degrees (`Polynomial.natDegree`)
of `p` and `q`. It turns out that if `f` is not a constant, its degree is equal to the degree of
the field extension K(X)/K(f) (`Module.finrank K⟮f⟯ (FractionRing K[X])`).

(In fact, since `finrank` is defined to be 0 when the extension is infinite,
the equality continue to hold even when `f` is a constant.)

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

variable {K : Type*} [Field K]

open Polynomial IntermediateField

namespace Polynomial

noncomputable section

local notation:10000 K"(X)" => FractionRing K[X]

abbrev toRatFunc : K[X] →+* K(X) := algebraMap ..

@[simp]
theorem C_toRatFunc (a : K) : (C a).toRatFunc = algebraMap K K(X) a := rfl

set_option quotPrecheck false

variable (p q : K[X]) (coprime : IsCoprime p q)
include coprime

/- `f = p / q` -/
local notation "f" => p.toRatFunc / q.toRatFunc

/- Show that `K⟮f⟯ = K` iff both `p` and `q` are constant. -/
theorem adjoin_p_dvd_q_eq_bot_iff : K⟮f⟯ = ⊥ ↔ p.natDegree = 0 ∧ q.natDegree = 0 := by
  rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
  constructor
  · rintro ⟨x, hx⟩
    /- Here, we need to show that if `p / q` is constant and `p` and `q` are coprime, then both
    `p` qnd `q` are constant. -/
    sorry
  · rintro ⟨hp, hq⟩
    rw [natDegree_eq_zero] at hp hq
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    use a / b
    simp

/- `X` considered as an element in K(X). -/
local notation "rfX" => toRatFunc (K := K) X

/- First show that `X` generates K(X) over K(f). -/
theorem adjoin_X_eq_top : K⟮f⟯⟮rfX⟯ = ⊤ := by
  sorry

/- Since `X` generates K(X) over K(f), the degree of the field extension K(X)/K(f) is equal to
the degree of the minimal polynomial of `X` over K(f). `p - f * q` is the obvious candidate for
the minimal polynomial of `X` (where `p` and `q` are considered as elements of K(f)[X] rather than
K[X], and `f` considered as an element of K(f)). First show that X is indeed a root of `p - f * q`,
and therefore K(X) is algebraic over K(f): -/

abbrev minpolyDiv : K⟮f⟯[X] :=
  p.map (algebraMap K K⟮f⟯) - C (AdjoinSimple.gen K f) * q.map (algebraMap K K⟮f⟯)

omit coprime in
theorem minpolyDiv_aeval (hq : q ≠ 0) : (minpolyDiv p q).aeval rfX = 0 := by
  have toRatFunc_ne_zero : q.toRatFunc ≠ 0 :=
    (map_ne_zero_iff _ <| IsFractionRing.injective _ _).mpr hq
  simp only [minpolyDiv, aeval_sub, aeval_map_algebraMap, map_mul, aeval_C,
    IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen]
  simp_rw [aeval_algebraMap_apply, aeval_X_left_apply, div_mul_cancel₀ _ toRatFunc_ne_zero]
  exact sub_self ((algebraMap K[X] K(X)) p)

-- Note: this needs f is not a constant, i.e. `max p.natDegree q.natDegree ≠ 0`.
theorem isAlgebraic_div (hq : 0 < q.natDegree) : IsAlgebraic K⟮f⟯ rfX := by
  use minpolyDiv p q
  refine ⟨?_, minpolyDiv_aeval p q (ne_zero_of_natDegree_gt hq)⟩
  intro H
  refine hq.ne ((adjoin_p_dvd_q_eq_bot_iff p q coprime).mp ?_).2.symm
  rw [IntermediateField.adjoin_simple_eq_bot_iff]
  use p.coeff q.natDegree / q.leadingCoeff
  have h_eq : (minpolyDiv p q).coeff q.natDegree = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [H]
    exact hq
  simp only [coeff_sub, coeff_map, coeff_C_mul, coeff_natDegree] at h_eq
  rw [sub_eq_zero] at h_eq
  replace h_eq := congrArg Subtype.val h_eq
  simp only [SubalgebraClass.coe_algebraMap, MulMemClass.coe_mul, AdjoinSimple.coe_gen] at h_eq
  simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, map_div₀]
  refine ((eq_div_iff ?_).mpr h_eq.symm).symm
  simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero]
  exact ne_zero_of_natDegree_gt hq

theorem isAlgebraic_adjoin_div (hq : 0 < q.natDegree) : Algebra.IsAlgebraic K⟮f⟯ K(X) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮rfX⟯ := by
    apply IntermediateField.isAlgebraic_adjoin_simple
    rw [←isAlgebraic_iff_isIntegral]
    exact isAlgebraic_div p q coprime hq
  exact ((IntermediateField.equivOfEq (adjoin_X_eq_top p q coprime)).trans
    IntermediateField.topEquiv).isAlgebraic

/- Hints:

* `IntermediateField.isAlgebraic_adjoin` and `isAlgebraic_iff_isIntegral` together with
  `minpolyDiv_aeval` shows that `K⟮f⟯⟮rfX⟯` is algebraic over `K⟮f⟯`.

* Now use `IntermediateField.equivOfEq` and `IntermediateField.topEquiv` to construct an `AlgHom`
  between `K⟮f⟯⟮rfX⟯` and K(X), and use `AlgEquiv.isAlgebraic` to conclude. -/

theorem finrank_eq_natDegree_minpoly (hq : 0 < q.natDegree) :
    Module.finrank K⟮f⟯ K(X) = (minpoly K⟮f⟯ rfX).natDegree := by
  have e : K⟮f⟯⟮rfX⟯ ≃ₐ[K⟮f⟯] K(X) :=
    ((IntermediateField.equivOfEq (adjoin_X_eq_top p q coprime)).trans IntermediateField.topEquiv)
  rw [←e.toLinearEquiv.finrank_eq]
  apply IntermediateField.adjoin.finrank
  apply IsAlgebraic.isIntegral
  exact isAlgebraic_div p q coprime hq

theorem transcendental_polynomial : Algebra.Transcendental K K(X) := by
  use rfX
  rintro ⟨g, gnotzero, grfXzero⟩
  simp only [aeval_algebraMap_eq_zero_iff, aeval_X_left, AlgHom.coe_id, id_eq] at grfXzero
  contradiction

theorem transcendental_adjoin_div (hq : 0 < q.natDegree) : Algebra.Transcendental K K⟮f⟯ := by
  have htrans := transcendental_polynomial p q  coprime
  have := isAlgebraic_adjoin_div p q coprime hq
  rw [Algebra.transcendental_iff_not_isAlgebraic] at ⊢ htrans
  intro H
  exact htrans (Algebra.IsAlgebraic.trans K K⟮f⟯ K(X))

theorem transcendental_div (hq : 0 < q.natDegree) : Transcendental K f := by
  intro h
  have h₁ : Algebra.IsAlgebraic K K⟮f⟯ := by
    apply IntermediateField.isAlgebraic_adjoin_simple
    exact h.isIntegral
  have h₂ : Algebra.IsAlgebraic K⟮f⟯ K(X) := by
    exact isAlgebraic_adjoin_div p q coprime hq
  have h₃ : Algebra.IsAlgebraic K K(X) := by
    exact Algebra.IsAlgebraic.trans K K⟮f⟯ K(X)
  have h₄ : Algebra.Transcendental K K(X) := by
    exact transcendental_polynomial p q coprime
  rw [Algebra.transcendental_iff_not_isAlgebraic] at h₄
  contradiction

local notation "K[f]" => Algebra.adjoin K {f}

def algEquivOfTranscendental (hq : 0 < q.natDegree) : K[X] ≃ₐ[K] K[f] := by
  let f' : K[f] := ⟨f, by apply Algebra.mem_adjoin_of_mem; simp⟩
  refine AlgEquiv.ofBijective (aeval (R := K) (A := K[f]) f') ?_
  constructor
  · rw [←transcendental_iff_injective]
    have h₁ := transcendental_div p q coprime hq
    rw [Transcendental] at ⊢ h₁
    have := @isAlgebraic_algHom_iff K K[f] _ _ _ K(X) _ _ K[f].val ?_ f'
    · simp at this
      rw [←this]
      exact h₁
    · exact
      (AlgHom.injective_codRestrict (Algebra.adjoin K {toRatFunc p / toRatFunc q}).val
            (Algebra.adjoin K {toRatFunc p / toRatFunc q}) Subtype.property).mp
        fun ⦃a₁ a₂⦄ a ↦ a
  · rw [←AlgHom.range_eq_top, eq_top_iff]
    sorry

lemma algEquivOfTranscendental_apply_X (hq : 0 < q.natDegree) :
    algEquivOfTranscendental p q coprime hq X = ⟨f, Algebra.subset_adjoin rfl⟩ := by
  sorry

#synth EuclideanDomain K[X] -- Polynomial.instEuclideanDomain
example : IsIntegrallyClosed K[X] := inferInstance

/- Since K[f] is isomorphic to K[X] and K[X] is integrally closed, K[f] is also integrally closed.
-/
theorem isIntegrallyClosed_adjoin_div : IsIntegrallyClosed K[f] := by
  sorry -- use `IsIntegrallyClosed.of_equiv`

/- If `p.natDegree > q.natDegree`, then `minpolyDiv p q` has degree equal to the degree of `p`.
If moreover `p` is monic, then `minpolyDiv p q` is also monic. For convenience, we shall assume
these conditions henceforth. -/

variable (lt : q.natDegree ≤ p.natDegree)
include lt

theorem natDegree_minpolyDiv (hq : 0 < q.natDegree) : (minpolyDiv p q).natDegree = p.natDegree := by
  unfold minpolyDiv
  have h_deg_p : (p.map (algebraMap K K⟮f⟯)).natDegree = p.natDegree := by
    simp only [natDegree_map]
  have h_deg_q : (C (AdjoinSimple.gen K f) * q.map (algebraMap K K⟮f⟯)).natDegree = q.natDegree := by
    rw [natDegree_C_mul]
    · rw [natDegree_map]
    · simp
      intro H
      replace H := congrArg Subtype.val H
      simp only [AdjoinSimple.coe_gen, ZeroMemClass.coe_zero, div_eq_zero_iff,
        FaithfulSMul.algebraMap_eq_zero_iff] at H
      rcases H with rfl | rfl
      · rw [natDegree_zero] at lt
        linarith
      · rw [natDegree_zero] at hq
        contradiction
  by_cases h_lt : q.natDegree < p.natDegree
  · rw [natDegree_sub_eq_left_of_natDegree_lt]
    · rw [natDegree_map]
    · simp
      rw [h_deg_q]
      exact h_lt
  · have h_eq : p.natDegree = q.natDegree := by linarith
    apply le_antisymm
    · rw [←Nat.max_eq_left lt]
      have := natDegree_sub_le (p.map (algebraMap K K⟮f⟯))
        (C (AdjoinSimple.gen K f) * q.map (algebraMap K K⟮f⟯))
      rw [h_deg_p, h_deg_q] at this
      exact this
    · apply Polynomial.le_natDegree_of_ne_zero
      simp
      intro H
      rw [sub_eq_zero] at H
      have q_leadingCoeff : q.coeff p.natDegree = q.leadingCoeff := by
        rw [h_eq]
        rfl
      rw [q_leadingCoeff, ←div_eq_iff] at H
      · replace H := congrArg Subtype.val H
        have : K⟮f⟯ = ⊥ := by
          rw [IntermediateField.adjoin_simple_eq_bot_iff]
          simp only [AdjoinSimple.coe_gen] at H
          rw [←H]
          use p.leadingCoeff / q.leadingCoeff
          simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, map_div₀]
          rfl
        rw [adjoin_p_dvd_q_eq_bot_iff p q coprime] at this
        exact hq.ne.symm this.2
      · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero]
        rintro rfl
        rw [natDegree_zero] at hq
        contradiction


theorem monic_minpolyDiv : (minpolyDiv p q).Monic := by
  sorry

/- By `minpoly.eq_iff_aeval_eq_zero`, to show that `minpolyDiv p q` is indeed the minimal
polynomial of X over K(f), it suffices to show it is irreducible.
The key lemma `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` (due to Gauss)
shows that it suffices to show it is irreducible over K[f]. -/

/-- Same as `minpolyDiv` but as a polynomial over K[f] instead of K(f). -/
def minpolyDiv' : K[f][X] :=
  p.map (algebraMap ..) - C ⟨f, Algebra.subset_adjoin rfl⟩ * q.map (algebraMap ..)

open scoped IntermediateField.algebraAdjoinAdjoin
#synth Algebra K[f] K⟮f⟯

theorem map_minpolyDiv' : (minpolyDiv' p q).map (algebraMap ..) = minpolyDiv p q := by
  sorry

/- If we swap the two variables `f` and `X`, then `p - C f * q` becomes `C p - f * C q`. -/

def swap : K[X][X] ≃+* K[X][X] :=
  .ofRingHom (eval₂RingHom (mapRingHom C) (C X)) (eval₂RingHom (mapRingHom C) (C X))
    (by ext <;> simp) (by ext <;> simp)

theorem algEquivOfTranscendental_swap_C_sub_C_X (hq : 0 < q.natDegree):
    map (algEquivOfTranscendental p q coprime hq) (swap (C p - X * C q)) = minpolyDiv' p q := by
  sorry

omit coprime lt in
lemma aux (hq : q ≠ 0) : (C p - X * C q).natDegree = 1 := by
  have h₁ : (C p - X * C q) = (C (- q) * X + C p) := by
    simp
    ring
  rw [h₁]
  apply Polynomial.natDegree_linear
  exact neg_ne_zero.mpr hq

lemma aux2 (hq : q ≠ 0) : (C p - X * C q).IsPrimitive := by
  classical
  rw [isPrimitive_iff_content_eq_one]
  rw [content_eq_gcd_leadingCoeff_content_eraseLead]
  have h₃ : (C p - X * C q).leadingCoeff = - q := by
    rw [leadingCoeff]
    rw [aux p q hq]
    simp only [X_mul_C, coeff_sub, coeff_C_succ, coeff_mul_X, coeff_C_zero, zero_sub]
  rw [h₃]
  have h₄ : (C p - X * C q).eraseLead = C p := by
    rw [sub_eq_add_neg]
    rw [eraseLead_add_of_natDegree_lt_right]
    · simp
      rw [neg_mul_eq_neg_mul]
      rw [← C_neg]
      rw [eraseLead_C_mul_X]
    simp
    rw [natDegree_C_mul_X]
    exact zero_lt_one
    exact hq
  rw [h₄]
  simp
  rw [← normalize_gcd]
  rw [normalize_eq_one]
  rw [gcd_isUnit_iff]
  rw [normalize_apply]
  rw [isCoprime_mul_unit_right_right]
  rw [IsCoprime.neg_left_iff]
  rw [isCoprime_comm]
  exact coprime
  exact Units.isUnit (normUnit p)

theorem irreducible_mul_X_sub (hq : q ≠ 0): Irreducible (C p - X * C q) := by
  classical
  have hnezero : (C p - X * C q) ≠ 0 := by
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [aux p q hq]
    exact zero_lt_one
  have h₂ : (C p - X * C q).IsPrimitive := by
    exact aux2 p q coprime lt hq
  apply @Polynomial.IsPrimitive.irreducible_of_irreducible_map_of_injective K[X] _ K(X) _ _ toRatFunc
  · exact FaithfulSMul.algebraMap_injective K[X] K(X)
  · exact h₂
  · apply Polynomial.irreducible_of_degree_eq_one
    rw [degree_eq_natDegree]
    rw [Nat.cast_eq_one]
    rw [← aux p q hq]
    rw [natDegree_map_eq_iff]
    simp
    left
    apply ne_zero_of_natDegree_gt (n := 0)
    rw [mul_comm]
    rw [aux p q hq]
    exact zero_lt_one
    rw [Polynomial.map_ne_zero_iff]
    exact hnezero
    exact FaithfulSMul.algebraMap_injective K[X] K(X)

theorem irreducible_minpolyDiv' (hq : 0 < q.natDegree) : Irreducible (minpolyDiv' p q) := by
  rw [← algEquivOfTranscendental_swap_C_sub_C_X p q coprime lt hq]


#check MulEquiv.irreducible_iff

theorem irreducible_minpolyDiv : Irreducible (minpolyDiv p q) := by
  classical
  rw [← map_minpolyDiv']
  rw [← IsPrimitive.irreducible_iff_irreducible_map_fraction_map]


#check Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map

theorem minpolyDiv_eq_minpoly : minpolyDiv p q = minpoly K⟮f⟯ rfX := by
  sorry -- use `minpoly.eq_iff_aeval_eq_zero`

-- Finally we conclude:
theorem finrank_eq_max_natDegree : Module.finrank K⟮f⟯ K(X) = max p.natDegree q.natDegree :=
  sorry

/- Next steps:

* Remove the condition `p.Monic`: dividing `p` by the leading coefficient does not change the
  degree, and does not affect the intermediate field generated by `f`.

* Remove the condition `q.natDegree < p.natDegree`: if `p.natDegree < q.natDegree`, notice that
  `q / p` generates the same intermediate field as `p / q`. If `p.natDegree = q.natDegree`,
  notice that `(p - c * q) / q` generates the same intermediate field, and you can choose `c`
  such that `p - c * q` has a lower degree.
  It can happen that both `p` and `q` are constants (i.e. of degree 0), in which case
  `K⟮f⟯ = ⊥` and [K(X) : K⟮f⟯] = ∞, but in Lean we have `Module.finrank K⟮f⟯ K(X) = 0`.

* Also remove these conditions from `transcendental_div`.

* Now we are ready to attack Lüroth's theorem.
  Let `E` be an intermediate field between `K` and `K(X)`,
  we must show that `E = K⟮f⟯` for some `f : K(X)` transcendental over `K`. -/

end

end Polynomial

open Polynomial

local notation:10000 K"(X)" => FractionRing K[X]

theorem FractionRing.exists_isCoprime_eq_div (f : K(X)) :
    ∃ p q : K[X], IsCoprime p q ∧ f = p.toRatFunc / q.toRatFunc := by
  sorry

/- First it is easy to show that `K(X)` does not contain any algebraic element over `K` other than
elements of `K`. Proof: use (a generalized version of) `transcendental_div`.
Potentially useful: `Localization.rec` and `FractionRing.mk_eq_div`. -/
instance : IsIntegrallyClosedIn K K(X) := by
  sorry

variable (E : IntermediateField K K(X)) (hE : E ≠ ⊥)
include hE

instance : Algebra.IsAlgebraic E K(X) := by
  sorry
  -- Choose `f ∈ E \ K`, then `K(X)` is algebraic over `K⟮f⟯`, and therefore algebraic over `E`.

/-- The minimal polynomial of `X : K(X)` over an intermediate field `E`. -/
def IntermediateField.minpolyX : E[X] :=
  minpoly E (X : K[X]).toRatFunc

-- TODO: fill in more details here from [Cohn] and [Jacobson]

theorem luroth : ∃ f : K(X), Transcendental K f ∧ E = K⟮f⟯ := by
  sorry
