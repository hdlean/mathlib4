/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Relrank
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Lüroth's theorem

The goal of this file is to prove Lüroth's theorem, which says that for every
field `K`, every intermediate field between `K` and the rational function field
`K(X)` is either `K` or isomorphic to `K(X)` as an K-algebra. The proof depends
on the following lemma on degrees of rational functions:

Let `f` be a rational function, i.e. an element in the field `K(X)` (`RatFunc
K`). Let `p` be its numerator and `q` its denominator. Then the degree of the
field extension `K(X)/K(f)` equals the maximum of the degrees of `p` and `q`,
see `finrank_eq_max_natDegree`. Since `finrank` is defined to be zero when the
extension is infinite, this holds even when `f` is constant.

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

@[expose] public section

namespace Polynomial

section

open IsLocalization

variable {R K : Type*} [Nontrivial R] [CommRing R] [NormalizedGCDMonoid R] [Field K] [Algebra R K]
  [IsFractionRing R K]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
lemma isInteger_mul_iff_left {f : R[X]} (hf : IsPrimitive f) (g : K[X]) :
    IsInteger R[X] (g * f.map (algebraMap R K)) ↔ IsInteger R[X] g := by
  refine ⟨?_, fun h ↦ isInteger_mul h ⟨f, rfl⟩⟩
  intro ⟨k, (hk : Polynomial.map _ _ = _)⟩
  let g' := integerNormalization (nonZeroDivisors R) g
  obtain ⟨⟨b, hb₁⟩, (hb₂ : Polynomial.map _ g' = _)⟩ :=
    integerNormalization_map_to_map (nonZeroDivisors R) g
  have g'_mul_f : g' * f = b • k := by
    apply Polynomial.map_injective (algebraMap R K) (FaithfulSMul.algebraMap_injective R K)
    rw [Polynomial.map_smul, algebraMap_smul, hk]
    rw [← smul_mul_assoc, ← hb₂, Polynomial.map_mul]
  use C (normUnit b : R) * C k.content * g'.primPart
  rw [Polynomial.algebraMap_def, coe_mapRingHom, Polynomial.map_mul, Polynomial.map_mul, map_C,
    ← smul_right_inj (nonZeroDivisors.ne_zero hb₁), ← hb₂, Algebra.smul_def, algebraMap_apply,
    Polynomial.map_C]
  conv_rhs => rw [eq_C_content_mul_primPart g']
  rw [Polynomial.map_mul, Polynomial.map_C, ← mul_assoc, ← C_mul, ← C_mul]
  congr
  conv_rhs => rw [← mul_one g'.content]
  rw [← hf.content_eq_one, ← content_mul, g'_mul_f, smul_eq_C_mul, content_mul, content_C,
    normalize_apply, map_mul, map_mul, mul_assoc]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
lemma isInteger_mul_iff_right {f : R[X]} (hf : IsPrimitive f) (g : K[X]) :
    IsInteger R[X] (f.map (algebraMap R K) * g) ↔ IsInteger R[X] g := by
  convert isInteger_mul_iff_left hf g using 2
  rw [mul_comm]

end

end Polynomial

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin
open scoped Polynomial

variable {K : Type*} [Field K] (f : RatFunc K)

local notation "K[f]" => Algebra.adjoin K {(f : RatFunc K)}

theorem adjoin_X : K⟮(X : RatFunc K)⟯ = ⊤ :=
  eq_top_iff.mpr fun g _ ↦ (mem_adjoin_simple_iff _ _).mpr ⟨g.num, g.denom, by simp⟩

theorem IntermediateField.adjoin_X (E : IntermediateField K (RatFunc K)) :
    E⟮(X : RatFunc K)⟯ = ⊤ := by
  rw [← restrictScalars_eq_top_iff (K := K), restrictScalars_adjoin, eq_top_iff]
  exact le_trans (le_of_eq RatFunc.adjoin_X.symm) (IntermediateField.adjoin.mono _ _ _ (by simp))

/-- The equivalence between `K⟮f⟯⟮X⟯` and `RatFunc K` as `K⟮f⟯`-algebras. -/
noncomputable def IntermediateField.adjoinXEquiv (E : IntermediateField K (RatFunc K)) :
    E⟮(X : RatFunc K)⟯ ≃ₐ[E] RatFunc K :=
  (IntermediateField.equivOfEq (IntermediateField.adjoin_X E)).trans IntermediateField.topEquiv

/-- The minimal polynomial of `X` over `K⟮f⟯`. It is defined as `f.num - f * f.denom`, viewed
as a polynomial with coefficients in `A`, where `A` is a `K[f]`-algebra. -/
noncomputable abbrev minpolyX (A : Type*) [CommRing A] [Algebra K A] [Algebra K[f] A] : A[X] :=
  f.num.map (algebraMap K A) -
  Polynomial.C (algebraMap K[f] A (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f])) *
    f.denom.map (algebraMap K A)

theorem minpolyX_map (A : Type*) [CommRing A] [Algebra K A] [Algebra (Algebra.adjoin K {f}) A]
    (B : Type*) [CommRing B] [Algebra K B] [Algebra K[f] B] [Algebra A B] [IsScalarTower K A B]
    [IsScalarTower K[f] A B] : (f.minpolyX A).map (algebraMap A B) = f.minpolyX B := by
  simp [minpolyX, Polynomial.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

@[simp]
theorem C_minpolyX (x : K) : (C x).minpolyX K⟮C x⟯ = 0 := by
  simp [minpolyX, sub_eq_zero, Subtype.ext_iff]

theorem minpolyX_aeval_X : (f.minpolyX K⟮f⟯).aeval (X : RatFunc K) = 0 := by
  simp only [Polynomial.aeval_sub, Polynomial.aeval_map_algebraMap, aeval_X_left_eq_algebraMap,
    map_mul, Polynomial.aeval_C, IntermediateField.algebraMap_apply, coe_algebraMap]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : (f.minpolyX K⟮f⟯).coeff f.denom.natDegree = (0 : RatFunc K)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((map_ne_zero C).mpr
    (Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpolyX_eq_zero_iff : (f.minpolyX K⟮f⟯) = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

section FNeC

-- In this section, we assume `f` is not constant.
variable (hf : ¬∃ c, f = C c)
include hf

theorem isAlgebraic_adjoin_simple_X : IsAlgebraic K⟮f⟯ (X : RatFunc K) :=
   ⟨f.minpolyX K⟮f⟯, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' : Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : RatFunc K)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

theorem natDegree_denom_le_natDegree_minpolyX :
    f.denom.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree :=
  Polynomial.le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem natDegree_num_le_natDegree_minpolyX :
    f.num.natDegree ≤ (f.minpolyX K⟮f⟯).natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply Polynomial.le_natDegree_of_ne_zero
  intro H
  replace H := congr($(H).val)
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_natDegree,
    Polynomial.coeff_C_mul, AddSubgroupClass.coe_sub, SubalgebraClass.coe_algebraMap,
    algebraMap_eq_C, MulMemClass.coe_mul, coe_algebraMap, ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩

omit hf in
theorem natDegree_minpolyX :
    (f.minpolyX K⟮f⟯).natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp
  apply le_antisymm
  · have : (f.minpolyX K⟮f⟯).natDegree ≤ _ := Polynomial.natDegree_sub_le _ _
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C_mul fun H ↦
      hf ⟨0, by simpa [map_zero] using congr($(H).val)⟩,
      Polynomial.natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| Polynomial.le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero congr($(H).val))

theorem transcendental_of_ne_C : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem irreducible_minpolyX' : Irreducible (f.minpolyX K[f]) := by
  let e := Polynomial.algEquivOfTranscendental K f (f.transcendental_of_ne_C hf)
  let φ : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ_map : φ.mapEquiv e.toRingEquiv = (f.minpolyX K[f]) := by
    simp only [AlgEquiv.toRingEquiv_eq_coe, Polynomial.algebraMap_eq, Polynomial.mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, Polynomial.algEquivOfTranscendental_apply,
      Polynomial.map_sub, Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C, RingHom.coe_coe,
      Polynomial.aeval_X, φ, e]
    congr 2 <;> ext <;> simp
  rw [← φ_map, MulEquiv.irreducible_iff]
  have : φ = Polynomial.Bivariate.swap
      (Polynomial.C f.num - Polynomial.X * Polynomial.C f.denom) := by
    simp only [Polynomial.X_mul_C, Polynomial.Bivariate.swap_apply, AlgHom.coe_comp,
      AlgHom.coe_restrictScalars', Polynomial.coe_aeval_eq_eval, Function.comp_apply,
      Polynomial.aeval_sub, Polynomial.aeval_C, Polynomial.algebraMap_def,
      Polynomial.coe_mapRingHom, map_mul, Polynomial.aeval_X, Polynomial.eval_sub,
      Polynomial.eval_map_algebraMap, Polynomial.eval_mul, Polynomial.eval_C]
    rw [mul_comm]
    rfl
  rw [this, MulEquiv.irreducible_iff]
  convert Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr f.denom_ne_zero)
    ((IsCoprime.neg_right_iff _ _).mpr f.isCoprime_num_denom).symm.isRelPrime using 1
  rw [add_comm, Polynomial.X_mul_C, map_neg, neg_mul]
  exact sub_eq_add_neg (Polynomial.C f.num) (Polynomial.C f.denom * Polynomial.X)

theorem irreducible_minpolyX : Irreducible (f.minpolyX K⟮f⟯) := by
  haveI : UniqueFactorizationMonoid K[f] :=
    (f.transcendental_of_ne_C hf).uniqueFactorizationMonoid_adjoin
  rw [← f.minpolyX_map K[f] K⟮f⟯,
    ← Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
  · exact f.irreducible_minpolyX' hf
  · apply (f.irreducible_minpolyX' hf).isPrimitive
    intro H
    have := Polynomial.natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := f.minpolyX K[f])
    rw [f.minpolyX_map K[f] K⟮f⟯, H, nonpos_iff_eq_zero, f.natDegree_minpolyX,
      Nat.max_eq_zero_iff, ← f.eq_C_iff] at this
    exact hf this

end FNeC

theorem finrank_eq_max_natDegree :
    Module.finrank K⟮f⟯ (RatFunc K) = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    rw [adjoin_simple_eq_bot_iff.mpr (show C c ∈ ⊥ from ⟨c, rfl⟩), finrank_bot',
      Module.finrank_of_not_finite fun H ↦  Algebra.transcendental_iff_not_isAlgebraic.mp
      transcendental <| Algebra.IsAlgebraic.of_finite K (RatFunc K)]
    simp
  rw [← (IntermediateField.adjoinXEquiv K⟮f⟯).toLinearEquiv.finrank_eq,
    adjoin.finrank (f.isAlgebraic_adjoin_simple_X hf).isIntegral,
    ← minpoly.eq_of_irreducible (f.irreducible_minpolyX hf) f.minpolyX_aeval_X, mul_comm,
    Polynomial.natDegree_C_mul <| inv_ne_zero <| Polynomial.leadingCoeff_ne_zero.mpr fun H ↦
    hf ((minpolyX_eq_zero_iff f).mp H), natDegree_minpolyX]


theorem IntermediateField.isAlgebraic_X (E : IntermediateField K (RatFunc K)) (hE : E ≠ ⊥) :
    IsAlgebraic E (X : RatFunc K) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

namespace Luroth

open Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K (RatFunc K)}

lemma finrank_pos (h : E ≠ ⊥) : 0 < Module.finrank E (RatFunc K) := by
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq,
    adjoin.finrank (IntermediateField.isAlgebraic_X E h).isIntegral]
  apply minpoly.natDegree_pos (IntermediateField.isAlgebraic_X E h).isIntegral

variable (E) in
private noncomputable abbrev ψ : E[X] := minpoly E (X : RatFunc K)

private lemma ψ_ne_zero (h : E ≠ ⊥) : ψ E ≠ 0 :=
  minpoly.ne_zero (IsAlgebraic.isIntegral (IntermediateField.isAlgebraic_X E h))

private lemma ψ_monic (h : E ≠ ⊥) : (ψ E).Monic :=
  minpoly.monic (IsAlgebraic.isIntegral (IntermediateField.isAlgebraic_X E h))

private lemma exists_coeff_not_mem (hE : E ≠ ⊥) :
    ∃ i, (ψ E).coeff i ∉ (algebraMap K E).range := by
  rw [← not_mem_map_range]
  intro ⟨ψ', hψ'⟩
  rw [coe_mapRingHom] at hψ'
  refine transcendental_X (K := K) ⟨ψ', ?_, ?_⟩
  · apply (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K E)).mp
    rw [hψ']
    exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral
  · replace hψ' := congr(aeval (X : RatFunc K) $(hψ'))
    rw [aeval_map_algebraMap, aeval_X_left_eq_algebraMap, minpoly.aeval,
      map_eq_zero_iff _ (algebraMap_injective K)] at hψ'
    rw [hψ', aeval_zero]

@[no_expose] noncomputable def generatorIndex (h : E ≠ ⊥) : ℕ :=
  (exists_coeff_not_mem h).choose

variable (E) in
open Classical in
@[no_expose] noncomputable def generator : RatFunc K := 
  if h : E = ⊥ then 0 else (ψ E).coeff (generatorIndex h)

private lemma generator_eq_zero (h : E = ⊥) : generator E = 0 := by
  unfold generator
  rw [dif_pos h]

private lemma generator_eq_coeff (h : E ≠ ⊥) : generator E = (ψ E).coeff (generatorIndex h) := by
  unfold generator
  rw [dif_neg h]

lemma generator_mem : generator E ∈ E := by
  by_cases h : E = ⊥
  · rw [generator_eq_zero h]
    exact E.zero_mem
  · rw [generator_eq_coeff h,]
    exact SetLike.coe_mem _

private lemma generator_spec (h : E ≠ ⊥) : generator E ∉ (algebraMap K (RatFunc K)).range := by
  rw [generator_eq_coeff h]
  intro ⟨f, hf⟩
  apply (exists_coeff_not_mem h).choose_spec
  exact ⟨f, by ext; exact hf⟩

private lemma generator_ne_C (h : E ≠ ⊥) : ¬ ∃ c, generator E = C c :=
  fun ⟨c, hc⟩ ↦ generator_spec h ⟨c, (by simpa using hc.symm)⟩

private lemma generator_ne_zero (h : E ≠ ⊥) : (generator E : RatFunc K) ≠ 0 :=
  fun H ↦ generator_ne_C h ⟨0, by simp [H]⟩

private lemma adjoin_generator_le : K⟮generator E⟯ ≤ E :=
  adjoin_simple_le_iff.mpr generator_mem

@[no_expose] private noncomputable instance : Algebra K⟮generator E⟯ E :=
  (IntermediateField.inclusion adjoin_generator_le).toAlgebra

variable (E) in
private noncomputable abbrev Φ' : K[X][Y] :=
  IsLocalization.integerNormalization (nonZeroDivisors K[X]) ((ψ E).map (algebraMap E (RatFunc K)))

variable (E) in
open Classical in
private noncomputable abbrev Φ : K[X][Y] := (Φ' E).primPart

variable (E) in
private noncomputable abbrev b : K[X] :=
  (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X])
    ((ψ E).map (algebraMap E (RatFunc K)))).choose.1

private lemma b_ne_zero : b E ≠ 0 :=
  nonZeroDivisors.ne_zero <| (IsLocalization.integerNormalization_map_to_map _
    ((ψ E).map (algebraMap ..))).choose.2

private lemma Φ'_map :
    (Φ' E).map (algebraMap K[X] (RatFunc K)) = (b E) • (ψ E).map (algebraMap E (RatFunc K)) :=
  (IsLocalization.integerNormalization_map_to_map _ ((ψ E).map (algebraMap ..))).choose_spec

variable (E) in
open Classical in
private noncomputable abbrev c : RatFunc K :=
  (algebraMap K[X] (RatFunc K) (Φ' E).content)⁻¹ * (algebraMap K[X] (RatFunc K) (b E))

private lemma c_ne_zero (h : E ≠ ⊥) : c E ≠ 0 := by
  classical
  rw [mul_ne_zero_iff]
  constructor
  · apply inv_ne_zero
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
      IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
    exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E h).isIntegral
  · exact (FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr b_ne_zero

private lemma C_c_mul_ψ (h : E ≠ ⊥) :
    Polynomial.C (c E) * (ψ E).map (algebraMap E (RatFunc K)) =
    (Φ E).map (algebraMap K[X] (RatFunc K)) := by
  classical
  rw [map_mul, mul_assoc]
  conv =>
    lhs; rhs
    rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← Φ'_map, eq_C_content_mul_primPart (Φ' E)]
  rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀,  map_one, one_mul]
  · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
      IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
    exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E h).isIntegral

private lemma Φ_coeff_ψ_natDegree (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (ψ E).natDegree) = c E := by
  have := congr($(C_c_mul_ψ h).coeff (ψ E).natDegree)
  rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
    ψ_monic h, OneMemClass.coe_one, mul_one] at this
  exact this.symm

private lemma c_denom (h : E ≠ ⊥) : (c E).denom = 1 := by
  rw [← Φ_coeff_ψ_natDegree h]
  exact denom_algebraMap _

private lemma Φ_coeff_ψ_natDegree' (h : E ≠ ⊥) :
    (Φ E).coeff (ψ E).natDegree = (c E).num := by
  apply algebraMap_injective
  rw [Φ_coeff_ψ_natDegree h]
  conv_lhs => rw [← num_div_denom (c E), c_denom h, map_one, div_one]

private lemma Φ_coeff_generatorIndex (h : E ≠ ⊥) :
    algebraMap K[X] (RatFunc K) ((Φ E).coeff (generatorIndex h)) =
    algebraMap K[X] (RatFunc K) (c E).num * generator E := by
  have := congr($(C_c_mul_ψ h).coeff (generatorIndex h))
  rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply] at this
  rw [← num_div_denom (c E), c_denom h, map_one, div_one] at this
  rw [generator_eq_coeff h]
  exact this.symm

private lemma generator_denom_dvd_c_num (h : E ≠ ⊥) : (generator E).denom ∣ (c E).num := by
  rw [denom_dvd (num_ne_zero (c_ne_zero h))]
  use (Φ E).coeff (generatorIndex h)
  rw [Φ_coeff_generatorIndex h,
    mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero (c_ne_zero h)))]

private lemma Φ_ne_zero (h : E ≠ ⊥) : Φ E ≠ 0 := by
  intro H
  have := Φ_coeff_ψ_natDegree' h ▸ congr($(H).coeff (ψ E).natDegree)
  rw [coeff_zero] at this
  exact num_ne_zero (c_ne_zero h) this

private lemma ψ_dvd_generator_minpolyX :
    ψ E ∣ ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) := by
  apply minpoly.dvd
  rw [← aeval_eq_aeval_map rfl]
  exact (generator E).minpolyX_aeval_X

variable (E) in
private noncomputable abbrev q : E[X] :=
  (ψ_dvd_generator_minpolyX (E := E)).choose

private lemma ψ_mul_q :
    ψ E * q E = ((generator E).minpolyX K⟮generator E⟯).map (algebraMap _ E) :=
  (ψ_dvd_generator_minpolyX (E := E)).choose_spec.symm

private lemma q_ne_zero (h : E ≠ ⊥) : q E ≠ 0 := right_ne_zero_of_mul <|
  ψ_mul_q (E := E) ▸ Polynomial.map_ne_zero <|
    (generator E).minpolyX_eq_zero_iff.not.mpr (generator_ne_C h)

variable (E) in
private noncomputable abbrev Q : (RatFunc K)[X] :=
  Polynomial.C ((algebraMap K[X] (RatFunc K) (generator E).denom) / c E) *
    (q E).map (algebraMap E (RatFunc K))

private lemma Q_ne_zero (h : E ≠ ⊥) : Q E ≠ 0 := by
  apply mul_ne_zero
  · apply C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).denom_ne_zero) (c_ne_zero h))
  · exact Polynomial.map_ne_zero (q_ne_zero h)

set_option backward.isDefEq.respectTransparency false in
/-- Lüroth's theorem. -/
theorem IntermediateField.eq_adjoin_simple : E = K⟮(generator E : RatFunc K)⟯ := by
  classical
  by_cases hE : E = ⊥
  · rwa [generator_eq_zero hE, adjoin_zero]

  refine le_antisymm (relfinrank_eq_one_iff.mp ?_) adjoin_generator_le

  suffices Module.finrank E (RatFunc K) = Module.finrank K⟮generator E⟯ (RatFunc K) from
    (mul_eq_right₀ ((this ▸ finrank_pos hE).ne.symm)).mp <|
      this ▸ relfinrank_mul_finrank_top (adjoin_generator_le (E := E))
  
  -- Define Φ and prove its spec
  let Φ' : K[X][Y] := IsLocalization.integerNormalization (nonZeroDivisors K[X])
    ((ψ E).map (algebraMap E (RatFunc K)))
  let Φ : K[X][Y] := Φ'.primPart
  obtain ⟨⟨b, hb₁⟩, (hb₂ : Φ'.map _ = _)⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X])
    ((ψ E).map (algebraMap E (RatFunc K)))
  let c : RatFunc K := (algebraMap K[X] (RatFunc K) Φ'.content)⁻¹ * (algebraMap K[X] (RatFunc K) <|
    (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X]) ((ψ E).map (algebraMap E (RatFunc K)))).choose.1)
  let hb₂ : Φ'.map _ = _ := (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X]) ((ψ E).map (algebraMap E (RatFunc K)))).choose_spec
  have c_ne_zero : c ≠ 0 := by
    rw [mul_ne_zero_iff]
    constructor
    · apply inv_ne_zero
      rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
        IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
      exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral
    · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
      exact nonZeroDivisors.ne_zero (IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X]) ((ψ E).map (algebraMap E (RatFunc K)))).choose.2

  have hcψ : Polynomial.C c * (ψ E).map (algebraMap E (RatFunc K)) = Φ.map (algebraMap K[X] (RatFunc K)) := by
    rw [map_mul, mul_assoc]
    conv =>
      lhs; rhs
      rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← hb₂, eq_C_content_mul_primPart Φ']
    rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀,  map_one, one_mul]
    · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
        IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
      exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral

  have Φ_coeff_n : (Φ.coeff (ψ E).natDegree) = c := by
    have := congr($(hcψ).coeff (ψ E).natDegree)
    rw [coeff_C_mul, coeff_map, coeff_map, coeff_natDegree, IntermediateField.algebraMap_apply,
      minpoly.monic (IntermediateField.isAlgebraic_X E hE).isIntegral, OneMemClass.coe_one,
      mul_one] at this
    exact this.symm

  have c_denom : c.denom = 1 := by
    rw [← Φ_coeff_n]
    exact denom_algebraMap _

  have Φ_coeff_n' : Φ.coeff (ψ E).natDegree = c.num := by
    apply algebraMap_injective
    rw [Φ_coeff_n]
    conv_lhs => rw [← num_div_denom c, c_denom, map_one, div_one]

  have Φ_coeff_i : algebraMap K[X] (RatFunc K) (Φ.coeff (generatorIndex hE)) =
      algebraMap K[X] (RatFunc K) c.num * (generator E).1 := by
    have := congr($(hcψ).coeff (generatorIndex hE))
    rw [coeff_map, coeff_C_mul, coeff_map, IntermediateField.algebraMap_apply] at this
    rw [← num_div_denom c, c_denom, map_one, div_one] at this
    rw [generator_eq hE]
    exact this.symm

  have u_denom_dvd_c_num : (generator E : RatFunc K).denom ∣ c.num := by
    rw [denom_dvd (num_ne_zero c_ne_zero)]
    use Φ.coeff (generatorIndex hE)
    rw [Φ_coeff_i, mul_div_cancel_left₀ _ (algebraMap_ne_zero (num_ne_zero c_ne_zero))]

  have Φ_ne_zero : Φ ≠ 0 := by
    intro H
    have := Φ_coeff_n' ▸ congr($(H).coeff (ψ E).natDegree)
    rw [coeff_zero] at this
    exact num_ne_zero c_ne_zero this

  -- Get Q
  obtain ⟨q, hq⟩ : ψ E ∣ ((generator E).1.minpolyX K⟮(generator E).1⟯).map (algebraMap _ E) := by
    apply minpoly.dvd
    rw [← aeval_eq_aeval_map rfl]
    exact (generator E).1.minpolyX_aeval_X
  let Q : (RatFunc K)[X] := Polynomial.C ((algebraMap K[X] (RatFunc K) (generator E).1.denom) / c) *
    q.map (algebraMap E (RatFunc K))
  have q_ne_zero : q ≠ 0 := right_ne_zero_of_mul <|
    hq ▸ Polynomial.map_ne_zero ((generator E).1.minpolyX_eq_zero_iff.not.mpr (generator_ne_C hE))
  have Q_ne_zero : Q ≠ 0 := by
    apply mul_ne_zero
    · apply C_ne_zero.mpr (div_ne_zero (algebraMap_ne_zero (generator E).1.denom_ne_zero) c_ne_zero)
    · exact Polynomial.map_ne_zero q_ne_zero

  -- Define θ := g(X) * f(Y) - f(X) * g(Y)
  let θ : K[X][Y] := Polynomial.C (generator E).1.denom * (generator E).1.num.map Polynomial.C -
    Polynomial.C (generator E).1.num * (generator E).1.denom.map Polynomial.C
  have swap_θ : Polynomial.Bivariate.swap θ = -θ := by
    rw [map_sub, map_mul, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Bivariate.swap_C,
      Bivariate.swap_map_C]
    ring
  have degθ : θ.natDegree ≤ max (generator E).1.num.natDegree (generator E).1.denom.natDegree := by
    convert natDegree_sub_le _ _ using 3
    · rw [natDegree_mul (C_ne_zero.mpr (generator E).1.denom_ne_zero)
        (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero hE))), natDegree_C, zero_add, natDegree_map]
    · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero (generator_ne_zero hE)))
        (Polynomial.map_ne_zero (generator E).1.denom_ne_zero), natDegree_C, zero_add, natDegree_map]

  -- Equation (11.3.8)
  have hQΦ : Q * Φ.map (algebraMap K[X] (RatFunc K)) = θ.map (algebraMap K[X] (RatFunc K)) := by
    rw [← hcψ, mul_assoc]
    conv =>
      lhs
      rhs
      rw [← mul_assoc]
      lhs
      rw [mul_comm]
    rw [← mul_assoc, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ c_ne_zero, mul_assoc,
      ← Polynomial.map_mul, mul_comm q (ψ E), ← hq]
    rw [Polynomial.map_map, Polynomial.map_sub, Polynomial.map_mul, map_C]
    simp only [RingHom.coe_comp, Function.comp_apply, IntermediateField.algebraMap_apply]
    rw [Polynomial.map_map, Polynomial.map_map] 
    rw [mul_sub, ← mul_assoc, ← map_mul]
    rw [(IntermediateField.inclusion (adjoin_generator_le E)).algebraMap_toAlgebra]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_inclusion]
    rw [coe_algebraMap]
    conv => lhs; rhs; lhs; rhs; rhs; rw [← num_div_denom (generator E).1]
    rw [mul_div_cancel₀ _ ((FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr (generator E).1.denom_ne_zero)]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, map_C, map_C]
    rw [Polynomial.map_map, Polynomial.map_map]
    rfl

  letI := Polynomial.algebra K[X] (RatFunc K)
  obtain ⟨Q', hQ'⟩ : IsLocalization.IsInteger K[X][Y] Q := by
    apply (Polynomial.isInteger_mul_iff_left Φ'.isPrimitive_primPart Q).mp
    rw [hQΦ]
    exact ⟨_, rfl⟩
  rw [← hQ', algebraMap_def, coe_mapRingHom, ← Polynomial.map_mul] at hQΦ
  replace hQΦ := Polynomial.map_injective _ (algebraMap_injective K) hQΦ
  have Q'_ne_zero : Q' ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp (hQ' ▸ Q_ne_zero)
  
  -- massage the goal to say Φ.natDegree = _
  rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq]
  rw [adjoin.finrank (IntermediateField.isAlgebraic_X E hE).isIntegral]
  have := congr($(hcψ).natDegree)
  rw [Polynomial.natDegree_mul 
       (Polynomial.C_ne_zero.mpr c_ne_zero)
       (Polynomial.map_ne_zero <| minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral)] at this
  simp only [natDegree_C, natDegree_map, zero_add] at this
  rw [this]
  rw [Polynomial.natDegree_map_eq_of_injective (algebraMap_injective K)]
  rw [finrank_eq_max_natDegree]
  
  have degΦ₁ : (generator E).1.num.natDegree ≤ (Φ.coeff (generator_index hE)).natDegree := by
    have := congr($(Φ_coeff_i) * algebraMap K[X] (RatFunc K) (generator E).1.denom)
    conv at this =>
      rhs
      lhs
      rhs
      rw [← num_div_denom (generator E).1]
    rw [mul_assoc] at this
    rw [div_mul_cancel₀ _ (algebraMap_ne_zero (generator E).1.denom_ne_zero)] at this
    rw [← map_mul, ← map_mul] at this
    replace this := congr($(algebraMap_injective K this).natDegree)
    rw [natDegree_mul, natDegree_mul] at this
    · rw [Nat.eq_sub_of_add_eq this, add_comm, Nat.add_sub_assoc]
      simp only [ge_iff_le, le_add_iff_nonneg_right, zero_le]
      exact natDegree_le_of_dvd u_denom_dvd_c_num (num_ne_zero c_ne_zero)
    -- side goals from `natDegree_mul`
    · exact num_ne_zero c_ne_zero
    · exact num_ne_zero (generator_ne_zero hE)
    · intro H
      replace H := congr(algebraMap K[X] (RatFunc K) $(H))
      rw [Φ_coeff_i] at H
      simp only [map_zero, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff, num_eq_zero_iff] at H
      refine Or.elim H c_ne_zero (generator_ne_zero hE)
    · exact (generator E).1.denom_ne_zero

  have degΦ₂ : (generator E).1.denom.natDegree ≤ (Φ.coeff (ψ E).natDegree).natDegree := by
    rw [Φ_coeff_n']
    exact natDegree_le_of_dvd u_denom_dvd_c_num (num_ne_zero c_ne_zero)
    
  have crucial : max (generator E).1.num.natDegree (generator E).1.denom.natDegree ≤ (Bivariate.swap Φ).natDegree := by
    rw [← sum_monomial_eq Φ, sum_def, map_sum]
    conv =>
      rhs; rhs; rhs; enter [x];
      rw [Bivariate.swap_monomial, mul_comm, ← Polynomial.smul_eq_C_mul]
      rw [← monomial_one_right_eq_X_pow]
      rhs;
      rw [← Polynomial.algebraMap_eq]
    rw [natDegree_sum_eq_of_linearIndepOn]
    swap
    · exact (basisMonomials K).linearIndepOn Φ.support --?
    apply max_le
    · apply degΦ₁.trans
      have : Φ.coeff (generator_index hE) ≠ 0 := by
        intro H
        replace H := congr(algebraMap K[X] (RatFunc K) $(H))
        rw [Φ_coeff_i] at H
        simp only [map_zero, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff, num_eq_zero_iff] at H
        exact Or.elim H c_ne_zero (generator_ne_zero hE)
      exact Finset.le_sup (f := fun i ↦ (Φ.coeff i).natDegree) (mem_support_iff.mpr this)
    · apply degΦ₂.trans
      have : Φ.coeff (ψ E).natDegree ≠ 0 := by
        rw [Φ_coeff_n']
        exact num_ne_zero c_ne_zero
      exact Finset.le_sup (f := fun i ↦ (Φ.coeff i).natDegree) (mem_support_iff.mpr this)
  
  have swapQ'_deg : (Bivariate.swap Q').natDegree = 0 := by
    have := congr(Bivariate.swap $(hQΦ))
    rw [map_mul] at this
    replace this := congr($(this).natDegree)
    rw [natDegree_mul
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr Q'_ne_zero)
      ((map_ne_zero_iff _ Bivariate.swap.injective).mpr Φ_ne_zero)] at this
    have foo : (Bivariate.swap θ).natDegree ≤ max (generator E).1.num.natDegree (generator E).1.denom.natDegree := by
      rw [swap_θ, natDegree_neg]
      exact degθ
    linarith

  let Q₂ : K[X] := (Bivariate.swap Q').coeff 0
  have hQ₂ : Q₂.map (algebraMap K K[X]) = Q' := by
    have := congr(Bivariate.swap $(eq_C_of_natDegree_eq_zero swapQ'_deg))
    rw [Bivariate.swap_swap_apply] at this
    rw [Bivariate.swap_C] at this
    exact this.symm
  rw [← hQ₂] at hQΦ

  suffices Q₂_deg : Q₂.natDegree = 0 by
    apply le_antisymm
    · have := congr($(hQΦ).natDegree)
      rw [natDegree_mul (by rwa [hQ₂]) Φ_ne_zero, natDegree_map, Q₂_deg, zero_add] at this
      rwa [this]
    · have := congr($(hQΦ).natDegree)

      rw [natDegree_mul (by rwa [hQ₂]) Φ_ne_zero, natDegree_map, Q₂_deg, zero_add] at this
      rw [this]
      have := congr((Bivariate.swap $(hQΦ)).natDegree)
      rw [eq_C_of_natDegree_eq_zero Q₂_deg] at this
      rw [map_C, map_mul, Bivariate.swap_C, algebraMap_eq, map_C] at this
      rw [natDegree_mul, natDegree_C, zero_add] at this
      · rw [← natDegree_neg θ, ← swap_θ, ← this]
        exact crucial
      · rw [C_ne_zero, ← eq_C_of_natDegree_eq_zero Q₂_deg]
        exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective K K[X])).mp (hQ₂ ▸ Q'_ne_zero)
      · exact ((map_ne_zero_iff _ Bivariate.swap.injective).mpr Φ_ne_zero)

  by_contra H
  let F := AlgebraicClosure K
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (Q₂.map (algebraMap K F)) (by
    rw [degree_map]
    exact (ne_of_not_ge (natDegree_eq_zero_iff_degree_le_zero.not.mp H)).symm
  )
  letI : Algebra K[X] F[X] := Polynomial.algebra K F
  simp only [IsRoot.def, eval_map_algebraMap] at hα

  apply_fun aeval (Polynomial.C α) at hQΦ
  rw [aeval_mul] at hQΦ
  rw [← map_aeval_eq_aeval_map (by ext; simp), hα, map_zero] at hQΦ
  rw [zero_mul] at hQΦ
  rw [aeval_sub, aeval_mul, aeval_mul, aeval_C, aeval_C] at hQΦ
  rw [← map_aeval_eq_aeval_map (by ext; simp)] at hQΦ
  rw [← map_aeval_eq_aeval_map (by ext; simp)] at hQΦ
  simp only [algebraMap_def, coe_mapRingHom] at hQΦ
  replace hQΦ := hQΦ.symm
  rw [sub_eq_zero] at hQΦ
  apply (generator E).1.eq_C_iff.not.mp (generator_ne_C hE)
  obtain ⟨aeval_num_ne_zero, aeval_denom_ne_zero⟩ : aeval α (generator E).1.num ≠ 0 ∧ aeval α (generator E).1.denom ≠ 0 := by
    obtain (h | h) := aeval_ne_zero_of_isCoprime (generator E).1.isCoprime_num_denom α
    · refine ⟨h, ?_⟩
      apply_fun Polynomial.C
      rw [map_zero]
      have := hQΦ ▸ mul_ne_zero (Polynomial.map_ne_zero (generator E).1.denom_ne_zero) ((Polynomial.C_ne_zero.mpr h))
      rw [mul_ne_zero_iff_left (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero hE)))] at this
      exact this
    · refine ⟨?_, h⟩
      apply_fun Polynomial.C
      rw [map_zero]
      have := hQΦ ▸ mul_ne_zero (Polynomial.map_ne_zero (num_ne_zero (generator_ne_zero hE))) ((Polynomial.C_ne_zero.mpr h))
      rw [mul_ne_zero_iff_left (Polynomial.map_ne_zero (generator E).1.denom_ne_zero)] at this
      exact this
  constructor
  · rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K F) (generator E).1.num]
    apply natDegree_eq_zero_of_isUnit
    rw [← Polynomial.coe_mapRingHom] at hQΦ
    refine IsCoprime.isUnit_of_dvd (IsCoprime.map (generator E).1.isCoprime_num_denom (Polynomial.mapRingHom (algebraMap K F))) ?_
    rw [← IsUnit.dvd_mul_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr aeval_num_ne_zero))]
    use Polynomial.C ((aeval α) (generator E).1.denom)
    exact hQΦ
  · rw [← natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K F) (generator E).1.denom]
    apply natDegree_eq_zero_of_isUnit
    rw [← Polynomial.coe_mapRingHom] at hQΦ
    refine IsCoprime.isUnit_of_dvd (IsCoprime.map (generator E).1.isCoprime_num_denom (Polynomial.mapRingHom (algebraMap K F))).symm ?_
    rw [← IsUnit.dvd_mul_right (isUnit_C.mpr (isUnit_iff_ne_zero.mpr aeval_denom_ne_zero))]
    use Polynomial.C ((aeval α) (generator E).1.num)
    exact hQΦ.symm

end Luroth

end RatFunc
