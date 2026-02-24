/-
Copyright (c) 2025 Miriam Philipp, Justus Springer and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.Relrank
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Lüroth's theorem

The goal of this file is to prove Lüroth's theorem, which says that for every field K,
every intermediate field between K and the rational function field K(X) is either K or
isomorphic to K(X) as an K-algebra. The proof depends on the following lemma on degrees of
rational functions:

Let `f` be a rational function, i.e. an element in the field `K(X)` (`RatFunc K`). Let `p` be its
numerator and `q` its denominator. Then the degree of the field extension `K(X)/K(f)` equals the
maximum of the degrees of `p` and `q`. Since `finrank` is defined to be zero when the extension
is infinite, this holds even when `f` is constant.

References:

- https://github.com/leanprover-community/mathlib4/pull/7788#issuecomment-1788132019
- P. M. Cohn, *Basic Algebra: Groups, Rings and Fields*, Springer, 2003, Proposition 11.3.1.
- N. Jacobson, *Basic Algebra II: Second Edition*, 1989 (Dover edition 2009), Theorem 8.38.

-/

@[expose] public section

namespace Polynomial

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

end Polynomial

namespace RatFunc

open IntermediateField algebraAdjoinAdjoin
open scoped Polynomial

variable {K : Type*} [Field K] (f : RatFunc K)

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
as a polynomial with coefficients in `K⟮f⟯`. -/
noncomputable abbrev minpolyX : K⟮f⟯[X] :=
  f.num.map (algebraMap K K⟮f⟯) -
  Polynomial.C (AdjoinSimple.gen K f) * f.denom.map (algebraMap K K⟮f⟯)

@[simp]
theorem C_minpolyX (x : K) : (C x).minpolyX = 0 := by
  rw [minpolyX, num_C, Polynomial.map_C, denom_C, Polynomial.map_one, mul_one, sub_eq_zero,
    Polynomial.C_inj, Subtype.ext_iff, AdjoinSimple.coe_gen, SubalgebraClass.coe_algebraMap,
    algebraMap_eq_C]

theorem minpolyX_aeval_X : f.minpolyX.aeval (X : RatFunc K) = 0 := by
  simp only [Polynomial.aeval_sub, Polynomial.aeval_map_algebraMap, aeval_X_left_eq_algebraMap,
    map_mul, Polynomial.aeval_C, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen]
  nth_rw 2 [← num_div_denom f]
  rw [div_mul_cancel₀ _ (algebraMap_ne_zero f.denom_ne_zero)]
  exact sub_self _

theorem eq_C_of_minpolyX_coeff_eq_zero
  (hf : f.minpolyX.coeff f.denom.natDegree = (0 : RatFunc K)) : ∃ c, f = C c := by
  use f.num.coeff f.denom.natDegree / f.denom.leadingCoeff
  rw [map_div₀, eq_div_iff ((map_ne_zero C).mpr
    (Polynomial.leadingCoeff_ne_zero.mpr f.denom_ne_zero)), eq_comm]
  simpa [sub_eq_zero] using hf

theorem minpolyX_eq_zero_iff : f.minpolyX = 0 ↔ ∃ c, f = C c :=
  ⟨fun h ↦ f.eq_C_of_minpolyX_coeff_eq_zero (by simp [h]), by rintro ⟨c, rfl⟩; simp⟩

section FNeC

-- In this section, we assume `f` is not constant.
variable (hf : ¬∃ c, f = C c)
include hf

local notation "K[f]" => Algebra.adjoin K {(f : RatFunc K)}

theorem isAlgebraic_adjoin_simple_X : IsAlgebraic K⟮f⟯ (X : RatFunc K) :=
   ⟨f.minpolyX, fun H ↦ hf (f.minpolyX_eq_zero_iff.mp H), f.minpolyX_aeval_X⟩

theorem isAlgebraic_adjoin_simple_X' : Algebra.IsAlgebraic K⟮f⟯ (RatFunc K) := by
  have : Algebra.IsAlgebraic K⟮f⟯ K⟮f⟯⟮(X : RatFunc K)⟯ :=
    isAlgebraic_adjoin_simple <| isAlgebraic_iff_isIntegral.mp <| f.isAlgebraic_adjoin_simple_X hf
  exact (IntermediateField.adjoinXEquiv K⟮f⟯).isAlgebraic

theorem natDegree_denom_le_natDegree_minpolyX : f.denom.natDegree ≤ f.minpolyX.natDegree :=
  Polynomial.le_natDegree_of_ne_zero fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero
    (congr_arg Subtype.val H))

theorem natDegree_num_le_natDegree_minpolyX : f.num.natDegree ≤ f.minpolyX.natDegree := by
  have f_ne_zero : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, (RingHom.map_zero C).symm⟩
  apply Polynomial.le_natDegree_of_ne_zero
  intro H
  replace H := congr_arg Subtype.val H
  simp only [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_natDegree,
    Polynomial.coeff_C_mul, AddSubgroupClass.coe_sub, SubalgebraClass.coe_algebraMap,
    algebraMap_eq_C, MulMemClass.coe_mul, AdjoinSimple.coe_gen, ZeroMemClass.coe_zero] at H
  rw [sub_eq_zero, ← mul_right_inj' (inv_ne_zero f_ne_zero), ← mul_assoc, inv_mul_cancel₀ f_ne_zero,
    one_mul, ← eq_div_iff <| (map_ne_zero C).mpr <| Polynomial.leadingCoeff_ne_zero.mpr
    (num_ne_zero f_ne_zero), ← inv_inj, inv_inv, ← map_div₀, ← map_inv₀] at H
  exact hf ⟨_, H⟩

omit hf in
theorem natDegree_minpolyX : f.minpolyX.natDegree = max f.num.natDegree f.denom.natDegree := by
  by_cases hf : ∃ c, f = C c
  · obtain ⟨c, rfl⟩ := hf
    simp [C_minpolyX]
  apply le_antisymm
  · have : f.minpolyX.natDegree ≤ _ := Polynomial.natDegree_sub_le _ _
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C_mul fun H ↦
      hf ⟨0, by simpa [map_zero] using congr_arg Subtype.val H⟩,
      Polynomial.natDegree_map] at this
    exact this
  · exact max_le (natDegree_num_le_natDegree_minpolyX f hf) <| Polynomial.le_natDegree_of_ne_zero
      fun H ↦ hf (f.eq_C_of_minpolyX_coeff_eq_zero (congr_arg Subtype.val H))

theorem transcendental_of_ne_C : Transcendental K f := by
  intro H
  have := IntermediateField.isAlgebraic_adjoin_simple H.isIntegral
  have tr : Algebra.Transcendental K (RatFunc K) := by infer_instance
  rw [Algebra.transcendental_iff_not_isAlgebraic] at tr
  exact tr <| Algebra.IsAlgebraic.trans _ _ _ (alg := f.isAlgebraic_adjoin_simple_X' hf)

theorem transcendental_of_ne_C' :
    Transcendental K (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f]):= by
  rw [← transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (Algebra.adjoin K {f}) (RatFunc K))]
  exact f.transcendental_of_ne_C hf

/-- The equivalence between `K[X]` and `K[f]` as `K`-algebras. Here, `f` is required to
be non-constant. -/
noncomputable def adjoinSimpleEquiv : K[X] ≃ₐ[K] K[f] :=
  AlgEquiv.ofBijective (Polynomial.aeval ⟨f, Algebra.self_mem_adjoin_singleton K f⟩) <| by
    refine ⟨transcendental_iff_injective.mp (f.transcendental_of_ne_C' hf), ?_⟩
    rw [← AlgHom.range_eq_top, eq_top_iff]
    rintro ⟨g, g_mem⟩ _
    obtain ⟨r, rfl⟩ := Algebra.adjoin_mem_exists_aeval _ _ g_mem
    exact ⟨r, by ext; simp⟩

@[simp]
theorem adjoinSimpleEquiv_coe : (f.adjoinSimpleEquiv hf : K[X] →+* K[f]) =
    Polynomial.aeval (R := K) (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f]) := rfl

@[simp]
theorem adjoinSimpleEquiv_apply (g : K[X]) : f.adjoinSimpleEquiv hf g =
    Polynomial.aeval (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f]) g := rfl

lemma algEquivOfTranscendental_apply_X :
    f.adjoinSimpleEquiv hf Polynomial.X = ⟨f, Algebra.subset_adjoin rfl⟩ := by
  rw [adjoinSimpleEquiv_apply, Subtype.ext_iff, Polynomial.coe_aeval_mk_apply, Polynomial.aeval_X]

theorem irreducible_minpolyX : Irreducible f.minpolyX := by
  have : UniqueFactorizationMonoid K[f] :=
    (f.adjoinSimpleEquiv hf).toMulEquiv.uniqueFactorizationMonoid inferInstance
  let φ : K[f][X] := f.num.map (algebraMap ..) -
    Polynomial.C (⟨f, Algebra.self_mem_adjoin_singleton K f⟩ : K[f]) * f.denom.map (algebraMap ..)
  suffices Irreducible φ by
    have φ_map : φ.map (algebraMap ..) = f.minpolyX := by
      simp only [φ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C]
      congr 1
      · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
        simp only [mul_eq_mul_right_iff, Polynomial.C_inj]
        exact .inl rfl
    rw [← φ_map, ← Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map]
    · exact this
    · apply this.isPrimitive
      intro H
      have := Polynomial.natDegree_map_le (f := algebraMap K[f] K⟮f⟯) (p := φ)
      rw [φ_map, H, nonpos_iff_eq_zero, f.natDegree_minpolyX, Nat.max_eq_zero_iff,
        ← f.eq_C_iff] at this
      exact hf this
  let φ' : K[X][X] := f.num.map (algebraMap ..) -
    Polynomial.C Polynomial.X * f.denom.map (algebraMap ..)
  have φ'_map : φ'.mapEquiv (f.adjoinSimpleEquiv hf).toRingEquiv = φ := by
    simp only [φ', AlgEquiv.toRingEquiv_eq_coe, Polynomial.algebraMap_eq, Polynomial.mapEquiv_apply,
      AlgEquiv.toRingEquiv_toRingHom, adjoinSimpleEquiv_coe, Polynomial.map_sub, Polynomial.map_map,
      Polynomial.map_mul, Polynomial.map_C, RingHom.coe_coe, Polynomial.aeval_X]
    congr 2 <;> ext <;> simp
  rw [← φ'_map, MulEquiv.irreducible_iff]
  have : φ' = Polynomial.Bivariate.swap
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


variable (E : IntermediateField K (RatFunc K)) (hE : E ≠ ⊥)
include hE

theorem IntermediateField.isAlgebraic_X : IsAlgebraic E (X : RatFunc K) := by
  rw [ne_eq, ← le_bot_iff, SetLike.not_le_iff_exists] at hE
  obtain ⟨f, hf₁, hf₂⟩ := hE
  exact IsAlgebraic.tower_top_of_subalgebra_le (adjoin_simple_le_iff.mpr hf₁) <|
    f.isAlgebraic_adjoin_simple_X (by rintro ⟨c, rfl⟩; exact hf₂ ⟨c, rfl⟩)

open Polynomial

open scoped Polynomial.Bivariate


theorem luroth : ∃ u : RatFunc K, E = K⟮u⟯ := by
  classical
  let ψ : E[X] := minpoly E (X : RatFunc K)
  obtain ⟨i, hi⟩ : ∃ i, ψ.coeff i ∉ (algebraMap K E).range := by
    by_contra! h
    obtain ⟨ψ', hψ'⟩ := (mem_map_range _).mpr h
    refine transcendental_X (K := K) ⟨ψ', ?_, ?_⟩
    · rintro rfl
      rw [coe_mapRingHom, Polynomial.map_zero, eq_comm] at hψ'
      exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral hψ'
    · replace hψ' := congrArg (aeval (X : RatFunc K)) hψ'
      rw [coe_mapRingHom, aeval_map_algebraMap, aeval_X_left_eq_algebraMap, minpoly.aeval,
        map_eq_zero_iff _ (algebraMap_injective K)] at hψ'
      rw [aeval_X_left_eq_algebraMap, FaithfulSMul.algebraMap_eq_zero_iff]
      exact hψ'
  let u : RatFunc K := ψ.coeff i
  have hu : ¬ ∃ c, u = C c := fun ⟨c, hc⟩ ↦ hi ⟨c, Subtype.ext (by simpa using hc.symm)⟩
  have u_ne_zero : u ≠ 0 := fun H ↦ hu ⟨0, by rwa [map_zero]⟩
  have adjoin_u_le : K⟮u⟯ ≤ E := adjoin_simple_le_iff.mpr (Subtype.property _)
  letI : Algebra K⟮u⟯ E := (IntermediateField.inclusion adjoin_u_le).toAlgebra
  have n_pos : 0 < Module.finrank E (RatFunc K) := by
    rw [← (IntermediateField.adjoinXEquiv E).toLinearEquiv.finrank_eq]
    rw [adjoin.finrank (IntermediateField.isAlgebraic_X E hE).isIntegral]
    apply minpoly.natDegree_pos (IntermediateField.isAlgebraic_X E hE).isIntegral
  refine ⟨u, le_antisymm (relfinrank_eq_one_iff.mp ?_) adjoin_u_le⟩

  suffices Module.finrank E (RatFunc K) = Module.finrank K⟮u⟯ (RatFunc K) from
    (mul_eq_right₀ (by lia)).mp (this ▸ relfinrank_mul_finrank_top adjoin_u_le)

  -- Define Φ and prove its spec
  let Φ' : K[X][Y] := IsLocalization.integerNormalization (nonZeroDivisors K[X])
    (ψ.map (algebraMap E (RatFunc K)))
  let Φ : K[X][Y] := Φ'.primPart
  obtain ⟨⟨b, hb₁⟩, (hb₂ : Φ'.map _ = _)⟩ :=
    IsLocalization.integerNormalization_map_to_map (nonZeroDivisors K[X])
    (ψ.map (algebraMap E (RatFunc K)))
  let c : RatFunc K := (algebraMap K[X] (RatFunc K) Φ'.content)⁻¹ * algebraMap K[X] (RatFunc K) b
  have c_ne_zero : c ≠ 0 := by
    rw [mul_ne_zero_iff]
    constructor
    · apply inv_ne_zero
      rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
        IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
      exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral
    · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
      exact nonZeroDivisors.ne_zero hb₁
  have hcψ : Polynomial.C c * ψ.map (algebraMap E (RatFunc K)) = Φ.map (algebraMap K[X] (RatFunc K)) := by
    rw [map_mul, mul_assoc]
    conv =>
      lhs; rhs
      rw [← Polynomial.smul_eq_C_mul, algebraMap_smul, ← hb₂, eq_C_content_mul_primPart Φ']
    rw [Polynomial.map_mul, map_C, ← mul_assoc, ← C_mul, inv_mul_cancel₀,  map_one, one_mul]
    · rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, content_eq_zero_iff,
        IsFractionRing.integerNormalization_eq_zero_iff, Polynomial.map_eq_zero]
      exact minpoly.ne_zero (IntermediateField.isAlgebraic_X E hE).isIntegral

  -- Get Q
  obtain ⟨q, hq⟩ : ψ ∣ (minpolyX u).map (algebraMap K⟮u⟯ E) := by
    apply minpoly.dvd
    rw [← aeval_eq_aeval_map rfl]
    exact u.minpolyX_aeval_X
  let Q : (RatFunc K)[X] := Polynomial.C ((algebraMap K[X] (RatFunc K) u.denom) / c) *
    q.map (algebraMap E (RatFunc K))
     
  -- Define θ := g(X) * f(Y) - f(X) * g(Y)
  let θ : K[X][Y] := Polynomial.C u.denom * u.num.map Polynomial.C -
    Polynomial.C u.num * u.denom.map Polynomial.C
  have swap_θ : Polynomial.Bivariate.swap θ = -θ := by
    rw [map_sub, map_mul, map_mul, Bivariate.swap_C, Bivariate.swap_map_C, Bivariate.swap_C,
      Bivariate.swap_map_C]
    ring
  have degθ : θ.natDegree ≤ max u.num.natDegree u.denom.natDegree := by
    convert natDegree_sub_le _ _ using 3
    · rw [natDegree_mul (C_ne_zero.mpr u.denom_ne_zero)
        (Polynomial.map_ne_zero (num_ne_zero u_ne_zero)), natDegree_C, zero_add, natDegree_map]
    · rw [natDegree_mul (C_ne_zero.mpr (num_ne_zero u_ne_zero))
        (Polynomial.map_ne_zero u.denom_ne_zero), natDegree_C, zero_add, natDegree_map]

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
      ← Polynomial.map_mul, mul_comm q ψ, ← hq]
    rw [Polynomial.map_map, Polynomial.map_sub, Polynomial.map_mul, map_C]
    simp only [RingHom.coe_comp, Function.comp_apply, IntermediateField.algebraMap_apply]
    rw [Polynomial.map_map, Polynomial.map_map] 
    rw [mul_sub, ← mul_assoc, ← map_mul]
    rw [(IntermediateField.inclusion adjoin_u_le).algebraMap_toAlgebra]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coe_inclusion, AdjoinSimple.coe_gen]
    conv => lhs; rhs; lhs; rhs; rhs; rw [← num_div_denom u]
    rw [mul_div_cancel₀ _ ((FaithfulSMul.algebraMap_eq_zero_iff _ _).not.mpr u.denom_ne_zero)]
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

  sorry

end RatFunc

