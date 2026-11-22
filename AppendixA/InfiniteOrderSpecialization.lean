module

public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Specializations preserving infinite multiplicative order

For a fixed finitely generated rational domain, points of uniformly bounded
degree over the rationals meet every nonempty principal open subset. A common
exponent for roots of unity in fields of that degree then lets one retain
infinite multiplicative order for finitely many chosen elements.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Submodule Module
open scoped Classical

private theorem torsion_exponent {K : Type} [Field K] [NumberField K] {D : ℕ}
    (hD : finrank ℚ K ≤ D) {z : K} (hz : IsOfFinOrder z) :
    z ^ ((D+1)*D).factorial = 1 := by
  let n := orderOf z
  have hn : 0 < n := hz.orderOf_pos
  have hi : Irreducible (Polynomial.cyclotomic (Nat.lcm n n) ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (Nat.lcm_pos hn hn)
  have ht : n.totient ≤ D := by
    have he := (IsPrimitiveRoot.orderOf z).lcm_totient_le_finrank (K := ℚ) (IsPrimitiveRoot.orderOf z) hi
    exact (show n.totient ≤ finrank ℚ K by simpa only [Nat.lcm_self] using he).trans hD
  apply orderOf_dvd_iff_pow_eq_one.mp
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ n).mpr
  intro p k hp hpk
  cases k with
  | zero => simp
  | succ k =>
    have h := (Nat.le_of_dvd (Nat.totient_pos.mpr hn) (Nat.totient_dvd_of_dvd hpk)).trans ht
    rw [Nat.totient_prime_pow_succ hp] at h
    have hpos := hp.one_lt
    have hpkpos := pow_pos hp.pos k
    have hpD : p - 1 ≤ D := (Nat.le_mul_of_pos_left _ hpkpos).trans h
    have hkD : p^k ≤ D := (Nat.le_mul_of_pos_right _ (by omega : 0 < p-1)).trans h
    apply Nat.dvd_factorial (pow_pos hp.pos _)
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul (by omega) hkD

private theorem bounded_degree_specialization (A : Type) [CommRing A] [IsDomain A]
    [Algebra ℚ A] [Algebra.FiniteType ℚ A] :
    ∃ D : ℕ, ∀ w : A, w ≠ 0 →
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (f : A →+* K),
        finrank ℚ K ≤ D ∧ f w ≠ 0 := by
  obtain ⟨s,g,hinj,hfin⟩ := exists_finite_inj_algHom_of_fg ℚ A
  let B := MvPolynomial (Fin s) ℚ
  let : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hfin
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨D,v,hv⟩ := Module.Finite.exists_fin (R := B) (M := A)
  refine ⟨D,fun w hw => ?_⟩
  let J := Ideal.span {w}
  obtain ⟨p,hpmon,hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) w
  obtain ⟨m,hpm,hm⟩ := Ideal.exists_coeff_ne_zero_mem_comap_of_root_mem (f := g.toRingHom) (I := J)
    hw (Ideal.subset_span (mem_singleton w)) hpmon.ne_zero hroot
  have hex : ∃ x : Fin s → ℚ, MvPolynomial.eval x (p.coeff m) ≠ 0 := by
    by_contra! hall
    exact hpm (MvPolynomial.funext fun x => by simpa using hall x)
  obtain ⟨x,hx⟩ := hex
  let ev : B →+* ℚ := MvPolynomial.eval x
  let P := RingHom.ker ev
  have : P.IsMaximal := RingHom.ker_isMaximal_of_surjective ev (fun r => ⟨MvPolynomial.C r,MvPolynomial.eval_C (f := x) r⟩)
  obtain ⟨Q,hQ,hPQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P (by
    change RingHom.ker g.toRingHom ≤ P
    rw [(RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hinj]
    exact bot_le)
  let := Ideal.Quotient.field Q
  have : Module.Finite ℚ (A ⧸ Q) := finite_of_finite_type_of_isJacobsonRing _ _
  let f := Ideal.Quotient.mk Q
  have hscalar (b : B) : f (g b) = algebraMap ℚ (A ⧸ Q) (ev b) := by
    have hker : b - MvPolynomial.C (ev b) ∈ P := by
      change ev _ = 0
      rw [map_sub,show ev (MvPolynomial.C (ev b)) = ev b from MvPolynomial.eval_C (f := x) _,sub_self]
    rw [← hPQ] at hker
    change g (b - MvPolynomial.C (ev b)) ∈ Q at hker
    have he := (Ideal.Quotient.eq_zero_iff_mem.mpr hker)
    change f (g (b - MvPolynomial.C (ev b))) = 0 at he
    rw [map_sub,map_sub,sub_eq_zero] at he
    rw [MvPolynomial.C_eq_algebraMap,g.commutes] at he
    exact he.trans ((Ideal.Quotient.mkₐ ℚ Q).commutes _)
  let V := span ℚ (range (fun j => f (v j)))
  have hV : V = ⊤ := by
    apply top_unique
    intro y hy
    clear hy
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective y
    have ha : a ∈ span B (range v) := hv ▸ mem_top
    induction ha using span_induction with
    | mem a ha => obtain ⟨i,rfl⟩ := ha; exact subset_span (mem_range_self i)
    | zero => simp
    | add x y _ _ h₁ h₂ => simpa using V.add_mem h₁ h₂
    | smul b x _ h =>
      change f (g b * x) ∈ V
      rw [map_mul,hscalar,← Algebra.smul_def]
      exact V.smul_mem _ h
  refine ⟨A ⧸ Q,inferInstance,NumberField.of_module_finite ℚ _,f,?_,?_⟩
  · have he := finrank_range_le_card (R := ℚ) (fun j => f (v j))
    change finrank ℚ V ≤ _ at he
    rw [hV,finrank_top] at he
    simp only [Fintype.card_fin] at he
    convert! he using 2
    exact Subsingleton.elim _ _
  · intro hf
    have hwQ := Ideal.Quotient.eq_zero_iff_mem.mp hf
    have hle : J ≤ Q := Ideal.span_le.mpr (singleton_subset_iff.mpr hwQ)
    apply hx
    change p.coeff m ∈ P
    rw [← hPQ]
    exact hle hm

/-- A single specialization preserves a finite collection of infinite-order
elements of a finitely generated rational domain and a given nonzero element. -/
theorem exists_numberField_preserving_infiniteOrder (A : Type) [CommRing A] [IsDomain A]
    [Algebra ℚ A] [Algebra.FiniteType ℚ A] (S : Finset A) (hS : ∀ z ∈ S, ¬IsOfFinOrder z)
    (w : A) (hw : w ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (f : A →+* K),
      f w ≠ 0 ∧ ∀ z ∈ S, ¬IsOfFinOrder (f z) := by
  obtain ⟨D,hD⟩ := bounded_degree_specialization A
  let m := ((D+1)*D).factorial
  let a := w * ∏ z ∈ S, (z^m - 1)
  have ha : a ≠ 0 := mul_ne_zero hw (Finset.prod_ne_zero_iff.mpr fun z hz =>
    sub_ne_zero.mpr (fun he => hS z hz (isOfFinOrder_iff_pow_eq_one.mpr ⟨m,Nat.factorial_pos _,he⟩)))
  obtain ⟨K,_,_,f,hdeg,hfa⟩ := hD a ha
  rw [show a = _ from rfl,map_mul,map_prod] at hfa
  refine ⟨K,inferInstance,inferInstance,f,left_ne_zero_of_mul hfa,fun z hz hfin => ?_⟩
  have hkeep := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hfa) z hz
  exact hkeep (by rw [map_sub,map_pow,map_one,torsion_exponent hdeg hfin,sub_self])

end
end MeyerGeneralProblem.LevOlevskii
