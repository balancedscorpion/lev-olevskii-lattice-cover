module

public import AppendixA.UnitFiniteness
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Jacobson.Ring

/-!
# Specialization of a finite family of solutions

A uniform bound for the algebraic-number case of the unit equation transfers
to complex data. Specialization must keep solutions distinct and must
preserve every nonzero subsum in the chosen finite family.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set
open scoped Classical

private theorem specialization (s : Finset ℂ) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : Subalgebra ℚ ℂ) (f : A →+* K),
      (s : Set ℂ) ⊆ A ∧ ∀ z : A, z.val ∈ s → z.val ≠ 0 → f z ≠ 0 := by
  let T := s ∪ s.image (·⁻¹)
  let A := Algebra.adjoin ℚ (T : Set ℂ)
  have memA {x : ℂ} (hx : x ∈ s) : x ∈ A := Algebra.subset_adjoin (Finset.mem_union_left _ hx)
  have invA {x : ℂ} (hx : x ∈ s) : x⁻¹ ∈ A :=
    Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
  have : Algebra.FiniteType ℚ A := A.fg_iff_finiteType.mp (Subalgebra.fg_adjoin_finset T)
  obtain ⟨I,hI⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field I
  have : Module.Finite ℚ (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing _ _
  let f := Ideal.Quotient.mk I
  refine ⟨A ⧸ I,inferInstance,NumberField.of_module_finite ℚ _,A,f,fun _ hx => memA hx,fun z hz hn => ?_⟩
  let w : A := ⟨z.val⁻¹,invA hz⟩
  have hw : z * w = 1 := Subtype.ext (mul_inv_cancel₀ hn)
  have he := congrArg f hw
  rw [map_mul,map_one] at he
  exact left_ne_zero_of_mul_eq_one he

/-- Coordinate values of a tuple expressed as a word in the torus generators. -/
def unitWord {ι ρ R : Type} [Fintype ρ] [CommRing R] (g : ρ → ι → Rˣ)
    (e : ρ → ℤ) (i : ι) : R := ↑(∏ k, g k i ^ e k)

/-- The prescribed exponent vectors give distinct nondegenerate solutions of
the same normalized equation. -/
def UnitSolutionFamily {ι ρ τ R : Type} [Fintype ι] [Fintype ρ] [CommRing R]
    (c : ι → R) (g : ρ → ι → Rˣ) (e : τ → ρ → ℤ) : Prop :=
  (∀ i, c i ≠ 0) ∧ Function.Injective (fun t => unitWord g (e t)) ∧
    (∀ t, ∑ i, c i * unitWord g (e t) i = 1) ∧
    ∀ t (J : Finset ι), J.Nonempty → ∑ i ∈ J, c i * unitWord g (e t) i ≠ 0

private theorem map_unitWord {ι ρ R K : Type} [Fintype ρ] [CommRing R] [CommRing K]
    (f : R →+* K) (g : ρ → ι → Rˣ) (e : ρ → ℤ) (i : ι) :
    f (unitWord g e i) = unitWord (fun k j => Units.map f.toMonoidHom (g k j)) e i := by
  change (Units.map f.toMonoidHom (∏ k, g k i ^ e k)).val = _
  simp only [unitWord,map_prod,map_zpow]

/-- A finite family and its integer exponent vectors can be realized in a
single number field, preserving distinctness and all nonvanishing conditions. -/
theorem specialize_unitSolutionFamily {ι ρ τ : Type} [Fintype ι] [Fintype ρ] [Fintype τ]
    {c : ι → ℂ} {g : ρ → ι → ℂˣ} (e : τ → ρ → ℤ) (h : UnitSolutionFamily c g e) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (b : ι → K) (u : ρ → ι → Kˣ),
      UnitSolutionFamily b u e := by
  let gen (p : ρ × ι) : ℂ := g p.1 p.2
  let dif (p : τ × τ × ι) := unitWord g (e p.1) p.2.2 - unitWord g (e p.2.1) p.2.2
  let sum (p : τ × Finset ι) := ∑ i ∈ p.2, c i * unitWord g (e p.1) i
  let S := range c ∪ range gen ∪ range (fun p => (gen p)⁻¹) ∪ range dif ∪ range sum
  have hS : S.Finite :=
    ((((finite_range _).union (finite_range _)).union (finite_range _)).union (finite_range _)).union (finite_range _)
  obtain ⟨K,fieldK,nf,A,f,hA,hf⟩ := specialization hS.toFinset
  have incl {x : ℂ} (hx : x ∈ S) : x ∈ A := hA (hS.mem_toFinset.mpr hx)
  have keep {x : A} (hs : x.val ∈ S) (hn : x.val ≠ 0) : f x ≠ 0 := hf _ (hS.mem_toFinset.mpr hs) hn
  have hc (i) : c i ∈ S := Or.inl (Or.inl (Or.inl (Or.inl (mem_range_self i))))
  let ca (i : ι) : A := ⟨c i,incl (hc i)⟩
  let ga (k : ρ) (i : ι) : Aˣ :=
    ⟨⟨gen (k,i),incl (Or.inl (Or.inl (Or.inl (Or.inr (mem_range_self (k,i))))))⟩,
     ⟨(gen (k,i))⁻¹,incl (Or.inl (Or.inl (Or.inr (mem_range_self (k,i)))))⟩,
     Subtype.ext (mul_inv_cancel₀ (g k i).ne_zero),Subtype.ext (inv_mul_cancel₀ (g k i).ne_zero)⟩
  have hga (k i) : Units.map A.val.toRingHom.toMonoidHom (ga k i) = g k i := Units.ext rfl
  have hword (t i) : (unitWord ga (e t) i).val = unitWord g (e t) i := by
    change A.val.toRingHom (unitWord ga (e t) i) = _
    simpa only [hga] using map_unitWord A.val.toRingHom ga (e t) i
  let sumA (t : τ) (J : Finset ι) := ∑ i ∈ J, ca i * unitWord ga (e t) i
  have hsumA (t J) : (sumA t J).val = sum (t,J) := by simp [sumA,sum,hword,ca]
  let u (k i) := Units.map f.toMonoidHom (ga k i)
  have hsum (t J) : f (sumA t J) = ∑ i ∈ J, f (ca i) * unitWord u (e t) i := by
    simp only [sumA,map_sum,map_mul,map_unitWord,u]
  refine ⟨K,fieldK,nf,fun i => f (ca i),u,fun i => keep (hc i) (h.1 i),?_,?_,?_⟩
  · intro t v he
    apply h.2.1
    funext i
    by_contra hne
    let w := unitWord ga (e t) i - unitWord ga (e v) i
    have hw : w.val = dif (t,v,i) := by simp [w,dif,hword]
    have hn := keep (x := w) (hw ▸ Or.inl (Or.inr (mem_range_self (t,v,i)))) (by
      rw [hw]
      exact sub_ne_zero.mpr hne)
    apply hn
    simpa only [w,map_sub,map_unitWord,sub_eq_zero] using congrFun he i
  · intro t
    rw [← hsum]
    have hone : sumA t Finset.univ = 1 := Subtype.ext ((hsumA ..).trans (h.2.2.1 t))
    rw [hone,map_one]
  · intro t J hJ
    rw [← hsum]
    apply keep
    · rw [hsumA]
      exact Or.inr (mem_range_self (t,J))
    · rw [hsumA]
      exact h.2.2.2 t J hJ

/-- For fixed numbers of coordinates and generators the number of
nondegenerate solutions is bounded uniformly over number fields, coefficients
and generator values. No particular numerical bound is prescribed. -/
def NumberFieldUnitEquationBound : Prop :=
  ∀ (ι ρ : Type) [Fintype ι] [Fintype ρ], ∃ N : ℕ,
    ∀ (K : Type) [Field K] [NumberField K] (c : ι → K) (g : ρ → ι → Kˣ)
      (e : Fin (N+1) → ρ → ℤ), ¬UnitSolutionFamily c g e

/-- Specialize any proposed counterexample larger than the number-field
bound, using precisely the same number of generators and the same exponents. -/
theorem unitEquations_of_numberFieldBound (h : NumberFieldUnitEquationBound) : UnitaryUnitEquationFiniteness := by
  intro ι _ Γ hΓ c hc
  obtain ⟨S,hspan,hfin⟩ := (AddSubgroup.fg_iff Γ).mp hΓ
  let := hfin.fintype
  let g (k : S) (i : ι) := Circle.toUnits (k.val i).toMul
  obtain ⟨N,hN⟩ := h ι S
  let Z := {z : ι → Additive Circle | z ∈ Γ ∧ (∑ i, c i * phaseValue (z i)) = 1 ∧
    ∀ J : Finset ι, J.Nonempty → ∑ i ∈ J, c i * phaseValue (z i) ≠ 0}
  change Z.Finite
  by_contra hinf
  let sel := Set.Infinite.natEmbedding Z hinf
  let z (t : Fin (N+1)) : ι → Additive Circle := (sel t.val).val
  have hz (t) : z t ∈ Z := (sel t.val).property
  have repr (t) : z t ∈ Submodule.span ℤ (range (fun k : S => k.val)) := by
    rw [Subtype.range_coe,← Submodule.mem_toAddSubgroup,Submodule.span_int_eq_addSubgroupClosure,hspan]
    exact (hz t).1
  choose e he using fun t => (Submodule.mem_span_range_iff_exists_fun ℤ).mp (repr t)
  have hw (t i) : unitWord g (e t) i = phaseValue (z t i) := by
    rw [← he t]
    simp [unitWord,g,phaseValue,Finset.sum_apply,Pi.smul_apply,toMul_sum]
    simp_rw [← Circle.coe_zpow]
    exact (map_prod Circle.coeHom (fun k : S => (k.val i).toMul ^ e t k) Finset.univ).symm
  have hfam : UnitSolutionFamily c g e := by
    refine ⟨hc,?_,?_,?_⟩
    · intro t v heq
      apply Fin.ext
      apply sel.injective
      apply Subtype.ext
      funext i
      apply Additive.toMul.injective
      apply Circle.coe_injective
      exact (hw t i).symm.trans ((congrFun heq i).trans (hw v i))
    · simpa only [hw] using fun t => (hz t).2.1
    · simpa only [hw] using fun t => (hz t).2.2
  obtain ⟨K,_,_,b,u,hbu⟩ := specialize_unitSolutionFamily e hfam
  exact hN K b u e hbu

/-- Uniform unit-equation bounds over number fields suffice for Theorem A.1,
even for Fourier pairs with arbitrary complex coefficients. -/
theorem theoremA1_of_numberFieldBound (h : NumberFieldUnitEquationBound) : theoremA1Statement :=
  theoremA1_of_unitEquations (unitEquations_of_numberFieldBound h)

end
end MeyerGeneralProblem.LevOlevskii
