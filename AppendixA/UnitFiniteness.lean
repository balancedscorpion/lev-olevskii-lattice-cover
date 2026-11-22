module

public import AppendixA.UnitEquations

/-!
# The normalized unit equation

We use the qualitative unitary case of Evertse–Schlickewei–Schmidt,
*Linear equations in variables which lie in a multiplicative group*,
Theorem 1.1 (Annals of Mathematics 155, 2002, 807–836).
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set
open scoped Classical

/-- In a finitely generated subgroup of a unitary torus, a linear equation
with nonzero complex coefficients has finitely many nondegenerate solutions.
Here nondegenerate means that every nonempty subsum is nonzero. -/
def UnitaryUnitEquationFiniteness : Prop :=
  ∀ {ι : Type} [Fintype ι] (Γ : AddSubgroup (ι → Additive Circle)), Γ.FG →
    ∀ c : ι → ℂ, (∀ i, c i ≠ 0) →
      {z : ι → Additive Circle | z ∈ Γ ∧ (∑ i, c i * phaseValue (z i)) = 1 ∧
        ∀ J : Finset ι, J.Nonempty → ∑ i ∈ J, c i * phaseValue (z i) ≠ 0}.Finite

/-- Divide a minimal vanishing sum by its term at the reference coordinate.
The resulting equation has right-hand side one, and the deleted coordinate
can be recovered because its ratio is one. -/
theorem nondegenerate_of_unitEquations (h : UnitaryUnitEquationFiniteness) :
    NondegenerateUnitRatioFiniteness := by
  intro G ι _ _ χ c F a ha
  let X := minimalZeros χ c F
  rcases X.eq_empty_or_nonempty with hX | ⟨x₀,h₀⟩
  · rw [show minimalZeros χ c F = ∅ from hX, image_empty]
    exact finite_empty
  by_cases hsingle : F = {a}
  · apply (finite_singleton 0).subset
    rintro _ ⟨x,_,rfl⟩
    apply mem_singleton_iff.mpr
    funext i
    have hi : i.val = a := Finset.mem_singleton.mp (hsingle ▸ i.property)
    change χ i.val x - χ a x = 0
    simp [hi]
  have hc (i) (hi : i ∈ F) : c i ≠ 0 := by
    have hs : {i} ⊂ F := lt_of_le_of_ne (Finset.singleton_subset_iff.mpr hi) (by
      intro he
      have hia : a = i := Finset.mem_singleton.mp (he ▸ ha)
      exact hsingle (hia ▸ he.symm))
    intro hz
    exact h₀.2 _ hs (Finset.singleton_nonempty _) (by simp [subsum,hz])
  let E := F.erase a
  let f : G →+ (E → Additive Circle) := AddMonoidHom.pi fun i => χ i.val - χ a
  let Γ := f.range
  have hΓ : Γ.FG := AddGroup.fg_of_surjective f.rangeRestrict_surjective
  let b (i : E) : ℂ := -c i.val / c a
  have hb (i : E) : b i ≠ 0 := div_ne_zero (neg_ne_zero.mpr (hc _ (Finset.mem_of_mem_erase i.property))) (hc a ha)
  have hsum (x : G) (J : Finset E) :
      (∑ i ∈ J, b i * phaseValue (f x i)) =
        -subsum χ c (J.map (Function.Embedding.subtype (· ∈ E))) x / (c a * phaseValue (χ a x)) := by
    simp only [subsum,Finset.sum_map,Function.Embedding.subtype_apply,← Finset.sum_neg_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change (-c i.val / c a) * (phaseValue (χ i.val x) / phaseValue (χ a x)) = _
    ring
  have hmap : (Finset.univ : Finset E).map (Function.Embedding.subtype (· ∈ E)) = E := by ext; simp
  have hsol (x : G) (hx : x ∈ X) :
      f x ∈ {z | z ∈ Γ ∧ (∑ i, b i * phaseValue (z i)) = 1 ∧
        ∀ J : Finset E, J.Nonempty → ∑ i ∈ J, b i * phaseValue (z i) ≠ 0} := by
    have hden : c a * phaseValue (χ a x) ≠ 0 := mul_ne_zero (hc a ha) (Circle.coe_ne_zero _)
    refine ⟨⟨x,rfl⟩,?_,?_⟩
    · rw [hsum,hmap,div_eq_one_iff_eq hden]
      have he := Finset.sum_erase_add (f := fun i => c i * phaseValue (χ i x)) F ha
      change subsum χ c E x + _ = subsum χ c F x at he
      rw [hx.1] at he
      linear_combination -he
    · intro J hn
      rw [hsum]
      apply div_ne_zero _ hden
      apply neg_ne_zero.mpr
      apply hx.2
      · apply lt_of_le_of_lt _ (Finset.erase_ssubset ha)
        rintro _ hi
        obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hi
        exact i.property
      · exact hn.map
  let restore (z : E → Additive Circle) (i : F) := if hi : i.val ∈ E then z ⟨i.val,hi⟩ else 0
  apply ((h Γ hΓ b hb).image restore).subset
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨f x,hsol x hx,?_⟩
  funext i
  by_cases he : i.val ∈ E
  · simp [restore,he,f,ratios]
  · have hia : i.val = a := by
      by_contra hn
      exact he (Finset.mem_erase.mpr ⟨hn,i.property⟩)
    simp only [restore,dite_eq_right he]
    change 0 = χ i.val x - χ a x
    simp [hia]

/-- Qualitative unit-equation finiteness alone suffices for Theorem A.1. -/
theorem theoremA1_of_unitEquations (h : UnitaryUnitEquationFiniteness) : theoremA1Statement :=
  theoremA1_of_nondegenerate (nondegenerate_of_unitEquations h)

end
end MeyerGeneralProblem.LevOlevskii
