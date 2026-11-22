module

public import AppendixA.LaurentEquations

/-!
# Nondegenerate unit equations and cosets

A minimal vanishing subsum is determined up to scaling by the ratios of its
characters. Finitely many such ratios yield a finite union of cosets. General
vanishing sums split into pairs of shorter vanishing subsums.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set
open scoped Classical

def phaseValue (u : Additive Circle) : ℂ := u.toMul

def subsum {G ι : Type} [AddCommGroup G] (χ : ι → G →+ Additive Circle) (c : ι → ℂ)
    (F : Finset ι) (x : G) : ℂ := ∑ i ∈ F, c i * phaseValue (χ i x)

/-- Points at which the indicated sum is zero and every nonempty proper
subsum is nonzero. -/
def minimalZeros {G ι : Type} [AddCommGroup G] (χ : ι → G →+ Additive Circle) (c : ι → ℂ)
    (F : Finset ι) : Set G :=
  {x | subsum χ c F x = 0 ∧ ∀ J : Finset ι, J ⊂ F → J.Nonempty → subsum χ c J x ≠ 0}

def ratios {G ι : Type} [AddCommGroup G] (χ : ι → G →+ Additive Circle)
    (F : Finset ι) (a : ι) : G →+ (F → Additive Circle) :=
  AddMonoidHom.pi fun i => χ i.val - χ a

/-- Projective form of nondegenerate unit-equation finiteness for characters
of a finitely generated group. Values are divided by one chosen term's
character, leaving finitely many possible tuples on a minimal vanishing sum. -/
def NondegenerateUnitRatioFiniteness : Prop :=
  ∀ {G ι : Type} [AddCommGroup G] [AddGroup.FG G] (χ : ι → G →+ Additive Circle)
    (c : ι → ℂ) (F : Finset ι) (a : ι), a ∈ F →
      (ratios χ F a '' minimalZeros χ c F).Finite

theorem IsFiniteCosetUnion.union {G : Type*} [AddCommGroup G] {S T : Set G}
    (hS : IsFiniteCosetUnion S) (hT : IsFiniteCosetUnion T) : IsFiniteCosetUnion (S ∪ T) := by
  obtain ⟨A,hA⟩ := hS
  obtain ⟨B,hB⟩ := hT
  refine ⟨A ∪ B,fun x => ?_⟩
  simp only [mem_union,hA,hB,Finset.mem_union]
  grind

private theorem finite_unions {G ι : Type*} [AddCommGroup G] (F : Finset ι) (S : ι → Set G)
    (h : ∀ i ∈ F, IsFiniteCosetUnion (S i)) : IsFiniteCosetUnion (⋃ i ∈ F, S i) := by
  induction F using Finset.induction_on with
  | empty => exact ⟨∅,by simp⟩
  | insert a F _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h _ (Finset.mem_insert_self ..)).union (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem cosets_of_finite_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (S : Set G) (hf : (f '' S).Finite)
    (hs : ∀ x ∈ S, ∀ y, f x = f y → y ∈ S) : IsFiniteCosetUnion S := by
  let I := hf.toFinset
  have hex (v : I) : ∃ x ∈ S, f x = v.val := hf.mem_toFinset.mp v.property
  choose t htS ht using hex
  refine ⟨Finset.univ.image (fun v : I => (t v,f.ker)),fun x => ⟨?_,?_⟩⟩
  · intro hx
    let v : I := ⟨f x,hf.mem_toFinset.mpr ⟨x,hx,rfl⟩⟩
    refine ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ v),?_⟩
    change f (x - t v) = 0
    rw [map_sub,ht,sub_self]
  · rintro ⟨_,hu,hx⟩
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hu
    apply hs (t v) (htS v)
    exact (sub_eq_zero.mp ((map_sub f x (t v)) ▸ (show f (x - t v) = 0 from hx))).symm

private theorem minimal_cosets (h : NondegenerateUnitRatioFiniteness) {G ι : Type} [AddCommGroup G]
    [AddGroup.FG G] (χ : ι → G →+ Additive Circle) (c : ι → ℂ) (F : Finset ι)
    (a : ι) (ha : a ∈ F) : IsFiniteCosetUnion (minimalZeros χ c F) := by
  apply cosets_of_finite_image _ _ (h χ c F a ha)
  intro x hx y hxy
  have hscale (J : Finset ι) (hJ : J ⊆ F) :
      subsum χ c J x / phaseValue (χ a x) = subsum χ c J y / phaseValue (χ a y) := by
    simp only [subsum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hv := congrArg phaseValue (congrFun hxy ⟨i,hJ hi⟩)
    change phaseValue (χ i x) / phaseValue (χ a x) = phaseValue (χ i y) / phaseValue (χ a y) at hv
    change c i * phaseValue (χ i x) / _ = _
    simpa only [mul_div_assoc] using congrArg (c i * ·) hv
  have hz (J : Finset ι) (hJ : J ⊆ F) : subsum χ c J x = 0 ↔ subsum χ c J y = 0 := by
    have he := congrArg (· = (0 : ℂ)) (hscale J hJ)
    simpa [phaseValue] using Iff.of_eq he
  exact ⟨(hz F (Finset.Subset.refl _)).mp hx.1,fun J hJ hn =>
    fun hzero => hx.2 J hJ hn ((hz J hJ.le).mpr hzero)⟩

private theorem all_zero_cosets (h : NondegenerateUnitRatioFiniteness) {G ι : Type} [AddCommGroup G]
    [AddGroup.FG G] (χ : ι → G →+ Additive Circle) (c : ι → ℂ) (F : Finset ι) :
    IsFiniteCosetUnion {x | subsum χ c F x = 0} := by
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    rcases F.eq_empty_or_nonempty with rfl | ⟨a,ha⟩
    · simpa [subsum] using isFiniteCosetUnion_univ G
    let splits := F.powerset.filter fun J => J ⊂ F ∧ J.Nonempty
    let Z (J : Finset ι) := {x | subsum χ c J x = 0}
    have hsplit (J) (hj : J ∈ splits) := (Finset.mem_filter.mp hj).2
    have hd (J) (hj : J ∈ splits) : F \ J ⊂ F :=
      Finset.sdiff_ssubset (hsplit J hj).1.le (hsplit J hj).2
    have hS := finite_unions splits (fun J => Z J ∩ Z (F \ J)) fun J hj =>
      (ih _ (hsplit J hj).1).inter (ih _ (hd J hj))
    have hadd (J) (hJ : J ⊆ F) (x : G) :
        subsum χ c (F \ J) x + subsum χ c J x = subsum χ c F x :=
      Finset.sum_sdiff hJ
    have he : Z F = minimalZeros χ c F ∪ ⋃ J ∈ splits, Z J ∩ Z (F \ J) := by
      ext x
      constructor
      · intro hx
        by_cases hmin : x ∈ minimalZeros χ c F
        · exact Or.inl hmin
        · have hdeg : ∃ J, J ⊂ F ∧ J.Nonempty ∧ subsum χ c J x = 0 := by
            simpa [minimalZeros,show subsum χ c F x = 0 from hx] using hmin
          obtain ⟨J,hJ,hn,hz⟩ := hdeg
          have hj : J ∈ splits := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hJ.le,hJ,hn⟩
          have hx' : subsum χ c F x = 0 := hx
          refine Or.inr (mem_iUnion₂.mpr ⟨J,hj,hz,?_⟩)
          change subsum χ c (F \ J) x = 0
          simpa only [hz,add_zero,hx'] using hadd J hJ.le x
      · rintro (hx | hx)
        · exact hx.1
        · obtain ⟨J,hj,h₁,h₂⟩ := mem_iUnion₂.mp hx
          change subsum χ c F x = 0
          rw [← hadd J (hsplit J hj).1.le,h₁,h₂,add_zero]
    rw [show {x | subsum χ c F x = 0} = Z F from rfl,he]
    exact (minimal_cosets h χ c F a ha).union hS

/-- Nondegenerate unit-equation finiteness suffices for every Laurent equation. -/
theorem unitaryEquation_of_nondegenerate (h : NondegenerateUnitRatioFiniteness) : UnitaryEquationCosetTheorem := by
  intro n Γ hΓ ι inst c m
  have : AddGroup.FG Γ := hΓ
  let χ (i : ι) : Γ →+ Additive Circle := ∑ j, m i j • ((Pi.evalAddMonoidHom _ j).comp Γ.subtype)
  convert! all_zero_cosets h χ c Finset.univ using 1
  ext x
  simp [subsum,χ,phaseValue,unitaryMonomial]

/-- The full Appendix A statement follows from finiteness of projective
ratios on nondegenerate unit equations. -/
theorem theoremA1_of_nondegenerate (h : NondegenerateUnitRatioFiniteness) : theoremA1Statement :=
  theoremA1_of_unitaryLaurent (unitaryLaurent_of_equation (unitaryEquation_of_nondegenerate h))

end
end MeyerGeneralProblem.LevOlevskii
