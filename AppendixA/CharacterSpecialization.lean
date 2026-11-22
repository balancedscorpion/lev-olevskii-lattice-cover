module

public import AppendixA.InfiniteOrderSpecialization
public import DiophantineApproximation.UnitEquationSeveral
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Number-field detection of solutions of a complex character equation

The number-field result used here is Bombieri–Gubler, Corollary 7.4.3,
formalized in Subspace-Theorems. It allows vanishing subsums. This matters
because specialization can introduce new vanishing subsums.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set
open scoped Classical

/-- The complex or number-field value of a unitary or multiplicative character,
using additive notation on its domain and on the type tag of its codomain. -/
def charValue {G K : Type} [AddCommGroup G] [Field K] (χ : G →+ Additive Kˣ) (x : G) : K :=
  (χ x).toMul.val

private theorem specialize_characters {G ι : Type} [AddCommGroup G] [AddGroup.FG G] [Fintype ι]
    (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) (w : ι → G)
    (hw : ∀ i, ¬IsOfFinOrder (charValue (χ i) (w i))) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (b : ι → Kˣ) (ψ : ι → G →+ Additive Kˣ),
      (∀ i, ¬IsOfFinOrder (charValue (ψ i) (w i))) ∧
        ∀ x, (∑ i, c i * charValue (χ i) x) = 1 → (∑ i, (b i : K) * charValue (ψ i) x) = 1 := by
  obtain ⟨S,hgen,hs⟩ := AddMonoid.fg_iff.mp (show AddMonoid.FG G from inferInstanceAs (AddGroup.FG G))
  let := hs.fintype
  let v (p : ι × S) := charValue (χ p.1) p.2.val
  let T := Finset.univ.image c ∪ Finset.univ.image v
  let A := Algebra.adjoin ℚ (T : Set ℂ)
  have : Algebra.FiniteType ℚ A := A.fg_iff_finiteType.mp (Subalgebra.fg_adjoin_finset T)
  have hval (i : ι) (x : G) : charValue (χ i) x ∈ A := by
    have hx : x ∈ AddSubmonoid.closure S := hgen ▸ AddSubmonoid.mem_top x
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx => exact Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_image_of_mem v (Finset.mem_univ (i,⟨x,hx⟩))))
    | zero => simp [charValue]
    | add x y _ _ h₁ h₂ => simpa [charValue] using A.mul_mem h₁ h₂
  let u (i : ι) (x : G) : Aˣ :=
    ⟨⟨charValue (χ i) x,hval i x⟩,⟨charValue (χ i) (-x),hval i (-x)⟩,
     Subtype.ext (by simp [charValue]),Subtype.ext (by simp [charValue])⟩
  let ca (i : ι) : A := ⟨c i,Algebra.subset_adjoin (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))⟩
  let W := Finset.univ.image (fun i => (u i (w i)).val)
  have hW (z) (hz : z ∈ W) : ¬IsOfFinOrder z := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    intro h
    obtain ⟨n,hn,he⟩ := h.exists_pow_eq_one
    exact hw i (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩)
  obtain ⟨K,_,_,f,hprod,hkeep⟩ := exists_numberField_preserving_infiniteOrder A W hW (∏ i, ca i)
    (Finset.prod_ne_zero_iff.mpr fun i _ => fun he => hc i (congrArg Subtype.val he))
  rw [map_prod] at hprod
  let b (i : ι) := Units.mk0 (f (ca i)) (Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i))
  let ψ (i : ι) : G →+ Additive Kˣ :=
    { toFun := fun x => Additive.ofMul (Units.map f.toMonoidHom (u i x))
      map_zero' := by
        change Units.map _ (u i 0) = 1
        rw [show u i 0 = 1 from Units.ext (Subtype.ext (by simp [u,charValue])),map_one]
      map_add' := fun x y => by
        change Units.map _ (u i (x+y)) = _ * _
        rw [show u i (x+y) = u i x * u i y from Units.ext (Subtype.ext (by simp [u,charValue])),map_mul]
        rfl }
  refine ⟨K,inferInstance,inferInstance,b,ψ,fun i => hkeep _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)),?_⟩
  intro x hx
  have he : (∑ i, ca i * (u i x).val) = 1 := Subtype.ext (by simpa [ca,u] using hx)
  change (∑ i, f (ca i) * f (u i x).val) = 1
  simpa only [map_sum,map_mul,map_one] using congrArg f he

/-- If every character has an infinite-order value, the solutions lie on
finitely many level sets of specialized characters, each of infinite image. -/
theorem finite_levels_of_character_equation {G ι : Type} [AddCommGroup G] [AddGroup.FG G] [Fintype ι]
    (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (w : ι → G) (hw : ∀ i, ¬IsOfFinOrder (charValue (χ i) (w i))) :
    ∃ (K : Type) (_ : Field K) (ψ : ι → G →+ Additive Kˣ) (levels : Finset (ι × Kˣ)),
      (∀ i, ¬IsOfFinOrder (charValue (ψ i) (w i))) ∧
      ∀ x, (∑ i, c i * charValue (χ i) x) = 1 → ∃ v ∈ levels, (ψ v.1 x).toMul = v.2 := by
  obtain ⟨K,_,_,b,ψ,hψ,he⟩ := specialize_characters χ c hc w hw
  have hr (i) : (ψ i).range.FG := AddGroup.fg_of_surjective (ψ i).rangeRestrict_surjective
  let Γ := ⨆ i, (ψ i).range.toSubgroup
  have hΓ : Γ.FG := Subgroup.FG.iSup _ fun i => (AddSubgroup.fg_iff_mul_fg _).mp (hr i)
  obtain ⟨P,hP⟩ := NumberField.exists_finset_le_unit hΓ
  obtain ⟨L,hL,hcover⟩ := NumberField.exists_finite_forall_exists_apply_eq P (fun i => (b i : K))
    Finset.univ (fun J _ => NumberField.finite_unitSolutions P _ (fun i : J => (b i.val).ne_zero))
  refine ⟨K,inferInstance,ψ,hL.toFinset,hψ,fun x hx => ?_⟩
  obtain ⟨v,hv,_,hEq⟩ := hcover (fun i => (ψ i x).toMul)
    (fun i => hP (le_iSup (fun j => (ψ j).range.toSubgroup) i (show ψ i x ∈ (ψ i).range from ⟨x,rfl⟩))) (he x hx)
  exact ⟨v,hL.mem_toFinset.mpr hv,hEq⟩

end
end MeyerGeneralProblem.LevOlevskii
