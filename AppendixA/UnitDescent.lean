module

public import AppendixA.CharacterSpecialization
public import AppendixA.UnitFiniteness
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Nondegenerate unit equations in complex characters

A coordinate with finite image can be fixed and deleted. When all coordinates
have infinite image, number-field specialization covers the solutions by
cosets of kernels of smaller integer rank. This gives induction on rank and
then on the number of coordinates.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Submodule Module
open scoped Classical

private def tuple {G ι : Type} [AddCommGroup G] (F : Finset ι)
    (χ : ι → G →+ Additive ℂˣ) (x : G) (i : F) := charValue (χ i.val) x

private def solutions {G ι : Type} [AddCommGroup G] (F : Finset ι)
    (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) : Set G :=
  {x | (∑ i ∈ F, c i * charValue (χ i) x) = 1 ∧
    ∀ J ⊆ F, J.Nonempty → ∑ i ∈ J, c i * charValue (χ i) x ≠ 0}

private theorem finite_or_infinite_order {G : Type} [AddCommGroup G] [AddGroup.FG G]
    (χ : G →+ Additive ℂˣ) : (range (charValue χ)).Finite ∨ ∃ w, ¬IsOfFinOrder (charValue χ w) := by
  by_cases h : ∃ w, ¬IsOfFinOrder (charValue χ w)
  · exact Or.inr h
  · push Not at h
    have : AddGroup.FG χ.range := AddGroup.fg_of_surjective χ.rangeRestrict_surjective
    have : Finite χ.range := AddCommGroup.finite_of_fg_isAddTorsion _ fun y => by
      obtain ⟨x,hx⟩ := y.property
      apply (χ.range.subtype_injective.isOfFinAddOrder_iff (f := χ.range.subtype)).mp
      change IsOfFinAddOrder y.val
      rw [← hx]
      exact (Units.isOfFinOrder_val.mp (h x) : IsOfFinOrder (χ x).toMul)
    exact Or.inl ((finite_range (fun y : χ.range => y.val.toMul.val)).subset (fun _ ⟨x,hx⟩ => ⟨χ.rangeRestrict x,hx⟩))

private theorem kernel_rank_lt {G K : Type} [AddCommGroup G] [AddGroup.FG G] [Field K]
    (ψ : G →+ Additive Kˣ) (w : G) (hw : ¬IsOfFinOrder (charValue ψ w)) :
    finrank ℤ ψ.ker < finrank ℤ G := by
  have : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let H := ψ.ker.toIntSubmodule
  have hpos : finrank ℤ (G ⧸ H) ≠ 0 := by
    intro hzero
    have ht := isAddTorsion_iff_isTorsion_int.mpr (Module.finrank_eq_zero_iff_isTorsion.mp hzero)
    obtain ⟨n,hn,hq⟩ := (ht (H.mkQ w)).exists_nsmul_eq_zero
    have hk : n • w ∈ H := (Submodule.Quotient.mk_eq_zero H).mp (by
      change H.mkQ (n • w) = 0
      rw [map_nsmul,hq])
    change ψ (n • w) = 0 at hk
    rw [map_nsmul] at hk
    apply hw
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg (fun z : Additive Kˣ => z.toMul.val) hk⟩
  have he := H.finrank_quotient_add_finrank
  change finrank ℤ H < finrank ℤ G
  omega

private theorem finite_with_fixed_coordinate {G ι : Type} [AddCommGroup G] (F : Finset ι)
    (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) {a : ι} (ha : a ∈ F)
    (hfin : (range (charValue (χ a))).Finite)
    (ih : ∀ b : ι → ℂ, (tuple (F.erase a) χ '' solutions (F.erase a) χ b).Finite) :
    (tuple F χ '' solutions F χ c).Finite := by
  let part (v : ℂ) := {x ∈ solutions F χ c | charValue (χ a) x = v}
  have hpart (v : ℂ) : (tuple F χ '' part v).Finite := by
    let d := 1 - c a * v
    let b (i : ι) := c i / d
    let restore (y : F.erase a → ℂ) (i : F) := if hi : i.val = a then v else y ⟨i.val,Finset.mem_erase.mpr ⟨hi,i.property⟩⟩
    by_cases hE : F.erase a = ∅
    · apply (finite_singleton (fun _ : F => v)).subset
      rintro _ ⟨x,hx,rfl⟩
      apply mem_singleton_iff.mpr
      funext i
      have hi : i.val = a := by
        by_contra hn
        have hy := Finset.mem_erase.mpr ⟨hn,i.property⟩
        rw [hE] at hy
        exact Finset.notMem_empty _ hy
      simpa only [tuple,hi] using hx.2
    apply ((ih b).image restore).subset
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨hs,hv⟩ := hx
    have hsum : (∑ i ∈ F.erase a, c i * charValue (χ i) x) = d := by
      have he := Finset.sum_erase_add (f := fun i => c i * charValue (χ i) x) F ha
      rw [hs.1,hv] at he
      exact eq_sub_of_add_eq he
    have hd : d ≠ 0 := hsum ▸ hs.2 _ (Finset.erase_subset ..) (Finset.nonempty_iff_ne_empty.mpr hE)
    have norm (J : Finset ι) : (∑ i ∈ J, b i * charValue (χ i) x) =
        (∑ i ∈ J, c i * charValue (χ i) x) / d := by
      simp only [Finset.sum_div,b]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨_,⟨x,⟨by rw [norm,hsum,div_self hd],fun J hJ hn => ?_⟩,rfl⟩,?_⟩
    · rw [norm]
      exact div_ne_zero (hs.2 _ (hJ.trans (Finset.erase_subset ..)) hn) hd
    · funext i
      by_cases hi : i.val = a
      · simp only [restore,dite_eq_left hi,tuple,hi,hv]
      · simp only [restore,dite_eq_right hi,tuple]
  apply (hfin.biUnion fun v _ => hpart v).subset
  rintro _ ⟨x,hx,rfl⟩
  exact mem_iUnion₂.mpr ⟨_,⟨x,rfl⟩,x,⟨hx,rfl⟩,rfl⟩

private theorem finite_on_level {G ι K : Type} [AddCommGroup G] [Field K] (F : Finset ι)
    (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) (ψ : G →+ Additive Kˣ) (v : Kˣ)
    (ih : ∀ b : ι → ℂ, (tuple F (fun i => (χ i).comp ψ.ker.subtype) ''
      solutions F (fun i => (χ i).comp ψ.ker.subtype) b).Finite) :
    (tuple F χ '' {x ∈ solutions F χ c | (ψ x).toMul = v}).Finite := by
  let X := {x ∈ solutions F χ c | (ψ x).toMul = v}
  change (tuple F χ '' X).Finite
  rcases X.eq_empty_or_nonempty with h | ⟨t,ht⟩
  · simp [h]
  let χ' (i) := (χ i).comp ψ.ker.subtype
  let b (i) := c i * charValue (χ i) t
  let shift (y : F → ℂ) (i : F) := charValue (χ i.val) t * y i
  apply ((ih b).image shift).subset
  rintro _ ⟨x,hx,rfl⟩
  have hk : x-t ∈ ψ.ker := by
    change ψ (x-t) = 0
    rw [map_sub,sub_eq_zero]
    exact Additive.toMul.injective (hx.2.trans ht.2.symm)
  let y : ψ.ker := ⟨x-t,hk⟩
  have he (i) : charValue (χ i) t * charValue (χ' i) y = charValue (χ i) x := by
    change charValue (χ i) t * charValue (χ i) (x-t) = _
    simp [charValue,mul_div_cancel₀]
  have hterm (i) : b i * charValue (χ' i) y = c i * charValue (χ i) x := by
    change (c i * _) * _ = _
    rw [mul_assoc,he]
  have hsol : y ∈ solutions F χ' b := ⟨by simpa only [hterm] using hx.1.1,
    fun J hJ hn => by simpa only [hterm] using hx.1.2 J hJ hn⟩
  exact ⟨_,⟨y,hsol,rfl⟩,funext (fun i => he i.val)⟩

private theorem finite_solution_tuples {G ι : Type} [AddCommGroup G] [AddGroup.FG G]
    (F : Finset ι) (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ) :
    (tuple F χ '' solutions F χ c).Finite := by
  suffices H : ∀ r : ℕ, ∀ (G : Type) [AddCommGroup G] [AddGroup.FG G], finrank ℤ G = r →
      ∀ F : Finset ι, ∀ (χ : ι → G →+ Additive ℂˣ) (c : ι → ℂ), (tuple F χ '' solutions F χ c).Finite from
    H _ G rfl F χ c
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
    intro G _ _ hr F
    induction F using Finset.strongInductionOn with
    | _ F ih =>
      intro χ c
      rcases (solutions F χ c).eq_empty_or_nonempty with hempty | ⟨x₀,h₀⟩
      · simp [hempty]
      have hc (i : F) : c i.val ≠ 0 := by
        intro hci
        exact h₀.2 {i.val} (Finset.singleton_subset_iff.mpr i.property) (Finset.singleton_nonempty _)
          (by simp [hci])
      by_cases hfinite : ∃ i ∈ F, (range (charValue (χ i))).Finite
      · obtain ⟨a,ha,hf⟩ := hfinite
        exact finite_with_fixed_coordinate F χ c ha hf (ih _ (Finset.erase_ssubset ha) χ)
      have hex (i : F) := (finite_or_infinite_order (χ i.val)).resolve_left
        (fun h => hfinite ⟨i.val,i.property,h⟩)
      choose w hw using hex
      obtain ⟨K,_,ψ,L,hψ,hcover⟩ := finite_levels_of_character_equation (fun i : F => χ i.val)
        (fun i => c i.val) hc w hw
      let part (v : F × Kˣ) := {x ∈ solutions F χ c | (ψ v.1 x).toMul = v.2}
      have hp (v : F × Kˣ) : (tuple F χ '' part v).Finite := by
        have : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr inferInstance
        let H := (ψ v.1).ker
        have : AddGroup.FG H := Module.Finite.iff_addGroup_fg.mp (inferInstanceAs (Module.Finite ℤ H.toIntSubmodule))
        apply finite_on_level
        exact ihr _ ((kernel_rank_lt _ _ (hψ v.1)).trans_eq hr) H rfl F _
      apply (L.finite_toSet.biUnion fun v _ => hp v).subset
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨v,hv,he⟩ := hcover x (by
        have he := hx.1
        rw [← Finset.sum_attach F] at he
        exact he)
      exact mem_iUnion₂.mpr ⟨v,hv,x,⟨hx,he⟩,rfl⟩

/-- Finiteness of nondegenerate unit-equation solutions on a finitely
generated subgroup of the unitary torus, with arbitrary complex coefficients. -/
theorem unitaryUnitEquationFiniteness : UnitaryUnitEquationFiniteness := by
  intro ι _ Γ hΓ c _
  have : AddGroup.FG Γ := hΓ
  let χ (i : ι) : Γ →+ Additive ℂˣ := Circle.toUnits.toAdditive.comp ((Pi.evalAddMonoidHom _ i).comp Γ.subtype)
  let F : Finset ι := Finset.univ
  let val (z : ι → Additive Circle) (i : F) := phaseValue (z i.val)
  have hinj : Function.Injective val := by
    intro z y he
    funext i
    exact Additive.toMul.injective (Circle.coe_injective (congrFun he ⟨i,Finset.mem_univ _⟩))
  apply Set.Finite.of_finite_image (f := val) _ hinj.injOn
  apply (finite_solution_tuples F χ c).subset
  rintro _ ⟨z,⟨hz,h1,h2⟩,rfl⟩
  exact ⟨⟨z,hz⟩,⟨h1,fun J _ => h2 J⟩,rfl⟩

end
end MeyerGeneralProblem.LevOlevskii
