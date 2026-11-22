module

public import AppendixA.LaurentReduction
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Reduction of the torus coset theorem to one equation

Positive and inverse coordinates realize every Laurent equation as an ordinary
polynomial. The Hilbert basis theorem selects finitely many such equations
defining the same closure.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set MvPolynomial
open scoped Classical

private abbrev Torus (n : ℕ) := Fin n → Additive Circle
private abbrev Poly (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) ℂ

private def coords {n : ℕ} (z : Torus n) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (fun i => ((z i).toMul : ℂ)) (fun i => (((z i).toMul)⁻¹ : Circle))

private def polyMonomial {n : ℕ} (m : Fin n → ℤ) : Poly n :=
  ∏ i, match m i with
    | .ofNat k => X (.inl i) ^ k
    | .negSucc k => X (.inr i) ^ (k+1)

private theorem eval_polyMonomial {n : ℕ} (m : Fin n → ℤ) (z : Torus n) :
    eval (coords z) (polyMonomial m) = unitaryMonomial m z := by
  change _ = Circle.coeHom ((∑ j, m j • z j).toMul)
  rw [toMul_sum, map_prod]
  simp only [polyMonomial, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change _ = ((m i • z i).toMul : ℂ)
  cases m i with
  | ofNat k => simp [coords]
  | negSucc k => simp [coords, inv_pow]

private def encoding {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℂ) (m : ι → Fin n → ℤ) : Poly n :=
  ∑ i, C (c i) * polyMonomial (m i)

private theorem eval_encoding {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℂ) (m : ι → Fin n → ℤ)
    (z : Torus n) : eval (coords z) (encoding c m) = ∑ i, c i * unitaryMonomial (m i) z := by
  simp [encoding, eval_polyMonomial]

private def encodedRelations {n : ℕ} (D : Set (Torus n)) : Set (Poly n) :=
  {p | (∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (m : ι → Fin n → ℤ), p = encoding c m) ∧
    ∀ x ∈ D, eval (coords x) p = 0}

private theorem finite_equations {n : ℕ} (D : Set (Torus n)) :
    ∃ S : Finset (Poly n), ↑S ⊆ encodedRelations D ∧
      ∀ z, z ∈ unitaryLaurentClosure D ↔ ∀ p ∈ S, eval (coords z) p = 0 := by
  let E := encodedRelations D
  have hfg := IsNoetherian.noetherian (R := Poly n) (Ideal.span E)
  obtain ⟨S,hS,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset E).mp hfg
  refine ⟨S,hS,fun z => ⟨?_,?_⟩⟩
  · intro hz p hp
    obtain ⟨⟨ι,inst,c,m,rfl⟩,hzero⟩ := hS hp
    simp only [eval_encoding] at hzero ⊢
    exact hz c m hzero
  · intro h ι inst c m hzero
    have hle : Ideal.span E ≤ RingHom.ker (eval (coords z)) := by
      change Ideal.span E = Ideal.span (S : Set _) at hspan
      rw [hspan]
      exact Ideal.span_le.mpr fun p hp => h p hp
    rw [← eval_encoding]
    apply hle (Ideal.subset_span (s := E) _)
    exact ⟨⟨ι,inst,c,m,rfl⟩,by simpa only [eval_encoding] using hzero⟩

/-- A finite union of translates of subgroups of an additive group. -/
def IsFiniteCosetUnion {G : Type*} [AddCommGroup G] (S : Set G) : Prop :=
  ∃ C : Finset (G × AddSubgroup G), ∀ x, x ∈ S ↔ ∃ u ∈ C, x - u.1 ∈ u.2

theorem isFiniteCosetUnion_univ (G : Type*) [AddCommGroup G] : IsFiniteCosetUnion (univ : Set G) := by
  refine ⟨{(0,⊤)},?_⟩
  simp

private theorem recenter {G : Type*} [AddCommGroup G] {a c x : G} {H : AddSubgroup G}
    (hc : c-a ∈ H) : x-a ∈ H ↔ x-c ∈ H := by
  constructor
  · intro h
    simpa only [sub_sub_sub_cancel_right] using H.sub_mem h hc
  · intro h
    simpa only [sub_add_sub_cancel] using H.add_mem h hc

/-- A nonempty intersection of two cosets is a translate of the intersection
of the two subgroups. Taking all such intersections preserves finiteness. -/
theorem IsFiniteCosetUnion.inter {G : Type*} [AddCommGroup G] {S T : Set G}
    (hS : IsFiniteCosetUnion S) (hT : IsFiniteCosetUnion T) : IsFiniteCosetUnion (S ∩ T) := by
  obtain ⟨A,hA⟩ := hS
  obtain ⟨B,hB⟩ := hT
  let good (v : (G × AddSubgroup G) × (G × AddSubgroup G)) :=
    ∃ t : G, t - v.1.1 ∈ v.1.2 ∧ t - v.2.1 ∈ v.2.2
  let I := (A ×ˢ B).filter good
  have hex (v : I) := (Finset.mem_filter.mp v.property).2
  choose t ht₁ ht₂ using hex
  let entry (v : I) : G × AddSubgroup G := (t v, v.val.1.2 ⊓ v.val.2.2)
  refine ⟨Finset.univ.image entry,fun x => ⟨?_,?_⟩⟩
  · rintro ⟨hs,hr⟩
    obtain ⟨a,ha,hxa⟩ := (hA x).mp hs
    obtain ⟨b,hb,hxb⟩ := (hB x).mp hr
    let v : I := ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,x,hxa,hxb⟩⟩
    exact ⟨entry v,Finset.mem_image_of_mem _ (Finset.mem_univ v),
      (recenter (ht₁ v)).mp hxa,(recenter (ht₂ v)).mp hxb⟩
  · rintro ⟨_,hv,hx⟩
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp v.property).1
    exact ⟨(hA x).mpr ⟨_,ha,(recenter (ht₁ v)).mpr hx.1⟩,
      (hB x).mpr ⟨_,hb,(recenter (ht₂ v)).mpr hx.2⟩⟩

/-- Arithmetic input for one finite exponential sum on a finitely generated
subgroup of the unitary torus. -/
def UnitaryEquationCosetTheorem : Prop :=
  ∀ (n : ℕ) (Γ : AddSubgroup (Fin n → Additive Circle)), Γ.FG →
    ∀ {ι : Type} [Fintype ι] (c : ι → ℂ) (m : ι → Fin n → ℤ),
      IsFiniteCosetUnion {x : Γ | ∑ i, c i * unitaryMonomial (m i) x.val = 0}

/-- The arithmetic result for one equation implies Laurent's entire
finite coset cover of the common zero set inside the finitely generated group. -/
theorem unitaryLaurent_of_equation (h : UnitaryEquationCosetTheorem) : UnitaryLaurentCosetTheorem := by
  intro n Γ hΓ D hD
  obtain ⟨S,hS,hzero⟩ := finite_equations D
  have hfinite (F : Finset (Poly n)) (hF : F ⊆ S) :
      IsFiniteCosetUnion {x : Γ | ∀ p ∈ F, eval (coords x.val) p = 0} := by
    induction F using Finset.induction_on with
    | empty => simpa using isFiniteCosetUnion_univ Γ
    | insert p F hp ih =>
      have hpS := hF (Finset.mem_insert_self p F)
      obtain ⟨⟨ι,inst,c,m,rfl⟩,_⟩ := hS hpS
      have he := h n Γ hΓ c m
      have hf := ih (Finset.Subset.trans (Finset.subset_insert _ _) hF)
      simpa only [Finset.forall_mem_insert,eval_encoding,Set.ofPred_and] using he.inter hf
  obtain ⟨C,hC⟩ := hfinite S (Finset.Subset.refl _)
  let e := (Fintype.equivFin C).symm
  let s (j) : Γ := (e j).val.1
  let P (j) := (e j).val.2.map Γ.subtype
  refine ⟨_,s,P,?_,?_⟩
  · intro x hx
    let z : Γ := ⟨x,hD hx⟩
    obtain ⟨u,hu,hmem⟩ := (hC z).mp (fun p hp => (hS hp).2 x hx)
    let j := e.symm ⟨u,hu⟩
    have hu' : (e j).val = u := congrArg Subtype.val (e.apply_symm_apply _)
    refine ⟨j,z - s j,?_,rfl⟩
    change z - s j ∈ (e j).val.2
    simpa only [s,hu'] using hmem
  · intro j y hy
    obtain ⟨v,hv,rfl⟩ := hy
    change v ∈ (e j).val.2 at hv
    let z := s j + v
    apply (hzero z.val).mpr
    apply (hC z).mpr
    exact ⟨_,(e j).property,by simpa only [z,s,add_sub_cancel_left] using hv⟩

end
end MeyerGeneralProblem.LevOlevskii
