module

public import AppendixA.QuotientWindows
public import AppendixA.LatticeOrbits

/-!
# Characters on a coset in the algebraic closure of the support
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Matrix FourierTransform
open scoped Matrix FourierTransform Classical RealInnerProductSpace

/-- The additive frequencies whose characters are identically one on a
subgroup of physical translations. -/
def integralDual {d : ℕ} (P : Submodule ℤ (Space d)) : Submodule ℤ (Space d) where
  carrier := {u | ∀ y ∈ P, ∃ z : ℤ, inner ℝ y u = (z : ℝ)}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := by
    intro u v hu hv y hy
    obtain ⟨a,ha⟩ := hu y hy
    obtain ⟨b,hb⟩ := hv y hy
    exact ⟨a+b,by simp [inner_add_right,ha,hb]⟩
  smul_mem' := by
    intro z u hu y hy
    obtain ⟨a,ha⟩ := hu y hy
    exact ⟨z*a,by simp [← Int.cast_smul_eq_zsmul ℝ,real_inner_smul_right,ha]⟩

/-- Every trigonometric polynomial with frequencies in the specified group
which vanishes on the sites also vanishes on the given translated subgroup. -/
def CosetSatisfiesRelations {d : ℕ} (A : Set (Space d)) (G : Submodule ℤ (Space d))
    (t : Space d) (P : Submodule ℤ (Space d)) : Prop :=
  ∀ {ι : Type} [Fintype ι] (c : ι → ℂ) (u : ι → Space d), (∀ i, u i ∈ G) →
    (∀ x ∈ A, ∑ i, c i * (frequencyPhase (u i) x : ℂ) = 0) →
    ∀ y ∈ P, ∑ i, c i * (frequencyPhase (u i) (t+y) : ℂ) = 0

private def subgroupCharacter {d : ℕ} (P : Submodule ℤ (Space d)) (u : Space d) :
    Multiplicative P →* ℂ where
  toFun y := frequencyPhase u y.toAdd.val
  map_one' := by change (frequencyPhase u 0 : ℂ) = 1; simp
  map_mul' y z := by
    change (frequencyPhase u (y.toAdd.val + z.toAdd.val) : ℂ) = _
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]

/-- Distinct residues modulo the integral dual give independent restricted
characters whenever the translated subgroup satisfies the vanishing relations. -/
theorem independent_characters_of_coset {d : ℕ} {A : Set (Space d)}
    {G P : Submodule ℤ (Space d)} {t : Space d} (h : CosetSatisfiesRelations A G t P)
    {ι : Type} [Fintype ι] (u : ι → Space d) (hu : ∀ i, u i ∈ G)
    (hinj : Function.Injective (fun i => (integralDual P).mkQ (u i))) :
    LinearIndependent ℂ (fun i (x : A) => (frequencyPhase (u i) x.val : ℂ)) := by
  have hchar : Function.Injective (fun i => subgroupCharacter P (u i)) := by
    intro i j he
    apply hinj
    apply (Submodule.Quotient.eq _).mpr
    intro y hy
    have hh := DFunLike.congr_fun he (Multiplicative.ofAdd (⟨y,hy⟩ : P))
    change (Real.fourierChar (inner ℝ y (u i)) : ℂ) = (Real.fourierChar (inner ℝ y (u j)) : ℂ) at hh
    apply fourierChar_eq_one_iff_int.mp
    rw [inner_sub_right, AddChar.map_sub_eq_div]
    exact div_eq_one.mpr (show Real.fourierChar _ = Real.fourierChar _ from Subtype.ext hh)
  have hli := (linearIndependent_monoidHom (Multiplicative P) ℂ).comp _ hchar
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have ho := h c u hu (fun x hx => by
    simpa using congrFun hc (⟨x,hx⟩ : A))
  have hz : ∑ j, (c j * (frequencyPhase (u j) t : ℂ)) •
      ((fun f : Multiplicative P →* ℂ => (f : Multiplicative P → ℂ)) ∘
        (fun j => subgroupCharacter P (u j))) j = 0 := by
    funext p
    simpa [Function.comp_def,subgroupCharacter,Finset.sum_apply,AddChar.map_add_eq_mul,mul_assoc]
      using ho p.toAdd.val p.toAdd.property
  exact (mul_eq_zero.mp ((Fintype.linearIndependent_iff.mp hli) _ hz i)).resolve_right (Circle.coe_ne_zero _)

private theorem lattice_containing_integral_dual {d : ℕ} (P : Submodule ℤ (Space d))
    (hP : Submodule.span ℝ (P : Set (Space d)) = ⊤) :
    ∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧ integralDual P ≤ matrixLattice T := by
  obtain ⟨u,hu,_,hind⟩ := show ∃ u : Fin d → Space d, (∀ i, u i ∈ P) ∧
      Submodule.span ℝ (range u) = ⊤ ∧ LinearIndependent ℝ u by
    have h := Submodule.exists_fun_fin_finrank_span_eq ℝ (P : Set (Space d))
    rw [hP,finrank_top,finrank_euclideanSpace_fin] at h
    exact h
  let M : Matrix (Fin d) (Fin d) ℝ := fun i j => u i j
  have hrows : LinearIndependent ℝ M.row :=
    hind.map' (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap (by simp)
  have hunit : IsUnit M.det := M.isUnit_iff_isUnit_det.mp (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)
  refine ⟨M⁻¹,(M.isUnit_nonsing_inv_det hunit).ne_zero,?_⟩
  intro v hv
  choose z hz using fun i => hv (u i) (hu i)
  have heq : M *ᵥ WithLp.ofLp v = fun i => (z i : ℝ) := by
    funext i
    simpa [M, Matrix.mulVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,mul_comm] using hz i
  have hf : v ∈ range (latticeSite 0 M⁻¹) := by
    refine ⟨z,?_⟩
    simp [latticeSite,← heq,Matrix.mulVec_mulVec,M.nonsing_inv_mul hunit]
  simpa using (mem_latticeCoset_iff ..).mp hf

theorem integralDual_uniformlyDiscrete_of_span {d : ℕ} (P : Submodule ℤ (Space d))
    (hP : Submodule.span ℝ (P : Set (Space d)) = ⊤) :
    UniformlyDiscrete (integralDual P : Set (Space d)) := by
  obtain ⟨T,hT,hle⟩ := lattice_containing_integral_dual P hP
  obtain ⟨η,hη,hs⟩ := latticeCoset_uniformlyDiscrete 0 T hT
  exact ⟨η,hη,hs.mono fun x hx => (mem_latticeCoset_iff ..).mpr (by simpa using hle hx)⟩

/-- When the integral dual spans, the physical subgroup lies in a full-rank
lattice. -/
theorem lattice_of_integralDual_span {d : ℕ} (P : Submodule ℤ (Space d))
    (hs : Submodule.span ℝ (integralDual P : Set (Space d)) = ⊤) :
    ∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧ P ≤ matrixLattice T := by
  obtain ⟨T,hT,h⟩ := lattice_containing_integral_dual _ hs
  refine ⟨T,hT,le_trans ?_ h⟩
  intro x hx y hy
  simpa only [real_inner_comm y x] using hy x hx

end
end MeyerGeneralProblem.LevOlevskii
