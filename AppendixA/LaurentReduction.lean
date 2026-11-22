module

public import AppendixA.CosetRank
public import AppendixA.FilteredRecurrence
public import AppendixA.FiniteDualClasses
public import AppendixA.Zero

/-!
# Reduction of Theorem A.1 to Laurent's torus theorem

The unitary torus is written additively, so an integer linear combination of
coordinates denotes a Laurent monomial. A point is in the Laurent closure
when it satisfies every finite Laurent polynomial vanishing on the given set.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Matrix FourierTransform Submodule
open scoped Matrix Classical FourierTransform

/-- The value of an integer Laurent monomial on the unitary torus. -/
def unitaryMonomial {n : ℕ} (m : Fin n → ℤ) (z : Fin n → Additive Circle) : ℂ :=
  ((∑ j, m j • z j).toMul : Circle)

/-- The common zeros on the unitary torus of all complex Laurent polynomials
that vanish on the specified subset. -/
def unitaryLaurentClosure {n : ℕ} (D : Set (Fin n → Additive Circle)) : Set (Fin n → Additive Circle) :=
  {z | ∀ {ι : Type} [Fintype ι] (c : ι → ℂ) (m : ι → Fin n → ℤ),
    (∀ x ∈ D, ∑ i, c i * unitaryMonomial (m i) x = 0) →
      ∑ i, c i * unitaryMonomial (m i) z = 0}

/-- The unitary case of Laurent's torus Mordell–Lang theorem, expressed
as a finite coset cover between a subset of a finitely generated group and
its Laurent closure. -/
def UnitaryLaurentCosetTheorem : Prop :=
  ∀ (n : ℕ) (Γ : AddSubgroup (Fin n → Additive Circle)), Γ.FG →
    ∀ D : Set (Fin n → Additive Circle), D ⊆ Γ →
      ∃ (k : ℕ) (s : Fin k → Γ) (P : Fin k → AddSubgroup (Fin n → Additive Circle)),
        (∀ z ∈ D, ∃ j, z - (s j).val ∈ P j) ∧
        ∀ j y, y ∈ P j → (s j).val + y ∈ unitaryLaurentClosure D

private def spectralCoordinates {d n : ℕ} (u : Fin n → Space d) :
    Space d →+ (Fin n → Additive Circle) :=
  AddMonoidHom.pi fun i => (frequencyPhase (u i)).toAddMonoidHom

private theorem monomial_on_coordinates {d n : ℕ} (u : Fin n → Space d)
    (m : Fin n → ℤ) (x : Space d) :
    unitaryMonomial m (spectralCoordinates u x) =
      (frequencyPhase (∑ i, m i • u i) x : ℂ) := by
  have symm (y w : Space d) : frequencyPhase y w = frequencyPhase w y := by
    change Real.fourierChar (inner ℝ w y) = Real.fourierChar (inner ℝ y w)
    rw [real_inner_comm]
  rw [symm _ x]
  let f := (frequencyPhase x).toAddMonoidHom
  have h (i) : spectralCoordinates u x i = f (u i) := congrArg Additive.ofMul (symm _ _)
  simp only [unitaryMonomial,h,← map_zsmul,← map_sum]
  rfl

private theorem physical_cosets_of_laurent (hL : UnitaryLaurentCosetTheorem)
    {d n : ℕ} (A : Set (Space d)) (hfg : (AddSubgroup.closure A).FG) (u : Fin n → Space d) :
    ∃ (k : ℕ) (t : Fin k → Space d) (P : Fin k → Submodule ℤ (Space d)),
      (∀ x ∈ A, ∃ j, x-t j ∈ P j) ∧
      ∀ j, CosetSatisfiesRelations A (span ℤ (range u)) (t j) (P j) := by
  let f := spectralCoordinates u
  let Γ := (AddSubgroup.closure A).map f
  have hΓ : Γ.FG := by
    apply (AddSubgroup.fg_iff_addSubmonoid_fg _).mpr
    exact ((AddSubgroup.fg_iff_addSubmonoid_fg _).mp hfg).map f
  obtain ⟨k,s,Q,hcover,hcoset⟩ := hL n Γ hΓ (f '' A) (by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨x,AddSubgroup.subset_closure hx,rfl⟩)
  choose t _ hts using fun j => (s j).property
  let P (j : Fin k) := ((Q j).comap f).toIntSubmodule
  refine ⟨k,t,P,?_,?_⟩
  · intro x hx
    obtain ⟨j,hj⟩ := hcover _ ⟨x,hx,rfl⟩
    exact ⟨j,show f (x-t j) ∈ Q j by simpa only [map_sub,hts] using hj⟩
  · intro j ι inst c v hv hzero y hy
    choose m hm using fun i => (mem_span_range_iff_exists_fun ℤ).mp (hv i)
    have eval (x : Space d) (i : ι) : unitaryMonomial (m i) (f x) = (frequencyPhase (v i) x : ℂ) := by
      rw [monomial_on_coordinates,hm]
    have htor := hcoset j (f y) hy c m (by
      rintro _ ⟨x,hx,rfl⟩
      simpa only [eval] using hzero x hx)
    have he : (s j).val + f y = f (t j+y) := by rw [map_add,hts]
    simpa only [he,eval] using htor

private theorem physical_cover_of_laurent (hL : UnitaryLaurentCosetTheorem) {d : ℕ}
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    HasFiniteLatticeCover A := by
  classical
  by_cases hBne : B.Nonempty
  swap
  · have hb := atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν hB
    have : IsEmpty B := ⟨fun i => hBne ⟨i.val,i.property⟩⟩
    have hzero : μ = 0 := by
      ext1 φ
      simpa [TemperedDistribution.fourier_apply] using (hb.2 (𝓕⁻ φ)).tsum_eq.symm
    exact (theoremA1_zero (hzero ▸ hμ) hA (hzero ▸ hν) hB).2.1
  obtain ⟨n,u,_,hspan,e,he⟩ := spectral_integer_basis hμ hA hν hB hBne
  let G := span ℤ (range u)
  have hBG : B ⊆ G := by simpa only [G,hspan] using (subset_span : B ⊆ span ℤ B)
  have hRG : span ℝ (G : Set (Space d)) = ⊤ := by
    apply top_unique
    let β := basisOfLinearIndependentOfCardEqFinrank' (u ∘ e) he (by simp)
    rw [← β.span_eq]
    apply span_mono
    rintro _ ⟨i,rfl⟩
    have hβ : ⇑β = u ∘ e := Module.Basis.coe_mk ..
    rw [hβ]
    exact subset_span (mem_range_self (e i))
  obtain ⟨k,t,P,hcover,hrelations⟩ := physical_cosets_of_laurent hL A
    (support_and_spectrum_groups_fg hμ hA hν hB).1 u
  let F (j : Fin k) := {x : Fin d → ℝ | WithLp.toLp 2 x - t j ∈ P j}
  refine finiteLatticeCover_of_lattice_or_subspace A (fun j => (t j).ofLp) F ?_ hcover ?_
  · intro j
    let W := span ℝ (P j : Set (Space d))
    by_cases hW : W = ⊤
    · obtain ⟨T,hT,hsub⟩ := spanning_coset_contained_in_lattice hμ hA hν hB G hBG hRG (t j) (P j) hW (hrelations j)
      refine Or.inl ⟨T,hT,fun x hx => ?_⟩
      obtain ⟨z,hz⟩ := (mem_latticeCoset_iff (t j) (WithLp.toLp 2 x) T).mpr (hsub hx)
      exact ⟨z,congrArg WithLp.ofLp hz.symm⟩
    · let l := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm
      refine Or.inr ⟨W.comap l.toLinearMap,?_,fun x hx => ?_⟩
      · intro htop
        apply hW
        apply top_unique
        intro y _
        obtain ⟨x,rfl⟩ := l.surjective y
        exact (show x ∈ W.comap l.toLinearMap by rw [htop]; trivial)
      · change l (x - (t j).ofLp) ∈ W
        rw [map_sub]
        exact subset_span hx
  · intro f hf hp
    obtain ⟨R,hR⟩ := relatively_dense_filtered_atoms hμ hA hν hB f hf hp
    refine ⟨R,fun c => ?_⟩
    obtain ⟨x,hx,hfx,hc⟩ := hR (WithLp.toLp 2 c)
    exact ⟨x,hx,hfx,(dist_pi_le_iff (dist_nonneg.trans hc)).mpr fun i => (PiLp.dist_apply_le (WithLp.toLp 2 c) x i).trans hc⟩

/-- Laurent's unitary torus theorem alone suffices for the complete
Appendix A conclusion under its original analytic hypotheses. -/
theorem theoremA1_of_unitaryLaurent (hL : UnitaryLaurentCosetTheorem) : theoremA1Statement :=
  theoremA1_of_physical_cover fun {_} _ {_ _ _ _ _} hμ hA hν hB => physical_cover_of_laurent hL hμ hA hν hB

end
end MeyerGeneralProblem.LevOlevskii
