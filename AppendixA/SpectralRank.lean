module

public import AppendixA.SpectralWindow

/-!
# Rank of restricted characters from a bounded spectral window

Cardinal tests for the individual sites express each modulating character on
the physical support as a linear combination indexed by the shifted spectral
sites in a common frequency ball.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Metric FourierTransform
open scoped FourierTransform

private theorem translated_window_sum {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ} (hν : HasAtomicExpansion (𝓕 μ) B b)
    (u : Space d) (φ : SchwartzMap (Space d) ℂ) {R : ℝ}
    (hs : Function.support φ ⊆ closedBall 0 R) (E : Finset (Space d))
    (hE : ∀ y ∈ B, ‖y + u‖ ≤ R → y + u ∈ E) :
    (𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ) =
      ∑ z ∈ E, recordWeight b (z-u) * φ z := by
  classical
  let F (z : Space d) := recordWeight b (z-u) * φ z
  let f (i : B) : Space d := i.val + u
  have hinj : Function.Injective f := (add_left_injective u).comp Subtype.val_injective
  have hz (z) (h : z-u ∉ B) : F z = 0 := by simp [F,recordWeight,h]
  have hsum : HasSum F ((𝓕 μ) ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)) := by
    apply (hinj.hasSum_iff (fun z h => hz z fun hy => h ⟨⟨z-u,hy⟩, sub_add_cancel ..⟩)).mp
    simpa [f,F,Function.comp_def,recordWeight,SchwartzMap.compSubConstCLM_apply] using
      hν.2 ((SchwartzMap.compSubConstCLM ℂ (-u)) φ)
  apply hsum.unique (hasSum_sum_of_ne_finset_zero (s := E) ?_)
  intro z he
  by_cases hy : z-u ∈ B
  · have hφ : φ z = 0 := by
      by_contra hn
      have h := hE (z-u) hy
      rw [sub_add_cancel] at h
      exact he (h (by simpa using hs hn))
    simp [F,hφ]
  · exact hz z hy

/-- For any finite list of frequencies, the rank of the corresponding
characters restricted to the physical sites is at most the number of shifted
spectral sites in the fixed window. The radius is independent of the list. -/
theorem restricted_character_rank_bound {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    ∃ R : ℝ, 0 < R ∧ ∀ {ι : Type*} [Fintype ι] (u : ι → Space d) (E : Finset (Space d)),
      (∀ i y, y ∈ B → ‖y + u i‖ ≤ R → y + u i ∈ E) →
      Module.finrank ℂ (Submodule.span ℂ (range (fun i (x : A) => (frequencyPhase (u i) x.val : ℂ)))) ≤
        E.card := by
  classical
  obtain ⟨η,hη,hsep⟩ := hA
  obtain ⟨R,hR,hiso⟩ := bandlimited_cardinal_interpolation d hη
  choose φ hs hone hoff using hiso A hsep
  have ha := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ ⟨η,hη,hsep⟩).2
  have hb := atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν hB
  refine ⟨R,hR,?_⟩
  intro ι inst u E hE
  let V (z : E) (x : A) := (a x)⁻¹ * φ x z.val
  let W (i : ι) (x : A) : ℂ := frequencyPhase (u i) x.val
  have he (i : ι) : W i = ∑ z : E, recordWeight b (z.val-u i) • V z := by
    funext x
    let test := (SchwartzMap.compSubConstCLM ℂ (-(u i))) (φ x)
    have h := (ha (𝓕 test)).unique (hasSum_single x (fun y hy => by
      simp [test, fourier_test_add, hoff x y hy]))
    change (𝓕 μ) test = _ at h
    simp only [test, fourier_test_add, hone, mul_one] at h
    have h' := translated_window_sum hb (u i) (φ x) (hs x) E (hE i)
    rw [← Finset.sum_coe_sort] at h'
    change (𝓕 μ) test = _ at h'
    have heq := congrArg (fun c : ℂ => (a x)⁻¹ * c) (h.symm.trans h')
    simpa [W,V,Finset.mul_sum, mul_left_comm, ← mul_assoc, hμ.1] using heq
  have hsub : Submodule.span ℂ (range W) ≤ Submodule.span ℂ (range V) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self j)))
  let := Module.Finite.span_of_finite ℂ (finite_range V)
  exact (Submodule.finrank_mono hsub).trans (by simpa [Set.finrank] using finrank_range_le_card (R := ℂ) V)

end
end MeyerGeneralProblem.LevOlevskii
