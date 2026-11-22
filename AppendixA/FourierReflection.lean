module

public import AppendixA.TranslationBound

/-!
# The reflected Fourier pair

Fourier inversion identifies the double transform with reflection. This
allows each one-sided estimate to be used with the spectrum as physical
support, with its original complex coefficients.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open FourierTransform Set
open scoped FourierTransform NNReal ENNReal

/-- The double Fourier transform of a locally atomic distribution has the
original coefficients at the reflected sites, with the same separation. -/
theorem reflected_atomic_expansion {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A) :
    let A' := {x : Space d | -x ∈ A}
    HasLocallyAtomicExpansion (𝓕 (𝓕 μ)) A' (fun x => a ⟨-x.val, x.property⟩) ∧
      UniformlyDiscrete A' := by
  let A' := {x : Space d | -x ∈ A}
  let e : A' ≃ A :=
    { toFun := fun x => ⟨-x.val, x.property⟩
      invFun := fun x => ⟨-x.val, by simp [A']⟩
      left_inv := fun x => Subtype.ext (neg_neg x.val)
      right_inv := fun x => Subtype.ext (neg_neg x.val) }
  constructor
  · refine ⟨fun x => hμ.1 (e x), fun φ hc => ?_⟩
    have hval (x : Space d) : (𝓕 (𝓕 φ)) x = φ (-x) := by
      have h := congrArg (fun ψ : SchwartzMap (Space d) ℂ => ψ (-x)) (fourierInv_fourier_eq (F := SchwartzMap (Space d) ℂ) φ)
      change (𝓕 (𝓕 φ)) (- -x) = φ (-x) at h
      simpa only [neg_neg] using h
    let ψ : SchwartzMap (Space d) ℂ := 𝓕 (𝓕 φ)
    have hc' : HasCompactSupport (⇑ψ) := by
      have hfun : ⇑ψ = (φ : Space d → ℂ) ∘ Homeomorph.neg (Space d) := funext hval
      rw [hfun]
      exact hc.comp_homeomorph _
    have h := e.hasSum_iff.mpr (hμ.2 _ hc')
    simpa [ψ, e, Function.comp_def, hval, TemperedDistribution.fourier_apply] using h
  · obtain ⟨η, hη, hsep⟩ := hA
    refine ⟨η, hη, ?_⟩
    intro x hx y hy hne
    simpa using hsep (show -x ∈ A from hx) (show -y ∈ A from hy) (fun h => hne (neg_injective h))

/-- A common finite variation bound for all physical and spectral balls of
the same radius. -/
theorem joint_atomic_variation_translation_bounded {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ c : Space d,
      (∑' x : {x : A // dist x.val c ≤ r}, ‖a x.val‖ₑ) ≤ M ∧
      (∑' y : {y : B // dist y.val c ≤ r}, ‖b y.val‖ₑ) ≤ M := by
  obtain ⟨href, hsep⟩ := reflected_atomic_expansion hμ hA
  obtain ⟨P, hP⟩ := atomic_variation_translation_bounded hμ hA hμhat hB r
  obtain ⟨Q, hQ⟩ := atomic_variation_translation_bounded hμhat hB href hsep r
  exact ⟨max P Q, fun c => ⟨(hP c).trans (by exact_mod_cast le_max_left P Q),
    (hQ c).trans (by exact_mod_cast le_max_right P Q)⟩⟩

end
end MeyerGeneralProblem.LevOlevskii
