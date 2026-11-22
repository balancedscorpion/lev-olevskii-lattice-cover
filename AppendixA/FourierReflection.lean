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

private theorem double_fourier_test_apply {d : ℕ} (φ : SchwartzMap (Space d) ℂ) (x : Space d) :
    (𝓕 (𝓕 φ)) x = φ (-x) := by
  have h := congrArg (fun ψ : SchwartzMap (Space d) ℂ => ψ (-x))
    (fourierInv_fourier_eq (F := SchwartzMap (Space d) ℂ) φ)
  change (𝓕 (𝓕 φ)) (- -x) = φ (-x) at h
  simpa only [neg_neg] using h

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
    have hval := double_fourier_test_apply φ
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

/-- The inverse transform has the reflected spectral record. Applying the
forward transform to this pair recovers the original distribution. -/
theorem inverse_atomic_expansion {d : ℕ} {B : Set (Space d)} {b : B → ℂ}
    {μ : TemperedDistribution (Space d) ℂ}
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    let B' := {x : Space d | -x ∈ B}
    HasLocallyAtomicExpansion (𝓕⁻ μ) B' (fun x => b ⟨-x.val, x.property⟩) ∧
      UniformlyDiscrete B' := by
  have hthree : 𝓕 (𝓕 (𝓕 μ)) = 𝓕⁻ μ := by
    ext φ
    change μ (𝓕 (𝓕 (𝓕 φ))) = μ (𝓕⁻ φ)
    congr 1
    ext x
    exact double_fourier_test_apply (𝓕 φ) x
  rw [← hthree]
  exact reflected_atomic_expansion hν hB

theorem reflected_lattice_cover {d : ℕ} {B : Set (Space d)} (hB : HasFiniteLatticeCover B) :
    HasFiniteLatticeCover {x : Space d | -x ∈ B} := by
  obtain ⟨m, hm, t, T, hT, h⟩ := hB
  refine ⟨m, hm, -t, T, hT, ?_⟩
  intro x hx
  obtain ⟨j, z, hz⟩ := h (-x) hx
  refine ⟨j, -z, ?_⟩
  have hcast : (fun i => (((-z) i : ℤ) : ℝ)) = -(fun i => (z i : ℝ)) := by ext; simp
  rw [latticeSite, hcast, Matrix.mulVec_neg, WithLp.toLp_neg]
  simpa only [latticeSite, Pi.neg_apply, neg_add_rev, neg_neg, add_comm] using congrArg Neg.neg hz

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
