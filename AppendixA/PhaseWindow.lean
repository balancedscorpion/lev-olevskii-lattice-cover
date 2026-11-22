module

public import AppendixA.TranslationHull
public import AppendixA.SpectralWindow

/-!
# Finite spectral windows distinguish phase limits
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Metric FourierTransform
open scoped FourierTransform

/-- Values on the spectrum inside a fixed ball determine the entire phase
vector in the closure of the translation orbit. -/
theorem phase_window_separates {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ closure (range (fun t : Space d => fun i : B => frequencyPhase i.val t)),
      ∀ w ∈ closure (range (fun t : Space d => fun i : B => frequencyPhase i.val t)),
      (∀ i : B, ‖i.val‖ ≤ R → z i = w i) → z = w := by
  obtain ⟨η,hη,hsep⟩ := hA
  obtain ⟨R,hR,hunique⟩ := separated_pair_spectral_window_uniqueness d hη
  refine ⟨R,hR,fun z hz w hw hlow => ?_⟩
  obtain ⟨T,E,c,hT,hE,hzT⟩ := realize_spectral_phase_orbit hη hμ hsep hν hB z hz
  obtain ⟨S,F,e,hS,hF,hwS⟩ := realize_spectral_phase_orbit hη hμ hsep hν hB w hw
  have he : T = S := hunique hT hE hS hF (fun φ hφ => by
    rw [← (hzT.2 φ).tsum_eq, ← (hwS.2 φ).tsum_eq]
    apply tsum_congr
    intro i
    by_cases hi : ‖i.val‖ ≤ R
    · exact congrArg (fun u : Circle => b i * (u : ℂ) * φ i.val) (hlow i hi)
    · have hzero : φ i = 0 := by by_contra hn; exact hi (by simpa using hφ hn)
      rw [hzero, mul_zero, mul_zero])
  subst S
  obtain ⟨φ,hc,hzero,hisol⟩ := exists_isolating_test hB
  funext i
  apply Subtype.ext
  apply mul_left_cancel₀ (hν.1 i)
  exact (translated_isolating_test_eq ⟨hzT.1,fun f _ => hzT.2 f⟩ φ hc hzero hisol i).symm.trans
    (translated_isolating_test_eq ⟨hwS.1,fun f _ => hwS.2 f⟩ φ hc hzero hisol i)

end
end MeyerGeneralProblem.LevOlevskii
