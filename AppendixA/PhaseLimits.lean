module

public import AppendixA.FourierReflection

/-!
# Spectral phases of limits of translates

Bounded coefficients on separated sites define a tempered distribution.
Consequently a pointwise limit of translation phases defines a distributional
limit on every Schwartz test.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Filter FourierTransform MeasureTheory
open scoped FourierTransform Topology

/-- Bounded nonzero weights on a separated carrier give a tempered atomic
record, with absolute convergence on all Schwartz tests. -/
theorem bounded_weights_tempered {d : ℕ} {B : Set (Space d)}
    (hB : UniformlyDiscrete B) (b : B → ℂ) (hne : ∀ i, b i ≠ 0)
    (hb : ∃ C : ℝ, ∀ i, ‖b i‖ ≤ C) :
    ∃ ν : TemperedDistribution (Space d) ℂ, HasAtomicExpansion ν B b := by
  obtain ⟨C, hC⟩ := hb
  let s := d + 1
  let w (i : B) := ((1 + ‖i.val‖)^s)⁻¹
  have hw := summable_inverse_weight hB s (Nat.lt_succ_self _)
  let S := (Finset.Iic (s,0)).sup (schwartzSeminormFamily ℂ (Space d) ℂ)
  let D := max C 0 * 2 ^ s
  have hD : 0 ≤ D := mul_nonneg (le_max_right ..) (by positivity)
  have bound (φ : SchwartzMap (Space d) ℂ) (i : B) :
      ‖b i * φ i‖ ≤ (D * S φ) * w i := by
    have hφ : (1 + ‖i.val‖)^s * ‖φ i‖ ≤ 2 ^ s * S φ := by
      have he : schwartzSeminormFamily ℂ (Space d) ℂ = (fun m => SchwartzMap.seminorm ℂ m.1 m.2) :=
        funext fun ⟨i,j⟩ => SchwartzMap.schwartzSeminormFamily_apply ..
      simpa only [norm_iteratedFDeriv_zero, S, he] using
        SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (s,0)) le_rfl le_rfl φ i.val
    unfold w
    rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc
      _ = ‖b i‖ * ((1 + ‖i.val‖)^s * ‖φ i‖) := by ring
      _ ≤ max C 0 * (2 ^ s * S φ) := mul_le_mul ((hC i).trans (le_max_left ..)) hφ
        (by positivity) (le_max_right ..)
      _ = _ := by dsimp [D]; ring
  have hs (φ : SchwartzMap (Space d) ℂ) : Summable (fun i => ‖b i * φ i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (bound φ) (hw.mul_left _)
  let F (φ : SchwartzMap (Space d) ℂ) := ∑' i, b i * φ i
  let L : SchwartzMap (Space d) ℂ →L[ℂ] ℂ := SchwartzMap.mkCLMtoNormedSpace F
    (fun φ ψ => by simpa [F, mul_add] using ((hs φ).of_norm.tsum_add (hs ψ).of_norm))
    (fun c φ => by simp [F, mul_left_comm, tsum_mul_left])
    (by
      refine ⟨Finset.Iic (s,0), D * ∑' i, w i, mul_nonneg hD (tsum_nonneg fun _ => by dsimp [w]; positivity), fun φ => ?_⟩
      calc
        ‖F φ‖ ≤ ∑' i, ‖b i * φ i‖ := norm_tsum_le_tsum_norm (hs φ)
        _ ≤ ∑' i, (D * S φ) * w i := (hs φ).tsum_le_tsum (bound φ) (hw.mul_left _)
        _ = _ := by rw [tsum_mul_left]; change _ = _ * S φ; ring)
  exact ⟨L, hne, fun φ => (hs φ).of_norm.hasSum⟩

/-- A phase limit twists the spectral weights and determines all translated
test limits. This holds for an arbitrary filter of translation parameters. -/
theorem spectral_phase_limit {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    {l : Filter (Space d)} (z : B → Circle)
    (hz : ∀ i : B, Tendsto (fun t => frequencyPhase i.val t) l (𝓝 (z i))) :
    ∃ μ' : TemperedDistribution (Space d) ℂ,
      HasAtomicExpansion (𝓕 μ') B (fun i => b i * (z i : ℂ)) ∧
      ∀ φ : SchwartzMap (Space d) ℂ, Tendsto (fun t => μ ((SchwartzMap.compSubConstCLM ℂ t) φ))
        l (𝓝 (μ' φ)) := by
  obtain ⟨href, hsep⟩ := reflected_atomic_expansion hμ hA
  obtain ⟨C, hC⟩ := atomic_coefficients_uniformly_bounded hν hB href hsep
  obtain ⟨ν, htw⟩ := bounded_weights_tempered hB (fun i => b i * (z i : ℂ))
    (fun i => mul_ne_zero (hν.1 i) (Circle.coe_ne_zero _))
    ⟨C, fun i => by simpa [norm_mul] using hC i⟩
  refine ⟨𝓕⁻ ν, by simpa using htw, fun φ => ?_⟩
  obtain ⟨hs, hv⟩ := translated_test_fourier_series hν hB φ
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun t (i : B) => (b i * (𝓕⁻ φ) i) * (frequencyPhase i.val t : ℂ))
    (g := fun i : B => b i * (𝓕⁻ φ) i * (z i : ℂ)) hs
    (fun i => (continuous_subtype_val.continuousAt.tendsto.comp (hz i)).const_mul _)
    (Eventually.of_forall fun t i => by simp)
  have hval := (htw.2 (𝓕⁻ φ)).tsum_eq
  simp_rw [← (hv _).tsum_eq]
  simpa only [mul_right_comm (b _) ((𝓕⁻ φ) _) _, hval, TemperedDistribution.fourierInv_apply] using hlim

end
end MeyerGeneralProblem.LevOlevskii
