module

public import AppendixA.BandlimitedInterpolation
public import AppendixA.ShrinkingTests

/-!
# Uniqueness from a bounded spectral window

For two separated records there may be pairs of distinct sites arbitrarily
close together. Around any selected point, at most one site of each record
needs an additional zero. A directional derivative inserts that zero without
enlarging the frequency window.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open MeasureTheory Metric Set FourierTransform LineDeriv
open scoped Topology FourierTransform Convolution Pointwise

private theorem erase_nearby_sample {d : ℕ} {p q : Space d} (hpq : p ≠ q)
    {R : ℝ} (φ : SchwartzMap (Space d) ℂ) (hsφ : Function.support φ ⊆ closedBall 0 R)
    (hφ : (𝓕 φ) p = 1) :
    ∃ ψ : SchwartzMap (Space d) ℂ, Function.support ψ ⊆ closedBall 0 R ∧
      (𝓕 ψ) p = 1 ∧ (𝓕 ψ) q = 0 ∧ ∀ x, (𝓕 φ) x = 0 → (𝓕 ψ) x = 0 := by
  let m := p - q
  let D : ℂ := 2 * Real.pi * Complex.I
  let a (x : Space d) : ℂ := D * ((inner ℝ x m : ℝ) : ℂ)
  let χ := ∂_{m} φ - a q • φ
  have hf (x : Space d) : (𝓕 χ) x = (a x - a q) * (𝓕 φ) x := by
    have hg : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
    have he : 𝓕 χ = 𝓕 (∂_{m} φ) - 𝓕 (a q • φ) := (SchwartzMap.fourierTransformCLM ℂ).map_sub ..
    rw [he]
    simp [a, D, fourier_smul, SchwartzMap.fourier_lineDerivOp_eq,
      SchwartzMap.smulLeftCLM_apply_apply hg, sub_mul, mul_assoc]
  have hne : a p - a q ≠ 0 := by
    have hm : m ≠ 0 := sub_ne_zero.mpr hpq
    have hpos := real_inner_self_pos.mpr hm
    have hinner : inner ℝ p m - inner ℝ q m ≠ 0 := by
      rw [← inner_sub_left]; exact hpos.ne'
    simpa only [a, ← mul_sub, ← Complex.ofReal_sub] using
      (mul_ne_zero (show D ≠ 0 by simp [D, Real.pi_ne_zero]) (Complex.ofReal_ne_zero.mpr hinner))
  let ψ := (a p - a q)⁻¹ • χ
  have hψ (x : Space d) : (𝓕 ψ) x = (a p - a q)⁻¹ * ((a x - a q) * (𝓕 φ) x) := by
    simp [ψ, fourier_smul, hf]
  refine ⟨ψ, ?_, by simp [hψ, hφ, hne], by simp [hψ], fun x hx => by simp [hψ, hx]⟩
  intro y hy
  by_contra hout
  have hts : y ∉ tsupport φ := fun h => hout (closure_minimal hsφ isClosed_closedBall h)
  have hz : φ y = 0 := by by_contra he; exact hts (subset_tsupport _ he)
  apply hy
  simp [ψ, χ, hz, SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_of_notMem_tsupport ℝ hts]

/-- The window can isolate a prescribed point even when it does not belong
to the carrier. Its radius depends only on the separation. -/
theorem bandlimited_isolation_at_point (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ (A : Set (Space d))
      (_ : A.Pairwise fun x y => η ≤ dist x y) (p : Space d),
      ∃ ψ : SchwartzMap (Space d) ℂ, Function.support ψ ⊆ closedBall 0 R ∧
        (𝓕 ψ) p = 1 ∧ ∀ i ∈ A, i ≠ p → (𝓕 ψ) i = 0 := by
  obtain ⟨R, hR, hinterp⟩ := bandlimited_cardinal_interpolation d (half_pos hη)
  refine ⟨R, hR, fun A hsep p => ?_⟩
  let F := {x ∈ A | η / 2 ≤ dist x p}
  let S := insert p F
  have hS : S.Pairwise fun x y => η / 2 ≤ dist x y := by
    intro x hx y hy hxy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (hxy rfl).elim
    · simpa [dist_comm] using hy.2
    · exact hx.2
    · exact (half_le_self hη.le).trans (hsep hx.1 hy.1 hxy)
  let p' : S := ⟨p, mem_insert ..⟩
  obtain ⟨φ, hsφ, hφ, hφz⟩ := hinterp S hS p'
  have hz (i : Space d) (hi : i ∈ F) (hip : i ≠ p) : (𝓕 φ) i = 0 :=
    hφz ⟨i, mem_insert_of_mem _ hi⟩ (fun h => hip (congrArg Subtype.val h))
  by_cases near : ∃ q ∈ A, q ≠ p ∧ dist q p < η / 2
  · obtain ⟨q, hq, hqp, hdist⟩ := near
    obtain ⟨ψ, hsψ, hψ, hψq, hψz⟩ := erase_nearby_sample hqp.symm φ hsφ hφ
    refine ⟨ψ, hsψ, hψ, fun i hi hip => ?_⟩
    by_cases he : i = q
    · simpa only [he] using hψq
    · apply hψz
      apply hz i ⟨hi, ?_⟩ hip
      have htri := dist_triangle i p q
      rw [dist_comm p q] at htri
      linarith [hsep hi hq he]
  · exact ⟨φ, hsφ, hφ, fun i hi hip => hz i ⟨hi, le_of_not_gt (fun h => near ⟨i, hi, hip, h⟩)⟩ hip⟩

private theorem isolated_test_value {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A : Set (Space d)} {a : A → ℂ} (hμ : HasAtomicExpansion μ A a)
    (p : Space d) (f : SchwartzMap (Space d) ℂ) (hfp : f p = 1)
    (hf : ∀ x ∈ A, x ≠ p → f x = 0) : μ f = recordWeight a p := by
  by_cases hp : p ∈ A
  · let i : A := ⟨p, hp⟩
    have hsingle := (hμ.2 f).unique (hasSum_single i fun z hzi => by
      rw [hf z z.property (fun h => hzi (Subtype.ext h)), mul_zero])
    simpa [i, recordWeight, hp, hfp] using hsingle
  · have hz (i : A) : a i * f i = 0 := by
      rw [hf i i.property (fun h => hp (h ▸ i.property)), mul_zero]
    simpa [recordWeight, hp, hz] using (hμ.2 f).tsum_eq.symm

/-- Two tempered records with a common positive separation are equal if
their transforms agree throughout a ball of radius determined solely by the
separation and the dimension. No separation between the two carriers is
required. -/
theorem separated_pair_spectral_window_uniqueness (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ {μ ν : TemperedDistribution (Space d) ℂ}
      {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ},
      HasLocallyAtomicExpansion μ A a → (A.Pairwise fun x y => η ≤ dist x y) →
      HasLocallyAtomicExpansion ν B b → (B.Pairwise fun x y => η ≤ dist x y) →
      (∀ ψ : SchwartzMap (Space d) ℂ, Function.support ψ ⊆ closedBall 0 R →
        (𝓕 μ) ψ = (𝓕 ν) ψ) → μ = ν := by
  obtain ⟨R, hR, hiso⟩ := bandlimited_isolation_at_point d hη
  refine ⟨R+R, by positivity, ?_⟩
  intro μ ν A B a b hμ hA hν hB hwindow
  have ha := atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ ⟨η, hη, hA⟩
  have hb := atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν ⟨η, hη, hB⟩
  have weights (p : Space d) : recordWeight a p = recordWeight b p := by
    obtain ⟨φ, hsφ, hφp, hφ⟩ := hiso A hA p
    obtain ⟨ψ, hsψ, hψp, hψ⟩ := hiso B hB p
    let M := ContinuousLinearMap.mul ℂ ℂ
    let f := SchwartzMap.convolution M φ ψ
    have hs : Function.support f ⊆ closedBall 0 (R+R) := by
      intro y hy
      have hm : y ∈ Function.support ((φ : Space d → ℂ) ⋆[M] (ψ : Space d → ℂ)) := by
        simpa only [Function.mem_support, f, SchwartzMap.convolution_apply] using hy
      obtain ⟨v, hv, w, hw, rfl⟩ := support_convolution_subset M hm
      simpa only [mem_closedBall, dist_zero_right] using
        (norm_add_le v w).trans (add_le_add (show ‖v‖ ≤ R by simpa using hsφ hv)
          (show ‖w‖ ≤ R by simpa using hsψ hw))
    have hval (z : Space d) : (𝓕 f) z = (𝓕 φ) z * (𝓕 ψ) z := by
      unfold f
      rw [SchwartzMap.fourier_convolution]; rfl
    have hp : (𝓕 f) p = 1 := by simp [hval, hφp, hψp]
    rw [← isolated_test_value ha p (𝓕 f) hp (fun z hz hn => by simp [hval, hφ z hz hn]),
      ← isolated_test_value hb p (𝓕 f) hp (fun z hz hn => by simp [hval, hψ z hz hn])]
    exact hwindow f hs
  have support_iff {S : Set (Space d)} {s : S → ℂ} (hne : ∀ i, s i ≠ 0) (p : Space d) :
      p ∈ S ↔ recordWeight s p ≠ 0 := by
    by_cases hp : p ∈ S <;> simp [recordWeight, hp, hne]
  have hsets : A = B := Set.ext fun p => (support_iff hμ.1 p).trans
    ((weights p) ▸ (support_iff hν.1 p).symm)
  subst B
  have heq : a = b := funext fun i => by simpa [recordWeight, i.property] using weights i.val
  subst b
  ext1 f
  exact (ha.2 f).unique (hb.2 f)

end
end MeyerGeneralProblem.LevOlevskii
