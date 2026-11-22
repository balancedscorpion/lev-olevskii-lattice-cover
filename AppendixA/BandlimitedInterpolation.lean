module

public import AppendixA.SeparatedInterpolation
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Compact-frequency cardinal interpolation in Euclidean space

An absolutely convergent sum of modulations of a compactly supported frequency
kernel interpolates prescribed data. Convolution with a modulated smooth bump
preserves the cardinal values and gives a smooth test with a uniform frequency
window.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii
noncomputable section

open MeasureTheory Metric Set FourierTransform
open scoped Topology Convolution FourierTransform lp ContDiff Pointwise

private theorem normalized_frequency_bump (d : ℕ) :
    ∃ g : SchwartzMap (Space d) ℂ, Function.support g ⊆ closedBall 0 1 ∧ 𝓕 g 0 = 1 := by
  let b : ContDiffBump (0 : Space d) := ⟨1/2, 1, by norm_num, by norm_num⟩
  let f : Space d → ℂ := Complex.ofRealCLM ∘ b.normed volume
  have hc : HasCompactSupport f := b.hasCompactSupport_normed.comp_left rfl
  have hdiff : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  refine ⟨hc.toSchwartzMap hdiff, ?_, ?_⟩
  · intro y hy
    have h : b.normed volume y ≠ 0 := by
      intro hz
      apply hy
      change ((b.normed volume y : ℝ) : ℂ) = 0
      rw [hz]; rfl
    have hm : y ∈ Function.support (b.normed volume) := h
    rw [b.support_normed_eq] at hm
    exact ball_subset_closedBall hm
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simpa [f, ← integral_complex_ofReal] using congrArg ((↑) : ℝ → ℂ) (b.integral_normed (μ := volume))

private def phaseAt {d : ℕ} (v y : Space d) : ℂ :=
  Real.fourierChar (inner ℝ y v)

private theorem phaseAt_smooth {d : ℕ} (v : Space d) : ContDiff ℝ ∞ (phaseAt v) := by
  change ContDiff ℝ ∞ (fun y => (Real.fourierChar (inner ℝ y v) : ℂ))
  simp only [Real.fourierChar_apply]
  change ContDiff ℝ ∞ (fun y => Complex.exp (Complex.ofRealCLM (2 * Real.pi * inner ℝ y v) * Complex.I))
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))).mul contDiff_const).cexp

private theorem fourier_modulated {d : ℕ} (g : Space d → ℂ) (v x : Space d) :
    𝓕 (fun y => phaseAt v y * g y) x = 𝓕 g (x - v) := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, phaseAt]
  simp_rw [inner_sub_right, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, Circle.coe_mul]
  congr 1
  ext
  ring

private theorem dilated_frequency_bump {d : ℕ} (g : SchwartzMap (Space d) ℂ)
    (hg : Function.support g ⊆ closedBall 0 1) {L : ℝ} (hL : 0 < L) :
    ∃ G : Space d → ℂ, Continuous G ∧ Function.support G ⊆ closedBall 0 L ∧
      ∀ x, 𝓕 G x = 𝓕 g (L • x) := by
  let D : ℝ := L ^ Module.finrank ℝ (Space d)
  let G (y : Space d) := D⁻¹ • g (L⁻¹ • y)
  refine ⟨G, by dsimp [G]; fun_prop, ?_, fun x => ?_⟩
  · intro y hy
    have hy' : g (L⁻¹ • y) ≠ 0 := fun h => hy (by simp [G, h])
    have hh := hg hy'
    simpa [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hL, inv_mul_eq_div, div_le_iff₀ hL] using hh
  · rw [SchwartzMap.fourier_coe, Real.fourier_eq, Real.fourier_eq]
    let f (y : Space d) := Real.fourierChar (-inner ℝ y (L • x)) • g y
    have changeVar := volume.integral_comp_inv_smul_of_nonneg f hL.le
    have h (y : Space d) : Real.fourierChar (-inner ℝ y x) • G y =
        D⁻¹ • f (L⁻¹ • y) := by
      simp [f, G, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
        mul_inv_cancel₀ hL.ne', smul_comm]
    simp_rw [h]
    rw [integral_smul, changeVar, smul_smul]
    simp [D, hL.ne', f]

private theorem synthesize_window {d : ℕ} {ι : Type*} [Countable ι] (u : ι → Space d)
    (c : ℓ¹(ι, ℂ)) (G : Space d → ℂ) (hG : Continuous G) {R : ℝ}
    (hsG : Function.support G ⊆ closedBall 0 R) :
    ∃ H : Space d → ℂ, Continuous H ∧ Function.support H ⊆ closedBall 0 R ∧
      ∀ x : Space d, HasSum (fun j => c j * 𝓕 G (x - u j)) (𝓕 H x) := by
  let k (j : ι) (y : Space d) := c j * phaseAt (u j) y
  have hk (j : ι) : Continuous (k j) := continuous_const.mul (phaseAt_smooth _).continuous
  have hn (j : ι) (y : Space d) : ‖k j y‖ = ‖c j‖ := by simp [k, phaseAt]
  have hc : Summable (fun j => ‖c j‖) := by simpa using c.2.summable
  let H (y : Space d) := (∑' j, k j y) * G y
  have hH : Continuous H := (continuous_tsum hk hc fun j y => (hn j y).le).mul hG
  refine ⟨H, hH, (Function.support_mul_subset_right ..).trans hsG, fun x => ?_⟩
  have hGc : HasCompactSupport G := HasCompactSupport.intro (isCompact_closedBall _ _) fun y hy => by
    by_contra h
    exact hy (hsG h)
  let F (j : ι) (y : Space d) := Real.fourierChar (-inner ℝ y x) • (k j y * G y)
  have hFint (j : ι) : Integrable (F j) :=
    (Real.fourierIntegral_convergent_iff x).mpr
      (((hk j).mul hG).integrable_of_hasCompactSupport (hGc.mul_left))
  have hFn (j : ι) (y : Space d) : ‖F j y‖ = ‖c j‖ * ‖G y‖ := by
    simp [F, hn]
  have hFnSum : Summable fun j => ∫ y, ‖F j y‖ := by
    simp_rw [hFn, integral_const_mul]
    exact hc.mul_right _
  have hint (j : ι) : (∫ y, F j y) = c j * 𝓕 G (x - u j) := by
    rw [← fourier_modulated, Real.fourier_eq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    simp [F, k, Circle.smul_def, mul_left_comm, mul_assoc]
  have hsum := hasSum_integral_of_summable_integral_norm hFint hFnSum
  simp_rw [hint] at hsum
  convert hsum using 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with y
  simp [F, H, Circle.smul_def, tsum_mul_left, tsum_mul_right]

/-- For a fixed positive separation there is a common frequency window
in which one can choose a smooth compact test whose transform interpolates
a Kronecker delta on any carrier of that separation. -/
theorem bandlimited_cardinal_interpolation (d : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∀ (A : Set (Space d))
      (_ : A.Pairwise fun x y => η ≤ dist x y) (p : A),
      ∃ ψ : SchwartzMap (Space d) ℂ, Function.support ψ ⊆ closedBall 0 R ∧
        (𝓕 ψ) p.val = 1 ∧ ∀ i : A, i ≠ p → (𝓕 ψ) i.val = 0 := by
  classical
  obtain ⟨g, hg, hg0⟩ := normalized_frequency_bump d
  obtain ⟨L, hL, hinterp⟩ := separated_schwartz_interpolation (𝓕 g) hg0 hη
  have hLpos : 0 < L := by linarith
  obtain ⟨G, hG, hsG, hGφ⟩ := dilated_frequency_bump g hg hLpos
  refine ⟨L + 1, by positivity, fun A hsep p => ?_⟩
  have hcount := (summable_inverse_weight (A := A) ⟨η, hη, hsep⟩ (d+1) d.lt_succ_self).countable_support
  have huniv : Set.Countable (Set.univ : Set A) := hcount.mono fun i _ => by
    change ((1 + ‖i.val‖) ^ (d+1))⁻¹ ≠ 0
    positivity
  let : Countable A := Set.countable_univ_iff.mp huniv
  let b : ℓ¹(A, ℂ) := lp.single 1 p 1
  obtain ⟨c, _, hc⟩ := hinterp Subtype.val (fun i j hij => hsep i.property j.property
    fun he => hij (Subtype.ext he)) b
  obtain ⟨H, hH, hsH, hHφ⟩ := synthesize_window Subtype.val c G hG hsG
  have hHsample (i : A) : 𝓕 H i.val = b i := by
    apply (hHφ i.val).unique
    simpa only [hGφ] using hc i
  let S (y : Space d) := phaseAt p.val y * g y
  have hSmooth : ContDiff ℝ ∞ S := (phaseAt_smooth p.val).mul (g.smooth _)
  have hsS : Function.support S ⊆ closedBall 0 1 :=
    (Function.support_mul_subset_right ..).trans hg
  have compactOfBall {f : Space d → ℂ} {r : ℝ} (hf : Function.support f ⊆ closedBall 0 r) :
      HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall _ _) fun y hy => by
    by_contra h
    exact hy (hf h)
  let M := ContinuousLinearMap.mul ℝ ℂ
  let k := H ⋆[M] S
  have hHc := compactOfBall hsH
  have hSc := compactOfBall hsS
  have hkc : HasCompactSupport k := hHc.convolution M hSc
  have hk : ContDiff ℝ ∞ k := hSc.contDiff_convolution_right M hH.locallyIntegrable hSmooth
  let ψ := hkc.toSchwartzMap hk
  have hsψ : Function.support ψ ⊆ closedBall 0 (L + 1) := by
    intro y hy
    obtain ⟨v, hv, w, hw, rfl⟩ := support_convolution_subset M hy
    simpa only [mem_closedBall, dist_zero_right] using
      (norm_add_le v w).trans (add_le_add (show ‖v‖ ≤ L by simpa using hsH hv)
        (show ‖w‖ ≤ 1 by simpa using hsS hw))
  have hψ (i : A) : (𝓕 ψ) i.val = b i * 𝓕 (g : Space d → ℂ) (i.val - p.val) := by
    change 𝓕 (H ⋆[ContinuousLinearMap.mul ℂ ℂ] S) i.val = _
    rw [Real.fourier_mul_convolution_eq (hH.integrable_of_hasCompactSupport hHc)
      (hSmooth.continuous.integrable_of_hasCompactSupport hSc), hHsample, fourier_modulated]
  refine ⟨ψ, hsψ, ?_, fun i hi => ?_⟩
  · rw [hψ, sub_self]
    simpa [b, lp.single_apply_self, SchwartzMap.fourier_coe] using hg0
  · rw [hψ, show b i = 0 from lp.single_apply_ne 1 p 1 hi, zero_mul]

end
end MeyerGeneralProblem.LevOlevskii
