module

public import AppendixA.Covering
public import AppendixA.SpectralRecurrence

/-!
# Recurrence of the atoms surviving a trigonometric polynomial

The phase map takes physical space into a compact product of circles. Both
the polynomial and the convolution with an isolating test extend continuously
to that product, so they recur simultaneously.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter FourierTransform Matrix
open scoped Topology FourierTransform Matrix RealInnerProductSpace

private abbrev PhaseSpace (d : ℕ) := Space d → Circle

private def phases {d : ℕ} (x : Space d) : PhaseSpace d := fun u => frequencyPhase u x

private theorem phases_add {d : ℕ} (x y : Space d) : phases (x + y) = phases x * phases y := by
  funext u
  exact (frequencyPhase u).map_add_eq_mul _ _

private theorem phases_continuous {d : ℕ} : Continuous (phases (d := d)) := by
  apply continuous_pi
  intro u
  apply Real.continuous_fourierChar.comp
  exact continuous_inner.comp (continuous_id.prodMk continuous_const)

private theorem phase_returns {d : ℕ} {U : Set (PhaseSpace d)} (hU : IsOpen U)
    (p : Space d) (hp : phases p ∈ U) :
    ∃ R : ℝ, ∀ c : Space d, ∃ y, phases y ∈ U ∧ dist c y ≤ R := by
  classical
  let V (t : Space d) : Set (PhaseSpace d) := {z | z / phases t * phases p ∈ U}
  have hop (t) : IsOpen (V t) := hU.preimage (by fun_prop)
  have hcover : closure (range (phases (d := d))) ⊆ ⋃ t, V t := by
    intro z hz
    let N : Set (PhaseSpace d) := {w | z / w * phases p ∈ U}
    have hn : IsOpen N := hU.preimage (by fun_prop)
    have hzN : z ∈ N := by simpa [N] using hp
    obtain ⟨_, hw, t, rfl⟩ := (mem_closure_iff.mp hz) N hn hzN
    exact mem_iUnion.mpr ⟨t, hw⟩
  obtain ⟨S, hS⟩ := isClosed_closure.isCompact.elim_finite_subcover V hop hcover
  refine ⟨∑ t ∈ S, ‖t - p‖, fun c => ?_⟩
  obtain ⟨t, hx⟩ := mem_iUnion.mp (hS (subset_closure (mem_range_self c)))
  obtain ⟨ht, hct⟩ := mem_iUnion.mp hx
  refine ⟨c - t + p, ?_, ?_⟩
  · have hsub : phases (c - t) = phases c / phases t := by
      funext u
      exact (frequencyPhase u).map_sub_eq_div _ _
    rw [phases_add, hsub]
    exact hct
  · rw [dist_eq_norm, show c - (c - t + p) = t - p by abel]
    exact Finset.single_le_sum (fun i _ => norm_nonneg (i - p)) ht

private theorem extend_polynomial {d : ℕ} {f : (Fin d → ℝ) → ℂ} (hf : f ∈ trigPolynomials d) :
    ∃ g : PhaseSpace d → ℂ, Continuous g ∧ ∀ x, g (phases x) = f (WithLp.ofLp x) := by
  unfold trigPolynomials at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨u, rfl⟩ := hf
    refine ⟨fun z => (z (WithLp.toLp 2 u) : ℂ), continuous_subtype_val.comp (continuous_apply _), fun x => ?_⟩
    simp [phases, frequencyPhase, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  | algebraMap c => exact ⟨fun _ => c, continuous_const, fun _ => rfl⟩
  | add f g _ _ ihf ihg =>
    obtain ⟨F, hF, hf⟩ := ihf
    obtain ⟨G, hG, hg⟩ := ihg
    exact ⟨F + G, hF.add hG, fun x => by simp [hf, hg]⟩
  | mul f g _ _ ihf ihg =>
    obtain ⟨F, hF, hf⟩ := ihf
    obtain ⟨G, hG, hg⟩ := ihg
    exact ⟨F * G, hF.mul hG, fun x => by simp [hf, hg]⟩


/-- If a trigonometric polynomial survives at one atom, it survives at
relatively dense atoms. The spectral hypothesis is on the original measure. -/
theorem relatively_dense_filtered_atoms {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (f : (Fin d → ℝ) → ℂ) (hf : f ∈ trigPolynomials d)
    (hp : ∃ p ∈ A, f (WithLp.ofLp p) ≠ 0) :
    ∃ R : ℝ, ∀ c : Space d, ∃ x ∈ A, f (WithLp.ofLp x) ≠ 0 ∧ dist c x ≤ R := by
  obtain ⟨p, hpA, hp⟩ := hp
  obtain ⟨g, hg, heq⟩ := extend_polynomial hf
  let N : Set (PhaseSpace d × Space d) := {v | g (v.1 * phases v.2) ≠ 0}
  have hN : IsOpen N := isOpen_ne_fun (hg.comp (continuous_fst.mul
    (phases_continuous.comp continuous_snd))) continuous_const
  have hpN : (phases p, 0) ∈ N := by
    have hzero : phases (0 : Space d) = 1 := funext fun u => (frequencyPhase u).map_zero_eq_one
    simpa [N, hzero, heq] using hp
  obtain ⟨U, V, hU, hpU, hV, h0V, hUV⟩ := mem_nhds_prod_iff'.mp (hN.mem_nhds hpN)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  obtain ⟨φ, hc, hzero, hisol, hsmall⟩ := exists_small_isolating_test hA r hr
  let γ (u : B) := b u * (𝓕⁻ φ) u
  let F (z : PhaseSpace d) := ∑' u : B, γ u * (z u.val : ℂ)
  obtain ⟨hs, hseries⟩ := translated_test_fourier_series hμhat hB φ
  have hF : Continuous F := continuous_tsum (fun u : B =>
    continuous_const.mul (continuous_subtype_val.comp (continuous_apply u.val))) hs
    (fun u z => by simp [γ])
  have hFval (y : Space d) : F (phases y) = μ ((SchwartzMap.compSubConstCLM ℂ y) φ) :=
    (hseries y).tsum_eq
  have hFp : F (phases p) ≠ 0 := by
    rw [hFval, translated_isolating_test_eq hμ φ hc hzero hisol ⟨p, hpA⟩]
    exact hμ.1 ⟨p, hpA⟩
  obtain ⟨R, hR⟩ := phase_returns (hU.inter (isOpen_ne_fun hF continuous_const))
    p ⟨hpU, hFp⟩
  refine ⟨R + r, fun c => ?_⟩
  obtain ⟨y, ⟨hyU, hyF⟩, hcy⟩ := hR c
  obtain ⟨x, hx⟩ : ∃ x : A, φ (x.val - y) ≠ 0 := by
    by_contra! hvanish
    apply hyF
    rw [hFval]
    have hsum := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ hA).2
      ((SchwartzMap.compSubConstCLM ℂ y) φ)
    simpa [SchwartzMap.compSubConstCLM_apply, hvanish] using hsum.tsum_eq.symm
  have hxy := hsmall _ hx
  have hv : x.val - y ∈ V := hball (by simpa using hxy)
  have hnonzero := hUV (Set.mk_mem_prod hyU hv)
  change g (phases y * phases (x.val - y)) ≠ 0 at hnonzero
  rw [← phases_add, add_sub_cancel, heq] at hnonzero
  refine ⟨x.val, x.property, hnonzero, (dist_triangle c y x.val).trans (add_le_add hcy ?_)⟩
  rw [dist_comm, dist_eq_norm]
  exact hxy.le

/-- Given the character fibers supplied by the algebraic step of Appendix A,
the two local atomic records imply a finite lattice cover. -/
theorem atomic_latticeCover_of_character_fibers {d n : ℕ} {ι : Type*} [Finite ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hμhat : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (L : Matrix (Fin n) (Fin d) ℝ) (hL : LinearIndependent ℤ L.row)
    (k : ι → ℕ) (hk : ∀ j, d ≤ k j) (t : ι → Fin d → ℝ)
    (C : (j : ι) → Matrix (Fin (k j)) (Fin n) ℤ) (hC : ∀ j, LinearIndependent ℤ (C j).row)
    (hfibers : ∀ x ∈ A, ∃ j, ∀ i, Real.fourierChar
      ((((C j).map (Int.castRingHom ℝ) * L) *ᵥ (WithLp.ofLp x - t j)) i) = 1) :
    HasFiniteLatticeCover A := by
  apply finiteLatticeCover_of_character_fibers A L hL k hk t C hC hfibers
  intro f hf hp
  obtain ⟨R, hR⟩ := relatively_dense_filtered_atoms hμ hA hμhat hB f hf hp
  refine ⟨R, fun c => ?_⟩
  obtain ⟨x, hx, hfx, hcx⟩ := hR (WithLp.toLp 2 c)
  refine ⟨x, hx, hfx, (dist_pi_le_iff (dist_nonneg.trans hcx)).mpr fun i => ?_⟩
  exact (PiLp.dist_apply_le (WithLp.toLp 2 c) x i).trans hcx

end
end MeyerGeneralProblem.LevOlevskii
