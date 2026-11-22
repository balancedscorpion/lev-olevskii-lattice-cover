module

public import AppendixA.RestrictedTransform

/-!
# Extracting individual Fourier coefficients by shrinking tests

These tests have value one at their center. The support of each test fits
inside the region where the previous test equals one. A local bound for a
complex linear functional controls the total variation of its values on
this nested sequence, so its coefficient at the center is an ordinary limit.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Filter Set Metric FourierTransform
open scoped Topology FourierTransform ContDiff Classical NNReal

def atomRadius (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def atomBump (d n : ℕ) : ContDiffBump (0 : Space d) where
  rIn := atomRadius (n+1)
  rOut := atomRadius n
  rIn_pos := by unfold atomRadius; positivity
  rIn_lt_rOut := by
    simp only [atomRadius, pow_succ]
    linarith [show 0 < (1 / 2 : ℝ) ^ n by positivity]

/-- Real profile of the shrinking test at the given center. -/
def atomProfile {d : ℕ} (n : ℕ) (x y : Space d) : ℝ := atomBump d n (y - x)

/-- Smooth test supported in the radius `2⁻ⁿ` ball about `x`. -/
def atomTest {d : ℕ} (n : ℕ) (x : Space d) : SchwartzMap (Space d) ℂ :=
  let b := atomBump d n
  let f := Complex.ofRealCLM ∘ b
  let hc : HasCompactSupport f := b.hasCompactSupport.comp_left rfl
  (SchwartzMap.compSubConstCLM ℂ x) (hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff))

theorem atomTest_apply {d : ℕ} (n : ℕ) (x y : Space d) :
    atomTest n x y = (atomProfile n x y : ℂ) := rfl

theorem atomProfile_bounds {d : ℕ} (n : ℕ) (x y : Space d) :
    0 ≤ atomProfile n x y ∧ atomProfile n x y ≤ 1 := ⟨(atomBump d n).nonneg, (atomBump d n).le_one⟩

theorem atomProfile_support {d : ℕ} (n : ℕ) (x y : Space d) (h : atomRadius n ≤ dist y x) :
    atomProfile n x y = 0 := (atomBump d n).zero_of_le_dist (by simpa [dist_eq_norm, atomBump] using h)

theorem atomProfile_decreasing {d : ℕ} (n : ℕ) (x y : Space d) :
    atomProfile (n+1) x y ≤ atomProfile n x y := by
  by_cases h : atomRadius (n+1) ≤ dist y x
  · rw [atomProfile_support _ _ _ h]
    exact (atomProfile_bounds ..).1
  · have hone : atomProfile n x y = 1 := (atomBump d n).one_of_mem_closedBall (by
      simpa only [atomBump, mem_closedBall, dist_zero_right, ← dist_eq_norm] using (le_of_not_ge h))
    rw [hone]
    exact (atomProfile_bounds ..).2

theorem atomTest_self {d : ℕ} (n : ℕ) (x : Space d) : atomTest n x x = 1 := by
  rw [atomTest_apply, atomProfile, sub_self, (atomBump d n).one_of_mem_closedBall
    (by simpa using (atomBump d n).rIn_pos.le)]
  norm_num

theorem norm_atomTest_le {d : ℕ} (n : ℕ) (x y : Space d) : ‖atomTest n x y‖ ≤ 1 := by
  simp only [atomTest_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (atomProfile_bounds ..).1]
  exact (atomProfile_bounds ..).2

theorem dist_lt_atomRadius_of_ne {d : ℕ} {n : ℕ} {x y : Space d} (h : atomTest n x y ≠ 0) :
    dist y x < atomRadius n := by
  by_contra! hle
  exact h (by simp [atomTest_apply, atomProfile_support n x y hle])

private def alignPhase (w : ℂ) : ℂ := (‖w‖ : ℂ) / w

private theorem norm_alignPhase_le (w : ℂ) : ‖alignPhase w‖ ≤ 1 := by
  by_cases hw : w = 0 <;> simp [alignPhase, hw]

private theorem alignPhase_mul (w : ℂ) : alignPhase w * w = (‖w‖ : ℂ) := by
  by_cases hw : w = 0 <;> simp [alignPhase, hw]

/-- A local sup norm bound implies convergence of the shrinking-test values
at a single site, for complex linear functionals. -/
theorem exists_atomTest_limit {d : ℕ} (L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ) (x : Space d)
    (M : ℝ) (hM : ∀ φ : SchwartzMap (Space d) ℂ, (∀ y, ‖φ y‖ ≤ 1) →
      (∀ y, φ y ≠ 0 → dist y x ≤ 1) → ‖L φ‖ ≤ M) :
    ∃ z : ℂ, Tendsto (fun n => L (atomTest n x)) atTop (𝓝 z) := by
  let Δ (n : ℕ) := atomTest n x - atomTest (n+1) x
  have hΔ (n : ℕ) (y : Space d) : ‖Δ n y‖ = atomProfile n x y - atomProfile (n+1) x y := by
    simp only [Δ, sub_apply, atomTest_apply, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (atomProfile_decreasing ..))]
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  apply summable_of_sum_range_le (c := M) (fun _ => dist_nonneg)
  intro N
  let Φ := ∑ n ∈ Finset.range N, alignPhase (L (Δ n)) • Δ n
  have hΦ (y : Space d) : ‖Φ y‖ ≤ atomProfile 0 x y - atomProfile N x y := by
    change ‖(∑ n ∈ Finset.range N, alignPhase (L (Δ n)) • Δ n : SchwartzMap _ ℂ) y‖ ≤ _
    rw [sum_apply, ← Finset.sum_range_sub' (fun n => atomProfile n x y)]
    apply norm_sum_le_of_le
    intro n _
    rw [smul_apply, norm_smul, ← hΔ]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alignPhase_le _)
  have hbound := hM Φ (fun y => (hΦ y).trans (by
    linarith [(atomProfile_bounds 0 x y).2, (atomProfile_bounds N x y).1])) (by
      intro y hy
      by_contra! hout
      have hz := atomProfile_support 0 x y (by simpa [atomRadius] using hout.le)
      have h := hΦ y
      rw [hz] at h
      linarith [norm_pos_iff.mpr hy, (atomProfile_bounds N x y).1])
  have heq : L Φ = ((∑ n ∈ Finset.range N, ‖L (Δ n)‖ : ℝ) : ℂ) := by
    simp [Φ, map_sum, alignPhase_mul]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at hbound
  simpa only [Δ, map_sub, dist_eq_norm] using hbound

/-- Translation-uniform local sup norm bounds on Schwartz tests supported
in a ball, allowing the bound to depend on its radius. -/
def HasLocalTestBounds {d : ℕ} (L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ) : Prop :=
  ∀ r : ℝ, ∃ M : ℝ≥0, ∀ c : Space d, ∀ φ : SchwartzMap (Space d) ℂ,
    (∀ z, ‖φ z‖ ≤ 1) → (∀ z, φ z ≠ 0 → dist z c ≤ r) → ‖L φ‖ ≤ M

/-- The coefficient detected at a point by the nested tests. -/
def testAtom {d : ℕ} (L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ) (x : Space d) : ℂ :=
  limUnder atTop fun n => L (atomTest n x)

theorem tendsto_testAtom {d : ℕ} {L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ}
    (hL : HasLocalTestBounds L) (x : Space d) :
    Tendsto (fun n => L (atomTest n x)) atTop (𝓝 (testAtom L x)) := by
  obtain ⟨M, hM⟩ := hL 1
  exact tendsto_nhds_limUnder (exists_atomTest_limit L x M (hM x))

theorem atomRadius_tendsto : Tendsto atomRadius atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The sum of the magnitudes of the extracted coefficients on a finite set
in a translated ball is bounded independently of that finite set. -/
theorem testAtom_variation_on_ball {d : ℕ} {L : SchwartzMap (Space d) ℂ →ₗ[ℂ] ℂ}
    (hL : HasLocalTestBounds L) (r : ℝ) :
    ∃ M : ℝ≥0, ∀ {ι : Type} [Fintype ι] (s : ι ↪ Space d) (c : Space d),
      (∀ i, dist (s i) c ≤ r) → ∑ i, ‖testAtom L (s i)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hL (r+1)
  refine ⟨M, fun {ι} _ s c hs => ?_⟩
  have hsep : ∀ᶠ n in atTop, ∀ i j, i ≠ j → 2 * atomRadius n < dist (s i) (s j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact .of_forall fun _ h => (h hij).elim
    · have hlim : Tendsto (fun n => 2 * atomRadius n) atTop (𝓝 0) := by
        simpa using atomRadius_tendsto.const_mul 2
      exact (hlim.eventually_lt_const (dist_pos.mpr (s.injective.ne hij))).mono fun _ hn _ => hn
  apply le_of_tendsto (tendsto_finsetSum Finset.univ (fun i _ => (tendsto_testAtom hL (s i)).norm))
  filter_upwards [hsep] with n hn
  let ψ (i : ι) := alignPhase (L (atomTest n (s i))) • atomTest n (s i)
  let Φ := ∑ i, ψ i
  have hv (y : Space d) : Φ y = ∑ i, ψ i y := sum_apply ..
  have hz (y : Space d) (i : ι) (h : atomTest n (s i) y = 0) : ψ i y = 0 := by simp [ψ, h]
  have htest := hM c Φ (fun y => by
    rw [hv]
    by_cases hex : ∃ i, atomTest n (s i) y ≠ 0
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · change ‖alignPhase _ • (atomTest n (s i) y : ℂ)‖ ≤ 1
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_alignPhase_le _)).trans (norm_atomTest_le ..)
      · intro j _ hji
        apply hz
        by_contra! hj
        have htri := dist_triangle (s j) y (s i)
        rw [dist_comm (s j) y] at htri
        linarith [hn j i hji, dist_lt_atomRadius_of_ne hj, dist_lt_atomRadius_of_ne hi]
      · simp
    · push Not at hex
      simp [fun i => hz y i (hex i)]) (fun y hy => by
        by_contra! hout
        apply hy
        rw [hv]
        apply Finset.sum_eq_zero
        intro i _
        apply hz
        by_contra! hi
        have hr : atomRadius n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith [dist_lt_atomRadius_of_ne hi, dist_triangle y (s i) c, hs i])
  have heq : L Φ = ((∑ i, ‖L (atomTest n (s i))‖ : ℝ) : ℂ) := by simp [Φ, ψ, map_sum, alignPhase_mul]
  simpa only [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] using htest

/-- Extend an atomic coefficient by zero to the whole ambient space. -/
def recordWeight {d : ℕ} {B : Set (Space d)} (b : B → ℂ) (x : Space d) : ℂ :=
  if hx : x ∈ B then b ⟨x, hx⟩ else 0

/-- The shrinking test eventually gives the actual coefficient on a uniformly
discrete record, including the value zero at every point outside the record. -/
theorem eventually_atomTest_eq_weight {d : ℕ} {ν : TemperedDistribution (Space d) ℂ}
    {B : Set (Space d)} {b : B → ℂ} (hν : HasLocallyAtomicExpansion ν B b)
    (hB : UniformlyDiscrete B) (x : Space d) :
    ∀ᶠ n in atTop, ν (atomTest n x) = recordWeight b x := by
  obtain ⟨η, hη, hsep⟩ := hB
  have hglobal := (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hν ⟨η, hη, hsep⟩).2
  by_cases hx : x ∈ B
  · filter_upwards [atomRadius_tendsto.eventually_lt_const hη] with n hn
    let y : B := ⟨x, hx⟩
    have hsingle := (hglobal (atomTest n x)).unique (hasSum_single y (fun v hv => by
      have hne : v.val ≠ x := fun h => hv (Subtype.ext h)
      simp [atomTest_apply, atomProfile_support n x v.val (hn.le.trans (hsep v.property hx hne))]))
    simpa [recordWeight, hx, y, atomTest_self] using hsingle
  · have hc := (Metric.isClosed_of_pairwise_le_dist hη hsep).isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hc x hx
    filter_upwards [atomRadius_tendsto.eventually_lt_const hr] with n hn
    have hz (v : B) : atomTest n x v.val = 0 := by
      rw [atomTest_apply, atomProfile_support]
      · simp
      · by_contra! h
        exact hball (Metric.mem_ball.mpr (h.trans hn)) v.property
    simpa [recordWeight, hx, hz] using (hglobal (atomTest n x)).tsum_eq.symm

/-- Fourier transforms of physical restrictions to finite lattice
intersections have well-defined coefficients at every spectral point. -/
theorem restrictedFourierLinear_hasLocalTestBounds {d : ℕ} {ι : Type} [Fintype ι]
    {μ : TemperedDistribution (Space d) ℂ} {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (t : ι → Space d) (T : ι → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0) :
    HasLocalTestBounds (restrictedFourierLinear hμ hA (⋂ j, range (latticeSite (t j) (T j)))) := by
  intro r
  obtain ⟨M, hM⟩ := restrictedTransform_local_bound hμ hA hν hB r
  exact ⟨M, hM t T hT⟩

end
end MeyerGeneralProblem.LevOlevskii
