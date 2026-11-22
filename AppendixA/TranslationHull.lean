module

public import AppendixA.PhaseLimits
public import Mathlib.Topology.Ultrafilter

/-!
# Limits of translated crystalline records

Each translated atom is assigned a label in the unit shell containing it.
Uniform packing supplies finitely many labels per shell. Taking limits of
the positions and weights at each label preserves separation wherever the
limiting weight is nonzero.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Filter Metric FourierTransform
open scoped Topology FourierTransform

private abbrev Label (N : ℕ → ℕ) := (n : ℕ) × Fin (N n)

private structure ShellRecord (d : ℕ) (N : ℕ → ℕ) (η C : ℝ) where
  entry : Label N → Space d × ℂ
  position_bound : ∀ j, ‖(entry j).1‖ ≤ (j.1 : ℝ) + 1
  weight_bound : ∀ j, ‖(entry j).2‖ ≤ C
  shell : ∀ j, (entry j).2 = 0 ∨ (j.1 : ℝ) ≤ ‖(entry j).1‖
  separated : ∀ i j, i ≠ j → (entry i).2 = 0 ∨ (entry j).2 = 0 ∨
    η ≤ dist (entry i).1 (entry j).1

private theorem translated_shell_records {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {η C : ℝ} (hη : 0 < η) (hA : A.Pairwise fun x y => η ≤ dist x y)
    (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C)
    {μ : TemperedDistribution (Space d) ℂ} (hμ : HasAtomicExpansion μ A a) :
    ∃ (N : ℕ → ℕ) (P : Space d → ShellRecord d N η C),
      ∀ t (φ : SchwartzMap (Space d) ℂ), HasSum
        (fun j => ((P t).entry j).2 * φ ((P t).entry j).1)
        (μ ((SchwartzMap.compSubConstCLM ℂ t) φ)) := by
  classical
  choose N hN using fun n : ℕ => uniformlyDiscrete_ball_embeddings ⟨η,hη,hA⟩ ((n : ℝ)+1)
  suffices ∀ t : Space d, ∃ P : ShellRecord d N η C, ∀ φ : SchwartzMap (Space d) ℂ,
      HasSum (fun j => (P.entry j).2 * φ (P.entry j).1)
        (μ ((SchwartzMap.compSubConstCLM ℂ t) φ)) by
    choose P hP using this
    exact ⟨N,P,hP⟩
  intro t
  let X (n : ℕ) := {i : A // dist i.val t ≤ (n : ℝ)+1}
  let idx (i : A) := ⌊‖i.val-t‖⌋₊
  have hupper (i : A) : dist i.val t ≤ (idx i : ℝ)+1 := by
    rw [dist_eq_norm]; exact (Nat.lt_floor_add_one _).le
  let f : A ↪ (n : ℕ) × X n := ⟨fun i => ⟨idx i,i,hupper i⟩, fun i k h =>
    congrArg (fun z : (n : ℕ) × X n => z.2.val) h⟩
  let e : A ↪ Label N := f.trans (Function.Embedding.sigmaMap (Function.Embedding.refl ℕ)
    (fun n => (hN n t).some))
  let entry := Function.extend e (fun i : A => (i.val-t, a i)) (fun _ => (0,0))
  have he (i : A) : entry (e i) = (i.val-t,a i) := e.injective.extend_apply ..
  have hzero (j : Label N) (hj : j ∉ range e) : entry j = (0,0) :=
    Function.extend_apply' _ _ _ hj
  let P : ShellRecord d N η C := {
    entry := entry
    position_bound := by
      intro j
      by_cases hj : j ∈ range e
      · obtain ⟨i,rfl⟩ := hj
        rw [he]; exact hupper i
      · rw [hzero j hj]; simp; positivity
    weight_bound := by
      intro j
      by_cases hj : j ∈ range e
      · obtain ⟨i,rfl⟩ := hj; rw [he]; exact ha i
      · rw [hzero j hj]; simpa using hC
    shell := by
      intro j
      by_cases hj : j ∈ range e
      · obtain ⟨i,rfl⟩ := hj; rw [he]; exact Or.inr (Nat.floor_le (norm_nonneg _))
      · rw [hzero j hj]; exact Or.inl rfl
    separated := by
      intro i j hij
      by_cases hi : i ∈ range e
      · obtain ⟨x,rfl⟩ := hi
        by_cases hj : j ∈ range e
        · obtain ⟨y,rfl⟩ := hj; simp only [he, dist_sub_right]
          exact Or.inr (Or.inr (hA x.property y.property (fun h => hij (congrArg e (Subtype.ext h)))))
        · exact Or.inr (Or.inl (congrArg Prod.snd (hzero j hj)))
      · exact Or.inl (congrArg Prod.snd (hzero i hi)) }
  refine ⟨P, fun φ => ?_⟩
  apply (e.injective.hasSum_iff (fun j hj => by change (entry j).2 * φ (entry j).1 = 0; simp [hzero j hj])).mp
  simpa only [Function.comp_def, P, he, SchwartzMap.compSubConstCLM_apply] using
    hμ.2 ((SchwartzMap.compSubConstCLM ℂ t) φ)

private theorem shell_limit {α : Type*} {N : ℕ → ℕ} {d : ℕ} {η C : ℝ}
    (P : α → ShellRecord d N η C) (U : Ultrafilter α) :
    ∃ Q : ShellRecord d N η C, ∀ j, Tendsto (fun t => (P t).entry j) U (𝓝 (Q.entry j)) := by
  have hex (j : Label N) : ∃ x : Space d × ℂ,
      Tendsto (fun t => (P t).entry j) U (𝓝 x) := by
    let K := (closedBall (0 : Space d) ((j.1 : ℝ)+1)) ×ˢ (closedBall (0 : ℂ) C)
    have hK : IsCompact K := (isCompact_closedBall ..).prod (isCompact_closedBall ..)
    have hm : K ∈ U.map (fun t => (P t).entry j) := by
      change {t | (P t).entry j ∈ K} ∈ (U : Filter α)
      apply Filter.univ_mem'
      intro t
      exact ⟨by simpa using (P t).position_bound j, by simpa using (P t).weight_bound j⟩
    obtain ⟨x, _, hx⟩ := hK.ultrafilter_le_nhds' _ hm
    exact ⟨x, hx⟩
  choose q hq using hex
  refine ⟨{
    entry := q
    position_bound := fun j => le_of_tendsto' (hq j).fst_nhds.norm (fun t => (P t).position_bound j)
    weight_bound := fun j => le_of_tendsto' (hq j).snd_nhds.norm (fun t => (P t).weight_bound j)
    shell := ?_
    separated := ?_ }, hq⟩
  · intro j
    by_cases hj : (q j).2 = 0
    · exact Or.inl hj
    · refine Or.inr (ge_of_tendsto (hq j).fst_nhds.norm ?_)
      filter_upwards [(hq j).snd_nhds.eventually_ne hj] with t ht
      exact ((P t).shell j).resolve_left ht
  · intro i j hij
    by_cases hi : (q i).2 = 0
    · exact Or.inl hi
    by_cases hj : (q j).2 = 0
    · exact Or.inr (Or.inl hj)
    refine Or.inr (Or.inr (ge_of_tendsto ((hq i).fst_nhds.dist (hq j).fst_nhds) ?_))
    filter_upwards [(hq i).snd_nhds.eventually_ne hi, (hq j).snd_nhds.eventually_ne hj] with t hti htj
    exact (((P t).separated i j hij).resolve_left hti).resolve_left htj

/-- Only finitely many shell labels can contribute to a fixed compact test,
uniformly over the translation parameter and its limits. -/
private theorem finite_shell_test {d : ℕ} (N : ℕ → ℕ) {η C : ℝ}
    (φ : SchwartzMap (Space d) ℂ) (hc : HasCompactSupport φ) :
    ∃ T : Finset (Label N), ∀ (P : ShellRecord d N η C) j, j ∉ T →
      (P.entry j).2 * φ (P.entry j).1 = 0 := by
  classical
  obtain ⟨r, hr⟩ := hc.isBounded.subset_closedBall (0 : Space d)
  obtain ⟨K, hK⟩ := exists_nat_gt r
  refine ⟨(Finset.range K).sigma (fun n => (Finset.univ : Finset (Fin (N n)))), fun P j hj => ?_⟩
  have hn : K ≤ j.1 := by simpa using hj
  rcases P.shell j with h | h
  · rw [h, zero_mul]
  · suffices φ (P.entry j).1 = 0 by rw [this, mul_zero]
    by_contra hne
    have hle := hr (subset_tsupport _ hne)
    rw [mem_closedBall, dist_zero_right] at hle
    have hh : (K : ℝ) ≤ j.1 := by exact_mod_cast hn
    linarith

/-- Limits on compact tests of translates with bounded weights still have an
atomic expansion with the original separation. -/
theorem translated_limit_locally_atomic {d : ℕ} {μ μ' : TemperedDistribution (Space d) ℂ}
    {A : Set (Space d)} {a : A → ℂ} {η : ℝ} (hη : 0 < η)
    (hA : A.Pairwise fun x y => η ≤ dist x y) (hμ : HasLocallyAtomicExpansion μ A a)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (U : Ultrafilter (Space d))
    (hlim : ∀ φ : SchwartzMap (Space d) ℂ, HasCompactSupport φ →
      Tendsto (fun t => μ ((SchwartzMap.compSubConstCLM ℂ t) φ)) U (𝓝 (μ' φ))) :
    ∃ (A' : Set (Space d)) (a' : A' → ℂ), HasLocallyAtomicExpansion μ' A' a' ∧
      A'.Pairwise fun x y => η ≤ dist x y := by
  classical
  obtain ⟨C,hC⟩ := ha
  obtain ⟨N,P,hP⟩ := translated_shell_records hη hA (le_max_right C 0)
    (fun i => (hC i).trans (le_max_left C 0))
    (atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete hμ ⟨η,hη,hA⟩)
  obtain ⟨Q, hQ⟩ := shell_limit P U
  have htest (φ : SchwartzMap (Space d) ℂ) (hc : HasCompactSupport φ) :
      HasSum (fun j => (Q.entry j).2 * φ (Q.entry j).1) (μ' φ) := by
    obtain ⟨T,hT⟩ := finite_shell_test (η := η) (C := max C 0) N φ hc
    have hfinite (V : ShellRecord d N η (max C 0)) : HasSum (fun j => (V.entry j).2 * φ (V.entry j).1) (∑ j ∈ T, (V.entry j).2 * φ (V.entry j).1) :=
      hasSum_sum_of_ne_finset_zero (hT V)
    have h := tendsto_finsetSum T (fun j _ => (hQ j).snd_nhds.mul (φ.continuous.continuousAt.tendsto.comp (hQ j).fst_nhds))
    have he (t) := (hfinite (P t)).unique (hP t φ)
    have he' := tendsto_nhds_unique (h.congr he) (hlim φ hc)
    rw [← he']
    exact hfinite Q
  let J := {j : Label N // (Q.entry j).2 ≠ 0}
  let v (j : J) := (Q.entry j.val).1
  have hsep (i j : J) (hij : i ≠ j) : η ≤ dist (v i) (v j) :=
    ((Q.separated i.val j.val (fun e => hij (Subtype.ext e))).resolve_left i.property).resolve_left j.property
  have hv : Function.Injective v := by
    intro i j he
    by_contra hij
    have h := hsep i j hij
    rw [he, dist_self] at h
    exact hη.not_ge h
  let e := Equiv.ofInjective v hv
  let a' (x : range v) := (Q.entry (e.symm x).val).2
  refine ⟨range v, a', ⟨fun x => (e.symm x).property, fun φ hc => ?_⟩, ?_⟩
  · apply e.hasSum_iff.mp
    let F (j : Label N) := (Q.entry j).2 * φ (Q.entry j).1
    have hj : HasSum (fun j : J => F j.val) (μ' φ) :=
      (Subtype.val_injective.hasSum_iff (fun j h => by
        have hz : (Q.entry j).2 = 0 := by
          by_contra hn; exact h ⟨⟨j,hn⟩,rfl⟩
        simp [hz])).mpr (htest φ hc)
    exact hj.congr_fun fun j => by simp [a', F, e, v]
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ hij
    exact hsep i j (fun h => hij (congrArg v h))

/-- Every point of the closed translation orbit of the spectral phases is
realized by a Fourier pair. The physical separation is preserved and every
spectral coefficient is multiplied by its limiting phase. -/
theorem realize_spectral_phase_orbit {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ} {η : ℝ} (hη : 0 < η)
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : A.Pairwise fun x y => η ≤ dist x y)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (z : B → Circle)
    (hz : z ∈ closure (range (fun t : Space d => fun i : B => frequencyPhase i.val t))) :
    ∃ (μ' : TemperedDistribution (Space d) ℂ) (A' : Set (Space d)) (a' : A' → ℂ),
      HasLocallyAtomicExpansion μ' A' a' ∧ (A'.Pairwise fun x y => η ≤ dist x y) ∧
      HasAtomicExpansion (𝓕 μ') B (fun i => b i * (z i : ℂ)) := by
  let f (t : Space d) (i : B) := frequencyPhase i.val t
  obtain ⟨V,hV,hVz⟩ := mem_closure_iff_ultrafilter.mp hz
  let U := V.map (Function.invFun f)
  have hmap : Tendsto f U (𝓝 z) := by
    have he : f ∘ Function.invFun f =ᶠ[(V : Filter (B → Circle))] id :=
      Filter.mem_of_superset hV fun y hy => Function.invFun_eq hy
    change Filter.map f (Filter.map (Function.invFun f) (V : Filter (B → Circle))) ≤ _
    rw [Filter.map_map, Filter.map_congr he, Filter.map_id]
    exact hVz
  have hz' : ∀ i : B, Tendsto (fun t => frequencyPhase i.val t) U (𝓝 (z i)) :=
    tendsto_pi_nhds.mp hmap
  obtain ⟨μ',hν',hlim⟩ := spectral_phase_limit hμ ⟨η,hη,hA⟩ hν hB z hz'
  obtain ⟨A',a',hμ',hsep⟩ := translated_limit_locally_atomic hη hA hμ
    (atomic_coefficients_uniformly_bounded hμ ⟨η,hη,hA⟩ hν hB) U (fun φ _ => hlim φ)
  exact ⟨μ',A',a',hμ',hsep,hν'⟩

end
end MeyerGeneralProblem.LevOlevskii
