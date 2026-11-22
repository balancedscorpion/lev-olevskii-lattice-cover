module

public import AppendixA.UnitSpecialization

/-!
# Induction on the number of variables in a unit equation

On a proper hyperplane, a minimal vanishing subsum supplies a normalized
equation for coordinate ratios. Fixing one of these ratios permits merging
two terms in the original equation. Both equations involve fewer variables.
-/

@[expose] public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Finset
open scoped Classical

private def wordOn {ι ρ K : Type} [Fintype ρ] [Field K] (F : Finset ι)
    (g : ρ → ι → Kˣ) (e : ρ → ℤ) (i : F) := unitWord g e i.val

private def partialSum {ι K : Type} [Field K] (c x : ι → K) (J : Finset ι) :=
  ∑ i ∈ J, c i * x i

private def nondegenerateOn {ι K : Type} [Field K] (F : Finset ι) (c x : ι → K) : Prop :=
  partialSum c x F = 1 ∧ ∀ J ⊆ F, J.Nonempty → partialSum c x J ≠ 0

private def boundedOn {ι ρ : Type} [Fintype ρ] (F : Finset ι) (N : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : ι → K) (g : ρ → ι → Kˣ)
    (E : Finset (ρ → ℤ)), (∀ e ∈ E, nondegenerateOn F c (unitWord g e)) →
    (E.image (wordOn F g)).card ≤ N

private theorem count_cover {α κ β : Type*} [DecidableEq β] (E : Finset α) (I : Finset κ)
    (parts : κ → Finset α) (f : α → β) (N : ℕ)
    (hcover : ∀ x ∈ E, ∃ k ∈ I, x ∈ parts k)
    (hbound : ∀ k ∈ I, ((parts k).image f).card ≤ N) :
    (E.image f).card ≤ I.card * N := by
  have hsub : E.image f ⊆ I.biUnion (fun k => (parts k).image f) := by
    rintro _ hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    obtain ⟨k,hk,hp⟩ := hcover x hx
    exact mem_biUnion.mpr ⟨k,hk,mem_image_of_mem _ hp⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _ ∈ I, N := sum_le_sum hbound
    _ = _ := by simp

private theorem word_ne_zero {ι ρ K : Type} [Fintype ρ] [Field K]
    (g : ρ → ι → Kˣ) (e : ρ → ℤ) (i : ι) : unitWord g e i ≠ 0 := Units.ne_zero _

private theorem word_ratio {ι ρ K : Type} [Fintype ρ] [Field K] (g : ρ → ι → Kˣ)
    (a : ι) (e : ρ → ℤ) (i : ι) :
    unitWord (fun k j => g k j / g k a) e i = unitWord g e i / unitWord g e a := by
  simp [unitWord,div_zpow,Finset.prod_div_distrib]

private theorem normalize_block {ι K : Type} [Field K] {J : Finset ι} {a : ι} (ha : a ∈ J)
    (b x : ι → K) (hb : b a ≠ 0) (hx : x a ≠ 0) (hz : partialSum b x J = 0)
    (hmin : ∀ L ⊂ J, L.Nonempty → partialSum b x L ≠ 0) :
    nondegenerateOn (J.erase a) (fun i => -b i / b a) (fun i => x i / x a) := by
  have he (L : Finset ι) : partialSum (fun i => -b i / b a) (fun i => x i / x a) L =
      -partialSum b x L / (b a * x a) := by
    simp only [partialSum,← sum_neg_distrib,sum_div]
    exact sum_congr rfl fun i _ => by ring
  constructor
  · rw [he,div_eq_one_iff_eq (mul_ne_zero hb hx)]
    have hadd := sum_erase_add (f := fun i => b i * x i) J ha
    change partialSum b x (J.erase a) + b a * x a = partialSum b x J at hadd
    rw [hz] at hadd
    linear_combination -hadd
  · intro L hL hn
    rw [he]
    exact div_ne_zero (neg_ne_zero.mpr (hmin L (lt_of_le_of_lt hL (erase_ssubset ha)) hn)) (mul_ne_zero hb hx)

private theorem merge_terms {ι K : Type} [Field K] {F : Finset ι} {a p : ι}
    (ha : a ∈ F) (hp : p ∈ F.erase a) (c x : ι → K) (q : K) (hq : x p = q * x a)
    (h : nondegenerateOn F c x) :
    nondegenerateOn (F.erase p) (fun i => if i = a then c a + c p * q else c i) x := by
  have hpa := (mem_erase.mp hp).1
  let merged (i : ι) := if i = a then c a + c p * q else c i
  have expand (L : Finset ι) (hL : L ⊆ F.erase p) :
      partialSum merged x L = partialSum c x (if a ∈ L then insert p L else L) := by
    by_cases hal : a ∈ L
    · have hpl : p ∉ L := fun hh => (mem_erase.mp (hL hh)).1 rfl
      rw [ite_eq_left hal]
      unfold partialSum
      rw [sum_insert hpl,← sum_erase_add L (fun i => merged i * x i) hal,
        ← sum_erase_add L (fun i => c i * x i) hal]
      have he : ∑ i ∈ L.erase a, merged i * x i = ∑ i ∈ L.erase a, c i * x i :=
        sum_congr rfl fun i hi => by simp [merged,(mem_erase.mp hi).1]
      rw [he,hq]
      simp [merged]
      ring
    · rw [ite_eq_right hal]
      exact sum_congr rfl fun i hi => by simp [merged,show i ≠ a from fun e => hal (e ▸ hi)]
  have haf : a ∈ F.erase p := mem_erase.mpr ⟨Ne.symm hpa,ha⟩
  constructor
  · rw [expand _ (Subset.refl _),ite_eq_left haf,insert_erase (mem_of_mem_erase hp)]
    exact h.1
  · intro L hL hn
    rw [expand _ hL]
    by_cases hal : a ∈ L
    · rw [ite_eq_left hal]
      exact h.2 _ (insert_subset (mem_of_mem_erase hp) (hL.trans (erase_subset ..))) (insert_nonempty ..)
    · rw [ite_eq_right hal]
      exact h.2 _ (hL.trans (erase_subset ..)) hn

private theorem block_bound {ι ρ K : Type} [Fintype ρ] [Field K] [NumberField K]
    {F J : Finset ι} (hJF : J ⊆ F) {a p : ι} (ha : a ∈ J) (hp : p ∈ J.erase a)
    (c b : ι → K) (hb : b a ≠ 0) (g : ρ → ι → Kˣ) (E : Finset (ρ → ℤ))
    (hn : ∀ e ∈ E, nondegenerateOn F c (unitWord g e))
    (hz : ∀ e ∈ E, partialSum b (unitWord g e) J = 0)
    (hm : ∀ e ∈ E, ∀ L ⊂ J, L.Nonempty → partialSum b (unitWord g e) L ≠ 0)
    {N : ℕ} (hsmall : ∀ L ⊂ F, boundedOn (ρ := ρ) L N) :
    (E.image (wordOn F g)).card ≤ N*N := by
  let gr (k : ρ) (i : ι) := g k i / g k a
  let proj := wordOn (J.erase a) gr
  have hn' (e) (he : e ∈ E) : nondegenerateOn (J.erase a) (fun i => -b i / b a) (unitWord gr e) := by
    have heq : unitWord gr e = fun i => unitWord g e i / unitWord g e a := funext (word_ratio g a e)
    rw [heq]
    exact normalize_block ha b _ hb (word_ne_zero g e a) (hz e he) (hm e he)
  have hr := hsmall _ (lt_of_lt_of_le (erase_ssubset ha) hJF) K _ gr E hn'
  let I := E.image proj
  let part (v : (J.erase a) → K) := E.filter fun e => proj e = v
  have hpart (v) (_ : v ∈ I) : ((part v).image (wordOn F g)).card ≤ N := by
    let q := v ⟨p,hp⟩
    have hrq (e) (he : e ∈ part v) : unitWord g e p = q * unitWord g e a := by
      apply (div_eq_iff (word_ne_zero g e a)).mp
      rw [← word_ratio g a]
      exact congrFun (mem_filter.mp he).2 ⟨p,hp⟩
    let merged (i : ι) := if i = a then c a + c p * q else c i
    have hpF : p ∈ F := hJF (mem_of_mem_erase hp)
    have hnM (e) (he : e ∈ part v) := merge_terms (hJF ha)
      (mem_erase.mpr ⟨(mem_erase.mp hp).1,hpF⟩) c _ q (hrq e he) (hn e (mem_filter.mp he).1)
    have hM := hsmall _ (erase_ssubset hpF) K merged g (part v) hnM
    let restore (x : (F.erase p) → K) (i : F) := if hi : i.val = p then
      q * x ⟨a,mem_erase.mpr ⟨(mem_erase.mp hp).1.symm,hJF ha⟩⟩ else x ⟨i.val,mem_erase.mpr ⟨hi,i.property⟩⟩
    have hsub : (part v).image (wordOn F g) ⊆ ((part v).image (wordOn (F.erase p) g)).image restore := by
      intro _ hy
      obtain ⟨e,he,rfl⟩ := mem_image.mp hy
      refine mem_image.mpr ⟨_,mem_image_of_mem _ he,?_⟩
      funext i
      by_cases hi : i.val = p
      · simpa only [restore,dite_eq_left hi,wordOn,hi] using (hrq e he).symm
      · simp only [restore,dite_eq_right hi,wordOn]
    exact (card_le_card hsub).trans (card_image_le.trans hM)
  have hcount := count_cover E I part (wordOn F g) N
    (fun e he => ⟨proj e,mem_image_of_mem _ he,mem_filter.mpr ⟨he,rfl⟩⟩) hpart
  exact hcount.trans (Nat.mul_le_mul_right N hr)

private def isBlock {ι K : Type} [Field K] (F J : Finset ι) (b x : ι → K) : Prop :=
  J ⊆ F ∧ J.Nontrivial ∧ (∀ i ∈ J, b i ≠ 0) ∧ partialSum b x J = 0 ∧
    ∀ L ⊂ J, L.Nonempty → partialSum b x L ≠ 0

private theorem exists_block {ι K : Type} [Field K] {F : Finset ι} (b x : ι → K)
    (hb : ∃ i ∈ F, b i ≠ 0) (hx : ∀ i, x i ≠ 0) (hz : partialSum b x F = 0) :
    ∃ J ∈ F.powerset, isBlock F J b x := by
  let B := F.filter (fun i => b i ≠ 0)
  have he : partialSum b x B = partialSum b x F := by
    apply sum_subset (filter_subset ..)
    intro i hi hout
    have hbi : b i = 0 := by simpa [B,hi] using hout
    rw [hbi,zero_mul]
  obtain ⟨j,hj,hbj⟩ := hb
  let P (J : Finset ι) := J ⊆ B ∧ J.Nonempty ∧ partialSum b x J = 0
  obtain ⟨J,hJ⟩ := exists_minimal_of_wellFoundedLT P
    ⟨B,Subset.refl _,⟨j,mem_filter.mpr ⟨hj,hbj⟩⟩,he.trans hz⟩
  obtain ⟨hJB,⟨a,ha⟩,hzero⟩ := hJ.prop
  have hs (i) (hi : i ∈ J) : b i ≠ 0 := (mem_filter.mp (hJB hi)).2
  have hn : J.Nontrivial := (nontrivial_iff_ne_singleton ha).mpr fun hsing => by
    have heq : b a * x a = 0 := by simpa [partialSum,hsing] using hzero
    exact (mul_ne_zero (hs a ha) (hx a)) heq
  have hJF := hJB.trans (filter_subset ..)
  exact ⟨J,mem_powerset.mpr hJF,hJF,hn,hs,hzero,fun L hL hnL hL0 =>
    hJ.not_prop_of_lt hL ⟨hL.le.trans hJB,hnL,hL0⟩⟩

private theorem hyperplane_bound {ι ρ K : Type} [Fintype ρ] [Field K] [NumberField K]
    {F : Finset ι} (c b : ι → K) (hb : ∃ i ∈ F, b i ≠ 0) (g : ρ → ι → Kˣ) (E : Finset (ρ → ℤ))
    (hn : ∀ e ∈ E, nondegenerateOn F c (unitWord g e))
    (hz : ∀ e ∈ E, partialSum b (unitWord g e) F = 0)
    {N : ℕ} (hsmall : ∀ L ⊂ F, boundedOn (ρ := ρ) L N) :
    (E.image (wordOn F g)).card ≤ F.powerset.card * (N*N) := by
  let part (J : Finset ι) := E.filter fun e => isBlock F J b (unitWord g e)
  apply count_cover E F.powerset part (wordOn F g) (N*N)
  · intro e he
    obtain ⟨J,hJ,hbJ⟩ := exists_block b _ hb (word_ne_zero g e) (hz e he)
    exact ⟨J,hJ,mem_filter.mpr ⟨he,hbJ⟩⟩
  · intro J hJ
    rcases (part J).eq_empty_or_nonempty with hempty | ⟨e₀,he₀⟩
    · simp [hempty]
    have hl (e) (he : e ∈ part J) := (mem_filter.mp he).2
    have hJ₀ := hl e₀ he₀
    obtain ⟨a,ha,p,hp,hap⟩ := hJ₀.2.1
    exact block_bound hJ₀.1 ha (mem_erase.mpr ⟨hap.symm,hp⟩) c b (hJ₀.2.2.1 a ha) g (part J)
      (fun e he => hn e (mem_filter.mp he).1) (fun e he => (hl e he).2.2.2.1)
      (fun e he => (hl e he).2.2.2.2) hsmall

/-- For the normalized equation on a torus over a number field, the solutions
in a group with a specified number of generators lie in a bounded number of
proper linear hyperplanes. The bound is uniform over the fields and data. -/
def NumberFieldUnitHyperplaneBound : Prop :=
  ∀ (ι ρ : Type) [Fintype ι] [Fintype ρ], 2 ≤ Fintype.card ι → ∃ M : ℕ,
    ∀ (K : Type) [Field K] [NumberField K] (c : ι → K), (∀ i, c i ≠ 0) →
      ∀ g : ρ → ι → Kˣ, ∃ b : Fin M → ι → K, (∀ j, b j ≠ 0) ∧
        ∀ e, (∑ i, c i * unitWord g e i) = 1 → ∃ j, (∑ i, b j i * unitWord g e i) = 0

private theorem bound_on_of_hyperplanes (h : NumberFieldUnitHyperplaneBound) {ι ρ : Type} [Fintype ρ]
    (F : Finset ι) : ∃ N, boundedOn (ρ := ρ) F N := by
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hcard : F.card ≤ 1
    · refine ⟨1,?_⟩
      intro K _ _ c g E hn
      apply card_le_one.mpr
      intro _ hy _ hz
      obtain ⟨t,ht,rfl⟩ := mem_image.mp hy
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
      funext i
      have heq := eq_singleton_iff_unique_mem.mpr ⟨i.property,fun j hj => card_le_one.mp hcard _ hj _ i.property⟩
      have hsol (e) (he : e ∈ E) : c i.val * unitWord g e i.val = 1 := by
        simpa only [partialSum,heq,sum_singleton] using (hn e he).1
      exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one (hsol t ht)) ((hsol t ht).trans (hsol v hv).symm)
    obtain ⟨M,hM⟩ := h F ρ (by simpa using show 2 ≤ F.card by omega)
    let small := F.powerset.filter fun L => L ⊂ F
    have hs (L : small) := ih L.val (mem_filter.mp L.property).2
    choose n hn using hs
    let N := ∑ L : small, n L
    have hsmall (L : Finset ι) (hl : L ⊂ F) : boundedOn (ρ := ρ) L N := by
      let l : small := ⟨L,mem_filter.mpr ⟨mem_powerset.mpr hl.le,hl⟩⟩
      intro K _ _ c g E he
      exact (hn l K c g E he).trans (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (mem_univ l))
    refine ⟨M * (F.powerset.card * (N*N)),?_⟩
    intro K _ _ c g E hnorm
    rcases E.eq_empty_or_nonempty with rfl | ⟨e₀,he₀⟩
    · simp
    have hc (i : F) : c i.val ≠ 0 := by
      intro hci
      exact (hnorm e₀ he₀).2 {i.val} (singleton_subset_iff.mpr i.property) (singleton_nonempty _)
        (by simp [partialSum,hci])
    let g' (k : ρ) (i : F) := g k i.val
    obtain ⟨B,hB,hcover⟩ := hM K (fun i => c i.val) hc g'
    let b (j : Fin M) (i : ι) := if hi : i ∈ F then B j ⟨i,hi⟩ else 0
    have hb (j : Fin M) : ∃ i ∈ F, b j i ≠ 0 := by
      by_contra! hz
      apply hB j
      funext i
      simpa [b,i.property] using hz i.val i.property
    have hre (j e) : partialSum (b j) (unitWord g e) F = ∑ i, B j i * unitWord g' e i := by
      rw [partialSum,← sum_attach F]
      simp [b,g',unitWord]
    let part (j : Fin M) := E.filter fun e => partialSum (b j) (unitWord g e) F = 0
    rw [← Fintype.card_fin M,← Finset.card_univ]
    apply count_cover E univ part (wordOn F g) (F.powerset.card * (N*N))
    · intro e he
      have heq := (hnorm e he).1
      rw [partialSum,← sum_attach F] at heq
      obtain ⟨j,hj⟩ := hcover e (by simpa [g',unitWord] using heq)
      exact ⟨j,mem_univ _,mem_filter.mpr ⟨he,(hre j e).trans hj⟩⟩
    · intro j _
      exact hyperplane_bound c (b j) (hb j) g (part j) (fun e he => hnorm e (mem_filter.mp he).1)
        (fun e he => (mem_filter.mp he).2) hsmall

/-- The uniform hyperplane cover implies a uniform bound for distinct
nondegenerate solutions, by induction on the set of coordinates. -/
theorem numberFieldBound_of_hyperplanes (h : NumberFieldUnitHyperplaneBound) : NumberFieldUnitEquationBound := by
  intro ι ρ _ _
  obtain ⟨N,hN⟩ := bound_on_of_hyperplanes (ρ := ρ) h (univ : Finset ι)
  refine ⟨N,?_⟩
  intro K _ _ c g e hfamily
  let E := univ.image e
  have hn (d) (hd : d ∈ E) : nondegenerateOn univ c (unitWord g d) := by
    obtain ⟨t,_,rfl⟩ := mem_image.mp hd
    exact ⟨hfamily.2.2.1 t,fun J _ => hfamily.2.2.2 t J⟩
  have hcard := hN K c g E hn
  let f (t : Fin (N+1)) := wordOn (univ : Finset ι) g (e t)
  have hf : Function.Injective f := by
    intro t v he
    apply hfamily.2.1
    funext i
    exact congrFun he ⟨i,mem_univ i⟩
  have he : E.image (wordOn (univ : Finset ι) g) = univ.image f := image_image ..
  rw [he,card_image_of_injective _ hf,card_univ,Fintype.card_fin] at hcard
  omega

/-- Proper-hyperplane bounds for unit equations over number fields suffice
for the complex Fourier-pair conclusions of Theorem A.1. -/
theorem theoremA1_of_unitHyperplanes (h : NumberFieldUnitHyperplaneBound) : theoremA1Statement :=
  theoremA1_of_numberFieldBound (numberFieldBound_of_hyperplanes h)

end
end MeyerGeneralProblem.LevOlevskii
