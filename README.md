# Theorem A.1 on crystalline measures

Martin’s Theorem A.1 holds in every positive dimension. If a crystalline measure and its Fourier transform have uniformly discrete sites, the measure is a finite sum of translated, modulated combs on full-rank lattices. Both sets of sites have finite lattice covers. The weights are complex and may approach zero. This answers the physical-support question posed by Lev and Olevskii in dimension at least two. [Martin, Appendix A](https://hexagonmath.org/pdf/2611.00744v2#page=12) · [Lev and Olevskii, §11.2(1)](https://arxiv.org/pdf/1512.08735v2#page=20)

| Lean declaration | Mathematical content |
| --- | --- |
| `theoremA1` | Unconditional proof of `theoremA1Statement`, including the comb decomposition and both lattice covers. Comparator checks this declaration. |
| `latticeCoverQuestion_holds` | The physical-support corollary in dimensions at least two, with the global atomic expansion and variation hypotheses of the source development. |

The weights at the specified sites are nonzero. Each comb has its own invertible matrix, shift, modulation and complex scalar. Its character is evaluated at the translated site. Contributions add where lattices overlap, and an empty sum represents the zero distribution.

## Proof

The covering argument uses finite generation and bounds on the rank of characters restricted to the support. A specialized form of Laurent’s torus theorem produces a finite coset cover. Each coset that spans physical space lies in a lattice translate by the character rank estimate. Recurrence removes the lower-dimensional pieces. The same argument applied to the inverse Fourier pair gives the spectral cover. Averaging over dual lattices, restricting to intersections and recovering the atomic coefficients then give the comb identity on all Schwartz tests.

For the arithmetic step, a specialization to a number field retains selected character values of infinite multiplicative order. The qualitative unit-equation theorem over that fixed number field puts the solutions on finitely many character level sets. Restriction to a level lowers the group rank. A character of finite image can instead be fixed and deleted. Induction gives finiteness over the complex numbers and hence the torus coset cover. The proof uses Ralf Stephan’s Lean formalization of the number-field unit-equation theorem. [Number-field dependency at the pinned revision](https://github.com/rwst/Subspace-Theorems/blob/2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d/DiophantineApproximation/UnitEquationSeveral.lean#L498)

| Source | Checked result |
| --- | --- |
| [Integer preimages](AppendixA/IntegerPreimage.lean) and [character separation](AppendixA/CharacterSeparation.lean) | The preimage of the specified integer character equations lies in one translated lattice or a translate of a proper real subspace. A finite product of characters minus one separates a point outside a finite lattice union. |
| [Affine subspaces](AppendixA/AffineEscape.lean) and [covering argument](AppendixA/Covering.lean) | Finite unions of proper affine subspaces leave arbitrarily large balls empty. A finite character-fiber cover therefore gives the required lattice cover when the atoms surviving each polynomial multiplier are relatively dense. |
| [Almost periods](AppendixA/AlmostPeriods.lean) | Absolutely convergent Fourier series have relatively dense uniform almost periods. A nonzero such series localized near the atoms implies their relative density. |
| [Atomic coefficients](AppendixA/AtomicGrowth.lean) | Translates of one compact Schwartz bump recover all individual weights on a uniformly discrete carrier. Tempered continuity gives a common polynomial bound on those weights in arbitrary dimension. This generalizes the one-dimensional [upstream estimate](https://github.com/ls558/MeyerGeneralProblem/blob/0f5c061c78d2e92821d47b7f87cf64152e68d108/lean/MeyerGeneralProblem/UniformDiscrete/AtomicGrowth.lean). |
| [Compact approximation](AppendixA/CompactApproximation.lean) and [absolute convergence](AppendixA/AtomicSeries.lean) | Local atomicity on a uniformly discrete set extends to an absolutely convergent expansion on every Schwartz test. |
| [Translated tests](AppendixA/SpectralRecurrence.lean) | The spectral coefficients give an absolutely convergent Fourier series for each translated physical test. The physical weights are uniformly bounded, and a nonempty physical support is relatively dense. |
| [Polynomial multipliers](AppendixA/FilteredRecurrence.lean) | If a trigonometric polynomial is nonzero at one atom, the atoms where it is nonzero are relatively dense. This supplies the recurrence required to pass from a finite character-fiber cover to a finite lattice cover. |
| [Translation bounds](AppendixA/TranslationBound.lean) and [Fourier reflection](AppendixA/FourierReflection.lean) | For every radius there is one finite upper bound on the total variation of each record over all translated balls. Fourier inversion identifies the double transform with the reflected physical record. |
| [Lattice averages](AppendixA/LatticeAverages.lean) | Dual-lattice box averages have modulus at most one and converge to the coset indicator. Finite products restrict the atomic expansion to any finite intersection of cosets on every Schwartz test. |
| [Invariant atoms](AppendixA/InvariantAtoms.lean) | If singleton masses of a locally finite measure are invariant under translation along a nonzero direction, each such mass vanishes. This is the atom-exclusion argument for lower-rank intersections. |
| [Transformed averages](AppendixA/TransformedAverages.lean) and [restricted transform](AppendixA/RestrictedTransform.lean) | On every Schwartz test the transform of a physical intersection is the limit of explicitly weighted translates of the spectrum. The weights have total absolute value one. The transformed restrictions satisfy a common bound on tests supported in a translated ball. |
| [Shrinking tests](AppendixA/ShrinkingTests.lean) and [restricted atoms](AppendixA/RestrictedAtoms.lean) | Nested smooth tests recover the spectral coefficients at every point, including zero off the spectrum. Restriction coefficients inherit the translation phase. Inclusion–exclusion reconstructs the original coefficients, and hyperplane restrictions have zero coefficients everywhere. |
| [Lattice intersections](AppendixA/LatticeIntersections.lean) and [full-rank restrictions](AppendixA/FullRankRestrictions.lean) | Given the physical cover, the entire spectral coefficient function is a finite integer combination of those of single full-rank physical coset restrictions. |
| [Dual cosets](AppendixA/DualCosets.lean) and [comb weights](AppendixA/CombWeights.lean) | On a dual-lattice coset each restriction coefficient has a fixed modulation. If the nonzero coefficients occupy finitely many such cosets, they give the distributional comb sum. Applying this to the inverse Fourier pair returns the formula for the physical distribution. |
| [Lattice orbits](AppendixA/LatticeOrbits.lean) and [box packing](AppendixA/BoxPacking.lean) | Finite orbits contribute only finitely many dual-lattice classes. For infinite orbits, packing disjoint translates gives upper bounds for the proportion of lattice points in shrinking neighborhoods of a coset. |
| [Finite dual classes](AppendixA/FiniteDualClasses.lean) | The spectral cover confines the nonzero coefficients of each full-rank restriction to finitely many dual-lattice classes. Theorem A.1 follows if the physical lattice cover can be proved for every admissible Fourier pair. Applying that covering result to the inverse pair also yields the spectral cover. |
| [Separated interpolation](AppendixA/SeparatedInterpolation.lean) and [bandlimited tests](AppendixA/BandlimitedInterpolation.lean) | A dilated Schwartz kernel interpolates absolutely summable data on any separated carrier. For a fixed separation, compactly supported smooth tests in a common frequency ball can isolate each individual site. |
| [Spectral window](AppendixA/SpectralWindow.lean) | In every dimension, two locally atomic tempered distributions of a prescribed separation are equal if their transforms agree on all smooth tests supported in a fixed ball. Each carrier is separately separated, so sites from different carriers can be arbitrarily close. This proves the bounded-window uniqueness input used by Alon and Kummer for finite generation. |
| [Phase limits](AppendixA/PhaseLimits.lean) and [translation limits](AppendixA/TranslationHull.lean) | Every phase vector in the closure of the spectral translation orbit is realized by another atomic Fourier pair. The new physical sites retain the original separation and the spectral weights acquire the limiting phases. |
| [Window coordinates](AppendixA/PhaseWindow.lean), [finite generation](AppendixA/PhaseGeneration.lean) and [spectral basis](AppendixA/SpectralBasis.lean) | Frequencies in one bounded spectral window generate the entire spectrum over the integers. The additive groups generated by the support and by the spectrum are both finitely generated. For a nonempty spectrum, an integer basis of its group contains a real basis of the ambient space. |
| [Restricted character rank](AppendixA/SpectralRank.lean) | For any finite family of characters restricted to the physical sites, the dimension of their span is bounded by the number of shifted spectral sites in a fixed ball. The radius is independent of the chosen characters. |
| [Quotient windows](AppendixA/QuotientWindows.lean), [coset characters](AppendixA/CosetCharacters.lean) and [coset rank](AppendixA/CosetRank.lean) | If a coset satisfies the support’s polynomial relations and its subgroup spans the ambient real space, the subgroup lies in a full-rank lattice. The proof compares independent characters on the coset with an upper bound from the spectrum. |
| [Laurent reduction](AppendixA/LaurentReduction.lean) | A finite coset cover in the unitary torus pulls back to a cover of the physical sites. The coset rank estimate and recurrence then imply the physical lattice cover. |
| [Laurent equations](AppendixA/LaurentEquations.lean), [minimal vanishing sums](AppendixA/UnitEquations.lean) and [unit-equation finiteness](AppendixA/UnitFiniteness.lean) | The Hilbert basis theorem reduces the Laurent closure to finitely many equations. Splitting vanishing subsums and dividing a minimal sum by one of its terms reduces the required coset theorem to finiteness of nondegenerate solutions of a single normalized unit equation. |
| [Number-field specialization](AppendixA/UnitSpecialization.lean) | Any finite family of distinct nondegenerate complex unit-equation solutions specializes to a single number field, with the same integer exponents and number of generators. Every nonzero subsum remains nonzero. A bound uniform over number fields then implies the needed complex finiteness. |
| [Hyperplane counting](AppendixA/UnitSubspaces.lean) | On each proper hyperplane, a minimal vanishing subsum bounds the possible ratios of two coordinates. For each fixed ratio, merging those two terms gives a shorter nondegenerate equation. Induction yields a uniform solution count from a uniform hyperplane cover. |
| [Infinite-order specialization](AppendixA/InfiniteOrderSpecialization.lean), [character specialization](AppendixA/CharacterSpecialization.lean) and [rank descent](AppendixA/UnitDescent.lean) | Rational specializations of bounded degree preserve a finite collection of infinite-order values. Number-field unit equations and induction on rank and number of coordinates prove the required complex unit-equation finiteness. |
| [Zero distribution](AppendixA/Zero.lean) | Theorem A.1 holds for the zero distribution, with both carriers empty and an empty comb sum. |

The direct rank argument proves the estimate needed for the covering step. The formalization follows the paper’s two-stage argument and supplies its own arithmetic proof of the required torus coset cover. [Alon and Kummer, §§3–4](https://arxiv.org/html/2611.24286v1)

## Verification

Challenge imports Mathlib. Solution imports the Appendix A modules and uses the predicates in [Definitions](AppendixA/Definitions.lean). Challenge has one intentional theorem placeholder. Solution supplies the proof under the same name in the namespace `MeyerGeneralProblem.LevOlevskii`. The allowed axioms are `propext`, `Quot.sound` and `Classical.choice`. [Challenge](Challenge.lean) · [Solution](Solution.lean) · [Comparator configuration](comparator.json)

Run these commands in a fresh clone with Elan installed. Lake reads the pinned Mathlib revision from the committed manifest.

```sh
lake exe cache get
lake build Challenge Solution
lake env lean -DwarningAsError=true Solution.lean
```

On Linux with Bubblewrap installed and user namespaces enabled, run `lake comparator --config comparator.json` for a local statement and kernel check.

The development builds with Lean 4.35.0-rc3. An independent type check expands the statement of Theorem A.1 to its four hypotheses and three conclusions. Lean reports `propext`, `Classical.choice` and `Quot.sound` for the theorem and the lattice-cover corollary.

## Palomar preparation

The mechanical preflight workflow runs the verifier on the exact public commit selected for dispatch. The project is at the repository root and the configuration is `comparator.json`. [Workflow](.github/workflows/palomar.yml) · [Palomar intake](https://submit.palomar-registry.org/)

## Provenance

Jamie Martin is the author and responsible maintainer. The statements and the implication from Theorem A.1 to the lattice-cover question were adapted from MeyerGeneralProblem. OpenAI Codex developed the standalone Lean proof and ran the build and axiom checks. The number-field theorem comes from the pinned Apache-2.0 Subspace-Theorems dependency. This repository’s proof code is MIT-licensed. [Upstream statements](https://github.com/ls558/MeyerGeneralProblem/blob/0f5c061c78d2e92821d47b7f87cf64152e68d108/lean/MeyerGeneralProblem/UniformDiscrete/LevOlevskiiLatticeCover.lean) · [Metadata](formalization.yaml) · [License](LICENSE)
