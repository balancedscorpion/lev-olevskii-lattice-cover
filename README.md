# From Martin’s Appendix A to the Lev–Olevskii lattice-cover question

**Proved in Lean:** If Martin’s Appendix A conclusion holds, including the lattice covers obtained in its proof, then the answer to Lev and Olevskii’s covering question is affirmative. On this branch the comb decomposition has also been proved assuming the finite lattice covers. Deriving the physical cover from the hypotheses of Theorem A.1 remains open in Lean. [Martin, Appendix A](https://hexagonmath.org/pdf/2611.00744v2#page=12) · [Lev and Olevskii, §11.2(1)](https://arxiv.org/pdf/1512.08735v2#page=20)

| Lean declaration | Mathematical content |
| --- | --- |
| `theoremA1Statement` | In every positive dimension, a tempered distribution and its Fourier transform with locally atomic expansions and uniformly discrete sites admit a finite translated, modulated, full-rank lattice-comb decomposition of the distribution and finite lattice covers of both sets of sites. |
| `latticeCoverQuestion` | In dimension at least two, global atomic expansions on Schwartz tests, a joint polynomial bound on variation, and uniform discreteness of both sets of sites imply a finite lattice cover of the physical support. |
| `theoremA1Statement_implies_latticeCoverQuestion` | The proved implication between the two propositions. This is the sole target in Comparator. |

The weights at the specified sites are nonzero. Each comb has its own invertible matrix, shift, modulation and complex scalar. Its character is evaluated at the translated site. Contributions add where lattices overlap, and an empty sum represents the zero distribution.

The proof restricts the two global atomic identities to compactly supported Schwartz tests, applies the Appendix A hypothesis in the same dimension, and takes the physical cover from its conclusion. It needs neither the polynomial bound nor the weighted decomposition for this last step.

## Appendix A proof in development

This branch targets the unconditional Theorem A.1. The proved declarations currently establish the following parts of its argument.

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
| [Zero distribution](AppendixA/Zero.lean) | Theorem A.1 holds for the zero distribution, with both carriers empty and an empty comb sum. |

The algebraic step still requires the dimension bound for the Zariski closure and the application of Laurent’s theorem to obtain the finite family of character fibers. The declaration `theoremA1_of_physical_cover` derives the complete conclusion of Theorem A.1 from the physical covering result alone. [Alon and Kummer, Sections 3 and 4](https://arxiv.org/html/2611.24286v1)

## Verification

Challenge imports Mathlib. Solution imports the Appendix A modules and uses the predicates in [Definitions](AppendixA/Definitions.lean). Challenge has one intentional theorem placeholder. Solution supplies the proof under the same name in the namespace `MeyerGeneralProblem.LevOlevskii`. The allowed axioms are `propext`, `Quot.sound` and `Classical.choice`. [Challenge](Challenge.lean) · [Solution](Solution.lean) · [Comparator configuration](comparator.json)

Run these commands in a fresh clone with Elan installed. Lake reads the pinned Mathlib revision from the committed manifest.

```sh
lake exe cache get Challenge.lean Solution.lean
lake build Challenge Solution
lake env lean -DwarningAsError=true Solution.lean
```

On Linux with Bubblewrap installed and user namespaces enabled, run `lake comparator --config comparator.json` for a local statement and kernel check.

On 22 November 2026 the two modules built with Lean 4.35.0-rc3. The solution compiled with warnings treated as errors. A local Comparator run on macOS accepted the theorem, including replay by Lean and NanoDa. This developer check ran without the Linux sandbox. An importing Lean file also checked a translated lattice cover, exclusion of a zero-weight site, and the empty comb representation of zero.

## Palomar preparation

Hold final intake for a proof of Theorem A.1. The current theorem is a direct consequence of the explicit physical-cover hypothesis. Palomar evaluates the research significance of the theorem selected in Comparator. [Submission criteria](https://github.com/PalomarRegistry/PalomarPolicy/blob/28bd48b9b71bbb2a82c718ce761d5a4220ef8e60/CONTRIBUTING.md#1-decide-whether-the-result-is-suitable)

After selecting the intended theorem and building it, a maintainer can run **Palomar mechanical preflight** from GitHub Actions on a public revision. The workflow checks the exact commit selected by the dispatch. Inspect the full mechanical report and its source SHA before deciding whether to send that revision to intake. [Workflow](.github/workflows/palomar.yml) · [Palomar intake](https://submit.palomar-registry.org/)

## Provenance

Jamie Martin is the author and responsible maintainer. The formalisation was extracted from the source module at commit `0f5c061c78d2e92821d47b7f87cf64152e68d108`. It preserves the predicates and proof, replaces the project bootstrap import with Mathlib imports, and uses Lean’s public module interface. [Pinned upstream source (access required)](https://github.com/ls558/MeyerGeneralProblem/blob/0f5c061c78d2e92821d47b7f87cf64152e68d108/lean/MeyerGeneralProblem/UniformDiscrete/LevOlevskiiLatticeCover.lean) · [Submission layout reference](https://github.com/balancedscorpion/countably-infinite-dimension-strong-meyer-spaces) · [Metadata and automation disclosure](formalization.yaml) · [MIT license](LICENSE)
