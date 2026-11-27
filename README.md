# Quantum error correction in Agda

Constructive proofs of binary linear algebra, quantum error-correcting codes and decoding algorithms.

## Results

### Binary linear algebra

[Binary.agda](src/Coding/Binary.agda) represents binary vectors
as functions `Fin n → Bool` and matrices as functions
`Fin m → Fin n → Bool`. Arithmetic uses the Boolean ring
from Agda stdlib.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `dot-comm : ∀ {n} (a b : Word n) → dot a b ≡ dot b a` | Symmetry | The binary dot product is symmetric. |
| `dot-add : ∀ {n} (a b c : Word n) → dot a (b ⊞ c) ≡ dot a b xor dot a c` | Linearity | The dot product distributes over addition. |
| `dot-unit : ∀ {n} (a : Word n) j → dot a (delta j) ≡ a j` | Coordinate selection | The dot product with a basis vector selects one coordinate. |
| `syndrome-add : ∀ {m n} (H : Matrix m n) e f → apply H (e ⊞ f) ≐ (apply H e ⊞ apply H f)` | $H(e+f)=He+Hf$ | Syndromes preserve addition. |
| `syndrome-coset : ∀ {m n} (H : Matrix m n) e c → Kernel H c → apply H (e ⊞ c) ≐ apply H e` | $Hc=0\implies H(e+c)=He$ | Adding a kernel word preserves the syndrome. |
| `adjoint : ∀ {m n} (H : Matrix m n) (a : Word m) (b : Word n) → dot a (apply H b) ≡ dot (apply (tr H) a) b` | $\langle a,Hb\rangle=\langle H^Ta,b\rangle$ | Moving a matrix across the dot product transposes it. |
| `dot-cat : ∀ {m n} (a c : Word m) (b d : Word n) → dot (cat a b) (cat c d) ≡ dot a c xor dot b d` | Dot product of concatenated vectors | The total dot product is the sum of the two block products. |

See: [Agda FiniteSums.agda], [Agda Bool Properties.agda].

### CSS codes and chain complexes

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `boundary-cycle : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) → Orthogonal X Z → ∀ s → Kernel X (apply (tr Z) s)` | $H_XH_Z^T=0\implies\mathrm{im}(H_Z^T)\subseteq\ker(H_X)$ | Every Z-stabilizer combination has zero X syndrome. |
| `cycle-rows : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) → (∀ s → Kernel X (apply (tr Z) s)) → Orthogonal X Z` | Converse of `boundary-cycle` | The chain condition implies row orthogonality. |

See: [Calderbank–Shor], [Steane]; [Lean-QEC CSS.lean]
`CSS_pair.of_matrices`; [QECLean BBChainComplex.lean].

### Binary symplectic representation

[Symplectic.agda](src/Coding/Symplectic.agda) models Pauli
representatives acting on signed computational basis labels.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `swap-label : ∀ {n} (p q : Pauli n) t → proj₁ (run p (run q t)) ≐ proj₁ (run q (run p t))` | Equality of basis labels | Exchanging two Pauli operators preserves the resulting basis label. |
| `swap-sign : ∀ {n} (p q : Pauli n) t → proj₂ (run p (run q t)) ≡ form p q xor proj₂ (run q (run p t))` | Symplectic commutation law | The binary symplectic product determines the sign change. |
| `pure-check : ∀ {n} (a b : Word n) → form (pauli a zero) (pauli zero b) ≡ dot a b` | Pure X/Z symplectic product | Commutation of pure X and Z operators depends on their binary overlap. |
| `css-sign : ∀ {m k n} (X : Matrix m n) (Z : Matrix k n) → Orthogonal X Z → ∀ i j t → proj₂ (run (pauli (X i) zero) (run (pauli zero (Z j)) t)) ≡ proj₂ (run (pauli zero (Z j)) (run (pauli (X i) zero) t))` | CSS commutation | Orthogonal X and Z checks preserve the sign when exchanged. |
| `x-syndrome : ∀ {m n} (X : Matrix m n) (p : Pauli n) i → form (pauli (X i) zero) p ≡ apply X (z p) i` | X-check syndrome | X checks detect the Z component of an error. |
| `z-syndrome : ∀ {k n} (Z : Matrix k n) (p : Pauli n) i → form (pauli zero (Z i)) p ≡ apply Z (x p) i` | Z-check syndrome | Z checks detect the X component of an error. |

The model captures binary Pauli commutation, not arbitrary
complex quantum states or measurement channels.

See: [Gottesman]; [QECLean SymplecticInner.lean]
`commutes_iff_symplectic_inner_zero`;
[Lean-QEC BinSymp.lean]
`BinSympPauli_toPauli_commute_iff_symplecticProd_zero`;
[Lean-QEC SyndromeAction.lean].

### Certified single-bit decoding

[Decoder.agda](src/Coding/Decoder.agda) implements syndrome
decoding for arbitrary binary parity-check matrices.

The module `Single` is parameterized by `H : Matrix m n`.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `search : (s : Word m) → Dec (Σ (Fin n) (λ j → Column j ≐ s))` | Decidable column search | Find a coordinate matching the syndrome or prove that none exists. |
| `flip-syndrome : ∀ c → Kernel H c → ∀ j → apply H (c ⊞ delta j) ≐ Column j` | $H(c+e_j)=He_j$ | The syndrome of a single-bit error is the corresponding column. |
| `one-error : (∀ j k → Column j ≐ Column k → j E.≡ k) → ∀ c → Kernel H c → ∀ j → correct (c ⊞ delta j) ≐ c` | Single-error correction | Distinct columns suffice to correct every single-bit corruption of a codeword. |
| `clean : (∀ j → Column j ≐ zero → ⊥) → ∀ c → Kernel H c → correct c ≐ c` | Preservation of codewords | Nonzero columns ensure that uncorrupted codewords remain unchanged. |

### Hamming code

[Hamming.agda](src/Coding/Hamming.agda) instantiates the
decoder with the seven nonzero binary columns of length three.

| Agda theorem | Mathematical content | Meaning |
|---|---|---|
| `column-value : ∀ j → number (D.Column j) E.≡ N.suc (F.toℕ j)` | Column enumeration | Column `j` represents the integer `j + 1`. |
| `distinct : ∀ j k → D.Column j ≐ D.Column k → j E.≡ k` | Injectivity | Different coordinates have different syndromes. |
| `nonzero : ∀ j → D.Column j ≐ zero → Data.Empty.⊥` | Nonzero columns | Every single-bit error has a nonzero syndrome. |
| `recover-one : ∀ c → Kernel H c → ∀ j → D.correct (c ⊞ delta j) ≐ c` | Single-error correction | Every single-bit corruption of every codeword is corrected. |
| `recover-clean : ∀ c → Kernel H c → D.correct c ≐ c` | Preservation of codewords | Decoding an uncorrupted codeword leaves it unchanged. |

See: [Hamming]; [Agda Fin Properties.agda] `any?`, `all?`.

The correction guarantees concern classical binary errors,
not arbitrary quantum errors or multiple-bit corruption.

## Tutorials

See [TUTORIALS.md](TUTORIALS.md).

## References

### Mathematical literature

- A. R. [Calderbank–Shor], *Good Quantum Error-Correcting Codes Exist* (1996).
- A. M. [Steane], *Multiple-Particle Interference and Quantum Error Correction* (1996).
- D. [Gottesman], *Stabilizer Codes and Quantum Error Correction* (1997).
- R. W. [Hamming], *Error Detecting and Error Correcting Codes* (1950).

### Related formalizations

- [QECLean SymplecticInner.lean] - binary symplectic commutation.
- [QECLean BBChainComplex.lean] - bicycle codes as chain complexes.
- [Lean-QEC CSS.lean] - CSS codes from orthogonal matrices.
- [Lean-QEC BinSymp.lean] - binary symplectic representation of Pauli operators.
- [Lean-QEC SyndromeAction.lean] - syndrome and Pauli action.

### Reused mathematics

- [Agda FiniteSums.agda] - finite sums, linearity, exchange of summation and Kronecker delta. Reused from agda-finite-fourier.
- [Agda Bool Properties.agda] - Boolean ring structure.
- [Agda Fin Properties.agda] - constructive finite existential and universal decision procedures.

[Calderbank–Shor]: https://doi.org/10.1103/PhysRevA.54.1098
[Steane]: https://arxiv.org/abs/quant-ph/9601029
[Gottesman]: https://arxiv.org/abs/quant-ph/9705052
[QECLean SymplecticInner.lean]: https://github.com/Stavan-Jain/QECLean/blob/47876ae4e0e204e850ae30993d12a3c22c6e4511/QEC/Stabilizer/Foundations/BinarySymplectic/SymplecticInner.lean
[QECLean BBChainComplex.lean]: https://github.com/Stavan-Jain/QECLean/blob/47876ae4e0e204e850ae30993d12a3c22c6e4511/QEC/Stabilizer/Framework/Homological/BBChainComplex.lean
[Lean-QEC CSS.lean]: https://github.com/VerifiedQC/Lean-QEC/blob/3ecc50283caaa257c9da3a000ab57c5401039e2e/LeanQEC/Stabilizer/CSS.lean
[Lean-QEC BinSymp.lean]: https://github.com/VerifiedQC/Lean-QEC/blob/3ecc50283caaa257c9da3a000ab57c5401039e2e/LeanQEC/Stabilizer/BinSymp.lean
[Lean-QEC SyndromeAction.lean]: https://github.com/VerifiedQC/Lean-QEC/blob/3ecc50283caaa257c9da3a000ab57c5401039e2e/LeanQEC/Decoding/SyndromeAction.lean
[Agda FiniteSums.agda]: https://github.com/verify-right/agda-finite-fourier/blob/72b5b977aa90c21d24926eae8d45ecbdbb1c1089/src/Algebra/FiniteSums.agda
[Agda Bool Properties.agda]: https://github.com/agda/agda-stdlib/blob/v2.4.1/src/Data/Bool/Properties.agda
[Hamming]: https://doi.org/10.1002/j.1538-7305.1950.tb00463.x
[Agda Fin Properties.agda]: https://github.com/agda/agda-stdlib/blob/v2.4.1/src/Data/Fin/Properties.agda
