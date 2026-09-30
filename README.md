# KLMRocq

A Rocq/Coq formalization of the representation theorem of Kraus, Lehmann and Magidor (KLM) for System C: a conditional assertion is derivable in System C if and only if it holds in every cumulative model.

## Main result

`klm_theorem` in `KLM/main.v`:

```coq
Theorem klm_theorem :
  forall (𝐊 : KnowledgeBase) (Γ : Ensemble Formula) (p q : Formula),
    (𝐊⊕Γ ⊢ p |~ q) <-> (𝐊⊕Γ ⊨ p |~w q).
```

- `𝐊` is a set of conditional assertions and `Γ` a classical background theory.
- `𝐊⊕Γ ⊢ p |~ q` is derivability in System C (Ref, LLE, RW, Cut, CM).
- `𝐊⊕Γ ⊨ p |~w q` means that `p |~ q` holds in every cumulative model satisfying `𝐊` and `Γ`.

Cumulative models follow KLM (1990): states are labelled with non-empty sets of worlds, the preference relation is an arbitrary binary relation, and smoothness is part of the definition of a model.

The proof uses no KLM-specific axioms. It depends only on the standard axioms `classic`, `epsilon_statement` and `Extensionality_Ensembles`, which the propositional logic library already requires.

## Structure

| File | Content |
|------|---------|
| `KLM/KLM_Base.v` | Worlds, satisfaction of a formula by a set of worlds |
| `KLM/KLM_Cumulative.v` | System C and derived rules |
| `KLM/KLM_Semantics.v` | Cumulative models and semantic entailment |
| `KLM/KLM_Soundness.v` | Soundness of System C |
| `KLM/KLM_Completeness.v` | Canonical model and completeness |
| `KLM/main.v` | Main theorem and examples |
| `A-Comprehensive-Formalization-of-Propositional-Logic-in-Coq/` | Propositional logic library by Guo and Yu |

The examples in `main.v` include the Tweety and Nixon diamond scenarios, and a countermodel showing that the rule Or is not derivable in System C.

## Building

Tested with Coq 8.20.1.

```
make
```

## References

- J. Walther, K. Sauerwald, J. Heyninck. *The KLM Representation Theorem for System C, Formally.* 23rd International Workshop on Nonmonotonic Reasoning (NMR 2025), CEUR-WS Vol-4071. https://ceur-ws.org/Vol-4071/paper21.pdf
- S. Kraus, D. Lehmann, M. Magidor. *Nonmonotonic reasoning, preferential models and cumulative logics.* Artificial Intelligence 44 (1990) 167–207.
- D. Guo, W. Yu. *A Comprehensive Formalization of Propositional Logic in Coq: Deduction Systems, Meta-Theorems, and Automation Tactics.* Mathematics 11 (2023) 2504.

## License

MIT, see `LICENSE`.
