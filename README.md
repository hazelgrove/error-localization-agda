# Total Type Error Localization and Recovery with Holes

This repository contains the full formalism and Agda mechanization for the marked lambda calculus, a
judgmental framework for bidirectional type error localization and recovery.

## Formalism

The formalism may be built from LaTeX via `make formalism.pdf`.

## Mechanization

All semantics and metatheorems are mechanized in the Agda proof assistant. To check the proofs, an
installation of [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download) is required.
The proofs are known to load cleanly under Agda 2.6.3.

Once installed, `agda all.agda` in the appropriate directory will cause Agda to check all the proofs.

### File Organization

Here is where to find each definition:

-   [prelude.agda](./prelude.agda) contains definitions and utilities not specific to the marked
    lambda calculus.

-   [core/](./core) contains definitions related to the core language:
    -   [typ.agda](./core/typ.agda) contains the syntax definition for types, the base, consistency,
        matched arrow and product types, and meet judgments, alongside useful lemmas about types.
    -   [uexp.agda](./core/uexp.agda) contains the syntax definition and bidirectional typing
        judgments for unmarked expressions.
    -   [mexp.agda](./core/mexp.agda) contains the syntax definition and bidirectional typing
        judgments for marked expressions.
    -   [erasure.agda](./core/erasure.agda) contains the definition of mark erasure.
    -   [lemmas.agda](./core/lemmas.agda) contains some lemmas about unmarked and marked
        expressions.

-   [marking/](./marking) contains definitions and [theorems](#where-to-find-each-theorem) related
    to marking:
    -   [marking.agda](./marking/marking.agda) contains the bidirectional marking judgment.
    -   [totality.agda](./marking/totality.agda), [unicity.agda](./marking/unicity.agda), and
        [wellformed.agda](./marking/wellformed.agda) contain theorems about marking (see the [next
    section](#where-to-find-each-theorem)).

-   [hazelnut/](./hazelnut) contains definitions and theorems related to the reified Hazelnut action
    calculus.
    -   [action.agda](./hazelnut/action.agda) contains the definition of actions, iterated actions,
        the movements judgment, and the sort judgments.
    -   [untyped/](./hazelnut/untyped) contains the untyped actions semantics and theorems.
        -   [zexp.agda](./hazelnut/untyped/zexp.agda) contains the syntax definitions for zippered
            types and expressions.
        -   [erasure.agda](./hazelnut/untyped/erasure.agda) contains judgmental and functional
            definitions of cursor erasure.
        -   [action.agda](./hazelnut/untyped/action.agda) contains the type and expression action
            judgments.
        -   [reachability.agda](./hazelnut/untyped/reachability.agda) contains the proof of
            reachability.
        -   [mei.agda](./hazelnut/untyped/mei.agda) contains the proof of movement erasure
            invariance.
        -   [constructability.agda](./hazelnut/untyped/constructability.agda) contains the proof of
            constructability.
        -   [determinism.agda](./hazelnut/untyped/determinism.agda) contains the proof of action
            determinism.

### Where to Find Each Theorem

Every theorem is proven in the mechanization. Here is where to find each theorem:

-   Theorem 2.1, *Marking Totality*, is in [marking/totality.agda](./marking/totality.agda), given
    by `↬⇒-totality` and `↬⇐-totality`.

-   Theorem 2.2, *Marking Well-Formedness*, is in
    [marking/wellformed.agda](./marking/wellformed.agda), given by `↬⇒□` and `↬⇐□`.

-   Theorem 2.3, *Marking of Well-Typed/Ill-Typed Expressions*, is in
    [marking/wellformed.agda](./marking/wellformed.agda), whose first part is given by `⇒τ→markless`
    and `⇐τ→markless`, and second part is given by `¬⇒τ→¬markless` and `¬⇐τ→¬markless`.

-   Theorem 2.4, *Marking Unicity*, is in [marking/unicity.agda](./marking/unicity.agda), given by
    `↬⇒-unicity` and `↬⇐-unicity`.

### Assumptions and Representation Decisions

-   Contexts are encoded as ordered association lists pairing variables and types.

-   The consistency rules are slightly different from those in the formalism and paper to facilitate
    a simpler unicity proof for marking. Type inconsistency is defined as the negation of
    consistency, that is, `τ₁ ~̸ τ₂ = ¬ (τ₁ ~ τ₂) = (τ₁ ~ τ₂) → ⊥`. This formulation is equivalent to
    a judgmental definition.

-   Since we are only concerned with well-typed marked expressions, they are encoded as
    intrinsically typed terms. Variables, while otherwise extraneous, are preserved in the syntax
    for the sake of mark erasure. As a result, judgments on marked expressions, such as `subsumable`
    and `markless`, are formulated bidirectionally.

-   Conjunctions in the antecedents of theorems have been converted into sequences of implications,
    which has no effect other than to simplify the proof text.

-   The formalism and paper do not state exactly what the `num` type is; for simplicity, we use
    unary natural numbers, as defined in [prelude.agda](./prelude.agda).
