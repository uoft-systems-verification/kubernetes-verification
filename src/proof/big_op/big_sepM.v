From iris.algebra Require Export big_op.
From Perennial.Helpers Require Import ipm.
From Perennial.algebra.big_op Require Import big_sepM.

Set Default Proof Using "Type".

Section map.
Context {PROP : bi} `{!BiAffine PROP, !BiPersistentlyForall PROP}.
Context `{Countable K} {A : Type}.
Implicit Types Φ Ψ : K → A → PROP.


End map.

Section map2.
Context {PROP : bi} `{!BiAffine PROP, !BiPersistentlyForall PROP}.
Context `{Countable K} {A B : Type}.
Implicit Types Φ Ψ : K → A → B → PROP.

End map2.
