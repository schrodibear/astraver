
Require Import Why.

Parameter l : Z.
Axiom l_pos : (0 < l)%Z.


Proof.
auto with *.
Qed.

Proof.
auto with *.
Qed.

Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; generalize (H7 k); intuition.
subst; intuition.
Qed.

Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; intuition.
Qed.

Proof.
intuition.
assert (k = x1 \/ k <> x1).
 omega.
 intuition.
subst; intuition.
rewrite H6; rewrite H5; apply H3; omega.
rewrite H5.
 rewrite H8; try omega.
apply H3; omega.
Qed.

Proof.
intuition.
Qed.

Proof.
generalize l_pos; intuition.
assert (k = 0%Z \/ (0 < k)%Z).
 omega.
 intuition.
subst; intuition.
Save.

