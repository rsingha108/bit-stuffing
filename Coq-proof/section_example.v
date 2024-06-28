Require Import Bool List Program Arith Lia FunInd Recdef.
Import ListNotations.

Section S1.

Variable a : list bool.
Variable k : list bool.


(*returns true if a starts with k, else false*)
Fixpoint starts_with (a1 k1 : list bool) : bool :=
  match a1,k1 with
    | ha::ta, hk::tk => eqb ha hk && starts_with ta tk
    | _, [] => true
    | _, _ => false
  end.

Hypothesis H : starts_with a k = true.


Lemma starts_with_skip : 
  k ++ skipn (length k) a = a.
Proof.
  enough (H' : forall (k : list bool), starts_with a k = true -> k ++ skipn (length k) a = a).
  {
    apply (H' k H).
  }
  clear H k.
  induction a as [| ha ta IH].
    - intros k H. destruct k as [| hk tk].
      + simpl. auto.
      + simpl in H. lia.
    - intros k H. destruct k as [| hk tk].
      + simpl. auto.
      + simpl in H. 
        apply andb_true_iff in H.
        destruct H as [HL HR].
        rewrite <- app_comm_cons.
        simpl.
        rewrite (IH tk HR).
        rewrite (eqb_prop ha hk HL).
        auto.
Qed.

End S1.
