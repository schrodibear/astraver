
Require Export caduceus_why.

Ltac Acc_upd :=
  rewrite acc_upd ||
  (rewrite acc_upd_eq; [ idtac | progress auto with * ]) ||
  (rewrite acc_upd_neq; [ idtac | progress auto with * ]); 
  auto with *.

Ltac caduceus := repeat Acc_upd.

Hint Resolve neq_base_addr_neq_shift.
Hint Resolve neq_offset_neq_shift.

Ltac valid := match goal with
  | id:(valid_range ?X1 ?X2 ?X3 ?X4) |- (valid ?X1 (shift ?X2 ?X5))
    => apply valid_range_valid_shift with X3 X4; auto with *
end.

Ltac CleanAssigns :=
  match goal with
(*
  | id:(store_extends ?X1 ?X1) |- _ =>
      clear id; CleanAssigns
*)
  | id:(assigns ?X2 ?X1 ?X1 ?X3) |- _ =>
      clear id; CleanAssigns
  | _ => idtac
  end.


Ltac AssignsRec :=
  match goal with
  | id:(assigns ?X1 ?X2 ?X3 ?X4) |- (assigns ?X1 ?X2 ?X3 ?X4) =>
      exact id
(*
  |  |- (assigns ?X1 ?X2 ?X2 ?X4) =>
      exact (modifiable_refl (h:=X1) X2 (unchanged:=X4))
*)
(*
  | id:(fresh ?X1 ?X3) |- (modifiable ?X1 ?X7 (update ?X2 ?X3 ?X4) ?X6) =>
      apply
       (modifiable_fresh_update (h:=X1) (m1:=X7) (m2:=X2) (unch:=X6) (v:=X3)
          X4 id); ModRec
*)
(*
  |  |- (assigns ?X1 ?X2 (upd ?X2 ?X3 ?X4) ?X6) =>
      apply (assigns_upd (h:=X1) X2 (unch:=X6) (v:=X3) X4); subst;
       krakatoa; progress auto
*)
(*
  |  |- (modifiable ?X1 ?X7 (update ?X2 ?X3 ?X4) ?X6) =>
      apply
       (modifiable_trans (h:=X1) (m1:=X7) (m2:=X2) (m3:=(
          update X2 X3 X4)) (unch:=X6)); ModRec
*)
  | id:(?X2 = ?X3) |- (assigns ?X1 ?X4 ?X2 ?X5) =>
      rewrite id; AssignsRec
(*
  | id:(modifiable ?X1 ?X2 ?X3 ?X4) |- (modifiable ?X5 ?X6 ?X3 ?X7) =>
      apply modifiable_trans_sub with (4:=id);
       [ subst; krakatoa; unfold inter_loc; intuition; fail 
       | Store | ModRec ]
*)
  end.


Ltac Assigns := CleanAssigns; AssignsRec.

Ltac Unchanged :=
  match goal with
  | |- (unchanged ?X1 (pointer_loc ?X2)) =>
      apply unchanged_pointer_intro;auto
 end.


Hint Extern 0 (assigns _ _ _ _) => Assigns.
Hint Extern 0 (unchanged _ _) => Unchanged.
