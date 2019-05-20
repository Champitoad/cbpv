Require Import Defs.
Open Scope list_scope.

Axiom TODO : forall A, A.

(** Question 1 *)

Module ΛHP_Machine.

Import ΛHP.
Import Types Terms.

Inductive marker :=
| Der
| Succ
| Arg (V : term)
| Fun (M : term)
| If (N : term) (z : var) (P : term).

Definition stack := list marker.

Reserved Notation "M ⊣ π -k-> M' ⊣ π'" (at level 100, M' at level 99).

Inductive step : term -> stack -> term -> stack -> Prop :=

(* Stack update rules *)

| SDer M π :
  der M ⊣ π -k-> M ⊣ Der :: π

| SSucc M π :
  succ M ⊣ π -k-> M ⊣ Succ :: π

| SArg M N π :
  <M>N ⊣ π -k-> N ⊣ Fun M :: π

| SFun V M π (H : value V) :
  V ⊣ Fun M :: π -k-> M ⊣ Arg V :: π

| SIf M N z P π :
  #if (M, N, [z] P) ⊣ π -k-> M ⊣ If N z P :: π

(* Reduction rules *)

| RDerBang M π :
  M! ⊣ Der :: π -k-> M ⊣ π

| RSucc (n : nat) π :
  Nat n ⊣ Succ :: π -k-> Nat (S n) ⊣ π

| RBeta x φ M V (H : value V) π :
  λ x:φ, M ⊣ Arg V :: π -k-> M[V/x] ⊣ π

| RIf_0 N z P π :
  Nat 0 ⊣ If N z P :: π -k-> N ⊣ π

| RIf_succ n N z P π :
  Nat (S n) ⊣ If N z P :: π -k-> P[(Nat n)/z] ⊣ π

where "M ⊣ π -k-> M' ⊣ π'" := (step M π M' π') : machine_scope.

Open Scope machine_scope.

Reserved Notation "M ⊣ π -k->* M' ⊣ π'" (at level 100, M' at level 99).

Inductive multistep : term -> stack -> term -> stack -> Prop :=

| multistep_refl M π :
  M ⊣ π -k->* M ⊣ π

| multistep_step M1 π1 M2 π2 M3 π3 :
  (M1 ⊣ π1 -k-> M2 ⊣ π2) -> (M2 ⊣ π2 -k->* M3 ⊣ π3) -> (M1 ⊣ π1 -k->* M3 ⊣ π3)

where "M ⊣ π -k->* M' ⊣ π'" := (multistep M π M' π') : machine_scope.

Lemma multistep_trans M1 π1 M2 π2 M3 π3 :
  (M1 ⊣ π1 -k->* M2 ⊣ π2) -> (M2 ⊣ π2 -k->* M3 ⊣ π3) -> (M1 ⊣ π1 -k->* M3 ⊣ π3).
Proof.
  intros. induction H.
  * assumption.
  * apply (multistep_step M1 π1 M2 π2 M3 π3).
    - assumption.
    - apply IHmultistep. assumption.
Qed.

End ΛHP_Machine.

Import ΛHP.
Import Terms Types Typing Smallstep.
Import ΛHP_Machine.

Inductive value_or_abs : term -> Prop :=
| value_or_abs_value V : value V -> value_or_abs V
| value_or_abs_abs x φ M : value_or_abs (λ x:φ, M).

Axiom weak_terminates :
  forall M, well_typed M ->
  exists W, M -w->* W /\ value_or_abs W.

Remark step_stack_closure π :
  forall M1 π1 M2 π2,
  (M1 ⊣ π1 -k->* M2 ⊣ π2) -> (M1 ⊣ π1 ++ π -k->* M2 ⊣ π2 ++ π).
Proof.
Admitted.

Fixpoint stack_of_context E :=
  match E with
  | CHole => []
  | CDer E => stack_of_context E ++ [Der]
  | CSucc E => stack_of_context E ++ [Succ]
  | CArg E V _ => stack_of_context E ++ [Arg V]
  | CFun M E => stack_of_context E ++ [Fun M]
  | CIf E N z P => stack_of_context E ++ [If N z P]
  end.

Lemma step_simulates_weak_comp :
  forall M N, M --> N -> M ⊣ [] -k->* N ⊣ [].
Proof.
  intros. induction H.
  * apply multistep_step with (M2 := M!) (π2 := [Der]).
    - apply SDer.
    - apply multistep_step with (M2 := M) (π2 := []).
      + apply RDerBang.
      + apply multistep_refl.
  * apply multistep_step with (M2 := n) (π2 := [Succ]).
    - apply SSucc.
    - apply multistep_step with (M2 := S n) (π2 := []).
      + apply RSucc.
      + apply multistep_refl.
  * apply multistep_step with (M2 := V) (π2 := [Fun (λ x:φ, M)]).
    - apply SArg.
    - apply multistep_step with (M2 := λ x:φ, M) (π2 := [Arg V]).
      + apply SFun. assumption.
      + apply multistep_step with (M2 := M[V/x]) (π2 := []).
        ** apply RBeta. assumption.
        ** apply multistep_refl.
  * apply multistep_step with (M2 := 0) (π2 := [If N z P]).
    - apply SIf.
    - apply multistep_step with (M2 := N) (π2 := []).
      + apply RIf_0.
      + apply multistep_refl.
  * apply multistep_step with (M2 := S n) (π2 := [If N z P]).
    - apply SIf.
    - apply multistep_step with (M2 := P[n/z]) (π2 := []).
      + apply RIf_succ.
      + apply multistep_refl.
Qed.

Lemma step_simulates_weak_ctx E :
  let π := stack_of_context E in
  forall M N, M --> N -> E[M] ⊣ [] -k->* N ⊣ π.
Proof.
  intros. induction E; simpl in *.
  * apply step_simulates_weak_comp. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [Der]).
    - apply SDer.
    - rewrite <- app_nil_l with (l := [Der]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [Succ]).
    - apply SSucc.
    - rewrite <- app_nil_l with (l := [Succ]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := V) (π2 := [Fun E[M]]).
    - apply SArg.
    - apply multistep_step with (M2 := E[M]) (π2 := [Arg V]).
      + apply SFun. assumption.
      + rewrite <- app_nil_l with (l := [Arg V]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [Fun M0]).
      + apply SArg.
      + rewrite <- app_nil_l with (l := [Fun M0]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [If N0 z P]).
      + apply SIf.
      + rewrite <- app_nil_l with (l := [If N0 z P]). apply step_stack_closure. assumption.
Qed.

Lemma step_context_to_stack E :
  let π := stack_of_context E in
  forall M, E[M] ⊣ [] -k->* M ⊣ π.
Proof.
  intros. induction E; simpl in *.
  * apply multistep_refl.
  * apply multistep_step with (M2 := E[M]) (π2 := [Der]).
    - apply SDer.
    - rewrite <- app_nil_l with (l := [Der]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [Succ]).
    - apply SSucc.
    - rewrite <- app_nil_l with (l := [Succ]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := V) (π2 := [Fun E[M]]).
    - apply SArg.
    - apply multistep_step with (M2 := E[M]) (π2 := [Arg V]).
      + apply SFun. assumption.
      + rewrite <- app_nil_l with (l := [Arg V]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [Fun M0]).
      + apply SArg.
      + rewrite <- app_nil_l with (l := [Fun M0]). apply step_stack_closure. assumption.
  * apply multistep_step with (M2 := E[M]) (π2 := [If N z P]).
      + apply SIf.
      + rewrite <- app_nil_l with (l := [If N z P]). apply step_stack_closure. assumption.
Qed.

Definition normal_form_step M π :=
  ~ exists M' π', M ⊣ π -k-> M' ⊣ π'.

Lemma value_or_abs_normal_form_step :
  forall W, value_or_abs W ->
  normal_form_step W ([]).
Proof.
  intros. intro. destruct H0 as (M' & π' & H0). destruct H.
  * destruct H; inversion H0.
  * inversion H0.
Qed.

Lemma multistep_deterministic : TODO _.
Proof.
Admitted.

Lemma one_way_to_normal_form :
  forall M1 π1 M2 π2 M3 π3,
  (M1 ⊣ π1 -k->* M3 ⊣ π3) -> (normal_form_step M3 π3) ->
  (M1 ⊣ π1 -k->* M2 ⊣ π2) ->
  (M2 ⊣ π2 -k->* M3 ⊣ π3).
Proof.
  (* The proof will use multistep_deterministic *)
Admitted.

Lemma step_simulates_weak_bigstep :
  forall M W, value_or_abs W ->
  M -w->* W -> M ⊣ [] -k->* W ⊣ [].
Proof.
  intros. induction H0 as [ M | M N W ].
  * apply multistep_refl.
  * destruct H0.
    pose proof (step_simulates_weak_ctx E M N H0).
    pose proof (step_context_to_stack E N).
    pose proof (value_or_abs_normal_form_step W H). apply IHmulti in H.
    pose proof (one_way_to_normal_form E[N] ([]) N (stack_of_context E) W ([]) H H4 H3).
    apply multistep_trans with (M2 := N) (π2 := stack_of_context E); assumption.
Qed.

Theorem step_terminates :
  forall M, well_typed M ->
  exists W, (M ⊣ [] -k->* W ⊣ []) /\ normal_form_step W ([]).
Proof.
  intros.
  pose proof weak_terminates M H. destruct H0 as (W & ? & ?).
  pose proof step_simulates_weak_bigstep M W H1 H0. exists W. split.
  * assumption.
  * apply value_or_abs_normal_form_step. assumption.
Qed.