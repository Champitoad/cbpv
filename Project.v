Require Import Defs.
Open Scope list_scope.

Axiom TODO : forall A, A.

Module ΛHP_Machine.

Import ΛHP.
Import Terms Types Typing Smallstep.

Inductive marker :=
| Der
| Succ
| Arg (V : term)
| Fun (M : term)
| If (N : term) (z : var) (P : term).

Hint Constructors marker.

Definition stack := list marker.

Reserved Notation "M ⊣ π -k-> M' ⊣ π'" (at level 100, M' at level 99).

(** Question 1 *)

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

Hint Constructors step.

Open Scope machine_scope.

Reserved Notation "M ⊣ π -k->* M' ⊣ π'" (at level 100, M' at level 99).

Inductive multistep : term -> stack -> term -> stack -> Prop :=

| multistep_refl M π :
  M ⊣ π -k->* M ⊣ π

| multistep_step M1 π1 M2 π2 M3 π3 :
  (M1 ⊣ π1 -k-> M2 ⊣ π2) -> (M2 ⊣ π2 -k->* M3 ⊣ π3) -> (M1 ⊣ π1 -k->* M3 ⊣ π3)

where "M ⊣ π -k->* M' ⊣ π'" := (multistep M π M' π') : machine_scope.

Hint Constructors multistep.

Lemma multistep_trans M1 π1 M2 π2 M3 π3 :
  (M1 ⊣ π1 -k->* M2 ⊣ π2) -> (M2 ⊣ π2 -k->* M3 ⊣ π3) -> (M1 ⊣ π1 -k->* M3 ⊣ π3).
Proof.
  intros. induction H.
  * assumption.
  * apply (multistep_step M1 π1 M2 π2 M3 π3).
    - assumption.
    - apply IHmultistep. assumption.
Qed.

(** Question 2/3 *)

Inductive value_or_abs : term -> Prop :=
| value_or_abs_value V : value V -> value_or_abs V
| value_or_abs_abs x φ M : value_or_abs (λ x:φ, M).

Hint Constructors value_or_abs.

(** To prove that the machine terminates, we assume that weak reduction terminates,
    and then show that the machine simulates weak reduction (in bigstep semantics) *)

Axiom weak_terminates :
  forall M, well_typed M ->
  exists W, M -w->* W /\ value_or_abs W.

Lemma app_cons_app {A} :
  forall (l1 l2 : list A) (a : A),
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1, l2; firstorder.
  rewrite <- app_comm_cons. rewrite IHl1.
  rewrite app_comm_cons. reflexivity.
Qed.

Remark step_stack_closure π :
  forall M1 π1 M2 π2,
  (M1 ⊣ π1 -k->* M2 ⊣ π2) -> (M1 ⊣ π1 ++ π -k->* M2 ⊣ π2 ++ π).
Proof.
  induction π.
  * intros. rewrite 2 app_nil_r. assumption.
  * intros.
    rewrite app_cons_app with (l1 := π1).
    rewrite app_cons_app with (l1 := π2).
    apply IHπ. induction H.
    - apply multistep_refl.
    - induction a; econstructor; eauto;
      destruct H; econstructor; eauto.
Qed.

Fixpoint stack_of_context E :=
  match E with
  | CHole => []
  | CDer E => stack_of_context E ++ [Der]
  | CSucc E => stack_of_context E ++ [Succ]
  | CArg E V _ => stack_of_context E ++ [Arg V]
  | CFun M E => stack_of_context E ++ [Fun M]
  | CIf E N z P => stack_of_context E ++ [If N z P]
  end.

Lemma step_simulates_weak_comp E :
  let π := stack_of_context E in
  forall M N, M --> N -> E[M] ⊣ [] -k->* N ⊣ π.
Proof.
  intros. induction E; simpl in *.
  * destruct H; econstructor; eauto.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Der]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Succ]). apply step_stack_closure. assumption.
  * econstructor. eauto. econstructor. eauto.
    rewrite <- app_nil_l with (l := [Arg V]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Fun M0]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [If N0 z P]). apply step_stack_closure. assumption.
Qed.

Lemma step_context_to_stack E :
  let π := stack_of_context E in
  forall M, E[M] ⊣ [] -k->* M ⊣ π.
Proof.
  intros. induction E; simpl in *.
  * apply multistep_refl.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Der]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Succ]). apply step_stack_closure. assumption.
  * econstructor. eauto. econstructor. eauto.
    rewrite <- app_nil_l with (l := [Arg V]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [Fun M0]). apply step_stack_closure. assumption.
  * econstructor. eauto.
    rewrite <- app_nil_l with (l := [If N z P]). apply step_stack_closure. assumption.
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

Theorem step_simulates_weak_bigstep :
  forall M W, value_or_abs W ->
  M -w->* W -> M ⊣ [] -k->* W ⊣ [].
Proof.
  intros. induction H0 as [ M | M N W ].
  * apply multistep_refl.
  * destruct H0.
    pose proof (step_simulates_weak_comp E M N H0).
    pose proof (step_context_to_stack E N).
    pose proof (value_or_abs_normal_form_step W H). apply IHmulti in H.
    pose proof (one_way_to_normal_form E[N] ([]) N (stack_of_context E) W ([]) H H4 H3).
    apply multistep_trans with (M2 := N) (π2 := stack_of_context E); assumption.
Qed.

Theorem step_terminates :
  forall M, well_typed M ->
  exists N, (M ⊣ [] -k->* N ⊣ []) /\ normal_form_step N ([]).
Proof.
  intros.
  pose proof weak_terminates M H. destruct H0 as (W & ? & ?).
  pose proof step_simulates_weak_bigstep M W H1 H0. exists W. split.
  * assumption.
  * apply value_or_abs_normal_form_step. assumption.
Qed.

(** Question 5 *)

Inductive status := Running | Done.
Inductive state :=
| State (M : term) (π : stack) (status : status).

Delimit Scope eval_scope with eval.
Bind Scope eval_scope with state.

Notation "M -| π" := (State M π Running) (at level 80) : machine_scope.

Definition fstep (s : state) : state :=
  match s with
  (* Stack update rules *)
  | (der M -| π) => M -| Der :: π
  | (succ M -| π) => M -| Succ :: π
  | (<M>N -| π) => N -| Fun M :: π
  | (Var _ as V -| Fun M :: π)
  | (Nat _ as V -| Fun M :: π)
  | (_!    as V -| Fun M :: π) => M -| Arg V :: π
  | (#if (M, N, [z] P) -| π) => M -| If N z P :: π
  (* Reduction rules *)
  | (M! -| Der :: π) => M -| π
  | (Nat n -| Succ :: π) => Nat (S n) -| π
  | (λ x:φ, M -| Arg V :: π) => M[V/x] -| π
  | (Nat 0 -| If N z P :: π) => N -| π
  | (Nat (S n) -| If N z P :: π) => P[(Nat n)/z] -| π
  (* Status management *)
  | State M π _ => State M π Done
  end.

Fixpoint run (fuel : nat) (s : state) { struct fuel } : state :=
  let s := fstep s in
  let (M, π, status) := s in
  match fuel, status with
  | S n, Running => run n (M -| π)
  | _, _ => s
  end.

Fixpoint unstack M π :=
  match π with
  | [] => (M -| π)
  | m :: π =>
    let M := match m with
    | Der => der M
    | Succ => succ M
    | Fun N => <N>M
    | Arg V => <M>V
    | If N z P => #if (M, N, [z] P)
    end
    in unstack M π
  end.

Definition eval (fuel : nat) (s : state) : term :=
  let (V, π, _) := run fuel s in
  match π with
  | [] => V
  | _ => let (V', _, _) := unstack V π in V'
  end.

Theorem eval_invariant_by_step :
  forall M π M' π', (M ⊣ π -k-> M' ⊣ π') ->
  exists n, eval n (M -| π) = eval n (M' -| π').
Proof.
  intros.
Admitted.

Theorem eval_simulates_step :
  forall M π V, value V -> (M ⊣ π -k->* V ⊣ []) ->
  exists n, eval n (M -| π) = V.
Proof.
  intros.
Admitted.

(** Question 4 *)

Inductive valid_stack_judgment : general -> stack -> general -> Prop :=

| Todo σ π τ : σ ⊢ π : τ

where "σ ⊢ π : τ" := (valid_stack_judgment σ π τ) : machine_scope.

Hint Constructors valid_stack_judgment.

Reserved Notation "⊢ ( M , π ) : σ" (at level 100, π at level 90, σ at level 90).

Inductive valid_state_judgment : term -> stack -> general -> Prop :=

| StateJudgment M π σ τ :
  ([] ⊢ M : σ)%typing -> σ ⊢ π : τ ->
  ⊢ (M, π) : τ

where "⊢ ( M , π ) : σ" := (valid_state_judgment M π σ) : machine_scope.

Theorem step_subject_reduction σ :
  forall M π M' π',
  ⊢ (M, π) : σ -> (M ⊣ π -k-> M' ⊣ π') ->
  ⊢ (M', π') : σ.
Proof.
Admitted.

Theorem eval_subject_reduction σ :
  forall M π, ⊢ (M, π) : σ ->
  exists n, ([] ⊢ eval n (M -| π) : σ)%typing.
Proof.
Admitted.

(** Question 6 *)