Require Import Defs Recdef Arith Lia.

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

End ΛHP_Machine.

(** Question 2 *)

Import ΛHP.
Import Terms Types Typing Smallstep.
Import ΛHP_Machine.

Inductive value_or_abs : term -> Prop :=
| value_or_abs_value V : value V -> value_or_abs V
| value_or_abs_abs x φ M : value_or_abs (λ x:φ, M).

Axiom weak_terminates :
  forall M, well_typed M ->
  exists W, M -w->* W /\ value_or_abs W.

Lemma step_simulates_weak_bigstep :
  forall M W, value_or_abs W ->
  M -w->* W -> M ⊣ [] -k->* W ⊣ [].
Proof.
Admitted.

Definition normal_form_step M π :=
  ~ exists M' π', M ⊣ π -k-> M' ⊣ π'.

Lemma value_or_abs_normal_form_step :
  forall W, value_or_abs W ->
  normal_form_step W ([]).
Proof.
Admitted.

Theorem step_terminates :
  forall M, well_typed M ->
  exists W, (M ⊣ [] -k->* W ⊣ []) /\ normal_form_step W ([]).
Proof.
Admitted.

forall M V, value V -> M -w->* V -> M ⊣ [] -k->* V ⊣ []

(** Question 3 *)

Inductive value_or_abs : term -> Prop :=
| value_or_abs_value V : value V -> value_or_abs V
| value_or_abs_abs x φ M : value_or_abs (λ x:φ, M).

Open Scope machine_scope.

Lemma step_context_closure π :
  forall M W, value_or_abs W ->
  (M ⊣ [] -k->* W ⊣ []) -> (M ⊣ π -k->* W ⊣ π).
Proof.
Admitted.

Lemma step_simulates_weak :
  forall M W, value_or_abs W ->
  M -w->* W -> M ⊣ [] -k->* W ⊣ [].
Proof.
  intros. induction H0.
  * apply multistep_refl.
  * admit.
Admitted.

(* Things that might be useful at some point *)

Fixpoint context_of_stack (π : stack) : context :=
  match π with
  | [] => CHole
  | m :: π =>
    let E := context_of_stack π in
    match m with
    | Der => CDer E
    | Succ => CSucc E
    | Arg V H => CArg E V H
    | Fun M => CFun M E
    | If N z P => CIf E N z P
    end
  end.

Definition normal_form_step M π :=
  ~ exists M' π', M ⊣ π -k-> M' ⊣ π'.

Lemma multistep_trans M1 π1 M2 π2 M3 π3 :
  (M1 ⊣ π1 -k->* M2 ⊣ π2) -> (M2 ⊣ π2 -k->* M3 ⊣ π3) -> (M1 ⊣ π1 -k->* M3 ⊣ π3).
Proof.
  intros. induction H.
  * assumption.
  * apply (multistep_step M1 π1 M2 π2 M3 π3).
    - assumption.
    - apply IHmultistep. assumption.
Qed.