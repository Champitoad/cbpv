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

Axiom weak_terminates : forall M,
  well_typed M ->
  exists W, M -w->* W /\ value_or_abs W.

Lemma app_cons_app {A} : forall (l1 l2 : list A) (a : A),
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1, l2; firstorder.
  rewrite <- app_comm_cons. rewrite IHl1.
  rewrite app_comm_cons. reflexivity.
Qed.

Remark step_stack_closure π : forall M1 π1 M2 π2,
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

Lemma step_simulates_weak_comp E : forall M N,
  let π := stack_of_context E in
  M --> N -> E[M] ⊣ [] -k->* N ⊣ π.
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

Lemma step_context_to_stack E : forall M,
  let π := stack_of_context E in
  E[M] ⊣ [] -k->* M ⊣ π.
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

Lemma value_or_abs_normal_form_step W :
  value_or_abs W -> normal_form_step W ([]).
Proof.
  intros. intro. destruct H0 as (M' & π' & H0). destruct H.
  * destruct H; inversion H0.
  * inversion H0.
Qed.

Lemma multistep_deterministic : TODO _.
Proof.
Admitted.

Lemma one_way_to_normal_form : forall M1 π1 M2 π2 M3 π3,
  (M1 ⊣ π1 -k->* M3 ⊣ π3) -> (normal_form_step M3 π3) ->
  (M1 ⊣ π1 -k->* M2 ⊣ π2) ->
  (M2 ⊣ π2 -k->* M3 ⊣ π3).
Proof.
  (* The proof will use multistep_deterministic *)
Admitted.

Theorem step_simulates_weak_bigstep : forall M W,
  value_or_abs W ->
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

Theorem step_terminates : forall M,
  well_typed M ->
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

Definition eval_step (s : state) : state :=
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

Lemma eval_step_simulates_step : forall M π M' π',
  (M ⊣ π -k-> M' ⊣ π') ->
  eval_step (M -| π) = (M' -| π').
Proof.
  destruct 1; simpl; auto.
  * destruct H; auto. destruct n; auto.
  * destruct n; auto.
Qed.

Fixpoint run (fuel : nat) (s : state) { struct fuel } : state :=
  let (M, π, status) := s in
  match fuel, status with
  | 0, _ | S _, Done => State M π Done
  | S n, Running => run n (eval_step s)
  end.

Lemma run_simulates_step : forall M π V,
  value V ->
  (M ⊣ π -k->* V ⊣ []) ->
  exists n, run n (M -| π) = State V ([]) Done.
Proof.
  induction 2.
  * exists 0. simpl. reflexivity.
  * apply eval_step_simulates_step in H0. apply IHmultistep in H.
    destruct H as (n & ?). exists (S n).
    unfold run. rewrite H0. fold run. assumption.
Qed.

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

Lemma eval_simulates_one_step : forall M π V,
  value V ->
  (M ⊣ π -k-> V ⊣ []) ->
  exists n, eval n (M -| π) = V.
Proof.
  intros. eapply multistep_step in H0; eauto.
  pose proof (run_simulates_step M π V H H0).
  destruct H1 as (n & ?). exists n. unfold eval.
  destruct (run n (M -| π)). inversion_clear H1. auto.
Qed.

Theorem eval_simulates_step : forall M π V,
  value V ->
  (M ⊣ π -k->* V ⊣ []) ->
  exists n, eval n (M -| π) = V.
Proof.
  intros. pose proof (run_simulates_step M π V H H0).
  destruct H1 as (n & ?). exists n. unfold eval.
  destruct (run n (M -| π)). inversion_clear H1. auto.
Qed.

Lemma eval_terminates : forall M π,
  exists n M', eval n (M -| π) = M'.
Proof.
Admitted.

Lemma run_eval_step : forall M π M' π',
  eval_step (M -| π) = (M' -| π') ->
  exists n, run n (M -| π) = run n (eval_step (M -| π)).
Proof.
  intros. destruct (eval_terminates M π) as (n & P & ?).
  exists n. unfold run at 1.
Admitted.

Lemma run_invariant_by_step : forall M π M' π',
  (M ⊣ π -k-> M' ⊣ π') ->
  exists n, run n (M -| π) = run n (M' -| π').
Proof.
  intros.
  pose proof (eval_step_simulates_step M π M' π' H).
  destruct (run_eval_step M π M' π' H0) as (n & ?).
  exists n. rewrite H1. rewrite H0. reflexivity.
Qed.

Theorem eval_invariant_by_step : forall M π M' π',
  (M ⊣ π -k-> M' ⊣ π') ->
  exists n, eval n (M -| π) = eval n (M' -| π').
Proof.
  intros. destruct (run_invariant_by_step M π M' π' H) as (n & ?).
  exists n. unfold eval. rewrite H0. reflexivity.
Qed.

(** Question 4 *)

Inductive valid_stack_judgment : general -> stack -> general -> Prop :=

| T_Empty τ :
  τ ⊢ [] : τ

| T_Der σ π τ :
  σ ⊢ π : τ ->
  !σ ⊢ (Der :: π) : τ

| T_Succ π τ :
  ι ⊢ π : τ ->
  ι ⊢ (Succ :: π) : τ

| T_Arg (φ : positive) σ V π τ :
  ([] ⊢ V : φ)%typing -> σ ⊢ π : τ ->
  (φ -o σ) ⊢ (Arg V :: π) : τ

| T_Fun (φ : positive) M π τ σ :
  ([] ⊢ M : φ -o σ)%typing -> σ ⊢ π : τ ->
  φ ⊢ (Fun M :: π) : τ

| T_If N z P π τ σ :
  ([] ⊢ N : σ)%typing -> ([z : ι] ⊢ P : σ)%typing -> σ ⊢ π : τ ->
  ι ⊢ (If N z P :: π) : τ

where "σ ⊢ π : τ" := (valid_stack_judgment σ π τ) : machine_scope.

Hint Constructors valid_stack_judgment.

Reserved Notation "⊢ ( M , π )  : σ" (at level 100, π at level 90, σ at level 90).

Inductive valid_state_judgment : term -> stack -> general -> Prop :=

| StateJudgment M π σ τ :
  ([] ⊢ M : σ)%typing -> σ ⊢ π : τ ->
  ⊢ (M, π) : τ

where "⊢ ( M , π ) : σ" := (valid_state_judgment M π σ) : machine_scope.

Open Scope typing_scope.

Definition subcontext (Γ Γ' : Typing.context) :=
  forall a, List.In a Γ -> List.In a Γ'.

Notation "Γ ⊂ Γ'" := (subcontext Γ Γ') (at level 60) : typing_scope.

Lemma valid_judgment_Wf_context Γ : forall M σ,
  Γ ⊢ M : σ -> Wf_context Γ.
Proof.
  induction 1; auto. firstorder.
Qed.

Lemma Wf_context_subcontext Γ Γ' :
  Γ' ⊂ Γ ->
  Wf_context Γ -> Wf_context Γ'.
Proof.
  unfold Wf_context. intros. apply (H0 a a') in H; auto.
Qed.

Lemma exchange x φ y ψ : forall Γ M σ,
  (x : φ :: y : ψ :: Γ) ⊢ M : σ <->
  (y : ψ :: x : φ :: Γ) ⊢ M : σ.
Proof.
  intros. split.
  * induction 1; auto.
Admitted.

Lemma weakening Γ Γ' :
  Γ ⊂ Γ' -> Wf_context Γ' ->
  forall M σ, Γ ⊢ M : σ -> Γ' ⊢ M : σ.
Proof.
  induction 3; auto.
  * destruct σ; intuition.
  * econstructor.
Admitted.

Lemma subst_typing :
  forall M σ V (φ : positive) x Γ (HWf : Wf_context Γ),
  (x : φ :: Γ) ⊢ M : σ -> Γ ⊢ V : φ ->
  Γ ⊢ M[V/x] : σ.
Proof.
  induction M; intros; simpl; inversion H; try (econstructor; eauto).
  * destruct σ.
    - case (string_dec x0 x) eqn:?.
      + destruct H4.
        ** congruence.
        ** admit. (* The proof would be by case on φ =? φ0,
                     but we don't have the decidable equality
                     on types yet... *)
      + destruct H4.
        ** congruence.
        ** constructor; assumption.
    - contradiction.
  * case (string_dec x0 x) eqn:?.
    - admit.
      (* Again a proof by case on φ =? φ0 *)
    - assert (Wf_context (x : φ :: Γ)).
      { apply valid_judgment_Wf_context in H6.
        eapply Wf_context_subcontext; eauto.
        unfold "⊂". intros. destruct H7.
        left. assumption. right. right. assumption. }
      eapply IHM; eauto.
      + apply exchange. eauto.
      + eapply weakening; eauto.
        unfold "⊂". intros. right. assumption.
  * case (string_dec x z) eqn:?.
    - admit.
      (* Again a proof by case on φ =? ι *)
    - assert (Wf_context (z : ι :: Γ)).
      { apply valid_judgment_Wf_context in H9.
        eapply Wf_context_subcontext; eauto.
        unfold "⊂". intros. destruct H10.
        left. assumption. right. right. assumption. }
      eapply IHM3; eauto.
      + apply exchange. eauto.
      + eapply weakening; eauto.
        unfold "⊂". intros. right. assumption.
Admitted.

Close Scope typing_scope.

Theorem step_subject_reduction σ : forall M π M' π',
  ⊢ (M, π) : σ -> (M ⊣ π -k-> M' ⊣ π') ->
  ⊢ (M', π') : σ.
Proof.
  destruct 2; inversion H.
  * inversion H0. econstructor; eauto.
  * inversion H0. econstructor; eauto. econstructor. congruence.
  * inversion H0. econstructor; eauto.
  * inversion H2. econstructor; eauto. econstructor; eauto. congruence.
  * inversion H0. econstructor; eauto.
  * inversion H0. inversion H1. econstructor; eauto. congruence.
  * inversion H0. inversion H1. econstructor; eauto.
  * inversion H1. inversion H2. econstructor; eauto.
    eapply subst_typing; eauto; try easy. congruence.
  * inversion H0. inversion H1. econstructor; eauto.
  * inversion H0. inversion H1. econstructor; eauto.
    eapply subst_typing; eauto.
Qed.

Theorem eval_subject_reduction σ : forall M π,
  ⊢ (M, π) : σ ->
  exists n, ([] ⊢ eval n (M -| π) : σ)%typing.
Proof.
  destruct 1.
Admitted.

End ΛHP_Machine.

(** Question 6 *)

Module Λv.

End Λv.

(** Question 7 *)

Module Λn.

Module Types.

Inductive type :=
| TNat
| TArrow (A : type) (B : type).

Hint Constructors type.

Delimit Scope n_types_scope with n_types.
Bind Scope n_types_scope with type.

Notation "'ι'" := TNat : n_types_scope.
Infix "~>" := TArrow (at level 20, right associativity) : n_types_scope.

Open Scope n_types_scope.

End Types.

Module Terms.

Import Types.

Inductive term :=
| Var (x : var)
| Nat (n : nat)
| Succ (M : term)
| Abs (x : var) (A : type) (M : term)
| App (M N : term).

Hint Constructors term.

Coercion Var : var >-> term.
Coercion Nat : nat >-> term.

Delimit Scope n_terms_scope with n_terms.
Bind Scope n_terms_scope with term.

Notation "'succ' M" := (Succ M) (at level 20) : n_terms_scope.
Notation "'λ' x : A , M" := (Abs x A M) (at level 50, x at level 25) : n_terms_scope.
Notation "< M > N" := (App M N) (at level 30, M at level 40) : n_terms_scope.

Open Scope n_terms_scope.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_nat n : value (Nat n).

Hint Constructors value.

Reserved Notation "M [ N / x ]" (at level 9, N at level 8).

Fixpoint subst (M N : term) (x : var) : term :=
  match M with
  | Var y => if string_dec x y then N else M
  | Nat _ => M
  | succ M => succ M[N/x]
  | λ y:A, M => λ y:A, if string_dec x y then M else M[N/x]
  | <M>M' => <M[N/x]>M'[N/x]
  end
where "M [ N / x ]" := (subst M N x) : n_terms_scope.

End Terms.

Module Typing.

Import Types Terms.

Inductive assertion :=
| Asst : var -> type -> assertion.

Hint Constructors assertion.

Delimit Scope n_typing_scope with n_typing.
Bind Scope n_typing_scope with assertion.

Notation "x : A" := (Asst x A) (at level 30) : n_typing_scope.

Open Scope n_typing_scope.

Definition context := list assertion.

Definition Wf_context (Γ : context) : Prop :=
  forall a a', List.In a Γ -> List.In a' Γ -> a <> a' ->
  let (x, _) := a in let (x', _) := a' in x <> x'.

Reserved Notation "Γ ⊢ M : A" (at level 10, M at level 20, A at level 20).

Inductive valid_judgment : context -> term -> type -> Prop :=

| T_Var Γ x A : Wf_context Γ ->
  In (x : A) Γ ->
  Γ ⊢ Var x : A

| T_Nat Γ n : Wf_context Γ ->
  Γ ⊢ Nat n : ι

| T_Succ Γ M :
  Γ ⊢ M : ι ->
  Γ ⊢ succ M : ι

| T_Abs Γ x M A B :
  (x : A :: Γ) ⊢ M : B ->
  Γ ⊢ (λ x:A, M) : A ~> B

| T_App Γ M N A B :
  Γ ⊢ M : A ~> B -> Γ ⊢ N : A ->
  Γ ⊢ (<M>N) : B

where "Γ ⊢ M : A" := (valid_judgment Γ M A) : n_typing_scope.

Hint Constructors valid_judgment.

Definition well_typed (M : term) :=
  exists A, [] ⊢ M : A.

End Typing.

Module Smallstep.

Import Types Terms.

Inductive context :=
| CHole
| CSucc (E : context)
| CApp (E : context) (M : term).

Hint Constructors context.

Reserved Notation "E [ M ]" (at level 9, M at level 8).

Fixpoint fill_context E M :=
  match E with
  | CHole => M
  | CSucc E => succ E[M]
  | CApp E N => <E[M]>N
  end
where "E [ M ]" := (fill_context E M) : n_smallstep_scope.

Open Scope n_smallstep_scope.

Reserved Notation "M --> N" (at level 60).
Reserved Notation "M -n-> N" (at level 60).

Inductive cbn_comp : term -> term -> Prop :=

| RSucc (n : nat) :
  succ n --> S n

| RBeta x A M N :
  <(λ x:A, M)> N --> M[N/x]

where "M --> N" := (cbn_comp M N) : n_smallstep_scope.

Hint Constructors cbn_comp.

Inductive cbn : term -> term -> Prop :=

| RCtx E M N :
  M --> N ->
  E[M] -n-> E[N]

where "M -n-> N" := (cbn M N) : n_smallstep_scope.

Hint Constructors cbn.

Notation "M '-n->*' N" := (multi cbn M N) (at level 60) : n_smallstep_scope.

End Smallstep.

Import ΛHP.Types ΛHP.Terms ΛHP.Typing ΛHP.Smallstep.
Import Types Terms Typing Smallstep.

Fixpoint compile_type (A : Λn.Types.type) : ΛHP.Types.general :=
  match A with
  | ι => ι
  | A ~> B => (!(compile_type A)) -o (compile_type B)
  end.

Fixpoint compile_term (M : Λn.Terms.term) : ΛHP.Terms.term :=
  match M with
  | Var x => der (ΛHP.Terms.Var x)
  | Nat n => ΛHP.Terms.Nat n
  | succ M => succ (compile_term M)
  | λ x:A, M => λ x:(!(compile_type A)), compile_term M
  | <M>N => <compile_term M>(compile_term N)!
  end.

Fixpoint compile_context (Γ : Λn.Typing.context) : ΛHP.Typing.context :=
  match Γ with
  | [] => []
  | x : A :: Γ => (x : !(compile_type A) :: compile_context Γ)%typing
  end.

Open Scope n_typing_scope.

Definition subcontext (Γ Γ' : Typing.context) :=
  forall a, List.In a Γ -> List.In a Γ'.

Notation "Γ ⊂ Γ'" := (subcontext Γ Γ') (at level 60) : typing_scope.

Lemma Wf_context_subcontext Γ Γ' :
  Γ' ⊂ Γ ->
  Wf_context Γ -> Wf_context Γ'.
Proof.
  unfold Wf_context. intros. apply (H0 a a') in H; auto.
Qed.

Lemma compile_Wf_context : forall Γ,
  Wf_context Γ -> ΛHP.Typing.Wf_context (compile_context Γ).
Proof.
  induction Γ.
  * simpl. easy.
  * simpl. intros. destruct a as (x & A).
Admitted.

Theorem compile_preserves_typing : forall Γ M A,
  Γ ⊢ M : A -> (compile_context Γ ⊢ compile_term M : compile_type A)%typing.
Proof.
  induction 1; simpl; econstructor; eauto.
  * econstructor.
    - apply compile_Wf_context. assumption.
    - induction Γ.
      + destruct H0.
      + simpl. destruct a as (y & B). destruct H0.
        ** inversion_clear H0. intuition.
        ** right. apply IHΓ; auto.
           eapply Wf_context_subcontext; eauto.
           unfold "⊂". intros. right. assumption.
  * apply compile_Wf_context. assumption.
Qed.

Lemma multi_weak_context_closure : forall E M N,
  M -w->* N -> (E[M] -w->* E[N])%smallstep.
Proof.
Admitted.

Lemma weak_simulates_cbn_subst : forall M N x,
  ((compile_term M)[((compile_term N)!)/x])%terms -w->* compile_term (M[N/x]).
Proof.
  induction M; intros; simpl.
  * case (string_dec x0 x) eqn:?.
    - econstructor.
      + apply (ΛHP.Smallstep.RCtx ΛHP.Smallstep.CHole
              (der (compile_term N) !) (compile_term N)).
        econstructor.
      + econstructor.
    - econstructor.
  * econstructor.
  * apply (multi_weak_context_closure (ΛHP.Smallstep.CSucc ΛHP.Smallstep.CHole)).
    apply IHM.
  * case (string_dec x0 x) eqn:?.
    - econstructor.
    - admit. (* Doesn't reduce under abstraction ! *)
  * admit.
Admitted.

Theorem weak_simulates_cbn : forall M N,
  M -n-> N -> compile_term M -w->* compile_term N.
Proof.
Admitted.

End Λn.