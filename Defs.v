Require Export String List.
Export ListNotations.
Open Scope string_scope.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X} (R : relation X) : relation X :=
| multi_refl x :
  multi R x x
| multi_step x y z :
  R x y -> multi R y z -> multi R x z.

Hint Constructors multi.

Lemma multi_trans {X} (R : relation X) : forall x y z,
  multi R x y -> multi R y z -> multi R x z.
Proof.
  induction 1.
  * easy.
  * intro. eapply multi_step; eauto.
Qed.

Definition normal_form {X} (R : relation X) (x : X) : Prop :=
  ~ exists y, R x y.

Definition var := string.
Definition string_to_var : string -> var := fun s => s.
Coercion string_to_var : string >-> var.

Module ΛHP.

Module Types.

Inductive positive :=
| TNat
| TBang (σ : general)
with general :=
| TPos (φ : positive)
| TArrow (φ : positive) (σ : general).

Hint Constructors positive general.

Coercion TPos : positive >-> general.

Delimit Scope types_scope with types.
Bind Scope types_scope with positive.
Bind Scope types_scope with general.

Notation "'ι'" := TNat : types_scope.
Notation "! σ" := (TBang σ) (at level 10) : types_scope.
Infix "-o" := TArrow (at level 20, right associativity) : types_scope.

Open Scope types_scope.

End Types.

Module Terms.

Import Types.

Inductive term :=
| Var (x : var)
| Nat (n : nat)
| Bang (M : term)
| Der (M : term)
| Succ (M : term)
| Abs (x : var) (φ : positive) (M : term)
| App (M N : term)
| If (M N : term) (z : var) (P : term).

Hint Constructors term.

Coercion Var : var >-> term.
Coercion Nat : nat >-> term.

Delimit Scope terms_scope with terms.
Bind Scope terms_scope with term.

Notation "M !" := (Bang M) (at level 10) : terms_scope.
Notation "'der' M" := (Der M) (at level 20) : terms_scope.
Notation "'succ' M" := (Succ M) (at level 20) : terms_scope.
Notation "'λ' x : φ , M" := (Abs x φ M) (at level 50, x at level 25) : terms_scope.
Notation "< M > N" := (App M N) (at level 30, M at level 40) : terms_scope.
Notation "'#if' ( M , N , [ z ] P )" := (If M N z P) (at level 40) : terms_scope.

Open Scope terms_scope.

Inductive value : term -> Prop :=
| value_var x : value (Var x)
| value_nat n : value (Nat n)
| value_bang M : value (M!).

Hint Constructors value.

Reserved Notation "M [ N / x ]" (at level 9, N at level 8).

Fixpoint subst (M N : term) (x : var) : term :=
  match M with
  | Var y => if string_dec x y then N else M
  | Nat _ => M
  | M! => M[N/x]!
  | der M => der M[N/x]
  | succ M => succ M[N/x]
  | λ y:φ, M => λ y:φ, if string_dec x y then M else M[N/x]
  | <M>M' => <M[N/x]>M'[N/x]
  | #if (M, N', [z] P) => #if (M[N/x], N'[N/x], [z] if string_dec x z then P else P[N/x])
  end
where "M [ N / x ]" := (subst M N x) : terms_scope.

End Terms.

Module Typing.

Import Types Terms.

Inductive positive_assertion :=
| Pos : var -> positive -> positive_assertion.

Hint Constructors positive_assertion.

Delimit Scope typing_scope with typing.
Bind Scope typing_scope with positive_assertion.

Notation "x : φ" := (Pos x φ) (at level 30) : typing_scope.

Open Scope typing_scope.

Definition context := list positive_assertion.

Definition Wf_context (Γ : context) : Prop :=
  forall a a', List.In a Γ -> List.In a' Γ -> a <> a' ->
  let (x, _) := a in let (x', _) := a' in x <> x'.

Reserved Notation "Γ ⊢ M : σ" (at level 10, M at level 20, σ at level 20).

Inductive valid_judgment : context -> term -> general -> Prop :=

| T_Var Γ x σ : Wf_context Γ ->
  match σ with TPos φ => In (x : φ) Γ | _ => False end ->
  Γ ⊢ Var x : σ

| T_Nat Γ n : Wf_context Γ ->
  Γ ⊢ Nat n : ι

| T_Bang Γ M σ :
  Γ ⊢ M : σ ->
  Γ ⊢ M! : !σ

| T_Der Γ M σ :
  Γ ⊢ M : !σ ->
  Γ ⊢ der M : σ

| T_Succ Γ M :
  Γ ⊢ M : ι ->
  Γ ⊢ succ M : ι

| T_Abs Γ x M φ σ :
  ((x : φ) :: Γ) ⊢ M : σ ->
  Γ ⊢ (λ x:φ, M) : φ -o σ

| T_App Γ M N φ σ :
  Γ ⊢ M : φ -o σ -> Γ ⊢ N : φ ->
  Γ ⊢ (<M>N) : σ

| T_If Γ z M N P σ :
  Γ ⊢ M : ι -> Γ ⊢ N : σ -> ((z : ι) :: Γ) ⊢ P : σ ->
  Γ ⊢ (#if (M, N, [z] P)) : σ

where "Γ ⊢ M : σ" := (valid_judgment Γ M σ) : typing_scope.

Hint Constructors valid_judgment.

Example Valid_Var_Instance : ["x" : ι] ⊢ "x" : ι.
Proof.
  apply T_Var.
  * unfold Wf_context. firstorder. congruence.
  * intuition.
Qed.

Definition well_typed (M : term) :=
  exists σ, [] ⊢ M : σ.

End Typing.

Module Smallstep.

Import Types Terms.

Inductive context :=
| CHole
| CDer (E : context)
| CSucc (E : context)
| CArg (E : context) (V : term) (H : value V)
| CFun (M : term) (E : context)
| CIf (E : context) (N : term) (z : var) (P : term).

Hint Constructors context.

Reserved Notation "E [ M ]" (at level 9, M at level 8).

Fixpoint fill_context E M :=
  match E with
  | CHole => M
  | CDer E => der E[M]
  | CSucc E => succ E[M]
  | CArg E V _ => <E[M]>V
  | CFun N E => <N>E[M]
  | CIf E N z P => #if (E[M], N, [z] P)
  end
where "E [ M ]" := (fill_context E M) : smallstep_scope.

Delimit Scope smallstep_scope with smallstep.
Open Scope smallstep_scope.

Reserved Notation "M --> N" (at level 60).
Reserved Notation "M -w-> N" (at level 60).

Inductive weak_comp : term -> term -> Prop :=

| RDerBang M :
  der M! --> M

| RSucc (n : nat) :
  succ n --> S n

| RBeta x φ M V : value V ->
  <(λ x:φ, M)> V --> M[V/x]

| RIf_0 N z P : 
  #if (0, N, [z] P) --> N

| RIf_succ n N z P :
  #if (S n, N, [z] P) --> P[n/z]

where "M --> N" := (weak_comp M N) : smallstep_scope.

Hint Constructors weak_comp.

Inductive weak : term -> term -> Prop :=

| RCtx E M N :
  M --> N ->
  E[M] -w-> E[N]

where "M -w-> N" := (weak M N) : smallstep_scope.

Hint Constructors weak.

Notation "M '-w->*' N" := (multi weak M N) (at level 60) : smallstep_scope.

Remark value_normal_form V :
  value V -> normal_form weak V.
Proof.
  intros. unfold normal_form. intro. destruct H0 as (M & ?).
  destruct H0. destruct H0; induction E; inversion H.
Qed.

End Smallstep.

End ΛHP.