Definition is_value (M : term) : bool :=
  match M with
  | Var _ => true
  | Nat _ => true
  | _ ! => true
  | _ => false
  end.

Definition value_is_value V :
  value V <-> is_value V = true.
Proof.
  intros. split; intro.
  * destruct H; easy.
  * destruct V; simpl in *; try easy.
    - apply value_var.
    - apply value_nat.
    - apply value_bang.
Defined.

Inductive status := Running | Done | Stuck.
Inductive state :=
| State (M : term) (π : stack) (status : status).

Bind Scope machine_scope with state.

Notation "M -| π " := (State M π Running) (at level 100) : machine_scope.

Definition fstep '(State M π status) : state :=
  match status with
  | Running =>
    match M, π with
    (* Stack update rules *)
    | der M, π => M -| Der :: π
    | succ M, π => M -| Succ :: π
    | <M>N, π => N -| Fun M :: π
    | V, Fun M :: π =>
      if is_value V
      then M -| Arg V :: π
      else V -| Fun M :: π
    | #if (M, N, [z] P), π => M -| If N z P :: π
    (* Reduction rules *)
    | M!, Der :: π => M -| π
    | Nat n, Succ :: π => Nat (S n) -| π
    | λ x:φ, M, Arg V :: π => M[V/x] -| π
    | Nat 0, If N z P :: π => N -| π
    | Nat (S n), If N z P :: π => P[(Nat n)/z] -| π
    (* Status management *)
    | _, [] => State M π Done
    | _, _ => State M π Stuck
    end
  | _ => State M π status
  end.

Lemma progress M π :
  let (_, _, status) := fstep (M -| π) in
  well_typed M -> status <> Stuck.
Proof.
Admitted.

Reserved Notation "| M |" (at level 100).

Fixpoint size_term M :=
  1 + match M with
  | Var _ | Nat _ => 0
  | M ! | der M | λ _:_, M => |M|
  | succ M => |M| + 1
  | <M>N => |M| + |N|
  | #if (M, N, [_] P) => |M| + |N| + |P|
  end
where "| M |" := (size_term M) : terms_scope.

Fixpoint size_stack π :=
  match π with
  | [] => 0
  | m :: π => |π| + match m with
    | Der => 0
    | Succ => 1
    | Fun M => |M|%terms
    | Arg _ => 0
    | If N _ P => (|N| + |P|)%terms
    end
  end
where "| π |" := (size_stack π) : stack_scope.

Bind Scope stack_scope with stack.

Definition size '(State M π _) := size_term M + size_stack π.

Lemma size_subst_var M y x :
  |M[(Var y)/x]| = |M|.
Proof.
  induction M; simpl; try auto; try (case (x =? x0); auto).
  case (x =? z); auto.
Qed.

Lemma size_subst_nat M n x :
  |M[(Nat n)/x]| = |M|.
Proof.
  induction M; simpl; try auto; try (case (x =? x0); auto).
  case (x =? z); auto.
Qed.

Definition scc := λ "n":ι, #if ("n", 1, ["z"] "z").
Definition two_church := λ"f" : !(ι -o ι), <der "f"> <der "f"> 0.
Definition two := <two_church> scc!.

Lemma well_typed_two :
  [] ⊢ two : ι.
Proof.
  unfold two. apply RApp with (φ := !(ι -o ι)).
  * unfold two_church. apply RAbs. apply RApp with (φ := ι).
    - apply RDer. apply RVar. intuition.
    - apply RApp with (φ := ι).
      + apply RDer. apply RVar. intuition.
      + apply RNat.
  * apply RBang. unfold scc. apply RAbs. apply RIf.
    - apply RVar. intuition.
    - apply RNat.
    - apply RVar. intuition.
Qed.

Compute |two|.
Compute let (M, _, _) := fstep (fstep (fstep (two -| []))) in |M|.

Compute size (two -| []).
Compute size (fstep (fstep (fstep (two -| [])))).

Lemma size_subst_value x φ M σ V :
  value V -> [x : φ] ⊢ M : σ -> [] ⊢ V : φ ->
  (|M| + |V| + 2) > |M[V/x]|.
Proof.
  intros. induction V.
  * rewrite size_subst_var. lia.
  * rewrite size_subst_nat. lia.
  * induction M.
    - simpl. case (x =? x0); simpl; lia.
    - simpl. lia.
    - simpl.
Admitted.

Function run (s : state) { measure size s } : state :=
  let s := fstep s in
  let (M, π, status) := s in
  match status with
  | Running => run (State M π status)
  | _ => s
  end.
Proof.
Admitted.

Definition eval (M : term) : term :=
  let (V, _, _) := run (M -| []) in V.

Compute eval 0.