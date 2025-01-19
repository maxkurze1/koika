(* Implementing hoare logic for koika's evaluation *)
Require Import Unicode.Utf8.

Require Import Koika.TypedSyntax.
Require Import Koika.TypedSemantics.

Inductive test_reg_t :=
  one | two | three | four.
(*
Inductive type_list {K}: list K -> Type :=
| TLNil: type_list []
| TLCons {l'} (k: K) (ctx: type_list l'): type_list (k :: l').

Require Import Coq.Program.Equality. *)

(* The only element that exists of a type_list *)
(* Fixpoint finite_element_type_list {K} (l : list K) : type_list l :=
  match l with
  | nil => TLNil
  | cons k l' => TLCons k (finite_element_type_list l')
  end. *)


Definition R (r : test_reg_t) : type := bits_t 4.
Definition env := ContextEnv.(create) R.

Search (Type -> Type -> Type).

(* This type carries a list on the type level and every element of this type
  identifies an element of this list *)
Inductive type_list {K}: list K -> Type :=
  (* first element of the list *)
  | TLHead: forall k l, type_list (k :: l)
  (* later element of the list *)
  | TLTail: forall k l, type_list l -> type_list (k :: l).

Fixpoint type_list_ft_idx {K} {l : list K} (tl : type_list l) :=
  match tl with
  | TLHead _ _ => 0
  | TLTail _ _ tl' => S (type_list_ft_idx tl')
  end.

Fixpoint type_list_ft_elem {K} (l : list K) : list (type_list l) :=
  match l with
  | [] => []
  | k :: l' => TLHead _ _ :: map (TLTail _ _) (type_list_ft_elem l')
  end.

Lemma type_list_ft_seq {K} {l : list K} :
  map type_list_ft_idx (type_list_ft_elem l) = seq 0 (List.length l).
Proof.
  induction l as [| ? ? IH]. reflexivity.
  cbn; f_equal. rewrite map_map. cbn. rewrite <- map_map, IH.
  apply seq_shift.
Qed.

#[refine] Instance type_list_ft {K} {l : list K} : FiniteType (type_list l) := {
  finite_index := type_list_ft_idx;
  finite_elements := (type_list_ft_elem l);
}.
  - intro a; induction a; try reflexivity.
    simpl in *. apply map_nth_error. assumption.
  - rewrite type_list_ft_seq.
    apply seq_NoDup.
Defined.

Definition R_part1 (r : type_list [one; two]) : type := bits_t 4.
Definition R_part2 (r : type_list [two; three]) : type := bits_t 8.

Definition env1 := ContextEnv.(create) R_part1.
Definition env2 := ContextEnv.(create) R_part2.

Require Import Koika.Frontend.

Definition some_action : UInternalFunction test_reg_t empty_ext_fn_t :=
{{
fun some_action (a : bits_t 0) : unit_t =>
  read0(one);
  pass
}}.

Class ElemOfTL {K} (k : K) (l : list K):= el_of_tl : type_list l.

Instance ElemOfTLHead {K} {k : K} {l'} : ElemOfTL k (cons k l') := TLHead k l'.
Instance ElemOfTLTail {K} {k k': K} {l'} {eotl : ElemOfTL k l'} : ElemOfTL k (cons k' l') := TLTail k' l' eotl.


Arguments el_of_tl {K} k {l} {ElemOfTL} : assert.
(* Instance tl_head : type_list [] *)

Definition test : type_list [one; two] := el_of_tl two.

Compute test.

Declare Scope type_list_scope.
Notation "'[[' ']]'" := (type_list []) : type_list_scope.
Notation "'[[' a ';' .. ';' b ']]'" := (type_list (cons a .. (cons b nil) ..)) : type_list_scope.

Open Scope type_list_scope.

(* Notation "'>' reg" := (el_of_tl reg) (in custom koika at level 0, reg constr). *)

Definition some_action2 : UInternalFunction [[ ]] empty_ext_fn_t :=
{{
fun some_action (a : bits_t 0) : unit_t =>
  pass
}}.

Definition some_action : action


Section SepLog.

  Definition hprop {reg_t} {R : reg_t -> type} {REnv : Env reg_t}
    := REnv.(env_t) R -> Prop.
  (* Implication *)
  Definition himp {reg_t} {R : reg_t -> type} {REnv : Env reg_t}
    (p q : @hprop reg_t R REnv) := forall h, p h -> q h.
  (* Equivalence *)
  Definition heq {reg_t} {R : reg_t -> type} {REnv : Env reg_t}
    (p q : @hprop reg_t R REnv) := forall h, p h <-> q h.
  (* Lifting a pure proposition: it must hold, and the heap must be empty. *)
  Inductive empty_reg_t :=.
  Definition empty_R (r : empty_reg_t) : type := match r with end.
  Definition empty_r (r : empty_reg_t) : type_denote (empty_R r) := match r with end.
  Definition lift {REnv : Env _} (P : Prop) : @hprop empty_reg_t empty_R REnv :=
    fun h => P /\ h = (REnv.(create) (fun r => match r with end)).


End SepLog.

Section SeperationLogic.

  Context {pos_t var_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Notation action := (action pos_t var_t fn_name_t R Sigma).

  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.
  Context {sig: tsig var_t}.




  Definition assertion := tcontext sig -> REnv.(env_t) R -> Prop.

  Inductive HoareTriple {tau: type} : assertion -> action sig tau -> (tau -> assertion) -> Prop :=
  | HTSeq : ∀ P Q R a1 a2,
    HoareTriple P a1 Q -> (forall r, HoareTriple (Q r) a2 R) ->
    HoareTriple P (Seq a1 a2) R
  | HTFail :
    HoareTriple (fun _ _ => False) (Fail tau) (fun _ _ _ => False).

  Declare Scope log_scope.
  Notation "[]" := log_empty : log_scope.
  Bind Scope log_scope with Log.

  Definition interp_action_update_env {tau} env sigma Gamma slog alog (act : action sig tau) :=
    option_map (fun '(l, r, Gamma') => (commit_update env l, r, Gamma')) (interp_action (REnv := REnv) env sigma Gamma slog alog act).

  (* Definition interp_weaken_log :
    interp_action env sigma Gamma slog alog a = Some (l, r, Gamma') -,> *)

  Theorem hoare_triple_interp_action {tau} : ∀ P (a : action sig tau) Q,
    HoareTriple P a Q ->
    ∀ env Γ Γ' sigma r slog alog alog',
    P Γ (commit_update env (log_app alog slog)) ->
    interp_action env sigma Γ slog alog a = Some (alog', r, Γ') ->
    Q r Γ' (commit_update env (log_app alog' slog)).
  Proof.
    induction 1.
    - intros.
      simpl in H2.
      destruct (interp_action env sigma Γ slog alog a1) eqn:Heq; inversion H2.
      do 2 destruct p. clear H2.
      specialize (IHHoareTriple1 _ _ _ _ _ _ _ _ H1 Heq).
      specialize (fun log => IHHoareTriple2 (commit_update env l) log t).



      specialize (IHHoareTriple2 _ _ _ _ _ _ _ _ IHHoareTriple1 H4).
      assumption.
  Qed.
