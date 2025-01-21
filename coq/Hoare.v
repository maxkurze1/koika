(* Implementing hoare logic for koika's evaluation *)
Require Import Unicode.Utf8.

Require Import Koika.TypedSyntax.
Require Import Koika.TypedSemantics.
Require Import Koika.TypedParsing.

Require Import Koika.SemanticProperties.
(* for more details about hoare triples refer to the
 * software foundations book:
 * https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html
 *)

Lemma latest_write_cons_read : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) r1 r2 p,
  latest_write (log_cons r1 {| kind := LogRead; port := p; val := tt |} l) r2 = latest_write l r2.
Proof.
  intros; unfold latest_write, log_find, log_cons.
  destruct (eq_dec r1 r2) as [Heq|Hneq].
  + now rewrite Heq, get_put_eq.
  + now rewrite get_put_neq.
Qed.

Lemma commit_read : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) reg port env,
  commit_update env (log_cons reg {| kind := LogRead; port := port; val := tt |} l) = commit_update env l.
Proof.
  intros; unfold commit_update.
  apply create_funext; intro.
  now rewrite latest_write_cons_read.
Qed.

Lemma commit_write : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) reg port val env,
  commit_update env (log_cons reg {| kind := LogWrite; port := port; val := val |} l) = (REnv.(putenv) (commit_update env l) reg val).
Proof.
  intros; unfold commit_update.
  apply equiv_eq; unfold equiv; intros.
  rewrite getenv_create.
  destruct (eq_dec k reg).
  - subst. now rewrite get_put_eq, latest_write_cons_eq.
  - now rewrite get_put_neq, getenv_create, latest_write_cons_neq by easy.
Qed.

Lemma commit_read_log : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) env,
  (∀ reg, log_existsb l reg is_write0 = false) ->
  (∀ reg, log_existsb l reg is_write1 = false) ->
  commit_update env l = env.
Proof.
  intros; unfold commit_update.
  apply equiv_eq; intro.
  rewrite getenv_create.
  now rewrite latest_write_None.
Qed.

Lemma commit_read_log_get : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv) env reg,
  log_existsb l reg is_write0 = false ->
  log_existsb l reg is_write1 = false ->
  getenv REnv (commit_update env l) reg = getenv REnv env reg.
Proof.
  intros; unfold commit_update.
  rewrite getenv_create.
  now rewrite latest_write_None.
Qed.

Lemma list_find_opt_app_some : ∀ A B l l' x (fn: A -> option B),
  list_find_opt fn l = Some x -> list_find_opt fn (l ++ l') = Some x.
Proof.
  intros.
  induction l. inversion H.
  cbn in H.
  destruct (fn a) eqn:Ha.
  cbn. now rewrite Ha, H.
  cbn. rewrite Ha.
  auto.
Qed.

Lemma list_find_opt_app_none : ∀ A B l l' (fn: A -> option B),
  list_find_opt fn l = None -> list_find_opt fn (l ++ l') = list_find_opt fn l'.
Proof.
  intros.
  induction l. reflexivity.
  cbn in H.
  destruct (fn a) eqn:Ha.
  inversion H.
  cbn. rewrite Ha.
  auto.
Qed.

Lemma commit_update_app : ∀ reg_t(*  `{FiniteType reg_t}  *){R : reg_t -> type} {REnv : Env reg_t} (l1 l2 : Log R REnv) env,
  commit_update (commit_update env l2) l1 = commit_update env (log_app l1 l2).
Proof.
  intros.
  unfold commit_update.
  apply create_funext.
  intro.
  rewrite getenv_create.
  destruct (latest_write l1 k) eqn:Hl2.
  unfold log_app, map2.
  unfold latest_write, log_find.
  rewrite getenv_create.
  erewrite list_find_opt_app_some. reflexivity. assumption.
  unfold latest_write, log_find, log_app, map2. rewrite getenv_create. now rewrite list_find_opt_app_none.
Qed.

Lemma log_app_inv_tail : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l l1 l2: Log R REnv),
 log_app l1 l = log_app l2 l ->
 l1 = l2.
Proof.
  intros reg_t R REnv * H.
  apply equiv_eq in H.
  unfold log_app, equiv in H.
  setoid_rewrite getenv_map2 in H.
  setoid_rewrite app_inv_tail_iff in H.
  apply equiv_eq in H.
  assumption.
Qed.

Lemma may_read_empty : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} p r,
  @may_read _ R REnv log_empty log_empty p r = true.
Proof.
  intros.
  unfold may_read.
  destruct p; [apply andb_true_iff; split|];
  now rewrite log_existsb_app, negb_true_iff, log_existsb_empty.
Qed.

Lemma log_cons_app : ∀ reg_t `{FiniteType reg_t} {R : reg_t -> type} {REnv : Env reg_t} r le (l1 l2: Log R REnv),
  log_cons r le (log_app l1 l2) = log_app (log_cons r le l1) l2.
Proof.
  intros.
  apply equiv_eq; unfold equiv, log_cons, log_app, map2.
  intros.
  destruct (eq_dec k r) as [Heq | Heq].
  - rewrite Heq, ?getenv_create, ?get_put_eq.
    apply app_comm_cons.
  - now rewrite get_put_neq, ?getenv_create, get_put_neq.
Qed.

Ltac simpl_hoare :=
  repeat match goal with
  | H: interp_action _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; simpl in H
  | H: opt_bind ?a _ = Some _ |- _ => destruct a eqn:?Heq; inversion H; clear H
  | H: prod _ _ |- _ => destruct H
  | H: and _ _ |- _ => destruct H
  | H: Some _ = Some _ |- _ => apply Some_inj in H
  | H: pair _ _ = pair _ _ |- _ => apply pair_inj in H
  | H: match ?x with _ => _ end = _ |- _ => destruct x eqn:?
  (* | H: (if ?x then _ else _) = Some _ |- _ => destruct x eqn:? *)
  | H: ?A = ?A |- _ => clear H
  | H: ?B = true |- context[?B] => rewrite H
  | H: ?B = false |- context[?B] => rewrite H
  | H: context[may_read] |- _ => unfold may_read in H
  | H: context[may_write] |- _ => unfold may_write in H
  | |- context[may_read] => unfold may_read
  | |- context[may_write] => unfold may_write
  | H: context[latest_write0 (log_app _ _ )] |- _ => rewrite latest_write0_app in H
  | H: latest_write0 ?l ?r = Some _ |- context[latest_write0 ?l ?r] => rewrite H
  | H: latest_write0 ?l ?r = None   |- context[latest_write0 ?l ?r] => rewrite H
  | H: _ && _ = true |- _ => apply andb_prop in H
  | H: _ || _ = false |- _ => rewrite orb_false_iff in H
  | H: negb _ = true |- _ => rewrite negb_true_iff in H
  | H: context[log_existsb (log_app _ _)] |- _ => rewrite log_existsb_app in H
  | |- context[log_existsb (log_app _ _)] => rewrite log_existsb_app
  | |- context[latest_write0 (log_app _ _)] => rewrite latest_write0_app
  | H1: log_existsb ?l ?reg is_write0 = false,
    H2: log_existsb ?l ?reg is_write1 = false |-
      context[latest_write ?l ?reg] => rewrite latest_write_None by assumption
  | |- context[getenv _ (commit_update _ _) _] => rewrite getenv_commit_update
  | H: log_existsb ?l ?idx is_write1 = false |- context[latest_write ?l ?idx] =>
    rewrite latest_write_latest_write0 by assumption
  | |- context[opt_bind (Some _) _] => cbn
  | |- context[opt_bind None _] => cbn
  | _ => progress subst
  | _ => progress cbn
  | _ => easy
  end.

Section Hoare.

  Context {reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  #[local] Notation action := (TypedSyntax.action unit string string R Sigma).

  #[local] Ltac simpl_hoare' custom :=
    repeat (simpl_hoare + custom).

  #[local] Tactic Notation "simpl_hoare" "[" tactic(c) "]" :=
    (simpl_hoare' c).

  #[local] Ltac clear_all keep :=
    repeat match goal with
      | H: _ |- _ => lazymatch H with
        | keep => fail
        | _ => clear H
        end
      end.

  #[local] Tactic Notation "clear_all" "keep[" hyp(k) "]" :=
    clear_all k.

  (* We can actually only proof an implication here since some evaluations might
    fail with a None on the longer scheduler log, but succeed with a Some on the
    shortened version *)
  Fixpoint interp_scheduler_log_irrelevance sig tau (a : action sig tau) :
    ∀ (env : REnv.(env_t) R) sigma Γ Γ' slog slog' alog alog_out r,
    interp_action env sigma Γ (log_app slog slog') alog a = Some (alog_out, r, Γ') ->
    interp_action (commit_update env slog') sigma Γ slog alog a = Some (alog_out, r, Γ').
  Proof.
    Local Ltac solve_shed_log_irr := simpl_hoare [try match goal with
    | H: ∀ _ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ (log_app _ _) _ _ = Some _ ->
      interp_action _ _ _ _ _ _ = Some _,
      H1: interp_action _ _ _ (log_app ?sl ?sl2 ) ?al ?a = Some _ |-
      context[interp_action (commit_update _ ?sl2) _ _ ?sl ?al ?a] =>
      setoid_rewrite (H _ _ _ _ _ _ _ _ _ _ _ _ H1)
    end].
    destruct a; cbn; intros; solve_shed_log_irr.
    (* Special treatment necessary for the induction over the argument list of a
      internal function call *)
    - enough (H : ∀ l r Γ Γ',
        interp_args env sigma Γ (log_app slog slog') alog args = Some (l, r, Γ') ->
        interp_args (commit_update env slog') sigma Γ slog alog args = Some (l, r, Γ')
      ).
      + rewrite (H _ _ _ _ Heq). solve_shed_log_irr.
      + clear_all keep[ interp_scheduler_log_irrelevance ].
        induction args; intros; cbn in H; solve_shed_log_irr.
        rewrite (IHargs _ _ _ _ Heq).
        solve_shed_log_irr.
  Qed.

  Fixpoint interp_action_log_irrelevance `{FiniteType reg_t} sig tau (a : action sig tau) :
    ∀ (env : REnv.(env_t) R) sigma Γ Γ' slog alog alog' alog_out r,
    interp_action env sigma Γ slog (log_app alog' alog) a = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_action env sigma Γ (log_app alog slog) alog' a = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog.
  Proof.
    Local Ltac solve_act_log_irr := simpl_hoare [try match goal with
    | H: _ -> ∀ _ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ _ (log_app _ _) _ = Some _ ->
      ∃ _, _,
      H1: interp_action _ _ _ ?sl (log_app ?al1 ?al2) ?a = Some _ |-
      context[interp_action _ _ _ (log_app ?al2 ?sl) ?al1 ?a] =>
      let H' := fresh "H" in
      pose proof (H' := H _ _ _ _ _ _ _ _ _ _ _ _ _ H1);
      destruct H' as [?l [H' ?]]; subst;
      setoid_rewrite H'
    | |- context[log_cons _ _ (log_app _ _)] => rewrite log_cons_app by easy
    | _ => solve [eexists; split; reflexivity]
    end].
    destruct a; cbn; intros; solve_act_log_irr.
    - enough (Hargs: ∀ alog_out r Γ Γ',
        interp_args env sigma Γ slog (log_app alog' alog) args = Some (alog_out, r, Γ') ->
        exists alog_out',
        interp_args env sigma Γ (log_app alog slog) alog' args = Some (alog_out', r, Γ') /\
        alog_out = log_app alog_out' alog
      ).
      + pose proof (H' := Hargs _ _ _ _ Heq).
        destruct H' as [? [H' ?]]; subst.
        rewrite H'. solve_act_log_irr.
      + (* clear_all keep[ interp_action_log_irrelevance ]. *)
        clear Heq Heq0 t1 t0 l r alog_out Γ Γ' fn.
        induction args; intros; cbn in H0; solve_act_log_irr.
        pose proof (H' := IHargs _ _ _ _ Heq).
        destruct H' as [? [H' ?]]; subst.
        rewrite H'.
        solve_act_log_irr.
  Qed.

  Fixpoint interp_log_irrelevance `{FiniteType reg_t} sig tau (a : action sig tau) :
    ∀ (env : REnv.(env_t) R) sigma Γ Γ' slog alog alog_out r,
    interp_action env sigma Γ slog alog a = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_action (commit_update env (log_app alog slog)) sigma Γ log_empty log_empty a = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog.
  Proof.
    intros * H'.
    rewrite <- (log_app_empty_r alog) in H'.
    pose proof (Ha := interp_action_log_irrelevance _ _ _ _ _ _ _ _ _ _ _ _ H').
    destruct Ha as [log [Ha Hlog]].
    rewrite <- (log_app_empty_r (log_app _ _)) in Ha.
    pose proof (Hs := interp_scheduler_log_irrelevance _ _ _ _ _ _ _ _ _ _ _ _ Ha).
    eexists log.
    now split.
  Qed.

  Context {sig: tsig string}.
  Section HoareTriple.
    (* Context {var_t : Type}. *)
    Context {tau: type}.

    (** An _assertion_ is a logical claim about the state of a circuit

      This state consists of the register environment, the variable valuation (Gamma/Γ),
      the scheduler log and the current action log.

      Unfortunately, the scheduler/action log and the register environment cannot be
      combined into a single 'register state'. One might think it should be possible,
      since problems like multiple writes to the same register are already eliminated
      by assuming (in `hoare_triple`) that `interp_action` evaluated to `Some _`. However,
      consider the case where a read0 is used after a write0 (which is considered bad style but
      legal koika). In this case the read0 should observe the value from the beginning of
      the cycle. However when merging the logs and the environment into a single state - we
      would no longer know if the register value in this state is still the one from the
      beginning of the cycle or the one from a previous `write1`.

      Letz go over that again with a specific example. Assume we would have merge the
      logs and the env. Now we would like to proove this property.

      {{ env.[reg] = 5 }} <{ read0(reg) }> {{ ret = 5 }}

      However, we would fail, as coq would bring to our attention that `reg = 5` might also
      be the result of `env.[reg] = 3` and `action_log = [write0(reg, 5)]`.

      So its turns out, we actually cannot prove our postcondition in every possible state that
      satisfies our precondition.
      *)
    (* an assertion depends on the current register state `env`
      and then local variable context `Gamma` or `Γ` *)
    Definition assertion := REnv.(env_t) R -> tcontext sig -> Prop.
    (* the return assertion additionally gets the returned value
      of an action to reason about *)
    Definition ret_assertion := tau -> assertion.

    (* an assertion expression *)
    Definition a_exp {t : type} := REnv.(env_t) R -> tcontext sig -> t.
    Definition ret_a_exp {t : type} := tau -> @a_exp t.

    (* The grammar for Hoare logic Assertions *)
    (* Declare Custom Entry assertion. *)

    (** One small limitation of this approach is that we don't have
        an automatic way to coerce a function application that appears
        within an assertion to make appropriate use of the state when its
        arguments should be interpets as Imp arithmetic expressions.
        Instead, we introduce a notation [#f e1 .. en] that stands for [(fun
        st => f (e1 st) .. (en st)], letting us manually mark such function
        calls when they're needed as part of an assertion.  *)

    (* Notation "# f x .. y" := (fun st => (.. (f ((x : a_exp) st)) .. ((y : a_exp) st)))
                      (in custom assertion at level 2,
                      f constr at level 0, x custom assertion at level 1,
                      y custom assertion at level 1) : assertion_scope. *)

    (* Notation "P -> Q"  := (fun env Γ => (P : assertion) env Γ ->  (Q : assertion) env Γ) (in custom assertion at level 99, right associativity) : assertion_scope.
    Notation "P <-> Q" := (fun env Γ => (P : assertion) env Γ <-> (Q : assertion) env Γ) (in custom assertion at level 95) : assertion_scope.

    Notation "P \/ Q" := (fun env Γ => (P : assertion) env Γ \/ (Q : assertion) env Γ) (in custom assertion at level 85, right associativity) : assertion_scope.
    Notation "P /\ Q" := (fun env Γ => (P : assertion) env Γ /\ (Q : assertion) env Γ) (in custom assertion at level 80, right associativity) : assertion_scope.
    Notation "~ P" := (fun env Γ => ~ ((P : assertion) env Γ)) (in custom assertion at level 75, right associativity) : assertion_scope.
    Notation "a = b"  := (fun env Γ => (a : a_exp) env Γ =  (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope.
    Notation "a <> b" := (fun env Γ => (a : a_exp) env Γ <> (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope.
    Notation "a <= b" := (fun env Γ => (a : a_exp) env Γ <= (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope.
    Notation "a < b"  := (fun env Γ => (a : a_exp) env Γ <  (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope.
    Notation "a >= b" := (fun env Γ => (a : a_exp) env Γ >= (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope.
    Notation "a > b"  := (fun env Γ => (a : a_exp) env Γ >  (b : a_exp) env Γ) (in custom assertion at level 70) : assertion_scope. *)
    (* Notation "'True'" := True.
    Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
    Notation "'False'" := False.
    Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope. *)

    (* Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
    Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
    Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope. *)

    (* Notation "'(' x ')'" := x (in custom assertion) : assertion_scope. *)

    (** Occasionally we need to "escape" a raw "Coq-defined" function to express
        a particularly complicated assertion.  We can do that using a [$] prefix,
        as in [{{ $(raw_coq) }}].

        For example, [{{ $(fun st => forall X, st X = 0) }}] indicates an assertion that
        every variable of [X] maps to [0] in the given state.
     *)
    (* Notation "$ f" := f (in custom assertion at level 0, f constr at level 0) : assertion_scope. *)
    (* Notation "x" := (x%assertion) (in custom assertion at level 0, x constr at level 0) : assertion_scope. *)
    (* Notation "x" := (x) (in custom assertion at level 0, x constr at level 0) : assertion_scope. *)

    (* Definition aImpl (P Q : assertion) : Prop :=
      forall env Γ, P env Γ -> Q env Γ.

    Definition aIff (P Q : assertion) : Prop :=
      aImpl P Q /\ aImpl P Q.

    Notation "P '->>' Q" := (aImpl P Q) (at level 80).

    Notation "P '<<->>' Q" := (aIff P Q) (at level 80). *)

    (* This definition implements the idea of hoare logic for
      koika. (refer to https://en.wikipedia.org/wiki/Hoare_logic)

      Here we define hoare triples based on the evaluation of `interp_action`
      using empty logs as the scheduler and action log. At first, this might
      seem like a weaker proposition than all-quantifying these logs, however
      please note how it enables us to reason over the current register state
      in a much more concise manner.

      Consider the following example, where we all-quantify the logs and then
      try to express the precondition that the register `reg1` has the value 5.

      In this case it wouldn't suffice to state that

      `{{ env.[reg1] = 5 }} ... {{ .. }}`

      because we could easily come up with a pair of logs that write to `reg1`
      and effectively change its current state. Consequently, in order to even
      state our desired precondition, the assertions would additionally need
      reason over both log. Suppose they could, then we would probably state
      something similar to this:

      `{{ (env.[reg1] = 5 /\ latest_write slog reg1 = None /\ latest_write alog reg1 = None) \/
          (exists a, latest_write slog reg1 = Some a /\ a = 5 /\ latest_write alog reg1 = None ) \/
          (exists a, latest_write alog reg1 = Some a /\ a = 5)
      }} ... {{ .. }}`

      With this proposition we would have coveres all cases, either `reg1` was
      written in the action log and the written value is 5 or it was only
      written in the scheduler log, or it wasn't written at all and its prior
      value was 5.

      And while it might be possible to hide this monstrosity of a precondition
      with some fancy notations, reasoning with multiple logs turns out quite painful.

      As a consequence, I decided to state this theorem with empty logs, such that the
      assertions only need to reason over the current environment state. And to make
      hoare triples more meaningful, I've prooven a seperate theorem, which shows that
      all properties that hold on empty logs also apply to all-quantified logs.
      However, while this seems to goog to be true, there is a small catch, I had to
      add a restriction to the `read0` command. This restriction forbids using a `read0`
      on a registers that was written before. Prior to this work, the `read0` would
      simply always return the value from the start of the cycle. Nevertheless, using
      `read0` this way was already considered bad style and even forbidding it does
      not reduce the expressiveness of Koika. The same effect can be accomplished
      by invoking `read0` prior to any writes and saving the value in a local variable.
       *)
    Context {sigma : (∀ f : ext_fn_t, Sig_denote (Sigma f))}.
    Definition hoare_triple
      (P : assertion) (a : action sig tau) (Q : ret_assertion) : Prop :=
      ∀ env Γ Γ' log r,
      P env Γ ->
      interp_action env sigma Γ log_empty log_empty a = Some (log, r, Γ') ->
      Q r (commit_update env log) Γ'.

    Definition hoare_triple_args {argspec: tsig var_t}
      (P : assertion) (args : acontext sig argspec (pos_t := unit) (fn_name_t := string)) (Q : tcontext argspec -> assertion) : Prop :=
      ∀ env Γ Γ' log r_ctx,
      P env Γ ->
      interp_args env sigma Γ log_empty log_empty args = Some (log, r_ctx, Γ') ->
      Q r_ctx (commit_update env log) Γ'.

    (* The evaluation of this definition is identical to `hoare_triple`.
       However, it reorders its parameter to infer value like `reg_t`, `R`, etc.
       from the given action `a` prior to the type checking of P and Q.

       Which improves its usability *)
    Definition hoare_triple'
      (a : action sig tau) (P : assertion) (Q : ret_assertion) : Prop :=
      hoare_triple P a Q.
    Arguments hoare_triple' a & P Q : assert.

    Definition hoare_triple_triple'_eq : ∀ a P, hoare_triple P a = hoare_triple' a P
      := fun _ _ => eq_refl.

    (* This lemma prooves the log irrelevance -

      if an assertion holds on empty logs then it holds on every pair of logs *)
    Lemma hoare_log_irr `{FiniteType reg_t} : ∀ P a Q,
      hoare_triple P a Q ->
      ∀ env Γ Γ' slog alog alog' r,
      P (commit_update env (log_app alog slog)) Γ ->
      interp_action env sigma Γ slog alog a = Some (alog', r, Γ') ->
      Q r (commit_update env (log_app alog' slog)) Γ'.
    Proof.
      intros P a Q Hht env Γ Γ' slog alog alog' r HP Hin.
      unfold hoare_triple in Hht.
      apply interp_log_irrelevance in Hin.
      destruct Hin as [? [Hin  Hlog]].
      specialize (Hht (commit_update env (log_app alog slog)) Γ Γ' _ _ HP Hin).
      now rewrite commit_update_assoc, log_app_assoc, <- Hlog in Hht.
    Qed.
  End HoareTriple.
End Hoare.

Section HoareCoercions.
  Context {reg_t (* ext_fn_t *): Type}.
  Context {R: reg_t -> type}.
  (* Context {Sigma: ext_fn_t -> ExternalSignature}. *)
  Context {sig: tsig string}.
  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  Notation assertion := (@assertion reg_t R REnv sig).
  Notation ret_assertion := (@ret_assertion reg_t R REnv sig).
  Notation a_exp := (@a_exp reg_t R REnv sig).
  Notation ret_a_exp := (@ret_a_exp reg_t R REnv sig).

  Coercion assertion_of_Prop (P : Prop) : assertion := fun _ _ => P.
  #[warnings="-uniform-inheritance"]
  Coercion assertion_of_ret_assertion {tau} (a : assertion) : @ret_assertion tau := fun _ => a.

  Coercion a_exp_of_const {t : type} (v : t) : a_exp := fun _ _ => v.
  Coercion a_exp_of_reg (r : reg_t) : a_exp := fun env _ => env.[r].
  (* Coercion a_exp_of_var (s : string) : a_exp := fun _ Γ => Γ.[r]. *)

  #[warnings="-uniform-inheritance"]
  Coercion ret_a_exp_of_exp {tau} {t : type} (a : a_exp) : @ret_a_exp tau t := fun _ => a.
End HoareCoercions.

Module Import HoareNotations.
  (* todo checkout custom assignment notations from sf*)
  (* todo check level *)
  Notation "'{{' P '}}' a '{{' Q '}}'" := (hoare_triple P a Q) (at level 10).

  Declare Scope assertion_scope.
  Declare Scope assertion_expr_scope.
  Bind Scope assertion_scope with assertion.
  Bind Scope assertion_expr_scope with a_exp.
  Delimit Scope assertion_scope with assertion.
  Delimit Scope assertion_expr_scope with a_exp.

  Notation "'#' f x .. y" := (fun env Γ => (.. (f ((x : a_exp) env Γ)) .. ((y : a_exp) env Γ)))
    (at level 0, f constr at level 0) : assertion_scope.
  Notation "P -> Q"  := (fun env Γ => (P : assertion) env Γ ->  (Q : assertion) env Γ) : assertion_scope.
  Notation "P <-> Q" := (fun env Γ => (P : assertion) env Γ <-> (Q : assertion) env Γ) : assertion_scope.
  Notation "P /\ Q"  := (fun env Γ => (P : assertion) env Γ /\  (Q : assertion) env Γ) : assertion_scope.
  Notation "P \/ Q"  := (fun env Γ => (P : assertion) env Γ \/  (Q : assertion) env Γ) : assertion_scope.
  Notation "~ P"     := (fun env Γ => ~((P : assertion) env Γ)) : assertion_scope.

  Notation "a = b"  := (fun env Γ => (a : a_exp) env Γ =  (b : a_exp) env Γ) : assertion_scope.
  Notation "a <> b" := (fun env Γ => (a : a_exp) env Γ <> (b : a_exp) env Γ) : assertion_scope.
  Notation "a <= b" := (fun env Γ => (a : a_exp) env Γ <= (b : a_exp) env Γ) : assertion_scope.
  Notation "a < b"  := (fun env Γ => (a : a_exp) env Γ <  (b : a_exp) env Γ) : assertion_scope.
  Notation "a >= b" := (fun env Γ => (a : a_exp) env Γ >= (b : a_exp) env Γ) : assertion_scope.
  Notation "a > b"  := (fun env Γ => (a : a_exp) env Γ >  (b : a_exp) env Γ) : assertion_scope.

  (* Definition idk : assertion := True.
  Definition idk2 : assertion := False.

  Definition idk3 : assertion := idk -> idk2 /\ ((fun r _ _ => r = Ob) : assertion). *)

  Declare Scope ret_assertion_scope.
  Declare Scope ret_assertion_expr_scope.
  Bind Scope ret_assertion_scope with ret_assertion.
  Bind Scope ret_assertion_expr_scope with ret_a_exp.
  Delimit Scope ret_assertion_scope with ret_assertion.
  Delimit Scope ret_assertion_expr_scope with ret_a_exp.

  Notation "'#' f x .. y" := (fun ret env Γ => (.. (f ((x : a_exp) ret env Γ)) .. ((y : a_exp) ret env Γ)))
    (at level 0, f constr at level 0) : ret_assertion_scope.
  Notation "P -> Q"  := (fun ret env Γ => (P : ret_assertion) ret env Γ ->  (Q : ret_assertion) ret env Γ) : ret_assertion_scope.
  Notation "P <-> Q" := (fun ret env Γ => (P : ret_assertion) ret env Γ <-> (Q : ret_assertion) ret env Γ) : ret_assertion_scope.
  Notation "P /\ Q"  := (fun ret env Γ => (P : ret_assertion) ret env Γ /\  (Q : ret_assertion) ret env Γ) : ret_assertion_scope.
  Notation "P \/ Q"  := (fun ret env Γ => (P : ret_assertion) ret env Γ \/  (Q : ret_assertion) ret env Γ) : ret_assertion_scope.
  Notation "~ P"     := (fun ret env Γ => ~((P : assertion)   ret env Γ)) : ret_assertion_scope.

  Notation "a = b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ =  (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
  Notation "a <> b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ <> (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
  Notation "a <= b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ <= (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
  Notation "a < b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ <  (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
  Notation "a >= b" := (fun ret env Γ => (a : ret_a_exp) ret env Γ >= (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
  Notation "a > b"  := (fun ret env Γ => (a : ret_a_exp) ret env Γ >  (b : ret_a_exp) ret env Γ) : ret_assertion_scope.
End HoareNotations.

Notation "'hoare(' ass ')'" := (forall env Γ, (ass%assertion) env Γ).
Hint Unfold hoare_triple : hoare.

Section HoareFacts.
  Context {reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  (* Context {sig: tsig string}. *)
  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  Local Ltac specialize_hoare :=
    match goal with
    | HP: ?P _ _,
      HHT: hoare_triple ?P ?a _,
      Hin: interp_action _ _ _ _ _ ?a = Some _ |- _=>
      specialize (HHT _ _ _ _ _ HP Hin)
    end.

  #[local] Notation action sig tau := (action unit string string R Sigma sig tau).

  Section sigma.
    Context {sigma : (∀ f : ext_fn_t, Sig_denote (Sigma f))}.
    #[local] Notation "'{{' P '}}' a '{{' Q '}}'" := (@hoare_triple _ _ R Sigma REnv _ _ sigma P a Q) (at level 10).

    Theorem hoare_post_true {sig tau} : ∀ P (a : action sig tau),
      {{ P }} a {{ True }}.
    Proof. easy. Qed.

    Theorem hoare_pre_false {sig tau} : ∀ Q (a : action sig tau),
      {{ False }} a {{ Q }}.
    Proof. easy. Qed.

    (* as the name signifies this rule is intended for backwards reasoning *)
    Theorem hoare_weaken_pre {sig tau} : ∀ P P' Q (a : action sig tau),
      {{ P' }} a {{ Q }} ->
      hoare( P -> P' ) ->
      {{ P }} a {{ Q }}.
    Proof. eauto with hoare. Qed.

    (* as the name signifies this rule is intended for backwards reasoning *)
    Theorem hoare_strengthen_post {sig tau} : ∀ P Q Q' (a : action sig tau),
      {{ P }} a {{ Q' }} ->
      (forall ret env Γ, Q' ret env Γ -> Q ret env Γ) ->
      {{ P }} a {{ Q }}.
    Proof. eauto with hoare. Qed.

    (* A combination of both rules *)
    Theorem hoare_consequence {sig tau} : ∀ P P' Q Q' (a : action sig tau),
      {{ P' }} a {{ Q' }} ->
      hoare( P -> P' ) ->
      (forall ret env Γ, Q' ret env Γ -> Q ret env Γ) ->
      {{ P }} a {{ Q }}.
    Proof. eauto with hoare. Qed.

    Theorem hoare_fail {sig} tau : ∀ Q,
      {{ True }} (Fail tau : action sig _) {{ Q }}.
    Proof. easy. Qed.

    Theorem hoare_var {sig tau} {k} (m : member (k,tau) _) : ∀ Q,
      {{ fun env Γ => Q (cassoc m Γ) env Γ }} (Var m : action sig tau) {{ Q }}.
    Proof.
      intros. unfold hoare_triple. intros * HP; inversion 1; subst.
      now rewrite commit_update_empty.
    Qed.

    Theorem hoare_const {sig tau} (cst : type_denote tau) : ∀ Q,
      {{ fun env Γ => Q cst env Γ }} (Const cst : action sig tau) {{ Q }}.
    Proof. unfold hoare_triple; intros * HP; inversion 1; subst.
      now rewrite commit_update_empty.
    Qed.

    Theorem hoare_assign {sig tau} {k} (m : member (k,tau) _) (exp : action sig tau): ∀ P Q,
      {{ P }} exp {{ fun r env Γ => Q Ob env (creplace m r Γ)}} ->
      {{ P }} (Assign m exp) {{ Q }}.
    Proof. intros * Hexp; unfold hoare_triple; intros * HP; inversion 1; subst.
      simpl_hoare.
      now specialize_hoare.
    Qed.

    Theorem hoare_seq `{FiniteType reg_t} {sig tau} c1 (c2 : action sig tau) : ∀ P Q R,
      {{ Q }} c2 {{ R }} →
      {{ P }} c1 {{ Q }} →
      {{ P }} <{ `c1`; `c2` }> {{ R }}.
    Proof.
      intros * Hc2 Hc1. unfold hoare_triple. intros * HP Hinterp.
      simpl_hoare.
      specialize_hoare; cbv beta in Hc1.
      rewrite <- (log_app_empty_l l) in Hc1.
      pose proof (Hl := hoare_log_irr _ _ _ Hc2  _ _ _ _ _ _ _ Hc1 H1).
      now rewrite <- (log_app_empty_l log).
    Qed.

    (* Γ[v ↦ exp] == CtxCons (v, _) val_of_expr Γ *)
    Theorem hoare_bind `{FiniteType reg_t} {sig tau tau'} v (exp : action sig tau') (body : action _ tau) :
      ∀ P Q R,
      {{ Q }} body {{ fun r env Γ => R r env (ctl Γ) }} ->
      {{ P }} exp {{ fun r env Γ => Q env (CtxCons (v, tau') r Γ) }} ->
      {{ P }} (Bind v exp body) {{ R }}.
    Proof.
      intros * Hbody Hexp; unfold hoare_triple; intros * Hp Hin. cbn in Hin.
      simpl_hoare.
      specialize_hoare.
      cbn in Hexp.
      rewrite <- (log_app_empty_l l) in Hexp.
      pose proof (hoare_log_irr _ _ _ Hbody _ _ _ _ _ _ _ Hexp Heq0).
      cbn in H0.
      now rewrite log_app_empty_l in H0.
    Qed.

    Theorem hoare_if `{FiniteType reg_t} {sig tau} (c : action sig (bits_t 1)) (tr fl : action sig tau): ∀ P Qtr Qfl R,
      {{ Qfl }} fl {{ R }} ->
      {{ Qtr }} tr {{ R }} ->
      {{ P }} c {{ fun r env Γ => if Bits.single r then Qtr env Γ else Qfl env Γ }} ->
      {{ P }} <{if `c` then `tr` else `fl`}> {{ R }}.
    Proof.
      intros * Hfl Htr Hc; unfold hoare_triple; intros * Hp Hin. cbn in Hin.
      simpl_hoare; specialize_hoare; cbn in Hc; rewrite Heqb, <- (log_app_empty_l l) in Hc.
      + pose proof (hoare_log_irr _ _ _ Htr _ _ _ _ _ _ _ Hc H1). now rewrite log_app_empty_l in H0.
      + pose proof (hoare_log_irr _ _ _ Hfl _ _ _ _ _ _ _ Hc H1). now rewrite log_app_empty_l in H0.
    Qed.

    Theorem hoare_read `{FiniteType reg_t} {sig} port reg : ∀ Q,
      {{ fun env Γ => Q env.[reg] env Γ }} (Read port reg : action sig _) {{ Q }}.
    Proof. intros. unfold hoare_triple. intros * HP Hin; cbn in Hin.
      rewrite may_read_empty in Hin; inversion Hin; subst.
      rewrite commit_read, commit_update_empty by easy.
      simpl_hoare.
      now rewrite latest_write0_empty in Heqo0.
    Qed.

    Theorem hoare_write `{FiniteType reg_t} {sig} port reg exp : ∀ (P Q : assertion),
      {{ P }} exp {{ fun ret env Γ => Q (REnv.(putenv) env reg ret) Γ }} ->
      {{ P }} (Write port reg exp: action sig _) {{ Q }}.
    Proof. intros * Hexp; unfold hoare_triple;intros * HP Hin; cbn in Hin.
      simpl_hoare;
      specialize_hoare; cbn in Hexp;
      now rewrite commit_write by easy.
    Qed.

    Theorem hoare_unop {sig} fn (a1 : action sig _) : ∀ P Q,
      {{ P }} a1 {{ fun r env Γ => Q ((PrimSpecs.sigma1 fn) r) env Γ }} ->
      {{ P }} (Unop fn a1) {{ Q }}.
    Proof. intros * Ha1. unfold hoare_triple. intros * HP Hin. cbn in Hin.
      simpl_hoare.
      now specialize_hoare.
    Qed.

    Theorem hoare_binop `{FiniteType reg_t} {sig} fn a1 (a2 : action sig _) r1: ∀ P Q R,
      {{ Q }} a2 {{ fun r2 env Γ => R ((PrimSpecs.sigma2 fn) r1 r2) env Γ }} ->
      {{ P }} a1 {{ fun r env Γ => r1 = r /\ Q env Γ }} ->
      {{ P }} (Binop fn a1 a2) {{ R }}.
    Proof. intros * Ha1 Ha2. unfold hoare_triple. intros * HP Hin. cbn in Hin.
      simpl_hoare.
      specialize_hoare.
      cbn in Ha2.
      destruct Ha2 as [? Ha2]. subst.
      rewrite <- (log_app_empty_l l) in Ha2.
      pose proof (hoare_log_irr _ _ _ Ha1 _ _ _ _ _ _ _ Ha2 Heq0).
      cbn in H0.
      now rewrite log_app_empty_l in H0.
    Qed.

    Theorem hoare_apos {sig tau} pos (a : action sig tau): ∀ P Q,
      {{ P }} a {{ Q }} ->
      {{ P }} (APos pos a) {{ Q }}.
    Proof. easy. Qed.
  End sigma.

  Theorem hoare_ext_call {sig} sigma fn a: ∀ P Q,
    hoare_triple P a (fun r env Γ => Q (sigma fn r) env Γ) (sigma := sigma) (REnv := REnv) ->
    hoare_triple P (ExternalCall fn a : action sig _) Q (sigma := sigma) (REnv := REnv).
  Proof. intros * Ha. unfold hoare_triple. intros * HP Hin. cbn in Hin.
    simpl_hoare.
    now specialize_hoare.
  Qed.

  (* Theorem hoare_int_call {sig tau} *)

End HoareFacts.

Require Import Koika.Frontend.

Inductive empty_reg_t :=.
Definition empty_R (r : empty_reg_t) : type := match r with end.

Definition min : function empty_R empty_Sigma := <{
fun min (a : bits_t 5) (b : bits_t 5) : bits_t 5 =>
  if (a < b)
    then a
    else b
}>.

Definition convert_ctx {K sig} : @TypedSemantics.tcontext K sig ->
  context (fun k_tau : K * type => snd k_tau) sig.
  exact id.
Defined.
Notation "ctx .[ f ]" := (@cassoc _ _ _ (f,_) _ (convert_ctx ctx)).
(* Set Typeclasses Debug. *)


(* Notation "{{ P }} a {{ Q }}" := (hoare_triple' a P Q) (only printing). *)
(* Notation "{ P } a { Q }" := (HoareTriple (fun _ _ _ _ => P) a Q) (only printing). *)

(* Notation "'Γ.[' a ']'" := ((fun _ Γ => @cassoc _ _ _ (a, _) _ (convert_ctx Γ)) : a_exp) (a custom koika_t_var). *)

Open Scope nat_scope.


Ltac hoare :=
  match goal with
  | |- hoare_triple ?P ?a ?Q => not_evar P; eapply (hoare_weaken_pre P _ Q a)
  end;
  repeat lazymatch goal with
  | |- hoare_triple _ (Fail ?tau) ?Q            => eapply (hoare_fail tau Q)
  | |- hoare_triple _ (Var ?m) ?Q               => eapply (hoare_var m Q)
  | |- hoare_triple _ (Const ?cst) ?Q           => eapply (hoare_const cst Q)
  | |- hoare_triple _ (Assign ?m ?exp) ?Q       => eapply (hoare_assign m exp _ Q)
  | |- hoare_triple _ (Seq ?c1 ?c2) ?R          => eapply (hoare_seq c1 c2 _ _ R)
  | |- hoare_triple _ (Bind ?var ?exp ?body) ?R => eapply (hoare_bind var exp body _ _ R)
  | |- hoare_triple _ (If ?c ?tr ?fl) ?R        => eapply (hoare_if c tr fl _ _ _ R)
  | |- hoare_triple _ (Read ?p ?idx) ?Q         => eapply (hoare_read p idx Q)
  | |- hoare_triple _ (Write ?p ?idx ?exp) ?Q   => eapply (hoare_write p idx exp _ Q)
  | |- hoare_triple _ (Unop ?fn ?a1) ?Q         => eapply (hoare_unop fn a1 _ Q)
  | |- hoare_triple _ (Binop ?fn ?a1 ?a2) ?R    => eapply (hoare_binop fn a1 a2 _ _ _ R)
  | |- hoare_triple _ (ExternalCall ?fn ?a) ?Q  => eapply (hoare_ext_call _ fn a _ Q)
  (* | |- hoare_triple _ (InternalCall ?fn ?args) ?Q => TODO *)
  | |- hoare_triple _ (APos ?pos ?a) ?Q         => eapply (hoare_apos pos a _ Q)
  end.

Lemma min_correct m n env:
  hoare_triple' (sigma := empty_sigma) (REnv := env)

  min.(int_body)
  (* (Γ.[ a ] = (a_exp_of_const (Bits.of_nat 5 m)) /\ Γ.[ b ] = Bits.of_nat 5 n) *)
  (fun _env Γ => Γ.["a"] = Bits.of_nat 5 m /\ Γ.["b"] = Bits.of_nat 5 n)
  (fun r _env _Γ => r = if m <? n then Bits.of_nat 5 m else Bits.of_nat 5 n).
Proof.
  unfold hoare_triple'.
  unfold min, int_body.
  unfold TypedParsing.refine_sig_tau.
  hoare.
  unfold convert_ctx, id. intros. destruct H. rewrite ?H, ?H0. split. reflexivity.
  simpl (arg2Sig _).
  rewrite H0.
  simpl (Bits.single _).
Admitted.
