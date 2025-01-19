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


Lemma log_find_empty : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} T r fn ,
  @log_find _ R REnv T log_empty r fn = None.
Proof.
  intros. unfold log_empty, log_find. now rewrite getenv_create.
Qed.

Lemma log_app_empty_l : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv),
  log_app log_empty l = l.
Proof.
  intros. apply equiv_eq.
  unfold equiv, log_app, map2, log_empty. intro.
  rewrite ?getenv_create.
  apply List.app_nil_l.
Qed.

Lemma log_app_empty_r : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l : Log R REnv),
  log_app l log_empty = l.
Proof.
  intros. apply equiv_eq.
  unfold equiv, log_app, map2, log_empty. intro.
  rewrite ?getenv_create.
  apply List.app_nil_r.
Qed.

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

(* Lemma log_cons_empty : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} le,
  @log_cons _ R REnv reg el log_empty = . *)

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

Lemma log_cons_app : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} r le (l1 l2: Log R REnv),
  log_cons r le (log_app l1 l2) = log_app (log_cons r le l1) l2.
Proof.
  intros.
  unfold log_cons.
  apply equiv_eq.
  unfold equiv.
  intros.
  unfold log_cons, log_app, map2, equiv.
  intro.
  (* unfold log_cons, log_app, map2. *)
  (* assert (getenv REnv (create REnv (λ k : reg_t, getenv REnv l1 k ++ getenv REnv l2 k)) r =
          getenv REnv ()) *)

  (* , equiv. *)
  (* intro. *)
  rewrite ?getenv_create.
  rewrite app_comm_cons.
Admitted.

Section Hoare.

  Context {pos_t (* var_t *) fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  (* Notation action := (action pos_t var_t fn_name_t R Sigma). *)

  (* Register environment a Map-Type from register names to their values *)
  Context {REnv: Env reg_t}.

  (** An _assertion_ is a logical claim about the state of a circuit

    This state consists of the register environment, the variable valuation (Gamma/Γ),
    the scheduler log and the current action log.

    Unfortunately, the scheduler/action log and the register environment cannot be
    combined into a single 'register state'. One might think it should be possible,
    since problems like multiple writes to the same register are already eliminated
    by assuming (in `hoare_triple`) that `interp_action` evaluated to `Some _`. However,
    consider the case where a read0 is used after a write0 (which is considered ugly but
    legal koika). In this case the read0 should observe the value from the beginning of
    the cycle. However when merging the logs and the environment into a single state - we
    would no longer know if the register value in this state is still the one from the
    beginning of the cycle or the one from a previous `write1`.

    Letz go over that again with a specific example. Assume we would have merge the
    logs and the env. Now we would like to proov this property.

    {{ reg = 5 }} <{ read0(reg) }> {{ ret = 5 }}

    However, we would fail, as coq would bring to our attention that `reg = 5` might also
    be the result of `env[reg] = 3` and `actionlog = [write0(reg, 5)]`.

    So its turns out, we actually cannot prove our postcondition in every possible state that
    satisfies our precondition.
    *)

  Lemma log_app_assoc : ∀ reg_t {R : reg_t -> type} {REnv : Env reg_t} (l1 l2 l3 : Log R REnv),
    log_app l1 (log_app l2 l3)  = log_app (log_app l1 l2) l3.
  Proof.
    intros.
    unfold log_app, map2. apply equiv_eq. unfold equiv. intro.
    rewrite ?getenv_create.
    apply List.app_assoc.
  Qed.

  Lemma commit_update_empty : ∀ (env : REnv.(env_t) R),
    commit_update env log_empty = env.
  Proof.
    intros.
    unfold commit_update.
    apply equiv_eq.
    unfold equiv.
    intros.
    rewrite getenv_create.
    unfold latest_write. now rewrite log_find_empty.
  Qed.

  Local Ltac simple_interp_some :=
    repeat match goal with
    | H: interp_action _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; simpl in H
    | H: opt_bind ?a _ = Some _ |- _ => destruct a eqn:?Heq; inversion H; clear H
    | H: prod _ _ |- _ => destruct H
    | H: and _ _ |- _ => destruct H
    | H: Some _ = Some _ |- _ => apply Some_inj in H
    | H: pair _ _ = pair _ _ |- _ => apply pair_inj in H
    | _ => progress subst
    end.

  Ltac solve_log_irrelevance :=
    repeat match goal with
    | H: ∀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ _ (log_app _ _) _ = Some _ ->
      interp_action _ _ _ (log_app _ _) _ _ = Some _ -> _,
      H1: interp_action _ _ _ ?l1 (log_app ?l2 ?l3) ?a = Some _,
      H2: interp_action _ _ _ (log_app ?l3 ?l1) ?l2 ?a = Some _ |- _ =>
      pose_once (H _ _ a _ _ _ _ _ _ _ _ _ _ _ _ H1 H2)
    | H: log_app _ ?l = log_app _ (log_app _ ?l) |- _ =>
      rewrite log_app_assoc in H;
      apply log_app_inv_tail in H
    | H: (if ?cond then Some _ else None) = Some _ |- _ =>
    destruct (cond) eqn:?Hc; inversion H
    | _ => progress simple_interp_some
    end;
    try solve [repeat match goal with
    | |- and _ _ => split
    | |- log_app (log_app _ _) _ = log_app _ (log_app _ _) => apply eq_sym, log_app_assoc
    | |- _ => solve [assumption + reflexivity + discriminate]
    end].

  Section Args.
(*
  Fixpoint interp_log_irrelevance' sig tau (a : action' R Sigma (sig := sig) (tau := tau)): ∀ (env : REnv.(env_t) R) sigma Γ Γ' Γ'' slog alog alog' alog_out alog_out'  r r',
    interp_action env sigma Γ slog (log_app alog' alog) a = Some (alog_out, r, Γ') ->
    interp_action env sigma Γ (log_app alog slog) alog' a = Some (alog_out', r', Γ'') ->

    (log_app alog_out slog) = (log_app alog_out' (log_app alog slog)) /\ r = r' /\ Γ' = Γ''.
    Context (interp_action:
                forall {sig: tsig var_t} {tau}
                  (Gamma: tcontext sig)
                  (sched_log: Log) (action_log: Log)
                  (a: action sig tau),
                  option (Log * type_denote tau * (tcontext sig))).

    Fixpoint interp_args'
              {sig: tsig var_t}
              (Gamma: tcontext sig)
              (sched_log: Log)
              (action_log: Log)
              {argspec: tsig var_t}
              (args: acontext sig argspec)
      : option (Log * tcontext argspec * (tcontext sig)) :=
      match args with
      | CtxEmpty => Some (action_log, CtxEmpty, Gamma)
      | @CtxCons _ _ argspec k_tau arg args =>
        let/opt3 action_log, ctx, Gamma := interp_args' Gamma sched_log action_log args in
        let/opt3 action_log, v, Gamma := interp_action _ _ Gamma sched_log action_log arg in
        Some (action_log, CtxCons k_tau v ctx, Gamma)
      end.
  End Args. *)
  Fixpoint interp_log_irrelevance' sig tau (a : action' R Sigma (sig := sig) (tau := tau)): ∀ (env : REnv.(env_t) R) sigma Γ Γ' Γ'' slog alog alog' alog_out alog_out'  r r',
    interp_action env sigma Γ slog (log_app alog' alog) a = Some (alog_out, r, Γ') ->
    interp_action env sigma Γ (log_app alog slog) alog' a = Some (alog_out', r', Γ'') ->

    (log_app alog_out slog) = (log_app alog_out' (log_app alog slog)) /\ r = r' /\ Γ' = Γ''.
    (* one should be able to show that r = r' and Γ' = Γ'' *)
  Proof.
    destruct a; cbn; intros.
    - discriminate.
    - inversion H; inversion H0. subst. repeat split. auto using log_app_assoc.
    - inversion H; inversion H0. subst. repeat split. auto using log_app_assoc.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
      destruct (Bits.single t0);
      solve_log_irrelevance.
    - solve_log_irrelevance.
      repeat split.
      now rewrite log_app_assoc, log_cons_app.
      now rewrite log_app_assoc.
    - solve_log_irrelevance.
      repeat split.
      now rewrite log_app_assoc, log_cons_app.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
    - solve_log_irrelevance.
      enough (∀ alo alo' r r' Γ Γ' Γ'',
        interp_args env sigma Γ slog (log_app alog' alog) args = Some (alo, r, Γ') ->
        interp_args env sigma Γ (log_app alog slog) alog' args = Some (alo', r', Γ'') ->
        (log_app alo slog) = (log_app alo' (log_app alog slog)) /\ r = r' /\ Γ' = Γ''
      ).
      + specialize (H _ _ _ _ _ _ _ Heq0 Heq).
        solve_log_irrelevance.
      + clear Heq Heq0 Heq1 Heq2 fn t0 t1 t4 t5 l l1 r r'.
        induction args.
        * intros. cbn in H, H0.
          solve_log_irrelevance.
        * intros. cbn in H, H0.
          solve_log_irrelevance.
          specialize (IHargs _ _ _ _ _ _ _ Heq0 Heq).
          solve_log_irrelevance.
    - solve_log_irrelevance.
  Qed.

  Lemma interp_log_irrelevance sig tau (a : action' R Sigma (sig := sig) (tau := tau)) :
    ∀ (env : REnv.(env_t) R) sigma Γ Γ' Γ'' slog alog alog_out alog_out'  r r',
    interp_action env sigma Γ slog alog a = Some (alog_out, r, Γ') ->
    interp_action env sigma Γ (log_app alog slog) log_empty a = Some (alog_out', r', Γ'') ->

    (log_app alog_out slog) = log_app alog_out' (log_app alog slog).
  Proof.
    intros.
    rewrite <- (log_app_empty_l _ alog) in H.
    pose proof (interp_log_irrelevance' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0).
    destruct H1.
    auto.
  Qed.


  Ltac solve_log_irrelevance' :=
    repeat match goal with
    | H: ∀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ (log_app _ _) _ _ = Some _ ->
      interp_action _ _ _ _ _ _ = Some _ -> _,
      H1: interp_action ?env _ _ (log_app ?l1 ?l2) _ ?a = Some _,
      H2: interp_action (commit_update ?env ?l2) _ _ ?l1 _ ?a = Some _ |- _ =>
      pose_once (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2)
    | H: log_app _ ?l = log_app _ (log_app _ ?l) |- _ =>
      rewrite log_app_assoc in H;
      apply log_app_inv_tail in H
    | H: (if ?cond then Some _ else None) = Some _ |- _ =>
    destruct (cond) eqn:?Hc; inversion H
    | _ => progress simple_interp_some
    end;
    try solve [repeat match goal with
    | |- and _ _ => split
    | |- log_app (log_app _ _) _ = log_app _ (log_app _ _) => apply eq_sym, log_app_assoc
    | |- _ => solve [assumption + reflexivity + discriminate]
    end].

  Lemma option_match_eq : ∀ A (o o' : option A) d,
  match
    match o with
    | Some a => Some a
    | None => o'
    end
  with
  | Some a => a
  | None => d
  end =
  match o with
  | Some a => a
  | None =>
      match o' with
      | Some a => a
      | None => d
      end
  end.
  Proof. intros. now destruct o, o'. Qed.

  Ltac solve_log_irrelevance'' :=
    repeat match goal with
    | H: ?A = ?A |- _ => clear H
    | H: ∀ _ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ (log_app _ _) _ _ = Some _ ->
      interp_action _ _ _ _ _ _ = Some _,
      H1: interp_action _ _ _ (log_app _ _ ) _ _ = Some _ |- _=>
      pose_once (H _ _ _ _ _ _ _ _ _ _ _ _ H1)
    | H: interp_action ?env ?sig ?Gam ?slog ?alog ?a = Some _ |-
      context[interp_action ?env ?sig ?Gam ?slog ?alog ?a] =>
      rewrite H
    | H: log_app _ ?l = log_app _ (log_app _ ?l) |- _ =>
      rewrite log_app_assoc in H;
      apply log_app_inv_tail in H
    | H: (if ?cond then Some _ else None) = Some _ |- _ =>
    destruct (cond) eqn:?Hc; inversion H
    | _ => progress simple_interp_some
    | _ => progress cbn
    | H: context[may_read] |- _ => unfold may_read in H
    | |- context[may_read] => unfold may_read
    | H: match ?p with | P0 => _ | P1 => _ end = _ |- _ => destruct p
    | H: _ && _ = true |- _ => apply andb_prop in H; destruct H
    | H: _ || _ = false |- _ => rewrite orb_false_iff in H; destruct H
    | H: negb _ = true |- _ => rewrite negb_true_iff in H
    | H: context[log_existsb (log_app _ _) _ _] |- _ => rewrite log_existsb_app in H
    | H: ?A = false |- context[?A] => rewrite H
    end;
    try solve [repeat match goal with
    | |- and _ _ => split
    | |- log_app (log_app _ _) _ = log_app _ (log_app _ _) => apply eq_sym, log_app_assoc
    | |- _ => solve [assumption + reflexivity + discriminate]
    end].

  Fixpoint interp_sched_log_irrelevance sig tau (a : action' R Sigma (sig := sig) (tau := tau)): ∀ (env : REnv.(env_t) R) sigma Γ Γ' slog slog' alog alog_out r,
    interp_action env sigma Γ (log_app slog slog') alog a = Some (alog_out, r, Γ') ->
    interp_action (commit_update env slog') sigma Γ slog alog a = Some (alog_out, r, Γ').
  Proof.
    destruct a; cbn; intros; try solve [solve_log_irrelevance''].
    - solve_log_irrelevance''.
      destruct (Bits.single t0);
      solve_log_irrelevance''.
    - solve_log_irrelevance''.
      +
        rewrite ?log_existsb_app.
        solve_log_irrelevance''.
        f_equal.
        f_equal.
        f_equal.
        (* unfold commit_update. *)
        rewrite getenv_commit_update.
        now rewrite latest_write_None.
      + rewrite ?log_existsb_app.
        solve_log_irrelevance''.
        f_equal.
        f_equal.
        f_equal.

        rewrite getenv_commit_update.

        rewrite log_app_assoc.
        rewrite (latest_write0_app _ slog') at 1.
        rewrite latest_write_latest_write0 by easy.
        apply eq_sym, option_match_eq.
    - solve_log_irrelevance''.
      unfold may_write in *.
      solve_log_irrelevance'';
      rewrite ?log_existsb_app;
      solve_log_irrelevance''.
    - solve_log_irrelevance''.
  Admitted.

  Fixpoint interp_sched_log_irrelevance'' sig tau (a : action' R Sigma (sig := sig) (tau := tau)): ∀ (env : REnv.(env_t) R) sigma Γ Γ' Γ'' slog slog' alog alog_out alog_out' r r',
    interp_action env sigma Γ (log_app slog slog') alog a = Some (alog_out, r, Γ') ->
    interp_action (commit_update env slog') sigma Γ slog alog a = Some (alog_out', r', Γ'') ->

    alog_out = alog_out' /\ r = r' /\ Γ' = Γ''.
  Proof.
    destruct a; cbn; intros; try solve [solve_log_irrelevance'].
    - solve_log_irrelevance'.
      destruct (Bits.single t0);
      solve_log_irrelevance'.
    - solve_log_irrelevance'.
      repeat split.
      clear H7 H6 H5 H4 H3 H2.
      rewrite getenv_commit_update.
      unfold may_read in Hc0.
      destruct port.
      + apply andb_prop in Hc0.
        destruct Hc0.
        rewrite negb_true_iff, log_existsb_app, orb_false_iff in H0, H.
        destruct H, H0.
        rewrite log_existsb_app, orb_false_iff in H1, H2.
        destruct H1, H2.
        now rewrite latest_write_None.
      + rewrite log_app_assoc.
        rewrite latest_write0_app.

        rewrite latest_write_latest_write0.
        apply option_match_eq.

        rewrite negb_true_iff, log_existsb_app, orb_false_iff in Hc0.
        destruct Hc0.
        rewrite log_existsb_app, orb_false_iff in H0.
        destruct H0.
        auto.
    - solve_log_irrelevance'.
      enough (∀ l1 l t4 t0 Γ Γ' Γ'',
        interp_args env sigma Γ (log_app slog slog') alog args = Some (l1, t4, Γ') ->
        interp_args (commit_update env slog') sigma Γ slog alog args = Some (l, t0, Γ'') ->
        l1 = l /\ t4 = t0 /\ Γ' = Γ''
      ).
      + specialize (H _ _ _ _ _ _ _ Heq0 Heq).
        destruct H, H0.
        subst.
        solve_log_irrelevance'.
      + clear Heq0 Heq Heq1 Heq2 fn t4 Γ Γ' Γ'' t0 t1 t5.
         (* intros. *)
        induction args.
        * intros. cbn in H, H0.
          solve_log_irrelevance'.
        * intros. cbn in H, H0.
          solve_log_irrelevance'.
          specialize (IHargs _ _ _ _ _ _ _ Heq0 Heq).
          solve_log_irrelevance'.
  Qed.

  Ltac solve_log_irrelevance''' :=
    repeat match goal with
    | H: ∀ _ _ _ _ _ _ _ _ _ _ _,
      interp_action _ _ _ _ _ _ = Some _ ->
      ∃ _, _,
      Hin: interp_action ?env _ _ ?slog ?alog _ = Some _ |-
      context [interp_action (commit_update ?env (log_app ?alog ?slog))] =>
      pose_once (H _ _ _ _ _ _ _ _ _ _ _ Hin)
    | H: interp_action ?env ?sig ?Gam ?slog ?alog ?a = Some _ |-
      context[interp_action ?env ?sig ?Gam ?slog ?alog ?a] =>
      rewrite H
    | H: ∃ _, _ |- _ => destruct H
    | H: context[let _ := _ in _] |-  _ =>
      cbv zeta in H
    | H: log_app _ ?l = log_app _ (log_app _ ?l) |- _ =>
      rewrite log_app_assoc in H;
      apply log_app_inv_tail in H
    | H: (if ?cond then Some _ else None) = Some _ |- _ =>
    destruct (cond) eqn:?Hc; inversion H
    | _ => progress simple_interp_some
    | _ => progress cbn
    end;
    try solve [repeat match goal with
    | |- and _ _ => split
    | |- log_app (log_app _ _) _ = log_app _ (log_app _ _) => apply eq_sym, log_app_assoc
    | |- _ => solve [assumption + reflexivity + discriminate]
    end].

  Fixpoint interp_log_irrelevance'' sig tau (a : action' R Sigma (sig := sig) (tau := tau)) : ∀  (env : REnv.(env_t) R) sigma Γ Γ' slog alog alog_out r,
    interp_action env sigma Γ slog alog a = Some (alog_out, r, Γ') ->
    exists alog_out',
    interp_action (commit_update env (log_app alog slog)) sigma Γ log_empty log_empty a = Some (alog_out', r, Γ') /\
    alog_out = log_app alog_out' alog.
  Proof.
  Admitted.
    (* destruct a; cbn; intros.
    - eexists. solve_log_irrelevance.
    - eexists. rewrite commit_update_empty. now inversion H.
    - eexists. solve_log_irrelevance.
      now rewrite commit_update_empty.
    - solve_log_irrelevance'''.
      eexists.
      now split.
    - solve_log_irrelevance'''.
      clear H H0 Heq t0.
      pose proof (interp_log_irrelevance'' _ _ _ _ _ _ _ _ _ _ _ H1).
      solve_log_irrelevance'''.
      rewrite H2 in H.
      assert (interp_action (commit_update env (log_app alog slog)) sigma t log_empty x a2 = Some (x0, r, Γ')).
  Admitted. *)

  Context {sig: tsig TypedParsing.var_t}.
  Section idk.
    Context {tau: type}.
    Notation action := (action' R Sigma (sig := sig) (tau := tau)).

    Definition assertion := REnv.(env_t) R -> tcontext sig -> Prop.

    Definition aTrue : assertion := fun _ _  => True.
    Definition aFalse : assertion := fun _ _  => False.

    Definition aImpl (P Q : assertion) : Prop :=
      forall env Γ, P env Γ -> Q env Γ.

    Definition aIff (P Q : assertion) : Prop :=
      aImpl P Q /\ aImpl P Q.

    Notation "P '->>' Q" := (aImpl P Q) (at level 80).

    Notation "P '<<->>' Q" := (aIff P Q) (at level 80).

    Definition hoare_triple
      (P : assertion) (a : action) (Q : tau -> assertion) : Prop :=
      ∀ env Γ Γ' sigma log r,
      P env Γ ->
      interp_action env sigma Γ log_empty log_empty a = Some (log, r, Γ') ->
      Q r (commit_update env log) Γ'.

    Lemma hoare_logs : ∀ P a Q,
      hoare_triple P a Q ->
      ∀ env Γ Γ' sigma slog alog alog' r,
      P (commit_update env (log_app alog slog)) Γ ->
      interp_action env sigma Γ slog alog a = Some (alog', r, Γ') ->
      Q r (commit_update env (log_app alog' slog)) Γ'.
    Proof.
      intros P a Q Hht env Γ Γ' sigma slog alog alog' r HP Hin.
      unfold hoare_triple in Hht.
      apply interp_log_irrelevance'' in Hin.
      destruct Hin as [log [Hin  Hlog]].
      specialize (Hht (commit_update env (log_app alog slog)) Γ Γ' sigma _ _ HP Hin).
      rewrite commit_update_assoc, log_app_assoc, <- Hlog in Hht.
      assumption.
    Qed.
  End idk.

  Local Ltac specialize_hoare :=
    match goal with
    | HP: ?P _ _,
      HHT: hoare_triple ?P ?a _,
      Hin: interp_action _ _ _ _ _ ?a = Some _ |- _=>
      specialize (HHT _ _ _ _ _ _ HP Hin)
    end.

  (* todo checkout custom assignment notations from sf*)
  (* todo check level *)
  Notation "'{{' P '}}' a '{{' Q '}}'" := (hoare_triple P a Q) (at level 10).
    (* ( P custom assn at level 99, , Q custom assn at level 99) *)

  Notation action tau := (action' R Sigma (sig := sig) (tau := tau)).

  Theorem hoare_post_true tau : ∀ P (a : action tau),
    (* hoare_triple P a (fun _ => aTrue). *)
    {{ P }} a {{ fun _ => aTrue }}.
  Proof. now unfold hoare_triple, aTrue. Qed.

  Theorem hoare_pre_false tau : ∀ Q (a : action tau),
    {{ aFalse }} a {{ Q }}.
  Proof. now unfold hoare_triple, aFalse. Qed.

  Theorem hoare_pass : ∀ P,
    {{ P }} <{ pass }> {{ fun _ => P}}.
  Proof. intros * ? * HP; inversion 1; subst.
    rewrite commit_update_empty; assumption. Qed.

  Theorem hoare_seq {tau} : ∀ P Q R c1 (c2 : action tau),
    {{ Q }} c2 {{ R }} →
    {{ P }} c1 {{ fun _ => Q }} →
    {{ P }} <{ `c1`; `c2` }> {{ R }}.
  Proof.
    intros * Hc2 Hc1 ? * HP Hinterp.
    simple_interp_some.
    specialize_hoare; cbv beta in Hc1.
    rewrite <- (log_app_empty_r _ l) in Hc1.
    pose proof (Hl := hoare_logs _ _ _ Hc2  _ _ _ _ _ _ _ _ Hc1 H0).
    now rewrite <- (log_app_empty_r _ log).
  Qed.

  Theorem hoare_consequence {tau} : ∀ P P' Q Q' (a : action tau),
    {{ P' }} a {{ Q' }} ->
    (forall env Γ, P env Γ -> P' env Γ) ->
    (forall env Γ ret, Q' ret env Γ -> Q ret env Γ) ->
    {{ P }} a {{ Q }}.
  Proof. unfold hoare_triple. eauto. Qed.

  Theorem hoare_read `{FiniteType reg_t} : ∀ P port reg,
    {{ P }} (Read port reg) {{ fun ret env Γ => ret = getenv _ env reg /\ P env Γ }}.
  Proof.
    intros * ? * HP Hint.
    cbn in Hint.
    rewrite may_read_empty in Hint.
    inversion Hint.

    solve_log_irrelevance.
    repeat match goal with
    | H: ?A = ?A |- _ => clear H
    end.
    split;
      [destruct port;
        [| rewrite (log_app_empty_r _ _), latest_write0_empty]|];
      now rewrite commit_read, commit_update_empty.
  Qed.

  Theorem hoare_if_true tau : ∀ P Q R (c : action (bits_t 1)) (tr fl : action tau),
    {{ P }} c {{ fun ret env Γ => ret = Ob~1 /\ R env Γ }} ->
    {{ R }} tr {{ Q }} ->
    {{ P }} <{if `c` then `tr` else `fl`}> {{ Q }}.
  Proof.
    intros ** ? * HP Hin.
    solve_log_irrelevance.
    unfold hoare_triple in H.
    specialize (H _ _ _ _ _ _ HP Heq).
    solve_log_irrelevance.
    cbn in H2.
    rewrite <- (log_app_empty_r _ l) in H1.
    pose proof (hoare_logs _ _ _ H0 _ _ _ _ _ _ _ _ H1 H2).
    now rewrite <- (log_app_empty_r _ log).
  Qed.

  Theorem hoare_if_false tau : ∀ P Q R (c : action (bits_t 1)) (tr fl : action tau),
    {{ P }} c {{ fun ret env Γ => ret = Ob~0 /\ R env Γ }} ->
    {{ R }} fl {{ Q }} ->
    {{ P }} <{if `c` then `tr` else `fl`}> {{ Q }}.
    intros ** ? * HP Hin.
    solve_log_irrelevance.
    unfold hoare_triple in H.
    specialize (H _ _ _ _ _ _ HP Heq).
    solve_log_irrelevance.
    cbn in H2.
    rewrite <- (log_app_empty_r _ l) in H1.
    pose proof (hoare_logs _ _ _ H0 _ _ _ _ _ _ _ _ H1 H2).
    now rewrite <- (log_app_empty_r _ log).
  Qed.

  (* Reserved Notation "'{{' P '}}' a '{{' Q '}}'" (at level 40). *)
  Inductive HoareTriple : forall {tau : type}, assertion -> action sig tau -> (tau -> assertion) -> Prop :=
  | HTSeq : ∀ tau P Q R a1 a2,
  (* TODO maybe swap preconditions *)
    HoareTriple P a1 Q ->
    (forall r, HoareTriple (Q r) a2 R) ->
    @HoareTriple tau P (Seq a1 a2) R
  | HTFail : ∀ tau P Q,
    HoareTriple P (Fail tau) Q
  | HTIf : ∀ tau P Q R cond tr fl,
    (@HoareTriple (bits_t 1) P cond (fun ret e Γ sl al => ret = Ob~1 /\ Q e Γ sl al) /\ @HoareTriple tau Q tr R) \/
    (@HoareTriple (bits_t 1) P cond (fun ret e Γ sl al => ret = Ob~0 /\ Q e Γ sl al) /\ @HoareTriple tau Q fl R) ->
    HoareTriple P (If cond tr fl) R
  | HTConst : ∀ tau cst P,
    @HoareTriple tau P (Const cst) (fun r _ _ _ _ => r = cst)
  | HTVar : ∀ tau nm m P,
    @HoareTriple tau P (Var m (k := nm)) (fun r _ Γ _ _ => r = cassoc m Γ)
  (* strengthen precondition + weaken postcondition *)
  | HTConsequence : forall tau P Q P' Q' c,
    @HoareTriple tau P c Q ->
    (forall e G sl al, P' e G sl al -> P e G sl al) ->
    (forall r e G sl al, Q r e G sl al -> Q' r e G sl al) ->
    @HoareTriple tau P' c Q'
  | HTBinop : forall fn a1 a2 P Q R v1 v2,
    HoareTriple P a1 (fun r e Γ sl al => r = v1 /\ Q e Γ sl al) ->
    HoareTriple Q a2 (fun r e Γ sl al => r = v2 /\ R e Γ sl al) ->
    HoareTriple P (Binop fn a1 a2) (fun r e Γ sl al => r = ((PrimSpecs.sigma2 fn) v1 v2) /\ R e Γ sl al).
  (* where "{{ P }} a {{ Q }}" := (HoareTriple (fun env Γ sl al => P) a (fun ret env Γ sl al => Q)). *)

  Fixpoint hoare_triple_interp_action {tau} P (a : action sig tau) Q (ht : HoareTriple P a Q) {struct ht}:
    ∀ env Γ Γ' sigma r slog alog alog',
    P env Γ alog slog ->
    interp_action env sigma Γ slog alog a = Some (alog', r, Γ') ->
    Q r env Γ' alog' slog.
  Proof.
    induction ht.
    - intros.
      simpl in H2.
      destruct (interp_action env sigma Γ slog alog a1) eqn:Heq; inversion H2.
      do 2 destruct p. clear H2.
      specialize (IHht _ _ _ _ _ _ _ _ H1 Heq).
      specialize (H0 _ _ _ _ _ _ _ _ _ IHht H4).
      assumption.
    - intros.
      simpl in H0. inversion H0.
    - intros.
      repeat match goal with
      | H: interp_action _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; simpl in H
      | H: opt_bind ?a _ = Some _ |- _ => destruct a eqn:?Heq; inversion H; clear H
      | H: prod _ _ |- _ => destruct H
      end.
      destruct H.
      + destruct H.
        pose proof (hoare_triple_interp_action _ _ _ _ H _ _ _ _ _ _ _ _ H0 Heq).
        simpl in H2.
        destruct H2.
        rewrite H2 in H3.
        simpl in H3.
        pose proof (hoare_triple_interp_action _ _ _ _ H1 _ _ _ _ _ _ _ _ H4 H3).
        assumption.
      + destruct H.
        pose proof (hoare_triple_interp_action _ _ _ _ H _ _ _ _ _ _ _ _ H0 Heq).
        simpl in H2.
        destruct H2.
        rewrite H2 in H3.
        simpl in H3.
        pose proof (hoare_triple_interp_action _ _ _ _ H1 _ _ _ _ _ _ _ _ H4 H3).
        assumption.
    - intros.
      simpl in H0. inversion H0. reflexivity.
    - intros.
      simpl in H0.
      inversion H0. reflexivity.
    - intros.
      clear hoare_triple_interp_action.
      eauto.
    - intros.
      repeat match goal with
      | H: interp_action _ _ _ _ _ ?a = Some _ |- _ => head_constructor a; simpl in H
      | H: opt_bind ?a _ = Some _ |- _ => destruct a eqn:?Heq; inversion H; clear H
      | H: prod _ _ |- _ => destruct H
      end.
      specialize (IHht1 _ _ _ _ _ _ _ _ H Heq).
      destruct IHht1. subst.
      specialize (IHht2 _ _ _ _ _ _ _ _ H2 Heq0).
      destruct IHht2. subst.
      inversion H1.
      split. reflexivity. subst. auto.
  Qed.

  Definition HoareTriple2 {tau} :
    action sig tau ->
    assertion -> (tau -> assertion) -> Prop :=
    fun a P Q => HoareTriple P a Q.
End Hoare.

Require Import Koika.Frontend.
Require Import Koika.TypedParsing.

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
Set Typeclasses Debug.


Notation "{ P } a { Q }" := (HoareTriple P a Q) (only printing).
(* Notation "{ P } a { Q }" := (HoareTriple (fun _ _ _ _ => P) a Q) (only printing). *)

Lemma min_correct m n env:
  HoareTriple2 (REnv := env)
  min.(int_body)
  (fun _ Γ _ _ => Γ.["a"] = Bits.of_nat 5 m /\ Γ.["b"] = Bits.of_nat 5 n)
  (fun r _ _ _ _ => r = Bits.of_nat 5 m ).
Proof.
  unfold HoareTriple2.
  unfold min, int_body.
  unfold TypedParsing.refine_sig_tau.
  eapply HTIf.

  destruct (m <? n)%nat eqn:Hc.
  - left.
    split.
    eapply HTConsequence.
    change (bits_t 1) with (retSig (PrimSignatures.Sigma2 (Bits2 (Compare false cLt 5)))).
    eapply HTBinop.
    eapply HTVar.

    2: {
      eapply HTConsequence.
      - apply HTVar.
      - intros ? ? ? ?; exact (id).
      - cbv beta. intros. subst. reflexivity. simpl.
    2:
  - right.
    split.
