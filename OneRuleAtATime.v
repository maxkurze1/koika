Require Import SGA.Common SGA.Syntax SGA.TypedSyntax SGA.Semantics.
Require Import Coq.Lists.List.

Import ListNotations.
Open Scope bool_scope.

Section EnvUpdates.
  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.

  Definition rlog_latest_write_fn {k} :=
    fun le: LogEntry (R k) => match le with
                           | LE LogWrite _ v => Some v
                           | _ => None
                           end.

  Definition rlog_latest_write k (ll: RLog (R k)) :=
    list_find_opt rlog_latest_write_fn ll.

  Definition commit_update (r0: REnv.(env_t) R) (log: Log R REnv) : REnv.(env_t) R :=
    REnv.(map2) (fun k ll v0 => match rlog_latest_write k ll with
                             | Some v => v
                             | None => v0
                             end) log r0.

  Lemma commit_update_assoc:
    forall (r : REnv.(env_t) R) (l l' : Log R REnv),
      commit_update (commit_update r l) l' = commit_update r (log_app l' l).
  Proof.
    unfold commit_update, log_app, map2; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    unfold rlog_latest_write.
    rewrite list_find_opt_app.
    destruct list_find_opt; reflexivity.
  Qed.

  Lemma commit_update_empty:
    forall (r : REnv.(env_t) R),
      commit_update r log_empty = r.
  Proof.
    intros; apply equiv_eq; intro.
    unfold commit_update, log_empty, map2; rewrite !getenv_create.
    reflexivity.
  Qed.
End EnvUpdates.

Section Proof.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log R REnv).
  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).

  Fixpoint interp_scheduler'_trace
         (sched_log: Log)
         (s: scheduler)
         {struct s} :=
  match s with
  | Done => Some ([], sched_log)
  | Try rl s1 s2 =>
    match interp_rule r sigma CtxEmpty sched_log log_empty rl with
    | Some l => match interp_scheduler'_trace (log_app l sched_log) s1 with
               | Some (rs, log) => Some (rl :: rs, log)
               | None => None
               end
    | CannotRun => interp_scheduler'_trace sched_log s2
    end
  end.

  Definition interp_scheduler_trace_and_update
        l
        (s: scheduler) :=
    match interp_scheduler'_trace l s with
    | Some (rs, log) => Some (rs, commit_update r log)
    | None => None
    end.

  Definition update_one r rl: option (REnv.(env_t) R) :=
    let/opt r := r in
    let log := @interp_scheduler' var_t reg_t fn_t R Sigma REnv r sigma log_empty (Try rl Done Done) in
    Some (commit_update r log).

  Definition latest_write (l: Log) idx: option (R idx) :=
    log_find l idx rlog_latest_write_fn.

  Lemma getenv_commit_update :
    forall sl r idx,
      REnv.(getenv) (commit_update r sl) idx =
      match latest_write sl idx with
      | Some v' => v'
      | None => REnv.(getenv) r idx
      end.
  Proof.
    unfold commit_update, map2; intros; rewrite getenv_create.
    reflexivity.
  Qed.

  Require Import Ring_theory Ring Coq.setoid_ring.Ring.

  Lemma getenv_logapp:
    forall (l l': Log) idx,
      REnv.(getenv) (log_app l l') idx =
      REnv.(getenv) l idx ++ REnv.(getenv) l' idx.
  Proof.
    unfold log_app, map2; intros; rewrite getenv_create; reflexivity.
  Qed.

  Lemma log_forallb_app:
    forall (l l': Log) reg (f: LogEntryKind -> Port -> bool),
      log_forallb (log_app l l') reg f =
      log_forallb l reg f && log_forallb l' reg f.
  Proof.
    unfold log_forallb.
    intros; rewrite getenv_logapp.
    rewrite !forallb_app; reflexivity.
  Qed.

  Lemma log_app_assoc:
    forall (l l' l'': Log),
      log_app l (log_app l' l'') =
      log_app (log_app l l') l''.
  Proof.
    unfold log_app, map2; intros.
    apply create_funext; intros.
    rewrite !getenv_create.
    apply app_assoc.
  Qed.

  Lemma log_app_empty_l : forall (l: Log),
      log_app l log_empty = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create, app_nil_r.
    reflexivity.
  Qed.

  Lemma log_app_empty_r : forall (l: Log),
      log_app log_empty l = l.
  Proof.
    intros.
    apply equiv_eq.
    unfold equiv, log_app, map2, log_empty; intros.
    rewrite !getenv_create.
    reflexivity.
  Qed.

  Ltac set_forallb_fns :=
    repeat match goal with
           | [  |- context[log_forallb _ _ ?fn] ] =>
             match fn with
             | (fun _ => _) => set fn
             end
           end.

  Lemma may_read0_app_sl :
    forall (sl sl' l: Log) idx,
      may_read0 (log_app sl sl') l idx =
      may_read0 sl l idx && may_read0 sl' l idx.
  Proof.
    unfold may_read0; intros.
    rewrite !log_forallb_app.
    set_forallb_fns.
    ring_simplify.
    f_equal.
    f_equal.
    rewrite <- !Bool.andb_assoc.
    rewrite Bool.andb_diag; reflexivity.
  Qed.

  Lemma may_read1_app :
    forall (sl sl': Log) idx,
      may_read1 (log_app sl sl') idx =
      may_read1 sl idx && may_read1 sl' idx.
  Proof.
    unfold may_read1; intros.
    rewrite !log_forallb_app.
    reflexivity.
  Qed.

  Lemma may_write_app_sl :
    forall (sl sl': Log) l lvl idx,
      may_write (log_app sl sl') l lvl idx =
      may_write sl l lvl idx && may_write sl' l lvl idx.
  Proof.
    unfold may_write; intros.
    destruct lvl; rewrite !log_forallb_app;
      ring_simplify;
      rewrite Bool.andb_diag;
      reflexivity.
  Qed.

  Lemma find_none_notb {A B}:
    forall (P: A -> option B) l,
      (forall a, List.In a l -> P a = None) ->
      list_find_opt P l = None.
  Proof.
    induction l; cbn; intros * Hnot.
    - reflexivity.
    - pose proof (Hnot a).
      destruct (P a); firstorder discriminate.
  Qed.

  Ltac bool_step :=
    match goal with
    | _ => progress Common.bool_step
    | [ H: log_forallb (log_app _ _) _ _ = _ |- _ ] =>
      rewrite log_forallb_app in H
    end.

  Lemma may_read0_no_writes :
    forall sl l idx,
      may_read0 sl l idx = true ->
      latest_write sl idx = None.
  Proof.
    unfold may_read0; intros.
    repeat (cleanup_step || bool_step).
    unfold log_forallb in *.
    rewrite forallb_forall in *.
    unfold latest_write, log_find.
    apply find_none_notb.
    intros a HIn.
    repeat match goal with
           | [ H: forall (_: LogEntry _), _ |- _ ] => specialize (H a HIn)
           end.
    destruct a; cbn in *; destruct kind; subst; try reflexivity.
    destruct port; discriminate.
  Qed.

  Lemma latest_write0_app :
    forall (sl sl': Log) idx,
      latest_write0 (log_app sl sl') idx =
      match latest_write0 sl idx with
      | Some e => Some e
      | None => latest_write0 sl' idx
      end.
  Proof.
    unfold latest_write0; eauto using log_find_app.
  Qed.

  Lemma may_read1_latest_write_is_0 :
    forall (l: Log) idx,
      may_read1 l idx = true ->
      latest_write l idx = latest_write0 l idx.
  Proof.
    unfold may_read1, latest_write, latest_write0, log_find, log_forallb.
    intros * H.
    set (getenv REnv l idx) as ls in *; cbn in *; clearbody ls.
    set (R idx) as t in *; cbn in *.
    revert H.
    induction ls.
    - reflexivity.
    - intros * H; cbn in H.
      repeat (bool_step || cleanup_step).
      rewrite (IHls ltac:(eassumption)).
      unfold rlog_latest_write_fn; cbn.
      destruct a, kind, port; try discriminate; reflexivity.
  Qed.

  Ltac t_step :=
    match goal with
    | _ => cleanup_step
    | [ H: context[may_read0 (log_app _ _) _ _] |- _ ] =>
      rewrite may_read0_app_sl in H
    | [ H: context[may_read1 (log_app _ _) _] |- _ ] =>
      rewrite may_read1_app in H
    | [ H: context[may_write (log_app _ _) _ _ _] |- _ ] =>
      rewrite may_write_app_sl in H
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    | [ H: opt_bind ?x _ = Some _ |- _ ] =>
      destruct x eqn:?; cbn in H; try discriminate
    | [ H: match ?x with _ => _ end = Some _ |- _ ] =>
      destruct x eqn:?; subst; cbn in H; try discriminate
    | _ =>
      bool_step
    | [ H: match ?x with _ => _ end = ?c |- _ ] =>
      let c_hd := constr_hd c in
      is_constructor c_hd; destruct x eqn:?
    | [ H: ?x = _ |- context[match ?x with _ => _ end] ] =>
      rewrite H
    end.

  Ltac t :=
    repeat t_step.

  Lemma interp_expr_commit:
    forall {sig tau} (ex: expr sig tau) (Gamma: vcontext sig) (sl sl': Log) rule_log lv,
      interp_expr r sigma Gamma (log_app sl sl') rule_log ex = Some lv ->
      interp_expr (commit_update r sl') sigma Gamma sl rule_log ex = Some lv.
  Proof.
    induction ex; cbn; intros Gamma sl sl' rule_log lv HSome; try congruence.

    - destruct port.
      + (* Read0 *)
        t.
        erewrite getenv_commit_update by eassumption.
        erewrite may_read0_no_writes by eauto.
        reflexivity.

      + (* Read1 *)
        t.
        rewrite log_app_assoc.
        rewrite (latest_write0_app (log_app _ _)).
        destruct latest_write0.
        * reflexivity.
        * erewrite getenv_commit_update by eassumption.
          rewrite may_read1_latest_write_is_0 by eassumption.
          reflexivity.

    - (* Call *)
      t.
      erewrite IHex1 by eauto; cbn.
      erewrite IHex2 by eauto; cbn.
      reflexivity.
  Qed.

  Lemma interp_rule_commit:
    forall {sig} (rl: rule sig) (Gamma: vcontext sig) (sl sl': Log) rule_log l,
      interp_rule r sigma Gamma (log_app sl sl') rule_log rl = Some l ->
      interp_rule (commit_update r sl') sigma Gamma sl rule_log rl = Some l.
  Proof.
    induction rl; cbn; intros Gamma sl sl' rule_log l HSome; try congruence.
    - (* Seq *)
      t.
      erewrite IHrl1 by eauto; cbn.
      erewrite IHrl2 by eauto; reflexivity.
    - (* Bind *)
      t.
      erewrite interp_expr_commit by eauto; cbn.
      erewrite IHrl by eauto; reflexivity.
    - (* If *)
      t;
        erewrite interp_expr_commit by eauto; cbn;
          [ erewrite IHrl1 by eauto; cbn |
            erewrite IHrl2 by eauto; cbn ];
          t; reflexivity.
    - (* Write *)
      t.
      erewrite interp_expr_commit by eauto; cbn.
      t; reflexivity.
  Qed.

  Lemma OneRuleAtATime':
    forall s rs r' l0,
      interp_scheduler_trace_and_update l0 s = Some (rs, r') ->
      List.fold_left (update_one) rs (Some (commit_update r l0)) = Some r'.
  Proof.
    induction s; cbn.
    - inversion 1; subst; cbn in *; eauto.
    - unfold interp_scheduler_trace_and_update; cbn; intros; t.
      + erewrite interp_rule_commit by (rewrite log_app_empty_r; eassumption);
          cbn.
        rewrite log_app_empty_l.
        rewrite commit_update_assoc.
        eapply IHs1.
        unfold interp_scheduler_trace_and_update.
        rewrite Heqo1; reflexivity.
      + eapply IHs2.
        unfold interp_scheduler_trace_and_update; rewrite Heqo.
        reflexivity.
  Qed.

  Lemma interp_scheduler_trace_correct :
    forall s l0 log,
      interp_scheduler' r sigma l0 s = log ->
      exists rs, interp_scheduler'_trace l0 s = Some (rs, log).
  Proof.
    induction s; cbn.
    - inversion 1; subst; eauto.
    - intros * Heq. destruct interp_rule as [log' | ] eqn:?.
      + destruct (IHs1 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
      + destruct (IHs2 _ _ Heq) as (rs & Heq').
        rewrite Heq'; eauto.
  Qed.

  Fixpoint scheduler_rules (s: scheduler) :=
    match s with
    | Done => []
    | Try r s1 s2 => r :: scheduler_rules s1 ++ scheduler_rules s2
    end.

  Lemma scheduler_trace_in_scheduler :
    forall s log l0 rs,
      interp_scheduler'_trace l0 s = Some (rs, log) ->
      (forall r : rule [], In r rs -> In r (scheduler_rules s)).
  Proof.
    induction s; cbn in *.
    - inversion 1; subst; inversion 1.
    - intros * H * H'; rewrite in_app_iff; t.
      + inversion H'; subst; eauto.
      + eauto.
  Qed.

  Theorem OneRuleAtATime:
    forall s log,
      interp_scheduler r sigma s = log ->
      exists rs,
        (forall rl, List.In rl rs -> List.In rl (scheduler_rules s)) /\
        List.fold_left update_one rs (Some r) = Some (commit_update r log).
  Proof.
    intros * H.
    apply interp_scheduler_trace_correct in H; destruct H as (rs & H).
    exists rs; split.
    - eauto using scheduler_trace_in_scheduler.
    - rewrite <- (commit_update_empty r) at 1.
      eapply OneRuleAtATime'.
      unfold interp_scheduler_trace_and_update; rewrite H; reflexivity.
  Qed.
End Proof.
