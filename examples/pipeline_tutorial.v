(*! Using WP calculus !*)
Require Import Koika.Frontend.
Require Import Koika.WP.
Require Import Koika.CompactSemantics.

Notation uaction := (uaction pos_t var_t fn_name_t).
Notation action := (action pos_t var_t fn_name_t).
Notation rule := (rule pos_t var_t fn_name_t).

Notation scheduler := (scheduler pos_t _).

Notation UInternalFunction reg_t ext_fn_t :=
  (InternalFunction var_t fn_name_t (uaction reg_t ext_fn_t)).
Notation InternalFunction R Sigma sig tau :=
  (InternalFunction var_t fn_name_t (action R Sigma sig tau)).

Inductive reg_t := queue_data | output_buffer | input_buffer | queue_empty.
Inductive ext_fn_t := NextInput | F | G.
Inductive rule_name_t := doF | doG.

Definition sz := (pow2 5).

Definition R r :=
  match r with
  | queue_data => bits_t sz
  | input_buffer => bits_t sz
  | output_buffer => bits_t sz
  | queue_empty => bits_t 1
  end.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | NextInput => {$ bits_t sz ~> bits_t sz $}
  | F => {$ bits_t sz ~> bits_t sz $}
  | G => {$ bits_t sz ~> bits_t sz $}
  end.

Definition _doF : uaction _ _ :=
  {{
     let v := read0(input_buffer) in
     write0(input_buffer, extcall NextInput(v));
     let queue_empty := read1(queue_empty) in
     if queue_empty then
       write1(queue_empty, Ob~0);
       write0(queue_data, extcall F(v))
     else
       fail
  }}.

Definition _doG : uaction _ _ :=
  {{
      let queue_empty := read0(queue_empty) in
      if !queue_empty then
        let data := read0(queue_data) in
        write0(output_buffer, extcall G(data));
        write0(queue_empty, Ob~1)
      else
        fail
  }}.

Definition rules :=
  tc_rules R Sigma
           (fun rl => match rl with
                   | doF => _doF
                   | doG => _doG
                   end).

Definition pipeline : scheduler :=
  doG |> doF |> done.

Require Lists.Streams.
Declare Scope stream_scope.
Infix ":::" := Streams.Cons (at level 60, right associativity) : stream_scope.
Open Scope stream_scope.

Section Streams.
  CoFixpoint coiterate {A} (f: A -> A) (init: A) :=
    init ::: coiterate f (f init).

  Lemma coiterate_eqn {A} (f: A -> A) (init: A) :
    coiterate f init =
    init ::: coiterate f (f init).
  Proof.
    rewrite (Streams.unfold_Stream (coiterate f init)) at 1; reflexivity.
  Qed.

  Fixpoint iterate_tr (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => iterate_tr n f (f init)
    end.

  Fixpoint iterate (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => f (iterate n f init)
    end.

  Lemma iterate_assoc:
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate n f (f init) = f (iterate n f init).
  Proof.
    induction n; simpl; intros; try rewrite IHn; reflexivity.
  Qed.

  Lemma iterate_S_acc :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate (S n) f init = iterate n f (f init).
  Proof. intros; symmetry; apply iterate_assoc. Qed.

  Lemma iterate_tr_correct :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate_tr n f init = iterate n f init.
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - rewrite IHn, iterate_assoc; reflexivity.
  Qed.

  Lemma iterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (* Use g because that's usually the simpler one *)
    (forall x, inv x -> inv (g x)) ->
    (forall x, inv x -> f x = g x) ->
    forall n,
    forall init: A,
      inv (init) ->
      iterate n f init = iterate n g init.
  Proof.
    intros Hinv Heq; induction n; intros init Hinvi.
    - reflexivity.
    - simpl; rewrite <- !iterate_assoc, Heq; auto.
  Qed.

  Lemma Str_nth_coiterate {A} (f: A -> A) :
    forall n (init: A),
      Streams.Str_nth n (coiterate f init) =
      iterate n f init.
  Proof.
    setoid_rewrite <- iterate_tr_correct.
    induction n; cbn; intros.
    - reflexivity.
    - rewrite coiterate_eqn.
      apply IHn.
  Qed.

  Lemma coiterate_pointwise {A} (f g: A -> A):
    (forall x, f x = g x) ->
    forall init: A,
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Heq; cofix IH; intros init.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; apply IH.
  Qed.

  Lemma coiterate_pointwise' {A} (f g: A -> A):
    (forall x, f x = g x) ->
    forall init: A,
      eq (coiterate f init) (coiterate g init).
  Admitted.

  Lemma coiterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (forall x, inv x -> inv (g x)) -> (* Use g because that's usually the simpler one *)
    (forall x, inv x -> f x = g x) ->
    forall init: A,
      inv (init) ->
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Hinv Heq; cofix IH; intros init Hinvi.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; auto.
  Qed.

  Lemma coiterate_pointwise_inv' {A} (f g: A -> A) (inv: A -> Prop):
    forall init: A,
      (forall x, inv x -> f x = g x) ->
      inv (init) ->
      (forall x, inv x -> inv (g x)) ->
      eq (coiterate f init) (coiterate g init).
  Admitted.

  Lemma map_eqn {A B} (f: A -> B) (s: Streams.Stream A) :
    Streams.map f s =
    f (Streams.hd s) ::: Streams.map f (Streams.tl s).
  Proof.
    rewrite (Streams.unfold_Stream (Streams.map f s)) at 1; reflexivity.
  Qed.

  Lemma Str_nth_0 {A} (hd: A) tl:
    Streams.Str_nth 0 (hd ::: tl) = hd.
  Proof. reflexivity. Qed.

  Lemma Str_nth_S {A} (hd: A) tl n:
    Streams.Str_nth (S n) (hd ::: tl) = Streams.Str_nth n tl.
  Proof. reflexivity. Qed.
End Streams.

Arguments wp_action {pos_t var_t fn_name_t} {reg_t ext_fn_t} {R Sigma} {REnv} r sigma
          {sig tau} _ !_ _ /.

Arguments interp_cycle_cps {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / {A}%type_scope k : assert.
Arguments interp_scheduler_cps {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / {A}%type_scope k : assert.
Arguments interp_rule_cps {pos_t var_t fn_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r sigma%function_scope !rl / {A}%type_scope k log : assert.

Arguments wp_scheduler {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / post : assert.

Arguments interp_cycle: simpl never.
Arguments id _ _ / : assert.

Declare Custom Entry context_mapping.

Notation "x  ->  y" :=
  (CtxCons x y CtxEmpty)
    (in custom context_mapping at level 80,
        x constr at level 0, y constr at level 80,
        no associativity).

Notation "x  ->  y ;  z" :=
  (CtxCons x y z)
    (in custom context_mapping at level 80,
        x constr at level 0, y constr at level 80,
        z custom context_mapping at level 80,
        right associativity).

Notation "#{  x  }#" := (x) (at level 0, x custom context_mapping at level 200) : context.
Arguments env_t: simpl never.
Arguments vect: simpl never.

Arguments wp_cycle {pos_t var_t fn_name_t rule_name_t reg_t ext_fn_t}%type_scope {R Sigma}%function_scope {REnv} r (sigma rules)%function_scope !s / post : assert.

Notation "env .[ idx ]" := (getenv ContextEnv env idx) (at level 1, format "env .[ idx ]").
(* FIXME remove these notations *)
Notation "0b0" := {| vhd := false; vtl := _vect_nil |}.
Notation "0b1" := {| vhd := true; vtl := _vect_nil |}.

Arguments may_read /.
Arguments may_write /.
Arguments logentry_app {T}%type_scope !l1 !l2 /: assert.

Opaque interp_cycle.

Section Correctness.
  Context {REnv: Env reg_t}.
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Definition rls :=
    Eval cbv in rules.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

  Section Experiments.
    Context (r: ContextEnv.(env_t) R).

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', Logs.commit_update init (TypedSemantics.interp_scheduler init sigma rls pipeline) = l'.
    Proof.
      intros; unfold pipeline.
      (* Time unfold TypedSemantics.interp_scheduler, *)
      (* TypedSemantics.interp_scheduler', *)
      (* TypedSemantics.interp_rule; simpl. (* 11s *) *)
    Abort.

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', CompactLogs.commit_update init (CompactSemantics.interp_scheduler init sigma rls pipeline) = l'.
    Proof.
      intros; unfold pipeline.
      (* Time unfold CompactSemantics.interp_scheduler, CompactSemantics.interp_scheduler', CompactSemantics.interp_rule; simpl. (* 17s *) *)
    Abort.

    Lemma cycle_correct :
      forall (init: ContextEnv.(env_t) R),
      exists l', WP.interp_cycle init sigma rls pipeline = l'.
    Proof.
      intros; unfold pipeline.
      apply wp_cycle_correct.
      Time simpl. (* 0.7s *)

      destruct (Bits.single init.[queue_empty]); simpl.
      - (* Initialization: nothing in the queue yet *)
        eexists; reflexivity.
      - (* Steady state: queue remains full *)
        eexists; reflexivity.
    Qed.

    Lemma scheduler_correct :
      exists l', interp_scheduler r sigma rls pipeline = l'.
    Proof.
      unfold pipeline.
      (* unfold interp_scheduler, interp_scheduler', interp_rule; simpl. *)
      (* rewrite <- interp_scheduler_cps_correct; simpl. *)
      apply wp_scheduler_correct.
      Time simpl.
      destruct (Bits.single (getenv ContextEnv r queue_empty)); simpl.
      all: eexists; reflexivity.
    Qed.

    Lemma scheduler_correct' :
      (interp_scheduler r sigma rls pipeline).[input_buffer].(lwrite1) = None.
    Proof.
      unfold pipeline.
      (* unfold interp_scheduler, interp_scheduler', interp_rule; simpl. *)
      (* rewrite <- interp_scheduler_cps_correct; simpl. *)
      apply wp_scheduler_correct.
      Time simpl.
      destruct (Bits.single (getenv ContextEnv r queue_empty)); simpl.
      all: eexists; reflexivity.
    Qed.

    Lemma doG_correct :
      Bits.single (r.[queue_empty]) = false ->
      exists l,
        interp_rule r sigma log_empty (rls doG) = Some l /\
        l.[queue_empty].(lwrite0) = Some Ob~1.
    (* FIXME: which style is better; exists or match? *)
    (* match interp_rule r sigma log_empty (rls doG) with *)
    (* | Some l => *)
    (*   l.[queue_empty] = [LE LogWrite P0 Ob~1; LE LogRead P0 tt] *)
    (* | None => False *)
    (* end. *)
    Proof.
      intros Hvalid.
      unfold interp_rule.
      (* Time simpl.  rewrite Hvalid; simpl; eexists; split; reflexivity. *)
      apply (wp_action_correct (rule_name_t := rule_name_t)).
      Time simpl; rewrite Hvalid; simpl; eexists; split; reflexivity.
    Qed.

    (* FIXME *)
    Arguments may_read0 /.
    Arguments may_read1 /.
    Arguments may_write0 /.
    Arguments may_write1 /.
    Arguments vect_cons: simpl never.

    Arguments env_t : simpl never.

    Ltac autorew :=
      (* The variant below isn't enough, because primitive projections are weird *)
      (* | [ H: ?a = _ |- _ ] => *)
      (*   match goal with (* Merging the two matches together results in a 20x slowdown *) *)
      (*   | [  |- context[a] ] => rewrite !H *)
      (*   end *)
      repeat match goal with
             | [ H: ?a = ?a' |- context[match ?b with _ => _ end] ] =>
               unify a b; replace b with a' by assumption
             end.               (* FIXME doesn't work here *)

    Lemma doF_correct :
      forall l,
        let l_input_buffer := l.[input_buffer] in
        let l_queue_empty := l.[queue_empty] in
        let l_queue_data := l.[queue_data] in
        l_input_buffer.(lwrite0) = None ->
        l_input_buffer.(lwrite1) = None ->
        l_input_buffer.(lread1) = false ->
        l_queue_data.(lread1) = false ->
        l_queue_data.(lwrite0) = None ->
        l_queue_data.(lwrite1) = None ->
        l_queue_empty.(lwrite1) = None ->
        l_queue_empty.(lwrite0) = Some Ob~1 ->
        (* r.[queue_data] = (sigma F) (r.[output_buffer]) -> *)
        exists l',
          interp_rule r sigma l (rls doF) = Some l'.
    Proof.
      intros.
      unfold interp_rule.
      (* rewrite (interp_action_cps_correct_rev (rule_name_t := rule_name_t)). *)
      (* simpl. *)
      apply (wp_action_correct (rule_name_t := rule_name_t)).
      Time simpl.
      Time autorew.
      simpl.
      eexists; reflexivity.
    Qed.

    (* Compact encoding of preconditions *)
    Lemma doF_correct' :
      forall qd0 ob qe0 qe1 ib0,
        let l :=
            #{ queue_data -> {| lread0 := qd0; lread1 := false; lwrite0 := None; lwrite1 := None |};
               output_buffer -> ob;
               input_buffer -> {| lread0 := ib0; lread1 := false; lwrite0 := None; lwrite1 := None |};
               queue_empty -> {| lread0 := qe0; lread1 := qe1; lwrite0 := Some Ob~1; lwrite1 := None |} }# in
        exists l', interp_rule r sigma l (rls doF) = Some l'.
    Proof.
      intros.
      unfold interp_rule.
      apply (wp_action_correct (rule_name_t := rule_name_t)).
      Time simpl.
      (* Nothing to rewrite! *)
      eexists; reflexivity.
    Qed.
  End Experiments.

  Section Spec.
    Context (r: ContextEnv.(env_t) R).

    (* The stream of inputs consumed by the spec *)
    Definition spec_inputs :=
      coiterate (sigma NextInput) r.[input_buffer].

    (* The expected stream of observable values *)
    Definition spec_observations :=
      let composed x := sigma G (sigma F x) in
      r.[output_buffer] ::: r.[output_buffer] ::: Streams.map composed spec_inputs.

    (* The actual stream of states produced by the implementation *)
    Definition impl_trace :=
      coiterate (fun r: env_t _ R => interp_cycle r sigma rls pipeline) r.

    (* The actual stream of observations produced by the implementation *)
    Definition impl_observations :=
      Streams.map (fun r: env_t _ R => r.[output_buffer]) impl_trace.
  End Spec.

  Section Proofs.
    Definition cycle (r: ContextEnv.(env_t) R) :=
      interp_cycle r sigma rls pipeline.

    Definition phi2
               (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      #{ queue_data -> sigma F (sigma NextInput r.[input_buffer]);
         output_buffer -> sigma G (sigma F r.[input_buffer]);
         input_buffer -> sigma NextInput (sigma NextInput r.[input_buffer]);
         queue_empty -> Ob~0 }#.

    Lemma phi2_correct :
      forall r, cycle (cycle r) = phi2 r.
    Proof.
      intros r; unfold cycle.
      rewrite (interp_cycle_cps_correct_rev r); simpl.
      destruct (Bits.single r.[queue_empty]); simpl.
      all: rewrite interp_cycle_cps_correct_rev; simpl;
        reflexivity.
    Qed.

    Definition phi_iterated n
               (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      #{ queue_data -> sigma F (iterate (S n) (sigma NextInput) r.[input_buffer]);
         output_buffer -> sigma G (sigma F (iterate n (sigma NextInput) r.[input_buffer]));
         input_buffer -> iterate (S (S n)) (sigma NextInput) r.[input_buffer];
         queue_empty -> Ob~0 }#.

    Lemma phi_iterated_correct :
      forall r n,
        iterate (S (S n)) cycle r =
        phi_iterated n r.
    Proof.
      intros r n.
      rewrite !iterate_S_acc, phi2_correct.
      revert n; apply Div2.ind_0_1_SS; simpl.
      - reflexivity.
      - unfold cycle; rewrite interp_cycle_cps_correct_rev; reflexivity.
      - intros n IH; simpl in IH; rewrite IH; reflexivity.
    Qed.

    Theorem correct_pipeline:
      forall r,
        r.[queue_empty] = Ob~1 ->
        Streams.EqSt (impl_observations r) (spec_observations r).
    Proof.
      intros r Hqueue_empty.
      unfold impl_observations, spec_observations, impl_trace.

      apply Streams.ntheq_eqst; intros [ | [ | n ] ]; simpl;
        unfold spec_inputs;
        rewrite ?Str_nth_0, ?Str_nth_S, ?Streams.Str_nth_map, ?Str_nth_coiterate.
      - reflexivity.
      - simpl.
        rewrite interp_cycle_cps_correct_rev; simpl.
        rewrite Hqueue_empty; reflexivity.
      - rewrite phi_iterated_correct.
        reflexivity.
    Qed.
  End Proofs.
End Correctness.

Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external pipeline.

Definition r reg : R reg :=
  match reg with
  | queue_data => Bits.zero
  | output_buffer => Bits.zero
  | input_buffer => Bits.zero
  | queue_empty => Ob~1
  end.

Definition circuits_result sigma :=
  interp_circuits (ContextEnv.(create) r) sigma circuits.

Definition cpp_extfuns := "class extfuns {
public:
  static bits<32> next_input(bits<32> lfsr) {
    return lfsr + bits<32>{1};
  }

  static bits<32> f(bits<32> x) {
    return ~(x << bits<32>{2}) - bits<32>{1};
  }

  static bits<32> g(bits<32> x) {
    return bits<32>{5} + ((x + bits<32>{1}) >> bits<32>{1});
  }
};".

Definition ext_fn_names fn :=
  match fn with
  | NextInput => "next_input"
  | F => "f"
  | G => "g"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r reg;
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "pipeline" |};

     ip_sim := {| sp_ext_fn_specs fn :=
                   {| efs_name := ext_fn_names fn;
                      efs_method := false |};
                 sp_prelude := Some cpp_extfuns |};

     ip_verilog := {| vp_ext_fn_specs fn :=
                       {| efr_name := ext_fn_names fn;
                          efr_internal := true |} |} |}.

Definition prog := Interop.Backends.register package.
Extraction "pipeline.ml" prog.