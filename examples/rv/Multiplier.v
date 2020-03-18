(*! Implementation of a multiplier module !*)
Require Import Coq.Lists.List.

Require Import Koika.Frontend Koika.Std Koika.SemanticProperties Koika.PrimitiveProperties Koika.Common.

Module Type Multiplier_sig.
  Parameter n: nat.
End Multiplier_sig.

Module Multiplier (s: Multiplier_sig).
  Import s.

  Inductive reg_t := valid | operand1 | operand2 | result | n_step | finished.

  Definition R r :=
    match r with
    | valid => bits_t 1          (* A computation is being done *)
    | operand1 => bits_t n       (* The first operand *)
    | operand2 => bits_t n       (* The second operand *)
    | result => bits_t (n+n)     (* The result being computed *)
    | n_step => bits_t (log2 n)  (* At which step of the computation we are *)
    | finished => bits_t 1       (* Indicates if the computation has finished *)
    end.

  Definition r idx : R idx :=
    match idx with
    | valid => Bits.zero
    | operand1 => Bits.zero
    | operand2 => Bits.zero
    | result => Bits.zero
    | n_step => Bits.zero
    | finished => Bits.zero
    end.

  Definition name_reg r :=
    match r with
    | valid => "valid"
    | operand1 => "operand1"
    | operand2 => "operand2"
    | result => "result"
    | n_step => "n_step"
    | finished => "finished"
    end.

  Definition enq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun enq (op1 : bits_t n) (op2 : bits_t n): bits_t 0 =>
         if (!read0(valid)) then
           write0(valid, #Ob~1);
           write0(operand1, op1);
           write0(operand2, op2);
           write0(result, |(n+n)`d0|);
           write0(n_step, |(log2 n)`d0|)
         else
           fail
    }}.

  Definition deq : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun deq () : bits_t (n+n) =>
         if (read1(valid) && read1(finished)) then
           write1(finished, #Ob~0);
           write1(valid, #Ob~0);
           read1(result)
         else
           fail@(bits_t (n+n))
    }}.

  Definition step : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun step () : bits_t 0 =>
         if (read0(valid) && !read0(finished)) then
           let n_step_val := read0(n_step) in
           (if read0(operand2)[n_step_val] then
             let partial_mul := zeroExtend(read0(operand1), n+n) << n_step_val in
             write0(result, read0(result) + partial_mul)
           else
             pass);
           if (n_step_val == #(Bits.of_nat (log2 n) (n-1))) then
             write0(finished, #Ob~1)
           else
             write0(n_step, n_step_val + |(log2 n)`d1|)
         else
           fail
    }}.

  Instance FiniteType_reg_t : FiniteType reg_t := _.

End Multiplier.

Module MultiplierProofs.
  Module Sig32 <: Multiplier_sig.
    Definition n := 32.
  End Sig32.
  Module mul32 := Multiplier Sig32.
  Import mul32.
  Import Sig32.

  Notation n := 32.

  Definition default := ContextEnv.(create) r.

  Definition typed_enq :=
    tc_function R empty_Sigma enq.

  Definition typed_step :=
    tc_function R empty_Sigma step.

  Definition typed_deq :=
    tc_function R empty_Sigma deq.

  Notation all_regs :=
    [valid; operand1; operand2; result; n_step; finished].

  Ltac interp_action_t :=
    repeat match goal with
           | [ H: interp_action _ _ _ _ _ ?action = Some _ |- _] =>
             unfold action in H;
             simpl (projT2 _) in H;
             unfold interp_action, opt_bind, no_latest_writes in *;
             repeat cleanup_log_step
           | _ => progress (simpl cassoc in *; simpl ctl in *; simpl chd in *)
           | [ H: match ?x with | Some(_) => _ | None => None end = Some (_) |- _ ] =>
             destruct x eqn:?; [ | solve [inversion H] ]
           | [ H: (if ?x then _ else None) = Some _ |- _ ] =>
             destruct x eqn:?; [ | solve [inversion H] ]
           | _ => progress cleanup_log_step
           end.

  Ltac interp_action_all_t :=
    repeat match goal with
           | _ => progress interp_action_t
           | [ H: (if ?c then _ else _) = Some (_, _, _) |- _ ] =>
             destruct c eqn:?
           end.

  Definition partial_mul (a b n_step: N) :=
    (a * (b mod (2 ^ n_step)))%N.

  Lemma partial_mul_step (a b n_step: N) :
    partial_mul a b (n_step + 1) =
    ((partial_mul a b n_step) +
     a * (N.b2n (N.testbit b n_step) * (2 ^ n_step)))%N.
  Proof.
  Admitted.

  Definition step_invariant (reg: ContextEnv.(env_t) R) :=
    (Bits.to_N (ContextEnv.(getenv) reg n_step) < N.of_nat n)%N.

  Definition finished_invariant (reg: ContextEnv.(env_t) R) :=
    let valid_val := Bits.to_N (ContextEnv.(getenv) reg valid) in
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    valid_val = 0%N -> finished_val = 0%N.

  Definition result_invariant (reg: ContextEnv.(env_t) R) :=
    let valid_val := Bits.to_N (ContextEnv.(getenv) reg valid) in
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    let result_val := Bits.to_N (ContextEnv.(getenv) reg result) in
    let op1_val := Bits.to_N (ContextEnv.(getenv) reg operand1) in
    let op2_val := Bits.to_N (ContextEnv.(getenv) reg operand2) in
    let n_step_val := Bits.to_N (ContextEnv.(getenv) reg n_step) in
    valid_val = 1%N ->
    finished_val = 0%N ->
    result_val = partial_mul op1_val op2_val n_step_val.

  Definition result_finished_invariant (reg: ContextEnv.(env_t) R) :=
    let finished_val := Bits.to_N (ContextEnv.(getenv) reg finished) in
    let result_val := Bits.to_N (ContextEnv.(getenv) reg result) in
    let op1_val := Bits.to_N (ContextEnv.(getenv) reg operand1) in
    let op2_val := Bits.to_N (ContextEnv.(getenv) reg operand2) in
    finished_val = 1%N ->
    (result_val = op1_val * op2_val)%N.

  Definition invariant reg :=
    step_invariant reg /\
    finished_invariant reg /\
    result_invariant reg /\
    result_finished_invariant reg.

  Lemma enq_preserves_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_enq =
      Some (action_log_new, v, Gamma_new) ->
      invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant,
           result_invariant, result_finished_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    repeat (split).
    - discriminate.
    - intros.
      unfold partial_mul. cbn.
      rewrite N.mod_1_r.
      ring.
    - intros.
      match goal with
      | [ H1: ?x = ?y, H2: _ -> ?x = ?z |- _ ] =>
        rewrite H2 in H1; [ discriminate | auto ]
      end.
  Qed.

  Lemma deq_preserves_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_deq =
      Some (action_log_new, v, Gamma_new) ->
      invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    repeat (split); auto || discriminate.
  Qed.

  Lemma step_preserves_finished_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
      Some (action_log_new, v, Gamma_new) ->
      finished_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    Bits_to_N_t;
    intros;
    match goal with
    | [H1: ?x = ?y, H2: ?x = ?z |- _ ] => rewrite H1 in H2; discriminate H2
    end.
  Qed.

  Lemma step_preserves_step_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
      Some (action_log_new, v, Gamma_new) ->
      step_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    Bits_to_N_t; try (assumption);
    rewrite Bits.to_N_of_N;
    lia_bits.
  Qed.

  (* The admitted subgoals should be handle by lia_bits *)
  Lemma step_preserves_result_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
      Some (action_log_new, v, Gamma_new) ->
      result_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant in *.
    interp_action_all_t;
    intros;
    Bits_to_N_t;
    unfold Sig32.n in *;
    try discriminate.
    match goal with
    | [ H: context[_ = partial_mul _ _ _] |- _ ] =>
      setoid_rewrite H; try assumption
    end; cbn in *.
    - rewrite Bits.to_N_of_N.
      + rewrite Bits.to_N_of_N; [ | lia_bits ].
        cbn. rewrite_all_hypotheses. cbn.
        rewrite partial_mul_step.
        rewrite_all_hypotheses.
        f_equal. cbn [N.b2n].
        admit.
      + admit.
    - rewrite Bits.to_N_of_N; [ | lia_bits ].
      rewrite partial_mul_step.
      rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      auto.
  Admitted.

  Lemma mul_to_partial_mul :
    forall n x y,
      (y < 2 ^ n)%N ->
      (x * y = partial_mul x y n)%N.
  Proof.
    intros.
    unfold partial_mul.
    rewrite N.mod_small; auto.
  Qed.

  Lemma step_preserves_result_finished_invariant :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
      Some (action_log_new, v, Gamma_new) ->
      result_finished_invariant (commit_update env (log_app action_log_new sched_log)).
  Proof.
    intros.
    unfold invariant, step_invariant, finished_invariant, result_invariant, result_finished_invariant in *.
    interp_action_all_t;
    intros;
    Bits_to_N_t;
    unfold Sig32.n in *;
    try match goal with
        | [ H1: ?x = ?y, H2: ?x = ?z |- _ ] =>
          rewrite H1 in H2; discriminate H2
        end;
    match goal with
    | [ H: context[_ = partial_mul _ _ _] |- _ ] =>
      setoid_rewrite H; try assumption
    end;
    cbn in *.
    - rewrite_all_hypotheses.
      rewrite Bits.to_N_of_N.
      + rewrite N.mod_small; [ | lia_bits ].
        rewrite (mul_to_partial_mul (N.of_nat Sig32.n) (Bits.to_N _) (Bits.to_N _)); [ | lia_bits ].
        cbn.
        assert (32 = 31 + 1)%N as H32S by reflexivity.
        rewrite H32S.
        rewrite partial_mul_step.
        repeat (f_equal; []).
        match goal with
        | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
          rewrite H1 in H2
        end.
        rewrite_all_hypotheses.
        reflexivity.
      + admit.
    - rewrite_all_hypotheses.
      rewrite (mul_to_partial_mul (N.of_nat Sig32.n)); [ | lia_bits ].
      cbn.
      assert (32 = 31 + 1)%N as H32S by reflexivity.
      rewrite H32S.
      rewrite partial_mul_step.
      repeat (f_equal; []).
      match goal with
      | [ H1: ?x = ?y, H2: context[N.testbit _ _] |- _ ] =>
        rewrite H1 in H2
      end.
      rewrite_all_hypotheses. cbn.
      rewrite N.mul_0_r. rewrite N.add_0_r.
      reflexivity.
    Admitted.

  Lemma enq_set_operands :
    forall (env: ContextEnv.(env_t) R) Gamma sched_log action_log action_log_new v Gamma_new,
      no_latest_writes action_log [operand1; operand2] ->
      interp_action env empty_sigma Gamma sched_log action_log typed_enq =
      Some (action_log_new, v, Gamma_new) ->
      latest_write action_log_new operand1 = Some (chd Gamma) /\
      latest_write action_log_new operand2 = Some (chd (ctl Gamma)).
  Proof.
    intros.
    interp_action_all_t.
    auto.
  Qed.

  Lemma step_keep_operands :
    forall (env: ContextEnv.(env_t) R) Gamma sched_log action_log action_log_new v Gamma_new,
      no_latest_writes action_log [operand1; operand2] ->
      interp_action env empty_sigma Gamma sched_log action_log typed_step =
      Some (action_log_new, v, Gamma_new) ->
      no_latest_writes action_log_new [operand1; operand2].
  Proof.
    intros.
    interp_action_all_t;
    auto.
  Qed.

  Lemma deq_result :
    forall env Gamma sched_log action_log action_log_new v Gamma_new,
      invariant (commit_update env sched_log) ->
      no_latest_writes action_log all_regs ->
      no_latest_writes sched_log all_regs ->
      interp_action env empty_sigma Gamma sched_log action_log typed_deq =
      Some (action_log_new, v, Gamma_new) ->
      let operand1_val := Bits.to_N (ContextEnv.(getenv) env operand1) in
      let operand2_val := Bits.to_N (ContextEnv.(getenv) env operand2) in
      (Bits.to_N v = operand1_val * operand2_val)%N.
  Proof.
    intros.
    unfold invariant, result_finished_invariant in *.
    interp_action_all_t.
    Bits_to_N_t.
    auto.
  Qed.

End MultiplierProofs.