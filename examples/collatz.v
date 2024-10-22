(*! Computing terms of the Collatz sequence (Coq version) !*)
Require Import Koika.Frontend.
Require Import Koika.TypedParsing.

Module Collatz.
  (*! We have one register ``r0``: !*)
  Inductive reg_t := r0.
  (*! …and two rules ``divide`` and ``multiply``: !*)
  Inductive rule_name_t := divide | multiply.

  Definition logsz := 4.
  Notation sz := (pow2 logsz).

  (*! ``r0`` is a register storing 2^4 = 16 bits: !*)
  Definition R r :=
    match r with
    | r0 => bits_t sz
    end.

  (*! ``r0`` is initialized to 18: !*)
  Definition r idx : R idx :=
    match idx with
    | r0 => Bits.of_nat sz 18
    end.

  Definition times_three : function R empty_Sigma :=
    <{ fun times_three (bs: bits_t 16) : bits_t 16 =>
         (bs << Ob~1) + bs }>.

  (*! Our first rule, ``divide``, reads from r0 and halves the result if it's even: !*)
  Program Definition _divide : action R empty_Sigma :=
    <{ let v := read0(r0) in
       let odd := v[Ob~0~0~0~0] in
       if !odd then
         write0(r0,v >> Ob~1)
       else
         fail }>.

  (*! Our second rule, ``multiply``, reads the output of ``divide`` and
      multiplies it by three and ads one if it is odd: !*)
  Program Definition _multiply : action R empty_Sigma :=
    <{ let v := read1(r0) in
       let odd := v[Ob~0~0~0~0] in
       if odd then
         write1(r0, times_three(v) + Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1)
       else
         fail }>.

  (*! The design's schedule defines the order in which rules should (appear to) run !*)
  Definition collatz : scheduler :=
    divide |> multiply |> done.

  (*! Rules are written in an untyped language, so we need to typecheck them: !*)
  Definition rules (r : rule_name_t) :=
    match r with
    | divide => _divide
    | multiply => _multiply
    end.

  (*! And now we can compute results: uncomment the ``Print`` commands below to show results. !*)

  Definition cr := ContextEnv.(create) r.

  Definition divide_result :=
    tc_compute (interp_action cr empty_sigma CtxEmpty log_empty log_empty
                              (rules divide)).

  (*! The output of ``divide`` when ``r0 = 18``: a write to ``r0`` with value ``0b1001 = 9``: !*)
  (* Print divide_result. *)

  Definition multiply_result :=
    tc_compute
      (let '(log, _, _) := must divide_result in
       interp_action cr empty_sigma CtxEmpty log_empty log (rules multiply)).

  (*! The output of ``multiply`` when ``r0 = 9``: a write to ``r0`` with value ``0b11100 = 28``: !*)
  (* Print multiply_result. *)

  Definition cycle_log :=
    tc_compute (interp_scheduler cr empty_sigma rules collatz).

  (*! The complete log over the first cycle: two writes to ``r0`` !*)
  (* Print cycle_log. *)

  Definition result :=
    tc_compute (commit_update cr cycle_log).

  (*! The values of the registers after the first cycle completes: ``r0 = 28`` !*)
  (* Print result. *)

  Definition external (r: rule_name_t) := false.

  Definition circuits :=
    compile_scheduler rules external collatz.

  Definition circuits_result :=
    tc_compute (interp_circuits empty_sigma circuits (lower_r (ContextEnv.(create) r))).

  (*! The same values computed by running compiled circuits: ``r0 = 28`` !*)
  (* Print circuits_result. *)

  Example test: circuits_result = Environments.map _ (fun _ => bits_of_value) result :=
    eq_refl.

  (*! This package configures compilation to C++ with Cuttlesim and Verilog with Kôika's verified compiler: !*)
  Definition package :=
    {| ip_koika := {| koika_reg_types := R;
                     koika_reg_init := r;
                     koika_ext_fn_types := empty_Sigma;
                     koika_rules := rules;
                     koika_rule_external := external;
                     koika_scheduler := collatz;
                     koika_module_name := "collatz" |};

       ip_sim := {| sp_ext_fn_specs := empty_ext_fn_props;
                   sp_prelude := None |};

       ip_verilog := {| vp_ext_fn_specs := empty_ext_fn_props |} |}.
End Collatz.

Require Import Koika.Testing.

(* Example for testing koika functions and actions using [TestingUtils.v] *)
Module Collatz_Test.
  Import Testing.
  Import Collatz.
  (*!
    If you need to assign inputs to the registers then here is
    how you can write a function to do so.
  !*)
  (* Definition r' n idx : R idx :=
    match idx with
    | r0 => Bits.of_nat sz n
    | r1 => Bits.of_nat sz n
    end. *)

  (*
   * This example checks if the value of register [r0]
   * is equal to 9 after executing divide once on the
   * register value assingment of r (r0 set to 18)
   *)
  Goal
    run_action r (rules divide)
    (fun ctxt =>
      let bits_r0 := ctxt.[r0] in
      Bits.to_nat bits_r0 = 9
    ).
  Proof.
    check.
  Defined.

  (*
   * This example checks the function times_three
   *)
  Goal
    (*
     * For functions, we have to add this boiler plate code.
     * It essentially type checks a function and turns it into an action.
     *)
    let func := times_three in
    (*
     * Passing the value 2 as input to our function
     *)
    let input := #{ ("bs", bits_t 16) => (Bits.of_nat 16 2) }# in

    run_function r input func.(int_body)
    (fun ctxt out =>
      let r0 := Bits.to_nat ctxt.[r0] in
      let out  := Bits.to_nat out in
      
      (*
       * We expect that the output is 3 times or input
       * and that the register value or r0 did not change
       *)
      r0 = 18 /\ out = 3 * 2
    ).
  Proof.
      check.
  Defined.

  (*
   * This example checks the overall output of a whole
   * cycle.
   *)
  Goal
    run_schedule r rules empty_sigma collatz
    (fun ctxt =>
      let bits_r0 := ctxt.[r0]           in
      let nat_r0  := Bits.to_nat bits_r0 in
      
      nat_r0 = (18/2)*3+1
    ).
  Proof.
    check.
  Defined.

End Collatz_Test.

(*! This is the entry point used by the compiler: !*)
Definition prog := Interop.Backends.register Collatz.package.
