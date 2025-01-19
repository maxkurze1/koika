(*! Language | Typed ASTs !*)
Require Export Koika.Common Koika.Environments Koika.Types Koika.Primitives.

Import PrimTyped PrimSignatures.

Section Syntax.
  Context {pos_t var_t rule_name_t fn_name_t reg_t ext_fn_t: Type}.
  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.

  Inductive action : tsig var_t -> type -> Type :=
  | Fail {sig} tau : action sig tau
  | Var {sig} {k: var_t} {tau: type}
        (m: member (k, tau) sig) : action sig tau
  | Const {sig} {tau: type}
          (cst: type_denote tau) : action sig tau
  | Assign {sig} {k: var_t} {tau: type}
           (m: member (k, tau) sig) (ex: action sig tau) : action sig unit_t
  | Seq {sig tau}
        (r1: action sig unit_t)
        (r2: action sig tau) : action sig tau
  | Bind {sig} {tau tau'}
         (var: var_t)
         (ex: action sig tau)
         (body: action (List.cons (var, tau) sig) tau') : action sig tau'
  | If {sig tau}
       (cond: action sig (bits_t 1))
       (tbranch fbranch: action sig tau) : action sig tau
  | Read {sig}
         (port: Port)
         (idx: reg_t): action sig (R idx)
  | Write {sig}
          (port: Port) (idx: reg_t)
          (value: action sig (R idx)) : action sig unit_t
  | Unop {sig}
          (fn: fn1)
          (arg1: action sig (arg1Sig (Sigma1 fn)))
    : action sig (retSig (Sigma1 fn))
  | Binop {sig}
          (fn: fn2)
          (arg1: action sig (arg1Sig (Sigma2 fn)))
          (arg2: action sig (arg2Sig (Sigma2 fn)))
    : action sig (retSig (Sigma2 fn))
  | ExternalCall {sig}
                 (fn: ext_fn_t)
                 (arg: action sig (arg1Sig (Sigma fn)))
    : action sig (retSig (Sigma fn))
  | InternalCall {sig tau}
                 (* TODO -- why does this list need to be reversed?? *)
                 {argspec : tsig var_t}
                 (fn : InternalFunction' fn_name_t (action argspec tau))
                 (args: context (fun k_tau => action sig (snd k_tau)) argspec)
    : action sig tau
  | APos {sig tau} (pos: pos_t) (a: action sig tau)
    : action sig tau.

  Fixpoint ctx_Forall {K} {V: K -> Type} (P: forall (k: K), V k -> Prop) {sig} (ctx: context V sig) :=
    match ctx with
    | CtxEmpty => True
    | CtxCons k v ctx => P k v /\ ctx_Forall P ctx
    end.

  Lemma action_ind_complete :
    forall P : forall (sig : tsig var_t) (tau : type), action sig tau -> Prop,

    (forall (sig : tsig var_t) (tau : type),
      P sig tau (Fail tau)) ->
    (forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig),
      P sig tau (Var m)) ->
    (forall (sig : tsig var_t) (tau : type) (cst : tau),
      P sig tau (Const cst)) ->
    (forall (sig : list (var_t * type)) (k : var_t) (tau : type) (m : member (k, tau) sig) (ex : action sig tau),
      P sig tau ex ->
      P sig unit_t (Assign m ex)) ->
    (forall (sig : tsig var_t) (tau : type) (r1 : action sig unit_t) (r2 : action sig tau),
      P sig unit_t r1 ->
      P sig tau r2 ->
      P sig tau (Seq r1 r2)) ->
    (forall (sig : tsig var_t) (tau tau' : type) (var : var_t) (ex : action sig tau) (body : action ((var, tau) :: sig) tau'),
      P sig tau ex ->
      P ((var, tau) :: sig) tau' body ->
      P sig tau' (Bind var ex body)) ->
    (forall (sig : tsig var_t) (tau : type) (cond : action sig (bits_t 1)) (tbranch : action sig tau) (fbranch : action sig tau),
      P sig (bits_t 1) cond ->
      P sig tau tbranch ->
      P sig tau fbranch ->
      P sig tau (If cond tbranch fbranch)) ->
    (forall (sig : tsig var_t) (port : Port) (idx : reg_t),
      P sig (R idx) (Read port idx)) ->
    (forall (sig : tsig var_t) (port : Port) (idx : reg_t) (value : action sig (R idx)),
      P sig (R idx) value -> P sig unit_t (Write port idx value)) ->
    (forall (sig : tsig var_t) (fn : fn1) (arg1 : action sig (arg1Sig (Sigma1 fn))),
      P sig (arg1Sig (Sigma1 fn)) arg1 ->
      P sig (retSig (Sigma1 fn)) (Unop fn arg1)) ->
    (forall (sig : tsig var_t) (fn : fn2) (arg1 : action sig (arg1Sig (Sigma2 fn))) (arg2 : action sig (arg2Sig (Sigma2 fn))),
      P sig (arg1Sig (Sigma2 fn)) arg1 ->
      P sig (arg2Sig (Sigma2 fn)) arg2 ->
      P sig (retSig (Sigma2 fn)) (Binop fn arg1 arg2)) ->
    (forall (sig : tsig var_t) (fn : ext_fn_t) (arg : action sig (arg1Sig (Sigma fn))),
      P sig (arg1Sig (Sigma fn)) arg ->
      P sig (retSig (Sigma fn)) (ExternalCall fn arg)) ->
    (forall (sig : tsig var_t) (tau : type) (argspec : tsig var_t) (fn : InternalFunction' fn_name_t (action argspec tau)) (args : context (fun k_tau : var_t * type => action sig (snd k_tau)) argspec),
      P argspec tau fn.(int_body) ->
      ctx_Forall (fun k_tau => P sig (snd k_tau)) args ->
      P sig tau (InternalCall fn args)) ->
    (forall (sig : tsig var_t) (tau : type) (pos : pos_t) (a : action sig tau),
      P sig tau a -> P sig tau (APos pos a)) ->
    forall (sig : tsig var_t) (tau : type) (a : action sig tau), P sig tau a.
  Proof.
    intros P H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
    fix IH 3.
    destruct a.
    - apply H1.
    - apply H2.
    - apply H3.
    - apply H4. auto.
    - apply H5; auto.
    - apply H6; auto.
    - apply H7; auto.
    - apply H8.
    - apply H9. auto.
    - apply H10. auto.
    - apply H11; auto.
    - apply H12. auto.
    - apply H13. auto. clear fn.
      induction args.
      + cbn. auto.
      + split. auto. assumption.
    - apply H14. auto.
  Qed.

  Definition rule := action nil unit_t.
End Syntax.

Arguments action pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma sig tau : assert.
Arguments rule pos_t var_t fn_name_t {reg_t ext_fn_t} R Sigma : assert.

Notation InternalFunction pos_t var_t fn_name_t R Sigma sig tau :=
  (InternalFunction' fn_name_t (action pos_t var_t fn_name_t R Sigma sig tau)).
